"""Minimal Redis-compatible storage on top of PostgreSQL (e.g. Neon).

Implements only the Redis commands main.py uses: ping, get, set (nx/ex), setex, delete,
keys (glob), incr, incrby, expire, hset, hget, lpush, ltrim. All values are returned as
str (like redis-py with decode_responses=True).
"""
import random
import threading

import psycopg2
import psycopg2.pool

_SCHEMA = """
CREATE TABLE IF NOT EXISTS kv (
    key text PRIMARY KEY,
    value text NOT NULL,
    expires_at timestamptz
);
CREATE INDEX IF NOT EXISTS kv_expires_idx ON kv (expires_at) WHERE expires_at IS NOT NULL;
CREATE TABLE IF NOT EXISTS kv_hash (
    name text NOT NULL,
    field text NOT NULL,
    value text NOT NULL,
    PRIMARY KEY (name, field)
);
CREATE TABLE IF NOT EXISTS kv_list (
    id bigserial PRIMARY KEY,
    key text NOT NULL,
    value text NOT NULL
);
CREATE INDEX IF NOT EXISTS kv_list_key_idx ON kv_list (key, id DESC);
"""

_LIVE = "(expires_at IS NULL OR expires_at > now())"


def _glob_to_like(pattern):
    out = []
    for ch in str(pattern):
        if ch == "*":
            out.append("%")
        elif ch == "?":
            out.append("_")
        elif ch in ("%", "_", "\\"):
            out.append("\\" + ch)
        else:
            out.append(ch)
    return "".join(out)


class PgRedis:
    def __init__(self, dsn, minconn=1, maxconn=8):
        self._pool = psycopg2.pool.ThreadedConnectionPool(minconn, maxconn, dsn)
        self._lock = threading.Lock()
        self._run(_SCHEMA, fetch=None)

    def _run(self, sql, params=None, fetch="all"):
        """Run one statement in autocommit mode; retry once on a dropped connection
        (serverless Postgres closes idle connections when the compute suspends)."""
        last = None
        for _ in range(2):
            conn = self._pool.getconn()
            broken = False
            try:
                conn.autocommit = True
                with conn.cursor() as cur:
                    cur.execute(sql, params)
                    if fetch == "all":
                        return cur.fetchall()
                    if fetch == "one":
                        return cur.fetchone()
                    return cur.rowcount
            except (psycopg2.OperationalError, psycopg2.InterfaceError) as e:
                broken = True
                last = e
            finally:
                self._pool.putconn(conn, close=broken)
        raise last

    def _maybe_cleanup(self):
        if random.random() < 0.01:
            try:
                self._run("DELETE FROM kv WHERE expires_at IS NOT NULL AND expires_at <= now()", fetch=None)
            except Exception:
                pass

    def ping(self):
        return self._run("SELECT 1", fetch="one")[0] == 1

    def get(self, key):
        row = self._run(f"SELECT value FROM kv WHERE key = %s AND {_LIVE}", (str(key),), fetch="one")
        return row[0] if row else None

    def set(self, key, value, nx=False, ex=None):
        key, value = str(key), str(value)
        if ex is not None:
            exp_sql = "now() + (%s || ' seconds')::interval"
            exp_params = (str(int(ex)),)
        else:
            exp_sql = "NULL"
            exp_params = ()
        if nx:
            row = self._run(
                f"INSERT INTO kv (key, value, expires_at) VALUES (%s, %s, {exp_sql}) "
                "ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value, expires_at = EXCLUDED.expires_at "
                "WHERE kv.expires_at IS NOT NULL AND kv.expires_at <= now() RETURNING 1",
                (key, value) + exp_params, fetch="one")
            self._maybe_cleanup()
            return True if row else None
        self._run(
            f"INSERT INTO kv (key, value, expires_at) VALUES (%s, %s, {exp_sql}) "
            "ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value, expires_at = EXCLUDED.expires_at",
            (key, value) + exp_params, fetch=None)
        self._maybe_cleanup()
        return True

    def setex(self, key, seconds, value):
        return self.set(key, value, ex=seconds)

    def delete(self, *keys):
        keys = [str(k) for k in keys]
        if not keys:
            return 0
        n = self._run("DELETE FROM kv WHERE key = ANY(%s)", (keys,), fetch=None)
        self._run("DELETE FROM kv_hash WHERE name = ANY(%s)", (keys,), fetch=None)
        self._run("DELETE FROM kv_list WHERE key = ANY(%s)", (keys,), fetch=None)
        return n

    def keys(self, pattern="*"):
        rows = self._run(
            f"SELECT key FROM kv WHERE key LIKE %s ESCAPE '\\' AND {_LIVE}",
            (_glob_to_like(pattern),))
        return [r[0] for r in rows]

    def incrby(self, key, amount=1):
        amount = int(amount)
        row = self._run(
            "INSERT INTO kv (key, value) VALUES (%s, %s) "
            "ON CONFLICT (key) DO UPDATE SET "
            "value = CASE WHEN kv.expires_at IS NOT NULL AND kv.expires_at <= now() "
            "THEN EXCLUDED.value ELSE ((kv.value)::bigint + %s)::text END, "
            "expires_at = CASE WHEN kv.expires_at IS NOT NULL AND kv.expires_at <= now() "
            "THEN NULL ELSE kv.expires_at END "
            "RETURNING value",
            (str(key), str(amount), amount), fetch="one")
        return int(row[0])

    def incr(self, key):
        return self.incrby(key, 1)

    def expire(self, key, seconds):
        n = self._run(
            f"UPDATE kv SET expires_at = now() + (%s || ' seconds')::interval WHERE key = %s AND {_LIVE}",
            (str(int(seconds)), str(key)), fetch=None)
        return bool(n)

    def hset(self, name, key=None, value=None, mapping=None):
        items = dict(mapping or {})
        if key is not None:
            items[key] = value
        for f, v in items.items():
            self._run(
                "INSERT INTO kv_hash (name, field, value) VALUES (%s, %s, %s) "
                "ON CONFLICT (name, field) DO UPDATE SET value = EXCLUDED.value",
                (str(name), str(f), str(v)), fetch=None)
        return len(items)

    def hget(self, name, key):
        row = self._run("SELECT value FROM kv_hash WHERE name = %s AND field = %s",
                        (str(name), str(key)), fetch="one")
        return row[0] if row else None

    def lpush(self, key, *values):
        for v in values:
            self._run("INSERT INTO kv_list (key, value) VALUES (%s, %s)", (str(key), str(v)), fetch=None)
        return len(values)

    def ltrim(self, key, start, stop):
        # Only the "keep the newest N" form is used (start == 0): keep entries 0..stop.
        keep = int(stop) + 1
        self._run(
            "DELETE FROM kv_list WHERE key = %s AND id < "
            "COALESCE((SELECT id FROM kv_list WHERE key = %s ORDER BY id DESC OFFSET %s LIMIT 1), 0)",
            (str(key), str(key), keep - 1), fetch=None)
        return True
