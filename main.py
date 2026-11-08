import os
import json
import requests
from datetime import datetime, timedelta, time as dtime
from flask import Flask, request, jsonify
import threading
from functools import wraps
import pytz
from apscheduler.schedulers.background import BackgroundScheduler
from apscheduler.triggers.cron import CronTrigger
from apscheduler.triggers.interval import IntervalTrigger
import redis
import atexit
import time
import random
import hashlib
import hmac
import csv
import re
import tempfile

from generator import MealGenerator, generate_user_daily_plan, WorkoutGenerator

app = Flask(__name__)
# If SECRET_KEY isn't set in the environment, fall back to a random key generated at
# startup (instead of a fixed guessable string). Note this means Flask sessions won't
# survive a restart unless SECRET_KEY is actually configured in production.
app.secret_key = os.getenv("SECRET_KEY", "").strip() or os.urandom(32).hex()

try:
    redis_url = os.getenv("REDIS_URL", "").strip()
    database_url = os.getenv("DATABASE_URL", "").strip()
    if redis_url:
        redis_client = redis.from_url(redis_url, decode_responses=True)
        redis_client.ping()
        redis_available = True
        print("✅ Redis connected")
    elif database_url:
        # Redis-compatible storage on PostgreSQL (e.g. Neon) - see pgkv.py.
        from pgkv import PgRedis
        redis_client = PgRedis(database_url)
        redis_client.ping()
        redis_available = True
        print("✅ Postgres storage connected")
    else:
        redis_client = None
        redis_available = False
        print("⚠️ REDIS_URL تنظیم نشده - local storage فعال شد")
except Exception as e:
    print(f"⚠️ Redis not available, using local storage | error: {e}")
    redis_client = None
    redis_available = False

local_users = {}
local_meals = {}
local_custom_meals = {}
local_custom_workouts = {}
local_tickets = {}
local_exercise_links = {}
local_polls = {}
local_poll_responses = {}

BLE_TOKEN = os.getenv("BLE_TOKEN")
ZIBAL_MERCHANT_ID = os.getenv("ZIBAL_MERCHANT", "").strip()
BASE_URL = os.getenv("BASE_URL", "").strip()
ZIBAL_CALLBACK_URL = os.getenv("ZIBAL_CALLBACK_URL", "").strip()
VIP_CHANNEL_LINK = os.getenv("VIP_CHANNEL_LINK", "").strip()
ZIBAL_PAYOUT_API_KEY = os.getenv("ZIBAL_PAYOUT_API_KEY", "").strip()

MONTHLY_PRICE = 999000  # تومان
SEMESTER_PRICE = 2999000  # تومان
YEARLY_PRICE = 4999000  # تومان

MONTHLY_DAYS = 30
SEMESTER_DAYS = 180
YEARLY_DAYS = 365

# Send a renewal reminder this many days before a paid subscription expires.
EXPIRY_REMINDER_DAYS_BEFORE = {3, 1}

BOT_LINK = "https://ble.ir/successplusbot"

ADMIN_CHAT_IDS = set([s.strip() for s in os.getenv("ADMIN_CHAT_IDS", "").split(",") if s.strip()])

def is_admin(chat_id):
    return str(chat_id) in ADMIN_CHAT_IDS

# Support-only staff: can view/reply to tickets, but NOT full admin commands
# (dashboard, broadcast, coupons, manual VIP grants, etc). Full admins (ADMIN_CHAT_IDS)
# automatically have support access too.
SUPPORT_ADMIN_CHAT_IDS = set([s.strip() for s in os.getenv("SUPPORT_ADMIN_CHAT_IDS", "").split(",") if s.strip()])

def is_support_staff(chat_id):
    return is_admin(chat_id) or str(chat_id) in SUPPORT_ADMIN_CHAT_IDS


# Shared secret used to verify that incoming /ble-webhook requests really come from Bale
# (set this same value when registering the webhook URL with Bale, e.g. as a query param
# ?secret=... or a header, depending on what Bale supports). If left empty, the webhook
# runs UNPROTECTED and anyone who knows the URL can impersonate any user, including admins.
BLE_WEBHOOK_SECRET = os.getenv("BLE_WEBHOOK_SECRET", "").strip()
if not BLE_WEBHOOK_SECRET:
    print("⚠️⚠️⚠️ BLE_WEBHOOK_SECRET تنظیم نشده - وب‌هوک بدون احراز هویت در معرض جعل درخواست است!", flush=True)

BROADCAST_DELAY = 0.5

meal_generator = MealGenerator(redis_client)
workout_generator = WorkoutGenerator(redis_client)

scheduler = BackgroundScheduler()

def add_log(message):
    try:
        print(message, flush=True)
        if redis_available:
            try:
                redis_client.lpush("logs", str(message))
                redis_client.ltrim("logs", 0, 999)
            except Exception:
                pass
    except Exception as e:
        print(f"log error: {e}", flush=True)

def redis_get_user(user_id):
    if redis_available:
        try:
            data = redis_client.get(f"user:{user_id}")
            return json.loads(data) if data else {}
        except Exception as e:
            add_log(f"redis_get_user error: {e}")
            return {}
    return local_users.get(str(user_id), {})

def redis_save_user(user_id, user_data):
    if redis_available:
        try:
            redis_client.set(f"user:{user_id}", json.dumps(user_data, ensure_ascii=False))
            return
        except Exception as e:
            add_log(f"redis_save_user error: {e}")
    local_users[str(user_id)] = user_data

def redis_get_meal(day_key):
    if redis_available:
        try:
            data = redis_client.get(f"meal:{day_key}")
            return json.loads(data) if data else {}
        except Exception as e:
            add_log(f"redis_get_meal error: {e}")
    return local_meals.get(day_key, {})

def redis_set_meal(day_key, plan):
    if redis_available:
        try:
            redis_client.setex(f"meal:{day_key}", 86400, json.dumps(plan, ensure_ascii=False))
            return
        except Exception as e:
            add_log(f"redis_set_meal error: {e}")
    local_meals[day_key] = plan

def redis_get_custom_meal(user_id, day, meal_type):
    if redis_available:
        try:
            data = redis_client.get(f"custom_meal:{user_id}:{day}:{meal_type}")
            return data if data else None
        except Exception as e:
            add_log(f"redis_get_custom_meal error: {e}")
    return local_custom_meals.get(str(user_id), {}).get(str(day), {}).get(meal_type)

def redis_set_custom_meal(user_id, day, meal_type, text):
    if redis_available:
        try:
            redis_client.set(f"custom_meal:{user_id}:{day}:{meal_type}", text)
        except Exception as e:
            add_log(f"redis_set_custom_meal error: {e}")
    if str(user_id) not in local_custom_meals:
        local_custom_meals[str(user_id)] = {}
    if str(day) not in local_custom_meals[str(user_id)]:
        local_custom_meals[str(user_id)][str(day)] = {}
    local_custom_meals[str(user_id)][str(day)][meal_type] = text

def redis_get_custom_workout(user_id, week, session):
    if redis_available:
        try:
            data = redis_client.get(f"custom_workout:{user_id}:{week}:{session}")
            return data if data else None
        except Exception as e:
            add_log(f"redis_get_custom_workout error: {e}")
    return local_custom_workouts.get(str(user_id), {}).get(str(week), {}).get(str(session))

def redis_set_custom_workout(user_id, week, session, exercises_text):
    if redis_available:
        try:
            redis_client.set(f"custom_workout:{user_id}:{week}:{session}", exercises_text)
        except Exception as e:
            add_log(f"redis_set_custom_workout error: {e}")
    if str(user_id) not in local_custom_workouts:
        local_custom_workouts[str(user_id)] = {}
    if str(week) not in local_custom_workouts[str(user_id)]:
        local_custom_workouts[str(user_id)][str(week)] = {}
    local_custom_workouts[str(user_id)][str(week)][str(session)] = exercises_text

def redis_get_exercise_links():
    if redis_available:
        try:
            data = redis_client.get("exercise_links")
            return json.loads(data) if data else {}
        except Exception as e:
            add_log(f"redis_get_exercise_links error: {e}")
    return local_exercise_links

def redis_set_exercise_links(links):
    if redis_available:
        try:
            redis_client.set("exercise_links", json.dumps(links, ensure_ascii=False))
        except Exception as e:
            add_log(f"redis_set_exercise_links error: {e}")
    local_exercise_links.update(links)

def redis_get_poll(poll_id):
    if redis_available:
        try:
            data = redis_client.get(f"poll:{poll_id}")
            return json.loads(data) if data else None
        except Exception as e:
            add_log(f"redis_get_poll error: {e}")
    return local_polls.get(str(poll_id))

def redis_set_poll(poll_id, poll_data):
    if redis_available:
        try:
            redis_client.set(f"poll:{poll_id}", json.dumps(poll_data, ensure_ascii=False))
        except Exception as e:
            add_log(f"redis_set_poll error: {e}")
    local_polls[str(poll_id)] = poll_data

def redis_get_poll_responses(poll_id):
    if redis_available:
        try:
            data = redis_client.get(f"poll_responses:{poll_id}")
            return json.loads(data) if data else {}
        except Exception as e:
            add_log(f"redis_get_poll_responses error: {e}")
    return local_poll_responses.get(str(poll_id), {})

def redis_set_poll_responses(poll_id, responses):
    if redis_available:
        try:
            redis_client.set(f"poll_responses:{poll_id}", json.dumps(responses, ensure_ascii=False))
        except Exception as e:
            add_log(f"redis_set_poll_responses error: {e}")
    local_poll_responses[str(poll_id)] = responses

def get_all_user_ids():
    if redis_available:
        try:
            keys = redis_client.keys("user:*")
            result = []
            for key in keys:
                try:
                    k = key.decode() if isinstance(key, bytes) else str(key)
                    result.append(k.split(":")[1])
                except Exception:
                    pass
            return result
        except Exception as e:
            add_log(f"get_all_user_ids error: {e}")
    return list(local_users.keys())

def find_user_by_referral_code(referral_code):
    referral_code = str(referral_code).strip()
    if redis_available:
        try:
            keys = redis_client.keys("user:*")
            for key in keys:
                try:
                    data = redis_client.get(key)
                    if not data:
                        continue
                    user_data = json.loads(data)
                    if str(user_data.get("referral_code", "")) == referral_code:
                        user_id = key.decode().split(":")[1] if isinstance(key, bytes) else str(key).split(":")[1]
                        return user_id
                except Exception:
                    continue
        except Exception as e:
            add_log(f"find_user_by_referral_code redis error: {e}")
    for user_id, user_data in local_users.items():
        if str(user_data.get("referral_code", "")) == referral_code:
            return str(user_id)
    return None

def find_user_by_track_id(track_id):
    """Fallback lookup used by zibal_webhook when Zibal's callback doesn't include orderId.
    Was previously called but never defined anywhere in this file (a NameError bug that
    would surface as '❌ خطای سرور' to the user despite a successful payment)."""
    track_id = str(track_id)
    if redis_available:
        try:
            keys = redis_client.keys("user:*")
            for key in keys:
                try:
                    data = redis_client.get(key)
                    if not data:
                        continue
                    user_data = json.loads(data)
                    if str(user_data.get("track_id", "")) == track_id:
                        user_id = key.decode().split(":")[1] if isinstance(key, bytes) else str(key).split(":")[1]
                        return user_id, user_data
                except Exception:
                    continue
        except Exception as e:
            add_log(f"find_user_by_track_id redis error: {e}")
    for user_id, user_data in local_users.items():
        if str(user_data.get("track_id", "")) == track_id:
            return str(user_id), user_data
    return None, None

def get_open_tickets():
    """Tickets currently waiting on an admin reply (status == 'open')."""
    tickets = []
    if redis_available:
        try:
            keys = redis_client.keys("ticket:*")
            for key in keys:
                try:
                    data = redis_client.get(key)
                    if data:
                        ticket = json.loads(data)
                        if ticket and isinstance(ticket, dict) and ticket.get("status") == "open":
                            tickets.append(ticket)
                except Exception as e:
                    add_log(f"get_open_tickets load error: {e}")
        except Exception as e:
            add_log(f"get_open_tickets redis error: {e}")
    else:
        for ticket_id, ticket in local_tickets.items():
            if ticket and isinstance(ticket, dict) and ticket.get("status") == "open":
                tickets.append(ticket)
    return sorted(tickets, key=lambda x: x.get("created_at", 0) if x and isinstance(x, dict) else 0)

def get_user_tickets(user_id):
    """All tickets (any status) belonging to a specific user, most recent first."""
    tickets = []
    if redis_available:
        try:
            keys = redis_client.keys("ticket:*")
            for key in keys:
                try:
                    data = redis_client.get(key)
                    if data:
                        ticket = json.loads(data)
                        if ticket and isinstance(ticket, dict) and str(ticket.get("user_id")) == str(user_id):
                            tickets.append(ticket)
                except Exception as e:
                    add_log(f"get_user_tickets load error: {e}")
        except Exception as e:
            add_log(f"get_user_tickets redis error: {e}")
    else:
        for ticket_id, ticket in local_tickets.items():
            if ticket and isinstance(ticket, dict) and str(ticket.get("user_id")) == str(user_id):
                tickets.append(ticket)
    return sorted(tickets, key=lambda x: x.get("updated_at", 0), reverse=True)

def get_ticket(ticket_id):
    if not ticket_id or not isinstance(ticket_id, str):
        return None
    if redis_available:
        try:
            data = redis_client.get(f"ticket:{ticket_id}")
            return json.loads(data) if data else None
        except Exception as e:
            add_log(f"get_ticket error: {e}")
            return None
    return local_tickets.get(str(ticket_id))

def save_ticket(ticket_id, ticket_data):
    if not ticket_id or not ticket_data or not isinstance(ticket_data, dict):
        add_log(f"save_ticket invalid input: ticket_id={ticket_id}, ticket_data={ticket_data}")
        return
    if redis_available:
        try:
            redis_client.set(f"ticket:{ticket_id}", json.dumps(ticket_data, ensure_ascii=False))
        except Exception as e:
            add_log(f"save_ticket error: {e}")
    local_tickets[str(ticket_id)] = ticket_data

def get_coupon_data(code):
    if redis_available:
        try:
            data = redis_client.get(f"coupons:{code}")
            return json.loads(data) if data else None
        except Exception:
            pass
    return None

def save_coupon_data(code, data):
    if redis_available:
        try:
            redis_client.set(f"coupons:{code}", json.dumps(data, ensure_ascii=False))
        except Exception:
            pass

def is_coupon_active(code):
    data = get_coupon_data(code)
    if not data:
        return False
    if data.get("disabled"):
        return False
    try:
        expiry = datetime.strptime(data["expiry"], "%Y-%m-%d").date()
        today = datetime.now(pytz.timezone("Asia/Tehran")).date()
        return expiry >= today and data.get("used_count", 0) < data.get("max_uses", 0)
    except Exception:
        return False

def preview_coupon_discount(code, original_price):
    """Read-only: computes the discounted price WITHOUT consuming a use of the coupon.
    Safe to call as many times as needed just to display a price."""
    data = get_coupon_data(code)
    if not data or not is_coupon_active(code):
        return original_price, None
    percent = data.get("percent", 0)
    discounted = int(original_price * (1 - percent / 100))
    return discounted, percent

def consume_coupon(code):
    """Actually increments used_count. Call this ONLY once a purchase is confirmed
    (in the Zibal webhook), never just for displaying a price - otherwise every time
    a user opens the subscription menu it silently burns through the coupon's max_uses."""
    data = get_coupon_data(code)
    if not data:
        return False
    data["used_count"] = data.get("used_count", 0) + 1
    save_coupon_data(code, data)
    return True

def get_trial_discount_percent(user_data):
    if not user_data or not user_data.get("trial_active"):
        return 0
    trial_start = user_data.get("trial_start")
    if not trial_start:
        return 0
    try:
        start = datetime.strptime(trial_start, "%Y-%m-%d").date()
        today = datetime.now(pytz.timezone("Asia/Tehran")).date()
        day_num = (today - start).days + 1
        if day_num == 1:
            return 60
        if day_num == 2:
            return 50
        if day_num == 3:
            return 40
        return 0
    except Exception:
        return 0

def prompt_coupon_or_pay(chat_id, user_id, user_data):
    """Shared by all three plan-selection callbacks. Previously each one forced the user
    to type a coupon code or literally type the word SKIP - a lot of people simply didn't
    know what to type and abandoned right here, between "picked a plan" and "started
    payment" (this showed up clearly as a ~65-70% drop-off in the conversion report).
    Now it's two tappable buttons instead of a free-text prompt."""
    active_coupons = [c for c in (redis_client.keys("coupons:*") if redis_available else []) if is_coupon_active(c.split(":")[1])]
    if active_coupons:
        keyboard = {"inline_keyboard": [
            [{"text": "🎟 کد تخفیف دارم", "callback_data": "enter_coupon"}],
            [{"text": "➡️ ادامه بدون کد تخفیف", "callback_data": "skip_coupon"}]
        ]}
        send_ble_message(chat_id, "اگه کد تخفیف داری وارد کن، وگرنه مستقیم برو مرحله‌ی پرداخت:", keyboard)
    else:
        user_data["applied_coupon"] = None
        redis_save_user(user_id, user_data)
        process_payment(chat_id, user_id)

REFERRED_USER_DISCOUNT_PERCENT = 10

def get_level_discount_percent(level):
    """A standing loyalty discount tied to the existing points/level system (levels
    1-10), so leveling up (from daily check-ins, challenges, etc.) has a real payoff
    beyond gamification and gives a reason to stay active during the trial."""
    if level >= 10:
        return 15
    if level >= 5:
        return 10
    return 0

def calculate_subscription_price(user_data, selected):
    """Read-only price calculation - safe to call repeatedly just to display prices.
    Returns (amount, days, desc). Use calculate_subscription_price_full() when you also
    need to know what produced the price (a coupon, referral, or level discount), e.g.
    to mark it consumed/used after a confirmed payment or to label it in a message."""
    amount, days, desc, _coupon_used, _source = calculate_subscription_price_full(user_data, selected)
    return amount, days, desc

def calculate_subscription_price_full(user_data, selected):
    if selected == "monthly":
        base = MONTHLY_PRICE
        days = MONTHLY_DAYS
        desc = "اشتراک ماهانه برنامه غذایی"
    elif selected == "semester":
        base = SEMESTER_PRICE
        days = SEMESTER_DAYS
        desc = "اشتراک ۶ ماهه برنامه غذایی"
    elif selected == "yearly":
        base = YEARLY_PRICE
        days = YEARLY_DAYS
        desc = "اشتراک سالانه برنامه غذایی"
    else:
        return None, None, None, None, None

    # Every applicable discount (trial, coupon, referral, loyalty level) is computed and
    # whichever gives the LOWEST price actually wins - so none of them can silently
    # cancel each other out or get ignored just because another one also applies.
    candidates = []  # (price, coupon_code_or_None, discount_source)

    trial_discount = get_trial_discount_percent(user_data)
    if trial_discount > 0:
        candidates.append((int(base * (1 - trial_discount / 100)), None, "trial"))

    coupon_code = user_data.get("applied_coupon")
    if coupon_code:
        coupon_price, coupon_percent = preview_coupon_discount(coupon_code, base)
        if coupon_percent is not None:
            candidates.append((coupon_price, coupon_code, "coupon"))

    if user_data.get("referrer_code") and not user_data.get("referred_discount_used"):
        candidates.append((int(base * (1 - REFERRED_USER_DISCOUNT_PERCENT / 100)), None, "referral"))

    level_discount = get_level_discount_percent(user_data.get("level", 1))
    if level_discount > 0:
        candidates.append((int(base * (1 - level_discount / 100)), None, "level"))

    if not candidates:
        return base, days, desc, None, None

    best_price, best_coupon, best_source = min(candidates, key=lambda c: c[0])
    return best_price, days, desc, best_coupon, best_source

    return base, days, desc, None, False

def rate_limit(key_prefix="rl", key_func=None, limit=20):
    """key_func, if given, is called with no args and should return an identity string
    (e.g. the sender's user_id) to rate-limit per-sender. Without it, falls back to
    request IP - which is WRONG for a bot webhook, since every update arrives from the
    messaging platform's own server IP, not the end user's IP: rate-limiting by IP there
    would throttle the whole bot for all users once combined traffic crosses the limit."""
    def decorator(f):
        @wraps(f)
        def decorated_function(*args, **kwargs):
            if not redis_available:
                return f(*args, **kwargs)
            identity = None
            if key_func:
                try:
                    identity = key_func()
                except Exception:
                    identity = None
            if not identity:
                identity = request.remote_addr or "unknown"
            key = f"{key_prefix}:{identity}"
            try:
                count = redis_client.incr(key)
                if count == 1:
                    redis_client.expire(key, 60)
                if count > limit:
                    return jsonify({"error": "Too Many Requests"}), 429
            except Exception:
                pass
            return f(*args, **kwargs)
        return decorated_function
    return decorator

def _ble_webhook_sender_id():
    update = request.get_json(silent=True) or {}
    if update.get("callback_query"):
        return str(update["callback_query"].get("from", {}).get("id", "")) or None
    if update.get("message"):
        return str(update["message"].get("from", {}).get("id", "")) or None
    return None

def send_ble_message(chat_id, text, keyboard=None, photo=None, parse_mode="HTML"):
    if not BLE_TOKEN:
        add_log("❌ BLE_TOKEN تنظیم نشده")
        return None
    if photo:
        url = f"https://tapi.bale.ai/bot{BLE_TOKEN}/sendPhoto"
        data = {"chat_id": str(chat_id), "photo": photo, "caption": str(text)[:1024], "parse_mode": parse_mode}
        if keyboard:
            data["reply_markup"] = json.dumps(keyboard, ensure_ascii=False)
    else:
        url = f"https://tapi.bale.ai/bot{BLE_TOKEN}/sendMessage"
        data = {"chat_id": str(chat_id), "text": str(text)[:4096], "parse_mode": parse_mode}
        if keyboard:
            data["reply_markup"] = json.dumps(keyboard, ensure_ascii=False)
    for attempt in range(3):
        try:
            response = requests.post(url, data=data, timeout=20)
            response.raise_for_status()
            return response.json()
        except requests.exceptions.RequestException as e:
            add_log(f"❌ Ble API Error (attempt {attempt + 1}/3): {e}")
    return None

def answer_callback(callback_query_id):
    if not BLE_TOKEN:
        return
    try:
        requests.post(f"https://tapi.bale.ai/bot{BLE_TOKEN}/answerCallbackQuery", data={"callback_query_id": callback_query_id}, timeout=10)
    except requests.exceptions.RequestException as e:
        add_log(f"❌ answerCallbackQuery Error: {e}")

def send_ble_document(chat_id, file_path, caption=None):
    if not BLE_TOKEN:
        add_log("❌ BLE_TOKEN تنظیم نشده")
        return None
    url = f"https://tapi.bale.ai/bot{BLE_TOKEN}/sendDocument"
    try:
        with open(file_path, "rb") as f:
            files = {"document": f}
            data = {"chat_id": str(chat_id)}
            if caption:
                data["caption"] = str(caption)[:1024]
            response = requests.post(url, data=data, files=files, timeout=30)
            response.raise_for_status()
            return response.json()
    except Exception as e:
        add_log(f"❌ send_ble_document Error: {e}")
        return None

def alert_admins(message, throttle_key=None, throttle_seconds=300):
    """Send critical error alerts to admins, with optional throttling so a repeating
    error doesn't spam every admin on every occurrence."""
    if throttle_key and redis_available:
        try:
            lock_key = f"alert_throttle:{throttle_key}"
            if not redis_client.set(lock_key, "1", nx=True, ex=throttle_seconds):
                return
        except Exception:
            pass
    for admin in ADMIN_CHAT_IDS:
        try:
            send_ble_message(admin, f"🚨 {message}")
        except Exception:
            pass

def acquire_run_lock(name, ttl_seconds):
    """Distributed lock so a scheduled job (weekly payout, daily broadcast, ...) only
    actually runs once even if this app is deployed with multiple workers/instances."""
    if not redis_available:
        return True
    try:
        return bool(redis_client.set(f"locks:{name}", "1", nx=True, ex=ttl_seconds))
    except Exception as e:
        add_log(f"⚠️ acquire_run_lock error for {name}: {e}")
        return True

local_counters = {}

def increment_counter(key, amount=1):
    """Simple persistent counter for lightweight funnel/conversion stats (offer views,
    plan selections, payment attempts, completed payments) - works with or without Redis."""
    if redis_available:
        try:
            redis_client.incrby(f"counter:{key}", amount)
            return
        except Exception as e:
            add_log(f"⚠️ increment_counter error for {key}: {e}")
    local_counters[key] = local_counters.get(key, 0) + amount

def get_counter(key):
    if redis_available:
        try:
            val = redis_client.get(f"counter:{key}")
            return int(val) if val else 0
        except Exception:
            return 0
    return local_counters.get(key, 0)

def get_today_tehran_date():
    return datetime.now(pytz.timezone("Asia/Tehran")).strftime("%Y-%m-%d")

def get_day_number(start_date):
    try:
        start = datetime.strptime(start_date, "%Y-%m-%d").date()
        today = datetime.now(pytz.timezone("Asia/Tehran")).date()
        return max(1, (today - start).days + 1)
    except Exception:
        return 1

def is_valid_int(text, min_value=None, max_value=None):
    try:
        value = int(str(text).strip())
        if min_value is not None and value < min_value:
            return None
        if max_value is not None and value > max_value:
            return None
        return value
    except Exception:
        return None

def next_7am_tehran(after_datetime=None):
    tz = pytz.timezone("Asia/Tehran")
    now = after_datetime.astimezone(tz) if after_datetime else datetime.now(tz)
    run = now.replace(hour=7, minute=0, second=0, microsecond=0)
    if now >= run:
        run = run + timedelta(days=1)
    return run

def is_subscription_active(user_data):
    if not user_data.get("paid"):
        return False
    paid_date_str = user_data.get("paid_date")
    if not paid_date_str:
        return False
    try:
        paid_date = datetime.strptime(paid_date_str, "%Y-%m-%d").date()
        today = datetime.now(pytz.timezone("Asia/Tehran")).date()
        subscription_days = user_data.get("subscription_days", 30)
        return (today - paid_date).days < subscription_days
    except Exception:
        return False

def get_main_keyboard(profile_completed=False, paid_active=False):
    keyboard = [
        [{"text": "📅 برنامه امروز"}, {"text": "📊 ماکروها"}],
        [{"text": "👤 پروفایل من"}, {"text": "💳 اشتراک ویژه"}],
        [{"text": "🆘 پشتیبانی"}, {"text": "📋 تیکت‌های من"}]
    ]
    if profile_completed:
        keyboard.append([{"text": "🏋️ برنامه تمرینی"}, {"text": "🏆 چالش‌ها"}, {"text": "💰 کسب درآمد"}])
        keyboard.insert(0, [{"text": "📝 ویرایش اطلاعات"}])
    else:
        keyboard.insert(0, [{"text": "📝 ثبت اطلاعات"}])
    if paid_active:
        keyboard.insert(1, [{"text": "✏️ شخصی‌سازی برنامه"}])
    return {"keyboard": keyboard, "resize_keyboard": True}

ALL_FLOW_FLAGS = ("step", "custom_step", "support_step", "poll_step",
                   "admin_dashboard_step", "admin_exercise_step", "admin_reply_step", "bank_step")

def clear_flow_flags(user_data, keep=None, chat_id=None):
    """Clear every multi-step-flow flag except `keep`, so starting one flow (support,
    coupon entry, poll creation, bank info, onboarding, ...) can never be silently
    hijacked by a leftover flag from a DIFFERENT flow the same person abandoned earlier.

    This bug bit multiple features because each one only checked its own flag in
    isolation and none of them cleared the others: a user mid-onboarding could get
    swallowed by a stale bank_step, a coupon-code entry could get swallowed by a stale
    poll_step, and an admin creating a broadcast could have their message misrouted into
    a leftover poll flow. All of these are the same root cause.

    Pass chat_id to also clear the admin's separate broadcast hash (it lives outside
    user_data), since that flow can just as easily be left dangling as any of these.
    """
    for flag in ALL_FLOW_FLAGS:
        if flag != keep:
            user_data.pop(flag, None)
    if chat_id is not None and redis_available:
        try:
            redis_client.delete(f"admin:broadcast:{chat_id}")
        except Exception:
            pass

def start_onboarding(chat_id, user_id):
    existing = redis_get_user(user_id) or {}
    user_data = {**existing, "chat_id": str(chat_id), "user_id": str(user_id), "step": "age", "paid": existing.get("paid", False), "start_date": existing.get("start_date", get_today_tehran_date())}
    # See clear_flow_flags() above for why this matters.
    clear_flow_flags(user_data, keep="step", chat_id=chat_id)
    if not user_data.get("referral_code"):
        user_data["referral_code"] = hashlib.md5(str(user_id).encode()).hexdigest()[:8].upper()
    user_data["wallet"] = user_data.get("wallet", 0)
    user_data["points"] = user_data.get("points", 0)
    user_data["level"] = calculate_level(user_data["points"])
    redis_save_user(user_id, user_data)
    send_ble_message(chat_id, "👤 سن خود را وارد کنید (عدد بین 10 تا 80):")

def show_gender_keyboard(chat_id):
    keyboard = {"inline_keyboard": [[{"text": "👨 مرد", "callback_data": "gender_male"}], [{"text": "👩 زن", "callback_data": "gender_female"}]]}
    send_ble_message(chat_id, "جنسیت خود را انتخاب کنید:", keyboard)

def show_goal_keyboard(chat_id):
    keyboard = {"inline_keyboard": [[{"text": "🔥 کاهش وزن", "callback_data": "goal_loss"}], [{"text": "💪 افزایش حجم", "callback_data": "goal_gain"}], [{"text": "⚖️ حفظ تناسب", "callback_data": "goal_keep"}]]}
    send_ble_message(chat_id, "هدف خود را انتخاب کنید:", keyboard)

def show_diet_keyboard(chat_id):
    keyboard = {"inline_keyboard": [[{"text": "🍽️ معمولی", "callback_data": "diet_normal"}], [{"text": "🌱 گیاهی", "callback_data": "diet_vegetarian"}], [{"text": "🥑 کتو", "callback_data": "diet_keto"}], [{"text": "🏛️ مدیترانه‌ای", "callback_data": "diet_mediterranean"}]]}
    send_ble_message(chat_id, "نوع رژیم غذایی را انتخاب کنید:", keyboard)

def show_activity_keyboard(chat_id):
    keyboard = {"inline_keyboard": [[{"text": "🪑 سبک", "callback_data": "activity_light"}], [{"text": "🚶 متوسط", "callback_data": "activity_medium"}], [{"text": "🏋️ سنگین", "callback_data": "activity_heavy"}]]}
    send_ble_message(chat_id, "سطح فعالیت روزانه را انتخاب کنید:", keyboard)

def send_profile_summary(chat_id, user_data):
    paid_active = is_subscription_active(user_data)
    referral_link = f"{BOT_LINK}?ref={user_data.get('referral_code', '')}"
    level = user_data.get("level", 1)
    current_level_discount = get_level_discount_percent(level)
    if current_level_discount > 0:
        level_note = f"⭐ سطح: {level} (🎉 {current_level_discount}% تخفیف دائمی خرید اشتراک فعال است)\n"
    elif level >= 5:
        level_note = f"⭐ سطح: {level} (به سطح ۱۰ برس تا تخفیف دائمی به ۱۵٪ برسه)\n"
    else:
        level_note = f"⭐ سطح: {level} (به سطح ۵ برس تا ۱۰٪ تخفیف دائمی روی خرید اشتراک بگیری)\n"
    text = (f"👤 پروفایل شما:\n"
            f"🎂 سن: {user_data.get('age', '-')}\n"
            f"⚧ جنسیت: {user_data.get('gender', '-')}\n"
            f"⚖️ وزن: {user_data.get('weight', '-')} کیلوگرم\n"
            f"📏 قد: {user_data.get('height', '-')} سانتی‌متر\n"
            f"🎯 هدف: {user_data.get('goal', '-')}\n"
            f"🍽️ رژیم: {user_data.get('diet_type', '-')}\n"
            f"📊 فعالیت: {user_data.get('activity', '-')}\n"
            f"🔥 کالری روزانه: {user_data.get('bmr', '-')} کیلوکالری\n"
            f"🏆 امتیاز: {user_data.get('points', 0)}\n"
            f"{level_note}"
            f"💰 کیف پول: {user_data.get('wallet', 0):,} تومان\n"
            f"💵 درآمد کل رفرال: {user_data.get('referral_total_earned', 0):,} تومان ({user_data.get('referral_paid_count', 0)} نفر)\n"
            f"🔗 لینک ارجاع: {referral_link}")
    if user_data.get("bank_card") and user_data.get("bank_sheba"):
        text += "\n💳 اطلاعات بانکی تنظیم شده."
    else:
        text += "\n⚠️ اطلاعات بانکی تنظیم نشده (برای تسویه)."
    keyboard = {"inline_keyboard": [
        [{"text": "⚙️ تنظیمات بانکی", "callback_data": "set_bank"}],
        [{"text": "🧾 تاریخچه پرداخت", "callback_data": "payment_history"}]
    ]}
    send_ble_message(chat_id, text, keyboard)

def start_customization(chat_id, user_id):
    user_data = redis_get_user(user_id)
    if not is_subscription_active(user_data):
        send_ble_message(chat_id, "این قابلیت فقط برای کاربران با اشتراک فعال است.")
        return
    keyboard = {"inline_keyboard": [
        [{"text": "🍽️ شخصی‌سازی برنامه غذایی", "callback_data": "custom_meal"}],
        [{"text": "🏋️ شخصی‌سازی برنامه تمرینی", "callback_data": "custom_workout"}],
        [{"text": "🔙 بازگشت", "callback_data": "custom_back"}]
    ]}
    send_ble_message(chat_id, "چه برنامه‌ای می‌خواهید شخصی‌سازی کنید؟", keyboard)

def start_custom_meal(chat_id, user_id):
    keyboard = {"inline_keyboard": []}
    for day in range(1, 8):
        keyboard["inline_keyboard"].append([{"text": f"روز {day}", "callback_data": f"custom_meal_day_{day}"}])
    keyboard["inline_keyboard"].append([{"text": "🔙 بازگشت", "callback_data": "custom_back"}])
    send_ble_message(chat_id, "روز مورد نظر برای شخصی‌سازی برنامه غذایی را انتخاب کنید:", keyboard)

def select_meal_type(chat_id, day):
    keyboard = {"inline_keyboard": [
        [{"text": "صبحانه", "callback_data": f"custom_meal_type_{day}_breakfast"}],
        [{"text": "ناهار", "callback_data": f"custom_meal_type_{day}_lunch"}],
        [{"text": "شام", "callback_data": f"custom_meal_type_{day}_dinner"}],
        [{"text": "میان‌وعده", "callback_data": f"custom_meal_type_{day}_snack"}],
        [{"text": "🔙 بازگشت", "callback_data": "custom_meal"}]
    ]}
    send_ble_message(chat_id, f"برای روز {day}، نوع وعده را انتخاب کنید:", keyboard)

def input_custom_meal_text(chat_id, user_id, day, meal_type):
    user_data = redis_get_user(user_id)
    user_data["custom_step"] = f"meal_{day}_{meal_type}"
    clear_flow_flags(user_data, keep="custom_step", chat_id=chat_id)
    redis_save_user(user_id, user_data)
    send_ble_message(chat_id, f"متن جدید برای {meal_type} روز {day} را وارد کنید:")

def save_custom_meal(user_id, day, meal_type, text):
    redis_set_custom_meal(user_id, day, meal_type, text)

def start_custom_workout(chat_id, user_id):
    keyboard = {"inline_keyboard": []}
    for week in range(1, 5):
        keyboard["inline_keyboard"].append([{"text": f"هفته {week}", "callback_data": f"custom_workout_week_{week}"}])
    keyboard["inline_keyboard"].append([{"text": "🔙 بازگشت", "callback_data": "custom_back"}])
    send_ble_message(chat_id, "هفته مورد نظر برای شخصی‌سازی برنامه تمرینی را انتخاب کنید:", keyboard)

def select_session_type(chat_id, week):
    keyboard = {"inline_keyboard": []}
    for session in range(1, 5):
        keyboard["inline_keyboard"].append([{"text": f"جلسه {session}", "callback_data": f"custom_workout_session_{week}_{session}"}])
    keyboard["inline_keyboard"].append([{"text": "🔙 بازگشت", "callback_data": "custom_workout"}])
    send_ble_message(chat_id, f"برای هفته {week}، جلسه را انتخاب کنید:", keyboard)

def input_custom_workout_text(chat_id, user_id, week, session):
    user_data = redis_get_user(user_id)
    user_data["custom_step"] = f"workout_{week}_{session}"
    clear_flow_flags(user_data, keep="custom_step", chat_id=chat_id)
    redis_save_user(user_id, user_data)
    send_ble_message(chat_id, f"لیست تمرین‌ها برای جلسه {session} هفته {week} را با فرمت زیر وارد کنید:\n\nتمرین۱ — ست×تکرار (یادداشت)\nتمرین۲ — ست×تکرار (یادداشت)\n...")

def save_custom_workout(user_id, week, session, exercises_text):
    redis_set_custom_workout(user_id, week, session, exercises_text)

def send_referral_info(chat_id, user_id):
    user_data = redis_get_user(user_id)
    referral_link = f"{BOT_LINK}?ref={user_data.get('referral_code', '')}"
    wallet = user_data.get('wallet', 0)
    total_earned = user_data.get('referral_total_earned', 0)
    referred_count = user_data.get('referral_paid_count', 0)
    text = (f"💰 کسب درآمد از طریق ارجاع:\n\n"
            f"🔗 لینک ارجاع شما:\n{referral_link}\n\n"
            f"📋 نحوه کار:\n"
            f"- لینک خود را برای دوستان ارسال کنید.\n"
            f"- اگر آنها اشتراک تهیه کنند، ۲۰% مبلغ اشتراک به کیف پول شما اضافه می‌شود.\n"
            f"- تسویه اتوماتیک هر شنبه (اگر کیف پول >= ۱۰۰۰ تومان).\n\n"
            f"👥 تعداد دعوت‌شده‌های پرداخت‌کننده: {referred_count} نفر\n"
            f"💵 درآمد کل تاکنون: {total_earned:,} تومان\n"
            f"💰 کیف پول فعلی (در انتظار تسویه): {wallet:,} تومان\n\n"
            f"⚙️ اطلاعات بانکی خود را در پروفایل تنظیم کنید تا تسویه فعال شود.")
    send_ble_message(chat_id, text)

def send_payment_history(chat_id, user_id):
    user_data = redis_get_user(user_id) or {}
    history = user_data.get("payment_history", [])
    if not history:
        send_ble_message(chat_id, "هنوز پرداختی ثبت نشده است.")
        return
    lines = ["🧾 تاریخچه پرداخت‌های شما:\n"]
    for h in reversed(history[-10:]):
        coupon_note = f" (کوپن {h['coupon']})" if h.get("coupon") else ""
        lines.append(f"📅 {h.get('date', '-')} | {h.get('amount', 0):,} تومان | {h.get('days', '-')} روز{coupon_note}")
    send_ble_message(chat_id, "\n".join(lines))

STATUS_LABELS_FA = {"open": "🟡 در انتظار پاسخ", "answered": "🟢 پاسخ داده شده", "closed": "⚪ بسته‌شده"}

def send_my_tickets(chat_id, user_id):
    tickets = get_user_tickets(user_id)
    if not tickets:
        send_ble_message(chat_id, "شما هنوز تیکتی برای پشتیبانی ثبت نکرده‌اید.")
        return
    lines = ["📋 تیکت‌های اخیر شما:\n"]
    for t in tickets[:10]:
        ticket_id = t.get("ticket_id", "-")
        status = STATUS_LABELS_FA.get(t.get("status"), t.get("status", "-"))
        msgs = t.get("messages", [])
        last_msg = msgs[-1] if msgs else {}
        snippet = (last_msg.get("text") or "(عکس)").strip()
        if len(snippet) > 60:
            snippet = snippet[:60] + "…"
        lines.append(f"#{ticket_id} | {status}\nآخرین پیام: {snippet}\n")
    if len(tickets) > 10:
        lines.append(f"…و {len(tickets) - 10} تیکت قدیمی‌تر دیگر.")
    send_ble_message(chat_id, "\n".join(lines))

def send_daily_plan_with_trial_nudge(chat_id, user_id):
    """During the 3-day free trial, send the daily plan AND actively tell the user
    what today's discount is. Previously the shrinking-discount mechanic
    (get_trial_discount_percent: 60%/50%/40%) existed only in the pricing formula and
    was never actually announced - a user would only see it if they happened to open
    "💳 اشتراک ویژه" themselves. Most people never did, so the urgency never worked."""
    send_daily_plan(chat_id, user_id)
    user_data = redis_get_user(user_id) or {}
    # Tracked so schedule_trial_jobs()'s startup catch-up logic knows whether today's
    # message already went out (and doesn't send it twice).
    user_data["trial_last_sent_date"] = datetime.now(pytz.timezone("Asia/Tehran")).strftime("%Y-%m-%d")
    redis_save_user(user_id, user_data)
    discount = get_trial_discount_percent(user_data)
    if discount > 0:
        kb = {"inline_keyboard": [[{"text": "💳 همین حالا با این تخفیف بگیر", "callback_data": "renew_subscription"}]]}
        if discount >= 60:
            note = "امروز تخفیف اشتراکت بیشترین مقداره - فردا کمتر می‌شه."
        elif discount >= 50:
            note = "امروز روز دومه - تخفیفت کمتر از دیروز شد، فردا هم کمتر می‌شه."
        else:
            note = "امروز آخرین روزیه که این تخفیف رو داری - از فردا تمومه."
        send_ble_message(chat_id, f"⏰ {discount}٪ تخفیف اشتراک ویژه هنوز فعاله. {note}", kb)

def schedule_trial_jobs(user_id, chat_id):
    try:
        user_data = redis_get_user(user_id) or {}
        tz = pytz.timezone("Asia/Tehran")
        now = datetime.now(tz)
        today = now.date()

        # BUG FIX: this function used to unconditionally reset trial_start/trial_end to
        # "today"/"today+2" every single time it ran - including when
        # restore_scheduled_jobs_on_startup() calls it again after every redeploy. Since
        # APScheduler's default job store is in-memory and loses all scheduled jobs on
        # restart, restore_scheduled_jobs_on_startup() re-registers each trial user's job
        # on every boot - and during active development we redeploy many times a day, so
        # this was silently resetting every trial user's clock back to "day 1" on every
        # single deploy, extending trials indefinitely and never letting anyone actually
        # reach day 2/3. Now it only initializes trial_start/trial_end the FIRST time.
        if user_data.get("trial_start") and user_data.get("trial_end"):
            trial_start = datetime.strptime(user_data["trial_start"], "%Y-%m-%d").date()
            trial_end = datetime.strptime(user_data["trial_end"], "%Y-%m-%d").date()
        else:
            trial_start = today
            trial_end = (now + timedelta(days=2)).date()
            user_data["trial_start"] = trial_start.strftime("%Y-%m-%d")
            user_data["trial_end"] = trial_end.strftime("%Y-%m-%d")
        user_data["trial_active"] = True
        redis_save_user(user_id, user_data)

        next_run = next_7am_tehran()
        end_run = tz.localize(datetime.combine(trial_end, dtime(7, 0)))
        job_id = f"trial_daily_{user_id}"
        try:
            scheduler.add_job(send_daily_plan_with_trial_nudge,
                              trigger=CronTrigger(hour=7, minute=0, timezone="Asia/Tehran"),
                              args=(chat_id, user_id),
                              id=job_id,
                              replace_existing=True,
                              start_date=next_run,
                              end_date=end_run)
            add_log(f"⏱ scheduled trial daily for user {user_id} from {next_run} to {end_run}")
        except Exception as e:
            add_log(f"❌ schedule_trial_jobs add_job error: {e}")

        # Catch-up: if the app was down/restarting exactly around 7am (very plausible
        # during active development with frequent redeploys - each one wipes the
        # in-memory scheduler), the day's cron occurrence for a user already past their
        # start date can be silently skipped and pushed to tomorrow.
        #
        # IMPORTANT: this window is deliberately narrow (7:00-7:59 only), NOT "any time
        # after 7am". An earlier version used `now.hour >= 7`, which matches nearly the
        # entire day - since schedule_trial_jobs() also runs on every redeploy (via
        # restore_scheduled_jobs_on_startup), that meant the FIRST redeploy of any given
        # day (7am through 11pm) would immediately fire the daily message at whatever
        # random time that redeploy happened, consuming the day's send. During active
        # development (many redeploys per day) the real 7am cron essentially never got a
        # chance to fire naturally, and a user watching specifically at 7am would see
        # nothing (because it already went out hours earlier, or will go out whenever the
        # next redeploy happens) - exactly this bug report.
        today_str = today.strftime("%Y-%m-%d")
        if (trial_start <= today <= trial_end and 7 <= now.hour < 8
                and user_data.get("trial_last_sent_date") != today_str):
            send_daily_plan_with_trial_nudge(chat_id, user_id)

        cleanup_time = end_run + timedelta(minutes=1)
        cleanup_job_id = f"trial_cleanup_{user_id}"
        def _cleanup_trial(u_id=user_id):
            try:
                u = redis_get_user(u_id) or {}
                u["trial_active"] = False
                redis_save_user(u_id, u)
                if u.get("chat_id"):
                    kb = {"inline_keyboard": [[{"text": "💳 مشاهده و خرید اشتراک", "callback_data": "renew_subscription"}]]}
                    send_ble_message(u["chat_id"], "⏳ دورهٔ آزمایشی شما به پایان رسید. برای ادامه دریافت برنامه، لطفاً اشتراک تهیه کنید.", kb)
                add_log(f"✅ trial cleaned up for {u_id}")
            except Exception as e:
                add_log(f"❌ _cleanup_trial error: {e}")

        try:
            scheduler.add_job(_cleanup_trial, trigger='date', run_date=cleanup_time, id=cleanup_job_id, replace_existing=True)
        except Exception as e:
            add_log(f"❌ schedule_trial_jobs cleanup add_job error: {e}")

    except Exception as e:
        add_log(f"❌ schedule_trial_jobs error: {e}")

def schedule_weekly_workout_for_paid(user_id, chat_id):
    try:
        first_run = next_7am_tehran()
        job_id = f"weekly_workout_{user_id}"
        try:
            scheduler.add_job(send_workout_program,
                              trigger=IntervalTrigger(days=7, start_date=first_run),
                              args=(chat_id, user_id),
                              id=job_id,
                              replace_existing=True)
            add_log(f"⏱ scheduled weekly workout for user {user_id} starting {first_run}")
        except Exception as e:
            add_log(f"❌ schedule_weekly_workout_for_paid add_job error: {e}")
    except Exception as e:
        add_log(f"❌ schedule_weekly_workout_for_paid error: {e}")

def cancel_trial_jobs(user_id):
    try:
        job_id = f"trial_daily_{user_id}"
        if scheduler.get_job(job_id):
            scheduler.remove_job(job_id)
        cleanup_id = f"trial_cleanup_{user_id}"
        if scheduler.get_job(cleanup_id):
            scheduler.remove_job(cleanup_id)
        add_log(f"♻️ canceled trial jobs for {user_id}")
    except Exception:
        pass

def restore_scheduled_jobs_on_startup():
    try:
        users = get_all_user_ids()
        tz = pytz.timezone("Asia/Tehran")
        for user_id in users:
            u = redis_get_user(user_id) or {}
            chat_id = u.get("chat_id")
            if not chat_id:
                continue
            if u.get("trial_active") and u.get("trial_end"):
                try:
                    end_date = datetime.strptime(u["trial_end"], "%Y-%m-%d").date()
                    today = datetime.now(tz).date()
                    if end_date >= today:
                        schedule_trial_jobs(user_id, chat_id)
                except Exception:
                    pass
            if u.get("paid") and is_subscription_active(u):
                schedule_weekly_workout_for_paid(user_id, chat_id)
    except Exception as e:
        add_log(f"❌ restore_scheduled_jobs_on_startup error: {e}")

def create_zibal_payment(user_id, amount_toman):
    amount_rial = amount_toman * 10
    if not ZIBAL_MERCHANT_ID:
        return {"ok": False, "message": "ZIBAL_MERCHANT تنظیم نشده است."}
    callback_url = ZIBAL_CALLBACK_URL or (f"{BASE_URL}/zibal-webhook" if BASE_URL else "")
    if not callback_url:
        return {"ok": False, "message": "ZIBAL_CALLBACK_URL یا BASE_URL تنظیم نشده است."}
    payload = {"merchant": ZIBAL_MERCHANT_ID, "amount": int(amount_rial), "callbackUrl": callback_url, "description": f"اشتراک برنامه غذایی - کاربر {user_id}", "orderId": str(user_id)}
    try:
        add_log(f"💳 Zibal request payload: {payload}")
        response = requests.post("https://gateway.zibal.ir/v1/request", json=payload, timeout=20)
        response.raise_for_status()
        data = response.json()
        add_log(f"💳 Zibal request response: {data}")
        if data.get("result") == 100 and data.get("trackId"):
            track_id = str(data["trackId"])
            payment_url = f"https://gateway.zibal.ir/start/{track_id}"
            return {"ok": True, "track_id": track_id, "payment_url": payment_url}
        return {"ok": False, "message": f"خطا از زیبال: result={data.get('result')} message={data.get('message','')}"}
    except requests.exceptions.RequestException as e:
        add_log(f"❌ Zibal Request Error: {e}")
        return {"ok": False, "message": f"خطا در ارتباط با زیبال: {e}"}
    except Exception as e:
        add_log(f"❌ create_zibal_payment Error: {e}")
        return {"ok": False, "message": f"خطای داخلی پرداخت: {e}"}

def verify_zibal_payment(track_id):
    if not ZIBAL_MERCHANT_ID:
        return {"ok": False, "message": "ZIBAL_MERCHANT تنظیم نشده است."}
    payload = {"merchant": ZIBAL_MERCHANT_ID, "trackId": str(track_id)}
    try:
        response = requests.post("https://gateway.zibal.ir/v1/verify", json=payload, timeout=20)
        response.raise_for_status()
        data = response.json()
        add_log(f"✅ Zibal verify response: {data}")
        if data.get("result") == 100:
            return {"ok": True, "data": data}
        return {"ok": False, "message": f"verify failed: {data}"}
    except requests.exceptions.RequestException as e:
        add_log(f"❌ Zibal Verify Error: {e}")
        return {"ok": False, "message": str(e)}
    except Exception as e:
        add_log(f"❌ verify_zibal_payment Error: {e}")
        return {"ok": False, "message": str(e)}

def payout_zibal(amount_toman, card_number, sheba):
    if not ZIBAL_PAYOUT_API_KEY:
        return {"ok": False, "message": "ZIBAL_PAYOUT_API_KEY تنظیم نشده است."}
    amount_rial = amount_toman * 10
    payload = {
        "amount": int(amount_rial),
        "cardNumber": card_number,
        "iban": sheba,
        "description": "تسویه ریفرال",
        "merchant": ZIBAL_MERCHANT_ID
    }
    headers = {"Authorization": f"Bearer {ZIBAL_PAYOUT_API_KEY}"}
    try:
        response = requests.post("https://gateway.zibal.ir/v1/payout", json=payload, headers=headers, timeout=20)
        response.raise_for_status()
        data = response.json()
        if data.get("result") == 100:
            return {"ok": True, "data": data}
        return {"ok": False, "message": f"payout failed: {data}"}
    except requests.exceptions.RequestException as e:
        add_log(f"❌ Zibal Payout Error: {e}")
        return {"ok": False, "message": str(e)}
    except Exception as e:
        add_log(f"❌ payout_zibal Error: {e}")
        return {"ok": False, "message": str(e)}

def process_referral_payment(user_id, amount_toman):
    user_data = redis_get_user(user_id)
    if not user_data or not user_data.get("referrer_code"):
        return
    referrer_id = find_user_by_referral_code(user_data["referrer_code"])
    if not referrer_id:
        return
    if str(referrer_id) == str(user_id):
        # Self-referral guard: a user should never be able to earn a bonus off their own
        # payment by putting their own referral code as their referrer.
        add_log(f"⛔ blocked self-referral payout attempt for user {user_id}")
        return
    referral_bonus = int(amount_toman * 0.2)
    referrer_data = redis_get_user(referrer_id)
    referrer_data["wallet"] = referrer_data.get("wallet", 0) + referral_bonus
    referrer_data["referral_total_earned"] = referrer_data.get("referral_total_earned", 0) + referral_bonus
    referrer_data["referral_paid_count"] = referrer_data.get("referral_paid_count", 0) + 1
    redis_save_user(referrer_id, referrer_data)
    if referrer_data.get("chat_id"):
        send_ble_message(referrer_data["chat_id"], f"🎉 تبریک! یک کاربر جدید از طریق لینک شما اشتراک خرید. {referral_bonus:,} تومان به کیف پول شما اضافه شد!")
    add_log(f"💰 Referral bonus {referral_bonus} added to user {referrer_id}")

def weekly_payout():
    # Prevent double-running this job (e.g. if the app is scaled to multiple
    # instances/workers, each with its own BackgroundScheduler) from paying users twice.
    week_key = datetime.now(pytz.timezone("Asia/Tehran")).strftime("%Y-W%U")
    if not acquire_run_lock(f"weekly_payout:{week_key}", ttl_seconds=6 * 24 * 3600):
        add_log(f"⏭️ weekly_payout skipped (already run this week by another instance): {week_key}")
        return
    try:
        users = get_all_user_ids()
        for user_id in users:
            user_data = redis_get_user(user_id)
            wallet = user_data.get("wallet", 0)
            if wallet < 1000:
                continue
            card = user_data.get("bank_card")
            sheba = user_data.get("bank_sheba")
            if not card or not sheba:
                if user_data.get("chat_id"):
                    send_ble_message(user_data["chat_id"], "⚠️ اطلاعات بانکی کامل نیست. برای تسویه تنظیم کنید.")
                continue
            result = payout_zibal(wallet, card, sheba)
            if result.get("ok"):
                user_data["wallet"] = 0
                redis_save_user(user_id, user_data)
                if user_data.get("chat_id"):
                    send_ble_message(user_data["chat_id"], f"✅ تسویه انجام شد. {wallet:,} تومان به کارت شما واریز گردید.")
            else:
                if user_data.get("chat_id"):
                    send_ble_message(user_data["chat_id"], f"❌ تسویه ناموفق: {result.get('message')}")
    except Exception as e:
        add_log(f"❌ weekly_payout error: {e}")
        alert_admins(f"خطا در تسویه هفتگی: {e}", throttle_key="weekly_payout_error")

def calculate_level(points):
    return min(10, (points // 100) + 1)

def check_daily_challenge(user_id):
    user_data = redis_get_user(user_id)
    today = get_today_tehran_date()
    last_check = user_data.get("last_daily_check")
    if last_check == today:
        return
    if user_profile_completed(user_data):
        user_data["points"] = user_data.get("points", 0) + 10
        user_data["last_daily_check"] = today
        user_data["level"] = calculate_level(user_data["points"])
        redis_save_user(user_id, user_data)
        if user_data.get("chat_id"):
            send_ble_message(user_data["chat_id"], "🏆 چالش روزانه کامل! ۱۰ امتیاز اضافه شد.")

def check_weekly_challenge(user_id):
    user_data = redis_get_user(user_id)
    start_weight = user_data.get("start_weight", user_data.get("weight", 70))
    current_weight = user_data.get("weight", 70)
    goal = user_data.get("goal", "keep")
    if goal == "loss" and current_weight <= start_weight - 0.5:
        user_data["points"] = user_data.get("points", 0) + 50
        user_data["level"] = calculate_level(user_data["points"])
        redis_save_user(user_id, user_data)
        if user_data.get("chat_id"):
            send_ble_message(user_data["chat_id"], "🏆 چالش هفتگی کامل! ۵۰ امتیاز اضافه شد.")

def send_challenges(chat_id, user_id):
    user_data = redis_get_user(user_id)
    points = user_data.get("points", 0)
    level = user_data.get("level", 1)
    next_level = points % 100
    text = (f"🏆 چالش‌های شما:\n"
            f"⭐ سطح فعلی: {level}\n"
            f"🏅 امتیاز: {points} (تا سطح بعدی: {100 - next_level})\n\n"
            f"📅 چالش روزانه: تکمیل برنامه غذایی (۱۰ امتیاز)\n"
            f"📆 چالش هفتگی: کاهش ۰.۵ کیلو وزن (۵۰ امتیاز)\n\n"
            f"جوایز سطح {level + 1}: تخفیف ۱۰% روی اشتراک!")
    send_ble_message(chat_id, text)

@app.route("/zibal-webhook", methods=["GET", "POST"])
@rate_limit("zibal_webhook")
def zibal_webhook():
    try:
        req_json = request.get_json(silent=True) or {}
        req_args = request.args.to_dict()
        add_log(f"📥 Zibal webhook args: {req_args}")
        add_log(f"📥 Zibal webhook json: {req_json}")
        track_id = req_args.get("trackId") or req_json.get("trackId")
        order_id = req_args.get("orderId") or req_json.get("orderId")
        success = req_args.get("success") or req_json.get("success")
        status = req_args.get("status") or req_json.get("status")
        add_log(f"📌 Parsed callback => track_id={track_id}, order_id={order_id}, success={success}, status={status}")
        if not track_id:
            return """
            <html>
              <head><meta charset="utf-8"><title>خطا</title></head>
              <body style="font-family:tahoma;direction:rtl;text-align:center;padding:40px;">
                <h2>❌ خطا</h2>
                <p>شناسه تراکنش دریافت نشد.</p>
              </body>
            </html>
            """, 400
        if str(success) == "0":
            return f"""
            <html>
              <head><meta charset="utf-8"><title>پرداخت لغو شد</title></head>
              <body style="font-family:tahoma;direction:rtl;text-align:center;padding:40px;background:#f8f8f8;">
                <div style="max-width:500px;margin:auto;background:white;padding:30px;border-radius:14px;box-shadow:0 2px 12px rgba(0,0,0,0.08);">
                  <h2 style="color:#d9534f;">⚠️ پرداخت لغو شد</h2>
                  <p>پرداخت شما کامل نشد. لطفاً دوباره تلاش کنید.</p>
                  <a href="{BOT_LINK}" style="display:inline-block;margin-top:20px;padding:12px 22px;background:#0d6efd;color:white;text-decoration:none;border-radius:8px;">
                    بازگشت به ربات
                  </a>
                </div>
              </body>
            </html>
            """
        verify_result = verify_zibal_payment(track_id)
        if not verify_result.get("ok"):
            add_log(f"❌ verify failed for track_id={track_id} | result={verify_result}")
            return f"""
            <html>
              <head><meta charset="utf-8"><title>تأیید نشد</title></head>
              <body style="font-family:tahoma;direction:rtl;text-align:center;padding:40px;background:#f8f8f8;">
                <div style="max-width:500px;margin:auto;background:white;padding:30px;border-radius:14px;box-shadow:0 2px 12px rgba(0,0,0,0.08);">
                  <h2 style="color:#d9534f;">❌ پرداخت تأیید نشد</h2>
                  <p>نتیجه بررسی تراکنش ناموفق بود.</p>
                  <p style="color:#666;font-size:14px;">{verify_result.get('message', '')}</p>
                  <a href="{BOT_LINK}" style="display:inline-block;margin-top:20px;padding:12px 22px;background:#0d6efd;color:white;text-decoration:none;border-radius:8px;">
                    بازگشت به ربات
                  </a>
                </div>
              </body>
            </html>
            """, 400
        user_id = None
        user_data = None
        if order_id:
            user_id = str(order_id)
            user_data = redis_get_user(user_id) or {}
        if not user_data:
            user_id, user_data = find_user_by_track_id(track_id)
        if not user_id or not user_data:
            add_log(f"❌ user not found for track_id={track_id} order_id={order_id}")
            return f"""
            <html>
              <head><meta charset="utf-8"><title>کاربر پیدا نشد</title></head>
              <body style="font-family:tahoma;direction:rtl;text-align:center;padding:40px;background:#f8f8f8;">
                <div style="max-width:500px;margin:auto;background:white;padding:30px;border-radius:14px;box-shadow:0 2px 12px rgba(0,0,0,0.08);">
                  <h2 style="color:#f0ad4e;">⚠️ پرداخت انجام شد</h2>
                  <p>اما کاربر مربوط به این تراکنش پیدا نشد.</p>
                  <p>لطفاً به پشتیبانی پیام دهید.</p>
                  <a href="{BOT_LINK}" style="display:inline-block;margin-top:20px;padding:12px 22px;background:#0d6efd;color:white;text-decoration:none;border-radius:8px;">
                    بازگشت به ربات
                  </a>
                </div>
              </body>
            </html>
            """, 400
        # Idempotency lock: Zibal (and flaky networks) can call this webhook more than once
        # for the same trackId. Without this, a payment could be credited twice (double
        # referral bonus, duplicate scheduling, etc).
        lock_acquired = True
        lock_key = f"zibal:processed:{track_id}"
        if redis_available:
            try:
                lock_acquired = bool(redis_client.set(lock_key, "1", nx=True, ex=3600))
            except Exception as e:
                add_log(f"⚠️ zibal_webhook lock error: {e}")

        already_paid = user_data.get("payment_status") == "paid" and user_data.get("track_id") == str(track_id)
        if lock_acquired and not already_paid:
            # Sanity-check the paid amount against what we expected for this purchase, so a
            # replayed/edited trackId for a smaller payment can't be used to unlock a bigger plan.
            expected_amount_rial = int(user_data.get("pending_amount", 0)) * 10
            paid_amount_rial = verify_result.get("data", {}).get("amount")
            if expected_amount_rial and paid_amount_rial and int(paid_amount_rial) != expected_amount_rial:
                add_log(f"⛔ amount mismatch for track_id={track_id}: expected {expected_amount_rial} got {paid_amount_rial}")
                return f"""
                <html>
                  <head><meta charset="utf-8"><title>مبلغ نامعتبر</title></head>
                  <body style="font-family:tahoma;direction:rtl;text-align:center;padding:40px;background:#f8f8f8;">
                    <div style="max-width:500px;margin:auto;background:white;padding:30px;border-radius:14px;box-shadow:0 2px 12px rgba(0,0,0,0.08);">
                      <h2 style="color:#d9534f;">❌ مبلغ پرداختی مطابقت ندارد</h2>
                      <p>لطفاً به پشتیبانی پیام دهید.</p>
                    </div>
                  </body>
                </html>
                """, 400

            subscription_days = int(user_data.get("pending_subscription_days") or user_data.get("subscription_days", 30))
            amount_toman = int(user_data.get("pending_amount") or (subscription_days * 1000))
            pending_coupon = user_data.get("pending_coupon")
            pending_referral_discount = user_data.get("pending_referral_discount")
            days_to_plan = {MONTHLY_DAYS: "monthly", SEMESTER_DAYS: "semester", YEARLY_DAYS: "yearly"}
            plan_name = user_data.get("pending_plan") or days_to_plan.get(subscription_days, "unknown")

            user_data["paid"] = True
            user_data["payment_status"] = "paid"
            user_data["track_id"] = str(track_id)
            user_data["subscription_days"] = subscription_days
            paid_date_str = datetime.now(pytz.timezone("Asia/Tehran")).strftime("%Y-%m-%d")
            user_data["paid_date"] = paid_date_str
            user_data["chat_id"] = str(user_data.get("chat_id", ""))
            user_data.pop("pending_subscription_days", None)
            user_data.pop("pending_amount", None)
            user_data.pop("pending_coupon", None)
            user_data.pop("pending_plan", None)
            user_data.pop("pending_referral_discount", None)

            # Only now - payment confirmed - actually consume the coupon usage.
            if pending_coupon:
                consume_coupon(pending_coupon)
            # Same idea for the one-time referred-user welcome discount: mark it used
            # only once the payment actually went through, and only once ever per account.
            if pending_referral_discount:
                user_data["referred_discount_used"] = True

            increment_counter(f"completed:{plan_name}")
            increment_counter(f"revenue:{plan_name}", amount_toman)

            # Keep a lightweight payment history so the user can review past purchases.
            history = user_data.get("payment_history", [])
            history.append({
                "date": paid_date_str,
                "amount": amount_toman,
                "days": subscription_days,
                "plan": plan_name,
                "track_id": str(track_id),
                "coupon": pending_coupon
            })
            user_data["payment_history"] = history[-20:]

            process_referral_payment(user_id, amount_toman)
            redis_save_user(user_id, user_data)
            chat_id = user_data.get("chat_id")
            if chat_id:
                text = f"🎉 پرداخت شما با موفقیت تأیید شد و اشتراک {subscription_days} روزه شما فعال شد."
                if VIP_CHANNEL_LINK:
                    text += f"\n\n💎 دسترسی ویژه به کانال VIP: {VIP_CHANNEL_LINK}"
                send_ble_message(chat_id, text, get_main_keyboard(True, True))
                cancel_trial_jobs(user_id)
                schedule_weekly_workout_for_paid(user_id, chat_id)
        return f"""
        <html>
          <head>
            <meta charset="utf-8">
            <title>تأیید پرداخت</title>
          </head>
          <body style="font-family:tahoma;direction:rtl;text-align:center;padding:40px;background:#f8f8f8;">
            <div style="max-width:500px;margin:auto;background:white;padding:30px;border-radius:14px;box-shadow:0 2px 12px rgba(0,0,0,0.08);">
              <h2 style="color:green;">✅ پرداخت با موفقیت انجام شد</h2>
              <p style="font-size:16px;">اشتراک شما فعال شد.</p>
              <p style="color:#555;">اکنون می‌توانید به ربات بله برگردید و از برنامه غذایی خود استفاده کنید.</p>
              <a href="{BOT_LINK}" style="display:inline-block;margin-top:20px;padding:12px 22px;background:#14a44d;color:white;text-decoration:none;border-radius:8px;">
                بازگشت به ربات
              </a>
            </div>
          </body>
        </html>
        """
    except Exception as e:
        add_log(f"❌ zibal_webhook Error: {e}")
        alert_admins(f"خطا در وب‌هوک پرداخت زیبال: {e}", throttle_key="zibal_webhook_error")
        return """
        <html>
          <head><meta charset="utf-8"><title>خطای سرور</title></head>
          <body style="font-family:tahoma;direction:rtl;text-align:center;padding:40px;">
            <h2>❌ خطای سرور</h2>
            <p>لطفاً بعداً دوباره تلاش کنید یا به پشتیبانی پیام دهید.</p>
          </body>
        </html>
        """, 500

def send_welcome(chat_id, user_id=None):
    user_data = redis_get_user(user_id) if user_id else {}
    profile_completed = user_profile_completed(user_data) if user_data else False
    paid_active = is_subscription_active(user_data) if user_data else False
    if paid_active:
        text = f"""
🎉 به ربات برنامه غذایی خوش آمدید! 🥗

شما دارای اشتراک فعال هستید. از قابلیت‌های شخصی‌سازی و چالش‌ها استفاده کنید!
📅 برنامه امروز را ببینید
📊 ماکروها را بررسی کنید
👤 پروفایل خود را مشاهده کنید
✏️ برنامه را شخصی‌سازی کنید
🏆 چالش‌ها را چک کنید
💰 کسب درآمد از ارجاع
"""
        if VIP_CHANNEL_LINK:
            text += f"\n💎 دسترسی ویژه: {VIP_CHANNEL_LINK}"
    elif user_data.get("paid"):
        text = """
🎉 به ربات برنامه غذایی خوش آمدید! 🥗

اشتراک شما منقضی شده. برای دسترسی کامل، اشتراک را تمدید کنید.
"""
    else:
        text = f"""
🎉 به ربات برنامه غذایی خوش آمدید! 🥗

برای دریافت برنامه دقیق و شخصی‌سازی‌شده،
ابتدا اطلاعات بدنی و هدف خود را ثبت کنید.
دوره آزمایشی ۳ روزه رایگان دارید!

💳 اشتراک ویژه از {MONTHLY_PRICE:,} تومان در ماه (با تخفیف روز اول تا ۶۰٪ کمتر)
"""
    send_ble_message(chat_id, text, get_main_keyboard(profile_completed, paid_active))

def send_daily_plan(chat_id, user_id):
    user_data = redis_get_user(user_id) or {}
    if not user_profile_completed(user_data):
        send_ble_message(chat_id, "📝 لطفاً ابتدا اطلاعات خود را کامل کنید.", get_main_keyboard(False, is_subscription_active(user_data)))
        return
    day_num = get_day_number(user_data.get("start_date", get_today_tehran_date()))
    day_key = f"day_{day_num}"
    plan = redis_get_meal(day_key)
    if not plan:
        try:
            plan = meal_generator.generate_daily_plan(user_data, day_num)
        except Exception:
            plan = generate_user_daily_plan(user_data, day_num)
        redis_set_meal(day_key, plan)
    breakfast = redis_get_custom_meal(user_id, day_num, "breakfast") or plan.get("breakfast", {}).get("text", "---")
    lunch = redis_get_custom_meal(user_id, day_num, "lunch") or plan.get("lunch", {}).get("text", "---")
    dinner = redis_get_custom_meal(user_id, day_num, "dinner") or plan.get("dinner", {}).get("text", "---")
    snack = redis_get_custom_meal(user_id, day_num, "snack") or plan.get("snack", {}).get("text", "---") if plan.get("snack") else "---"
    text = f"""
🥗 برنامه غذایی - روز {day_num}

صبحانه: {breakfast}
ناهار: {lunch}
شام: {dinner}
میان‌وعده: {snack}
"""
    check_daily_challenge(user_id)
    if user_data.get("trial_active") and day_num in [1, 2, 3]:
        text += f"\n\n💡 برای دسترسی به شخصی‌سازی برنامه، کاهش وزن سریع‌تر و حمایت ۲۴/۷، اشتراک ویژه تهیه کنید!\n\n💳 اشتراک ویژه"
        keyboard = {"inline_keyboard": [[{"text": "💳 اشتراک ویژه تهیه کنید", "callback_data": "cta_payment"}]]}
        send_ble_message(chat_id, text, keyboard)
    else:
        send_ble_message(chat_id, text)

def send_macro_info(chat_id, user_data):
    if not user_profile_completed(user_data):
        send_ble_message(chat_id, "📝 لطفاً ابتدا اطلاعات خود را کامل کنید.", get_main_keyboard(False, is_subscription_active(user_data)))
        return
    day_num = get_day_number(user_data.get("start_date", get_today_tehran_date()))
    day_key = f"day_{day_num}"
    plan = redis_get_meal(day_key)
    if not plan:
        try:
            plan = meal_generator.generate_daily_plan(user_data, day_num)
        except Exception:
            plan = generate_user_daily_plan(user_data, day_num)
        redis_set_meal(day_key, plan)
    total_macros = {"calories": 0, "protein": 0, "carb": 0, "fat": 0}
    for meal in plan.values():
        if isinstance(meal, dict):
            macros = meal.get("macros", {})
            total_macros["calories"] += macros.get("calories", 0)
            total_macros["protein"] += macros.get("protein", 0)
            total_macros["carb"] += macros.get("carb", 0)
            total_macros["fat"] += macros.get("fat", 0)
    # Give the numbers context the user can actually judge - protein per kg bodyweight
    # is the standard reference point, since a bare gram count means little on its own.
    weight = int(user_data.get("weight", 70)) or 70
    protein_per_kg = total_macros["protein"] / weight if weight else 0
    text = (f"📊 ماکروهای امروز (بر اساس برنامه):\n"
            f"🔥 کالری: {total_macros['calories']} کیلوکالری\n"
            f"🥩 پروتئین: {total_macros['protein']}گ (≈{protein_per_kg:.1f} گرم به‌ازای هر کیلوگرم وزن بدن)\n"
            f"🌾 کربوهیدرات: {total_macros['carb']}گ\n"
            f"🧈 چربی: {total_macros['fat']}گ\n\n"
            f"ℹ️ این عدد کالری هدف روزانه‌ی شماست که بر اساس هدف‌تان تنظیم شده، نه صرفاً کالری نگه‌داشت وزن.")
    send_ble_message(chat_id, text)

def send_payment_offer(chat_id, user_id):
    user_data = redis_get_user(user_id) or {}
    increment_counter("offer_views")
    bmr = user_data.get("bmr", 2000)
    goal = user_data.get("goal", "حفظ تناسب")
    diet_type = user_data.get("diet_type", "معمولی")

    # Figure out which discount actually wins (same logic as
    # calculate_subscription_price_full) just to label the message correctly - which
    # discount type is cheapest doesn't depend on which plan, since they're all a plain
    # percentage off the same base price.
    _, _, _, winning_coupon, winning_source = calculate_subscription_price_full(user_data, "monthly")
    if winning_source == "coupon":
        coupon_data = get_coupon_data(winning_coupon)
        pct = coupon_data.get("percent", 0) if coupon_data else 0
        discount_note = f" (🎟 تخفیف کد {winning_coupon} - {pct}% اعمال شد)"
    elif winning_source == "referral":
        discount_note = f" (🎁 تخفیف {REFERRED_USER_DISCOUNT_PERCENT}% ویژه کاربران معرفی‌شده اعمال شد)"
    elif winning_source == "level":
        level = user_data.get("level", 1)
        pct = get_level_discount_percent(level)
        discount_note = f" (⭐ تخفیف وفاداری {pct}% ویژه سطح {level} اعمال شد)"
    elif winning_source == "trial":
        discount_note = f" (تخفیف دوره آزمایشی {get_trial_discount_percent(user_data)}% اعمال شد)"
    else:
        discount_note = ""
    monthly_price, _, _ = calculate_subscription_price(user_data, "monthly")
    semester_price, _, _ = calculate_subscription_price(user_data, "semester")
    yearly_price, _, _ = calculate_subscription_price(user_data, "yearly")
    text = f"""
💎 اشتراک ویژه برنامه غذایی شخصی‌سازی‌شده

🔥 بر اساس هدف: {goal}
🍽️ رژیم: {diet_type}
📊 کالری روزانه: {bmr}

گزینه‌های اشتراک{discount_note}:
📅 ماهانه: {monthly_price:,} تومان (۳۰ روز)
⭐ ۶ ماهه: {semester_price:,} تومان (۱۸۰ روز) - محبوب‌ترین انتخاب
📅 سالانه: {yearly_price:,} تومان (۳۶۵ روز)
"""
    keyboard = {"inline_keyboard": [
        [{"text": f"📅 ماهانه - {monthly_price:,} تومان", "callback_data": "select_monthly"}],
        [{"text": f"⭐ ۶ ماهه - {semester_price:,} تومان (محبوب‌ترین)", "callback_data": "select_semester"}],
        [{"text": f"📅 سالانه - {yearly_price:,} تومان", "callback_data": "select_yearly"}]
    ]}
    send_ble_message(chat_id, text, keyboard)

def process_payment(chat_id, user_id):
    user_data = redis_get_user(user_id) or {}
    if not user_profile_completed(user_data):
        send_ble_message(chat_id, "📝 لطفاً ابتدا اطلاعات خود را کامل کنید.", get_main_keyboard(False, is_subscription_active(user_data)))
        return
    selected = user_data.get("selected_subscription")
    if not selected:
        send_ble_message(chat_id, "اشتراک انتخاب نشده.")
        return
    amount, days, desc, coupon_used, discount_source = calculate_subscription_price_full(user_data, selected)
    if not amount:
        send_ble_message(chat_id, "اشتراک نامعتبر.")
        return
    result = create_zibal_payment(user_id, amount)
    if not result.get("ok"):
        send_ble_message(chat_id, f"❌ {result.get('message', 'خطا در ایجاد پرداخت')}")
        return
    increment_counter(f"initiated:{selected}")
    track_id = str(result["track_id"])
    payment_url = result["payment_url"]
    user_data["track_id"] = track_id
    user_data["chat_id"] = str(chat_id)
    user_data["payment_status"] = "pending"
    # NOTE: do NOT touch the live "subscription_days" here - the user hasn't paid yet.
    # Store the pending purchase separately; it's only applied once Zibal confirms payment
    # in zibal_webhook. Otherwise a user with an active subscription could start (and abandon)
    # an "upgrade" purchase to silently extend their current subscription for free.
    user_data["pending_subscription_days"] = days
    user_data["pending_amount"] = amount
    user_data["pending_plan"] = selected
    user_data["pending_referral_discount"] = (discount_source == "referral")
    # The coupon (if any) is only actually consumed once payment is confirmed in the
    # webhook - not here, and never just from displaying a price - so an abandoned
    # payment doesn't burn through the coupon's usage limit.
    user_data["pending_coupon"] = coupon_used
    redis_save_user(user_id, user_data)
    keyboard = {"inline_keyboard": [[{"text": "💳 پرداخت", "url": payment_url}]]}
    send_ble_message(chat_id, "برای تکمیل پرداخت روی دکمه زیر کلیک کنید:", keyboard)
    schedule_abandoned_checkout_reminder(user_id, chat_id, track_id)

def maybe_send_upgrade_offer(user_id, user_data, days_passed, subscription_days):
    """Mid-cycle upgrade nudge: a user on the monthly (or semester) plan gets offered a
    move to a longer plan at roughly the midpoint of their current cycle, with credit
    for their unused days deducted from the longer plan's price. Sent at most once per
    subscription cycle (tracked via upgrade_offer_sent_for)."""
    if subscription_days >= YEARLY_DAYS:
        return  # already on the top plan - nothing to upgrade to
    halfway = subscription_days // 2
    if days_passed != halfway:
        return
    paid_date_str = user_data.get("paid_date")
    if not paid_date_str or user_data.get("upgrade_offer_sent_for") == paid_date_str:
        return
    if not user_data.get("chat_id"):
        return

    history = user_data.get("payment_history", [])
    last_payment = history[-1] if history else None
    paid_amount = last_payment.get("amount") if last_payment else subscription_days * 1000
    remaining_days = subscription_days - days_passed
    credit = int(paid_amount * (remaining_days / subscription_days))

    if subscription_days <= MONTHLY_DAYS:
        target_plan, target_days, target_price, target_label = "semester", SEMESTER_DAYS, SEMESTER_PRICE, "۶ ماهه"
    else:
        target_plan, target_days, target_price, target_label = "yearly", YEARLY_DAYS, YEARLY_PRICE, "سالانه"

    # Never let the credit make the upgrade look absurdly cheap or free - cap the
    # discount at 70% of the target plan's price as a sanity guard.
    upgrade_price = max(target_price - credit, int(target_price * 0.3))

    user_data["pending_upgrade_plan"] = target_plan
    user_data["pending_upgrade_days"] = target_days
    user_data["pending_upgrade_price"] = upgrade_price
    user_data["upgrade_offer_sent_for"] = paid_date_str
    redis_save_user(user_id, user_data)

    kb = {"inline_keyboard": [[{"text": f"⬆️ ارتقا به {target_label} با {upgrade_price:,} تومان", "callback_data": "accept_upgrade_offer"}]]}
    send_ble_message(user_data["chat_id"],
                      f"💡 نصف اشتراک فعلیت گذشته! با احتساب {remaining_days} روز باقی‌مونده، می‌تونی همین حالا به پلن {target_label} ارتقا بدی و فقط {upgrade_price:,} تومان پرداخت کنی (به‌جای قیمت کامل {target_price:,} تومان).",
                      kb)

def process_upgrade_payment(chat_id, user_id):
    user_data = redis_get_user(user_id) or {}
    target_plan = user_data.get("pending_upgrade_plan")
    target_days = user_data.get("pending_upgrade_days")
    upgrade_price = user_data.get("pending_upgrade_price")
    if not target_plan or not upgrade_price:
        send_ble_message(chat_id, "این پیشنهاد دیگر معتبر نیست.")
        return
    result = create_zibal_payment(user_id, upgrade_price)
    if not result.get("ok"):
        send_ble_message(chat_id, f"❌ {result.get('message', 'خطا در ایجاد پرداخت')}")
        return
    increment_counter(f"initiated:upgrade_{target_plan}")
    track_id = str(result["track_id"])
    payment_url = result["payment_url"]
    user_data["track_id"] = track_id
    user_data["chat_id"] = str(chat_id)
    user_data["payment_status"] = "pending"
    # Reuses the exact same pending_* fields process_payment uses, so zibal_webhook
    # doesn't need any special-casing for an upgrade vs. a normal purchase.
    user_data["pending_subscription_days"] = target_days
    user_data["pending_amount"] = upgrade_price
    user_data["pending_plan"] = target_plan
    user_data["pending_coupon"] = None
    user_data["pending_referral_discount"] = False
    user_data.pop("pending_upgrade_plan", None)
    user_data.pop("pending_upgrade_days", None)
    user_data.pop("pending_upgrade_price", None)
    redis_save_user(user_id, user_data)
    keyboard = {"inline_keyboard": [[{"text": "💳 پرداخت", "url": payment_url}]]}
    send_ble_message(chat_id, "برای تکمیل ارتقا و پرداخت مابه‌التفاوت روی دکمه زیر کلیک کنید:", keyboard)
    schedule_abandoned_checkout_reminder(user_id, chat_id, track_id)

def _abandoned_checkout_reminder(user_id, chat_id, track_id, round_num=1):
    try:
        u = redis_get_user(user_id) or {}
        # Only nudge if this specific attempt is still unpaid (not superseded by a
        # newer attempt and not already completed).
        if u.get("track_id") == str(track_id) and u.get("payment_status") == "pending":
            kb = {"inline_keyboard": [[{"text": "💳 ادامه و تکمیل پرداخت", "callback_data": "renew_subscription"}]]}
            if round_num == 1:
                msg = "👋 پرداخت شما ناتمام مونده! اگه مشکلی پیش اومده یا نظرت عوض شده، همینجا می‌تونی دوباره تلاش کنی:"
            elif round_num == 2:
                msg = "⏰ هنوز پرداختت تکمیل نشده. اگه درگاه مشکل داشت یا وسط راه قطع شدی، الان دوباره امتحان کن:"
            else:
                msg = "🔔 آخرین یادآوری: اشتراکت هنوز فعال نشده چون پرداخت تکمیل نشد. اگه هنوز علاقه داری، همین الان تمومش کن:"
            send_ble_message(chat_id, msg, kb)
    except Exception as e:
        add_log(f"❌ _abandoned_checkout_reminder error: {e}")

def schedule_abandoned_checkout_reminder(user_id, chat_id, track_id):
    """Nudges a user who started checkout but never completed payment - a common
    conversion leak point. Sends up to 3 reminders (45min / 3h / 6h after checkout
    started), each only firing if that specific attempt is STILL pending at that time -
    so a completed or superseded payment silently cancels the remaining reminders."""
    try:
        for round_num, delay_minutes in enumerate([45, 180, 360], start=1):
            run_at = datetime.now(pytz.timezone("Asia/Tehran")) + timedelta(minutes=delay_minutes)
            scheduler.add_job(_abandoned_checkout_reminder, trigger='date', run_date=run_at,
                               args=(user_id, chat_id, track_id, round_num),
                               id=f"abandoned_checkout_{user_id}_{track_id}_{round_num}", replace_existing=True)
    except Exception as e:
        add_log(f"❌ schedule_abandoned_checkout_reminder error: {e}")

def send_workout_program(chat_id, user_id):
    user_data = redis_get_user(user_id) or {}
    if not user_profile_completed(user_data):
        send_ble_message(chat_id, "📝 لطفاً ابتدا اطلاعات خود را کامل کنید.", get_main_keyboard(False, is_subscription_active(user_data)))
        return
    try:
        start = datetime.strptime(user_data.get("start_date", get_today_tehran_date()), "%Y-%m-%d").date()
        today = datetime.now(pytz.timezone("Asia/Tehran")).date()
        week_num = max(1, ((today - start).days // 7) + 1)
    except Exception:
        week_num = 1
    # Personalize weekly session count by activity level instead of hardcoding everyone
    # (beginner or "light" activity user) to the same 4 sessions/week as an advanced one.
    activity = user_data.get("activity", "متوسط")
    sessions_map = {"سبک": 3, "متوسط": 4, "سنگین": 5}
    sessions_per_week = sessions_map.get(activity, 4)
    equipment_pref = bool(user_data.get("equipment", True))
    # Include sessions_per_week/equipment in the cache key so changing them in the
    # profile (e.g. switching activity level) actually produces a different plan
    # instead of serving last week's cached plan for up to 7 more days.
    cache_key = f"workout:{user_id}:week:{week_num}:{sessions_per_week}:{int(equipment_pref)}"
    plan = None
    if redis_available:
        try:
            data = redis_client.get(cache_key)
            if data:
                plan = json.loads(data)
        except Exception:
            plan = None
    if not plan:
        plan = workout_generator.generate_weekly_workout(user_data, week_num=week_num, sessions_per_week=sessions_per_week, equipment=equipment_pref)
        if redis_available:
            try:
                redis_client.setex(cache_key, 7*24*3600, json.dumps(plan, ensure_ascii=False))
            except Exception:
                pass
    lines = [f"🏋️ برنامه تمرینی - هفته {plan.get('week')} (جلسات در هفته: {plan.get('sessions_per_week')})\n"]
    exercise_links = redis_get_exercise_links()
    for s in plan.get("sessions", []):
        # generator.py's WorkoutGenerator outputs each session's index under the key
        # "day", not "session_number" - the old code below always fell back to the
        # default (1), so admin-set custom workouts for any session other than the
        # first one were silently never applied.
        session_num = s.get("day", 1)
        custom_ex = redis_get_custom_workout(user_id, week_num, session_num)
        if custom_ex:
            lines.append(f"🔹 جلسه {session_num}:")
            for ex_line in custom_ex.split('\n'):
                if ex_line.strip():
                    lines.append(f"• {ex_line.strip()}")
                    match = re.match(r"(.+?) —", ex_line.strip())
                    ex_name = match.group(1).strip() if match else ex_line.strip()
                    if ex_name in exercise_links:
                        lines.append(f"   [نمایش درست حرکت]({exercise_links[ex_name]})")
        else:
            lines.append(f"🔹 {s['title']}:")
            for ex in s.get("exercises", []):
                note = f" ({ex['notes']})" if ex.get('notes') else ""
                lines.append(f"• {ex['name']} — {ex['sets']} ست × {ex['reps']} تکرار{note}")
                if ex['name'] in exercise_links:
                    lines.append(f"   [نمایش درست حرکت]({exercise_links[ex['name']]})")
        lines.append("")
    check_daily_challenge(user_id)
    if user_data.get("trial_active") and week_num == 1:
        lines.append("💡 برای دسترسی به شخصی‌سازی برنامه، کاهش وزن سریع‌تر و حمایت ۲۴/۷، اشتراک ویژه تهیه کنید!\n\n💳 اشتراک ویژه")
        keyboard = {"inline_keyboard": [[{"text": "💳 اشتراک ویژه تهیه کنید", "callback_data": "cta_payment"}]]}
        send_ble_message(chat_id, "\n".join(lines), keyboard)
    else:
        send_ble_message(chat_id, "\n".join(lines), get_main_keyboard(True, is_subscription_active(user_data)))

def send_daily_to_all_users():
    today = datetime.now(pytz.timezone("Asia/Tehran")).date()
    # Prevent double-sending to every paid user if this app runs with multiple
    # instances/workers, each with its own BackgroundScheduler.
    if not acquire_run_lock(f"daily_broadcast:{today.isoformat()}", ttl_seconds=20 * 3600):
        add_log(f"⏭️ send_daily_to_all_users skipped (already run today by another instance): {today}")
        return
    try:
        users = get_all_user_ids()
        for user_id in users:
            user_data = redis_get_user(user_id)
            if not user_data.get("paid", False):
                continue
            paid_date_str = user_data.get("paid_date")
            if not paid_date_str:
                continue
            try:
                paid_date = datetime.strptime(paid_date_str, "%Y-%m-%d").date()
            except Exception:
                continue
            subscription_days = user_data.get("subscription_days", 30)
            days_passed = (today - paid_date).days
            days_left = subscription_days - days_passed
            if days_passed >= subscription_days:
                user_data["paid"] = False
                user_data["payment_status"] = "expired"
                user_data.pop("expiry_reminder_sent_for", None)
                redis_save_user(user_id, user_data)
                if user_data.get("chat_id"):
                    send_ble_message(user_data["chat_id"], f"⏰ اشتراک شما (مدت {subscription_days} روزه) منقضی شده! برای تمدید به 💳 اشتراک ویژه مراجعه کنید.")
            else:
                if user_data.get("chat_id") and user_profile_completed(user_data):
                    send_daily_plan(user_data["chat_id"], user_id)
                # Reminder a few days before the subscription actually expires, sent once
                # per user per subscription cycle (tracked via expiry_reminder_sent_for).
                if (days_left in EXPIRY_REMINDER_DAYS_BEFORE
                        and user_data.get("expiry_reminder_sent_for") != user_data.get("paid_date")
                        and user_data.get("chat_id")):
                    kb = {"inline_keyboard": [[{"text": "💳 تمدید اشتراک", "callback_data": "renew_subscription"}]]}
                    send_ble_message(user_data["chat_id"], f"⏳ فقط {days_left} روز تا پایان اشتراک شما مانده. برای جلوگیری از قطع دسترسی، همین حالا تمدید کنید:", kb)
                    user_data["expiry_reminder_sent_for"] = user_data.get("paid_date")
                    redis_save_user(user_id, user_data)
                # Mid-cycle upgrade offer: suggest moving to a longer plan, at a
                # prorated price, around the midpoint of the current cycle.
                maybe_send_upgrade_offer(user_id, user_data, days_passed, subscription_days)
        add_log("✅ ارسال روزانه انجام شد.")
    except Exception as e:
        add_log(f"send_daily_to_all_users error: {e}")
        alert_admins(f"خطا در ارسال روزانه: {e}", throttle_key="daily_broadcast_error")

def check_weekly_challenge_for_all_users():
    """check_weekly_challenge() takes a user_id, but APScheduler was given it with NO
    arguments. That made scheduler.add_job() raise ("arguments have not been supplied:
    user_id") inside the startup try-block, BEFORE scheduler.start() was reached - so the
    scheduler never started at all and no scheduled job (7am daily plan, trial plans,
    weekly payout, abandoned-checkout reminders) ever ran. This wrapper runs it per user."""
    if not acquire_run_lock(f"weekly_challenge:{get_today_tehran_date()}", ttl_seconds=20 * 3600):
        return
    for uid in get_all_user_ids():
        try:
            check_weekly_challenge(uid)
        except Exception as e:
            add_log(f"❌ check_weekly_challenge error for {uid}: {e}")

try:
    scheduler.add_job(send_daily_to_all_users, CronTrigger(hour=7, minute=0, timezone="Asia/Tehran"), id="global_paid_daily", replace_existing=True)
    scheduler.add_job(weekly_payout, CronTrigger(day_of_week=5, hour=8, minute=0, timezone="Asia/Tehran"), id="weekly_payout", replace_existing=True)
    scheduler.add_job(check_weekly_challenge_for_all_users, CronTrigger(day_of_week=5, hour=7, minute=30, timezone="Asia/Tehran"), id="weekly_challenge_check", replace_existing=True)
    scheduler.start()
    restore_scheduled_jobs_on_startup()
    # Startup catch-up: if this process happens to (re)start right around 7am - which is
    # common during active development, since every redeploy wipes APScheduler's
    # in-memory jobs - today's occurrence of the cron job could be skipped entirely,
    # pushing paid users' daily plan to tomorrow. send_daily_to_all_users() is already
    # idempotent per calendar day (via acquire_run_lock), so calling it once here is safe
    # even if today's scheduled run already happened - it will just no-op in that case.
    #
    # The window is deliberately narrow (7:00-7:59), NOT "any time after 7am" - an
    # earlier version used `hour >= 7`, which matches nearly the whole day, so the FIRST
    # redeploy of any given day (7am through 11pm) would consume that day's send at
    # whatever random time the redeploy happened, instead of at 7am. During active
    # development (frequent redeploys) the real 7am cron essentially never got to fire
    # naturally, and paid users watching specifically at 7am would see nothing.
    current_hour = datetime.now(pytz.timezone("Asia/Tehran")).hour
    if 7 <= current_hour < 8:
        threading.Thread(target=send_daily_to_all_users, daemon=True).start()
    atexit.register(lambda: scheduler.shutdown(wait=False))
except Exception as e:
    add_log(f"scheduler start error: {e}")

@app.route("/health", methods=["GET"])
def health():
    # redis_available is only set once at startup; do a live ping here so /health
    # actually reflects the current state instead of a stale connection check.
    redis_ok = False
    if redis_available:
        try:
            redis_ok = bool(redis_client.ping())
        except Exception:
            redis_ok = False
    status = "ok" if redis_ok or not redis_available else "degraded"
    return jsonify({"status": status, "redis": redis_ok, "time": datetime.now().isoformat()})

@app.route("/ble-webhook", methods=["POST"])
@rate_limit("ble_webhook", key_func=_ble_webhook_sender_id)
def ble_webhook():
    try:
        if BLE_WEBHOOK_SECRET:
            provided = request.headers.get("X-Webhook-Secret") or request.args.get("secret", "")
            if not provided or not hmac.compare_digest(str(provided), BLE_WEBHOOK_SECRET):
                add_log(f"⛔ Rejected ble-webhook call with invalid secret from {request.remote_addr}")
                return jsonify({"error": "unauthorized"}), 401
        update = request.get_json(silent=True) or {}
        if redis_available:
            try:
                redis_client.lpush("logs", json.dumps(update, ensure_ascii=False))
                redis_client.ltrim("logs", 0, 999)
            except Exception:
                pass
        threading.Thread(target=_process_update, args=(update,), daemon=True).start()
        return jsonify({"status": "ok", "timestamp": datetime.now().isoformat()})
    except Exception as e:
        add_log(f"❌ Webhook Error: {e}")
        return jsonify({"error": "Internal Error"}), 500

def _process_update(update):
    try:
        if "message" in update:
            _handle_message(update["message"])
        elif "callback_query" in update:
            _handle_callback(update["callback_query"])
    except Exception as e:
        add_log(f"❌ Process Update Error: {e}")
        alert_admins(f"خطا در پردازش پیام ورودی: {e}", throttle_key="process_update_error")

def _handle_message(message):
    try:
        chat_id = message["chat"]["id"]
        user_id = message["from"]["id"]
        text = message.get("text", "").strip()
        photo = message.get("photo")
        user_data = redis_get_user(user_id) or {}
        if not user_data:
            user_data = {"chat_id": str(chat_id), "user_id": str(user_id), "paid": False, "start_date": get_today_tehran_date(), "step": None}
        user_data["chat_id"] = str(chat_id)
        if text.startswith("/start") and "ref=" in text:
            ref_code = text.split("ref=")[1].split()[0] if " " in text else text.split("ref=")[1]
            own_referral_code = hashlib.md5(str(user_id).encode()).hexdigest()[:8].upper()
            if not user_data.get("referrer_code") and ref_code and ref_code.upper() != own_referral_code:
                user_data["referrer_code"] = ref_code
        redis_save_user(user_id, user_data)
        paid_active = is_subscription_active(user_data)
        step = user_data.get("step")
        custom_step = user_data.get("custom_step")
        support_step = user_data.get("support_step")
        admin_reply_step = user_data.get("admin_reply_step")
        admin_dashboard_step = user_data.get("admin_dashboard_step")
        admin_exercise_step = user_data.get("admin_exercise_step")
        poll_step = user_data.get("poll_step")
        bank_step = user_data.get("bank_step")

        # "/done" is not a real top-level command - it's an in-flow terminator used
        # specifically inside the poll-options flow (see poll_step == "options" below)
        # to say "I'm finished adding options", and needs poll_step to stay exactly as
        # it is so that check can see it. Excluding it here is what the "keep=None"
        # blanket-clear below must NOT apply to; every other "/"-prefixed message is
        # treated as an unambiguous top-level command.
        if text.startswith("/") and text != "/done":
            # An explicit command is always a clear signal of "get me out of whatever
            # flow I'm stuck in and run THIS" - previously, a leftover flag from an
            # earlier abandoned flow (support_step, poll_step, bank_step, ...) could
            # swallow a typed command instead of running it. This is exactly how typing
            # "/coupon" got filed as a support ticket instead of running as an admin
            # command: support_step was still "question" from an earlier test, and that
            # check happened to come before the message could be recognized as a stray
            # command. clear_flow_flags() at every flow's entry point prevents this
            # going forward, but doesn't retroactively fix state that was already stuck
            # before that fix existed - this catches those cases too, for good.
            clear_flow_flags(user_data, keep=None, chat_id=chat_id)
            redis_save_user(user_id, user_data)
            step = custom_step = support_step = admin_reply_step = None
            admin_dashboard_step = admin_exercise_step = poll_step = bank_step = None

        if text == "/myid":
            send_ble_message(chat_id, f"🔎 your_id: {user_id}")
            return
        if text == "/dashboard":
            if is_admin(chat_id):
                report = generate_dashboard_report()
                keyboard = {"inline_keyboard": [
                    [{"text": "لیست کاربران تکمیل‌شده", "callback_data": "admin_list_completed"}],
                    [{"text": "💳 لیست کاربران دارای اشتراک فعال", "callback_data": "admin_list_paid"}],
                    [{"text": "لیست همه کاربران", "callback_data": "admin_list_all"}],
                    [{"text": "📥 خروجی CSV همه کاربران", "callback_data": "admin_export_csv"}],
                    [{"text": "📈 نرخ تبدیل پلن‌ها", "callback_data": "admin_conversion_report"}]
                ]}
                send_ble_message(chat_id, report, keyboard)
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text == "/tickets":
            if is_support_staff(chat_id):
                tickets = get_open_tickets()
                if not tickets:
                    send_ble_message(chat_id, "تیکت باز وجود ندارد.")
                    return
                keyboard = {"inline_keyboard": []}
                for ticket in tickets[:10]:
                    ticket_id = ticket.get("ticket_id", "")
                    if not ticket_id:
                        continue
                    last_msg = ticket.get("messages", [])[-1] if ticket.get("messages") else {}
                    snippet = (last_msg.get("text") or "(عکس)")[:25]
                    btn_text = f"#{ticket_id} | {ticket.get('user_id', '')} | {snippet}"
                    keyboard["inline_keyboard"].append([{"text": btn_text, "callback_data": f"reply_ticket_{ticket_id}"}])
                note = f"\n\n(و {len(tickets) - 10} تیکت باز دیگر - دوباره /tickets را بزنید تا لیست به‌روز شود)" if len(tickets) > 10 else ""
                send_ble_message(chat_id, f"🗂 تیکت‌های باز (اولویت: قدیمی‌تر):{note}", keyboard)
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text.startswith("/find_tickets "):
            if is_support_staff(chat_id):
                target_uid = text.split("/find_tickets ", 1)[1].strip()
                tickets = get_user_tickets(target_uid)
                if not tickets:
                    send_ble_message(chat_id, f"تیکتی برای کاربر {target_uid} یافت نشد.")
                    return
                keyboard = {"inline_keyboard": []}
                for ticket in tickets[:10]:
                    ticket_id = ticket.get("ticket_id", "")
                    status = STATUS_LABELS_FA.get(ticket.get("status"), ticket.get("status", "-"))
                    keyboard["inline_keyboard"].append([{"text": f"#{ticket_id} | {status}", "callback_data": f"reply_ticket_{ticket_id}"}])
                send_ble_message(chat_id, f"🗂 تیکت‌های کاربر {target_uid}:", keyboard)
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text.startswith("/vip"):
            uid_str = str(user_id)
            if is_admin(chat_id):
                parts = text.split()
                page = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 1
                users = get_all_user_ids()
                if not users:
                    send_ble_message(chat_id, "کاربری یافت نشد.")
                    return
                per_page = 10
                start = (page - 1) * per_page
                end = start + per_page
                page_users = users[start:end]
                keyboard = {"inline_keyboard": []}
                for uid in page_users:
                    u = redis_get_user(uid)
                    name = u.get("user_id", uid) if u else uid
                    keyboard["inline_keyboard"].append([{"text": f"{name}", "callback_data": f"vip_user_{uid}"}])
                nav = []
                if page > 1:
                    nav.append({"text": "⬅️ قبلی", "callback_data": f"vip_page_{page-1}"})
                if end < len(users):
                    nav.append({"text": "بعدی ➡️", "callback_data": f"vip_page_{page+1}"})
                if nav:
                    keyboard["inline_keyboard"].append(nav)
                send_ble_message(chat_id, f"کاربران (صفحه {page}):", keyboard)
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text.startswith("/exercise_links"):
            uid_str = str(user_id)
            if is_admin(chat_id):
                parts = text.split()
                if len(parts) < 3:
                    send_ble_message(chat_id, "فرمت: /exercise_links نام_تمرین لینک\nمثال: /exercise_links اسکوات https://youtube.com/example")
                    return
                exercise_name = parts[1]
                link = parts[2]
                links = redis_get_exercise_links()
                links[exercise_name] = link
                redis_set_exercise_links(links)
                send_ble_message(chat_id, f"لینک برای {exercise_name} ذخیره شد.")
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text == "/coupons":
            if is_admin(chat_id):
                keys = redis_client.keys("coupons:*") if redis_available else []
                if not keys:
                    send_ble_message(chat_id, "هیچ کوپنی ثبت نشده.")
                    return
                lines = ["🎟 لیست کوپن‌ها:\n"]
                for key in keys:
                    code = key.decode().split(":", 1)[1] if isinstance(key, bytes) else str(key).split(":", 1)[1]
                    data = get_coupon_data(code) or {}
                    status = "⚪ غیرفعال" if data.get("disabled") else ("🟢 فعال" if is_coupon_active(code) else "🔴 منقضی/تمام‌شده")
                    lines.append(f"#{code} | {data.get('percent', 0)}% | تا {data.get('expiry', '-')} | {data.get('used_count', 0)}/{data.get('max_uses', 0)} | {status}")
                send_ble_message(chat_id, "\n".join(lines))
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text.startswith("/coupon_off "):
            if is_admin(chat_id):
                code = text.split("/coupon_off ", 1)[1].strip().upper()
                data = get_coupon_data(code)
                if not data:
                    send_ble_message(chat_id, "کوپن یافت نشد.")
                    return
                data["disabled"] = True
                save_coupon_data(code, data)
                send_ble_message(chat_id, f"کوپن {code} غیرفعال شد.")
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text.startswith("/coupon ") or text == "/coupon":
            if is_admin(chat_id):
                parts = text.split()
                if len(parts) != 5:
                    send_ble_message(chat_id, "فرمت اشتباه. استفاده: /coupon CODE PERCENT EXPIRY MAX_USES\nمثال: /coupon DISCOUNT10 10 2026-12-31 5")
                    return
                code = parts[1].upper()
                try:
                    percent = int(parts[2])
                    max_uses = int(parts[4])
                except ValueError:
                    send_ble_message(chat_id, "درصد و حداکثر استفاده باید عدد صحیح باشند.")
                    return
                expiry = parts[3]
                try:
                    expiry_date = datetime.strptime(expiry, "%Y-%m-%d").date()
                except ValueError:
                    send_ble_message(chat_id, "فرمت تاریخ انقضا اشتباه است. مثال درست: 2026-12-31")
                    return
                if expiry_date < datetime.now(pytz.timezone("Asia/Tehran")).date():
                    send_ble_message(chat_id, "تاریخ انقضا نمی‌تواند در گذشته باشد.")
                    return
                if not (0 < percent <= 100):
                    send_ble_message(chat_id, "درصد باید بین 1 تا 100 باشد.")
                    return
                if max_uses <= 0:
                    send_ble_message(chat_id, "حداکثر استفاده باید عددی بزرگتر از صفر باشد.")
                    return
                coupon_data = {"percent": percent, "expiry": expiry, "max_uses": max_uses, "used_count": 0, "disabled": False}
                save_coupon_data(code, coupon_data)
                send_ble_message(chat_id, f"کوپن {code} ایجاد شد. درصد: {percent}%, انقضا: {expiry}, حداکثر استفاده: {max_uses}")
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text == "/poll":
            if is_admin(chat_id):
                user_data["poll_step"] = "question"
                clear_flow_flags(user_data, keep="poll_step", chat_id=chat_id)
                redis_save_user(user_id, user_data)
                send_ble_message(chat_id, "سوال نظرسنجی را وارد کنید:")
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text.startswith("/poll_results"):
            if is_admin(chat_id):
                parts = text.split()
                if len(parts) < 2:
                    send_ble_message(chat_id, "فرمت: /poll_results POLL_ID")
                    return
                poll_id = parts[1]
                poll = redis_get_poll(poll_id)
                if not poll:
                    send_ble_message(chat_id, "نظرسنجی یافت نشد.")
                    return
                responses = redis_get_poll_responses(poll_id)
                total = len(responses)
                if total == 0:
                    send_ble_message(chat_id, "هیچ پاسخی ثبت نشده.")
                    return
                counts = {}
                for r in responses.values():
                    counts[r] = counts.get(r, 0) + 1
                lines = [f"📊 نتایج نظرسنجی {poll_id}:\nسوال: {poll['question']}\nکل پاسخ‌ها: {total}"]
                for i, option in enumerate(poll['options'], 1):
                    count = counts.get(str(i), 0)
                    percent = (count / total) * 100 if total > 0 else 0
                    lines.append(f"{i}. {option}: {count} پاسخ ({percent:.1f}%)")
                send_ble_message(chat_id, "\n".join(lines))
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text == "/post":
            if is_admin(chat_id):
                # Clear any leftover flow state (e.g. an old poll_step) before starting a
                # fresh broadcast - otherwise the admin's content message later could get
                # swallowed by a stale flag instead of actually being broadcast.
                clear_flow_flags(user_data, keep=None, chat_id=chat_id)
                redis_save_user(user_id, user_data)
                start_broadcast_select_target(chat_id)
            else:
                send_ble_message(chat_id, "❌ شما دسترسی مدیریت ندارید.")
            return
        if text == "/start":
            send_welcome(chat_id, user_id)
            return
        if text in ["📝 ثبت اطلاعات", "📝 ویرایش اطلاعات"]:
            start_onboarding(chat_id, user_id)
            return
        if text == "👤 پروفایل من":
            if not user_profile_completed(user_data):
                send_ble_message(chat_id, "📝 هنوز اطلاعات شما کامل نشده است.", get_main_keyboard(False, paid_active))
            else:
                send_profile_summary(chat_id, user_data)
            return
        if text == "📅 برنامه امروز":
            send_daily_plan(chat_id, user_id)
            return
        if text == "📊 ماکروها":
            send_macro_info(chat_id, redis_get_user(user_id) or user_data)
            return
        if text == "💳 اشتراک ویژه":
            if not user_profile_completed(user_data):
                send_ble_message(chat_id, "📝 لطفاً ابتدا اطلاعات خود را کامل کنید.", get_main_keyboard(False, paid_active))
            else:
                send_payment_offer(chat_id, user_id)
            return
        if text == "🆘 پشتیبانی":
            open_ticket_id = user_data.get("open_ticket_id")
            open_ticket = get_ticket(open_ticket_id) if open_ticket_id else None
            cancel_kb = {"inline_keyboard": [[{"text": "❌ انصراف", "callback_data": "support_cancel"}]]}
            if open_ticket and open_ticket.get("status") != "closed":
                if open_ticket.get("status") == "answered":
                    hint = f"تیم پشتیبانی به تیکت شما (#{open_ticket_id}) پاسخ داده. اگر مشکل حل نشده، پیام بعدی خود را بنویسید:"
                else:
                    hint = f"شما یک تیکت باز دارید (#{open_ticket_id}) که هنوز پاسخ داده نشده. پیام بعدی شما به همین تیکت اضافه می‌شود:"
                cancel_kb["inline_keyboard"].append([{"text": "❌ بستن تیکت", "callback_data": f"close_ticket_{open_ticket_id}"}])
                send_ble_message(chat_id, hint, cancel_kb)
            else:
                send_ble_message(chat_id, "لطفاً سوال یا مشکل خود را تایپ یا عکس آن را ارسال کنید. تیم پشتیبانی به زودی پاسخ خواهد داد.", cancel_kb)
            user_data["support_step"] = "question"
            clear_flow_flags(user_data, keep="support_step", chat_id=chat_id)
            redis_save_user(user_id, user_data)
            return
        if text == "📋 تیکت‌های من":
            send_my_tickets(chat_id, user_id)
            return
        if text == "🏋️ برنامه تمرینی":
            send_workout_program(chat_id, user_id)
            return
        if text == "🏆 چالش‌ها":
            send_challenges(chat_id, user_id)
            return
        if text == "💰 کسب درآمد":
            send_referral_info(chat_id, user_id)
            return
        if text == "✏️ شخصی‌سازی برنامه" and paid_active:
            start_customization(chat_id, user_id)
            return

        if is_admin(chat_id) and redis_available:
            broadcast_step = redis_client.hget(f"admin:broadcast:{chat_id}", "step")
            if broadcast_step == "content":
                target = redis_client.hget(f"admin:broadcast:{chat_id}", "target")
                content = text if text else ""
                ph = None
                if photo:
                    ph = photo[-1]["file_id"]
                    content = message.get("caption", "") or "عکس ارسال شده"
                if target:
                    threading.Thread(target=broadcast_worker, args=(chat_id, content, target, ph), daemon=True).start()
                    send_ble_message(chat_id, "در حال ارسال...")
                    redis_client.delete(f"admin:broadcast:{chat_id}")
                    return
                else:
                    # Defensive cleanup: if this state is somehow corrupted (step set
                    # without a target), drop it instead of silently falling through to
                    # whatever flow check comes next - that fall-through was exactly how
                    # a stray admin message could end up getting misrouted into a
                    # leftover poll flow instead of failing loudly.
                    redis_client.delete(f"admin:broadcast:{chat_id}")
                    send_ble_message(chat_id, "⚠️ ارسال قبلی ناقص بود و لغو شد. لطفاً دوباره /post را بزنید.")
                    return

        if poll_step == "question":
            poll_id = str(int(time.time())) + "_" + str(user_id)
            user_data["current_poll_id"] = poll_id
            poll_data = {"poll_id": poll_id, "question": text, "options": [], "admin_chat_id": str(chat_id)}
            redis_set_poll(poll_id, poll_data)
            user_data["poll_step"] = "options"
            redis_save_user(user_id, user_data)
            send_ble_message(chat_id, "گزینه ۱ را وارد کنید (یا /done برای پایان):")
            return
        if poll_step == "options":
            poll_id = user_data.get("current_poll_id")
            if not poll_id:
                send_ble_message(chat_id, "خطا در ایجاد نظرسنجی.")
                return
            poll = redis_get_poll(poll_id)
            if text == "/done":
                if len(poll["options"]) < 2:
                    send_ble_message(chat_id, "حداقل ۲ گزینه نیاز است.")
                    return
                user_data["poll_step"] = "target"
                redis_save_user(user_id, user_data)
                keyboard = {"inline_keyboard": [
                    [{"text": "ارسال به همه", "callback_data": f"poll_target_all_{poll_id}"}],
                    [{"text": "ارسال به تکمیل‌شده‌ها", "callback_data": f"poll_target_completed_{poll_id}"}]
                ]}
                send_ble_message(chat_id, "مخاطبان نظرسنجی را انتخاب کنید:", keyboard)
                return
            poll["options"].append(text)
            redis_set_poll(poll_id, poll)
            option_num = len(poll["options"]) + 1
            send_ble_message(chat_id, f"گزینه {option_num} را وارد کنید (یا /done برای پایان):")
            return

        if support_step == "question":
            photo_file_id = photo[-1]["file_id"] if photo else None
            msg_text = text or (message.get("caption", "") or "")
            if not msg_text and not photo_file_id:
                send_ble_message(chat_id, "لطفاً یک پیام متنی یا عکس ارسال کنید، یا برای انصراف روی دکمه بالا بزنید.")
                return
            now_ts = int(time.time())
            existing_ticket_id = user_data.get("open_ticket_id")
            existing_ticket = get_ticket(existing_ticket_id) if existing_ticket_id else None
            if existing_ticket and existing_ticket.get("status") != "closed":
                # Continue the same conversation instead of splitting it into a new,
                # disconnected ticket every time the user writes something.
                ticket_id = existing_ticket_id
                ticket = existing_ticket
                ticket.setdefault("messages", []).append({"from": "user", "text": msg_text, "photo": photo_file_id, "timestamp": now_ts})
                ticket["status"] = "open"
                ticket["updated_at"] = now_ts
                notify_header = f"➕ پیام جدید در تیکت #{ticket_id} از کاربر {user_id}:"
            else:
                ticket_id = f"{now_ts}_{user_id}_{random.randint(1000, 9999)}"
                ticket = {
                    "ticket_id": ticket_id,
                    "user_id": str(user_id),
                    "chat_id": str(chat_id),
                    "status": "open",
                    "created_at": now_ts,
                    "updated_at": now_ts,
                    "messages": [{"from": "user", "text": msg_text, "photo": photo_file_id, "timestamp": now_ts}]
                }
                user_data["open_ticket_id"] = ticket_id
                notify_header = f"🆘 تیکت جدید #{ticket_id} از کاربر {user_id}:"
            save_ticket(ticket_id, ticket)
            user_data["support_step"] = None
            redis_save_user(user_id, user_data)
            if not ADMIN_CHAT_IDS:
                add_log(f"⚠️ ADMIN_CHAT_IDS خالی است - هیچ ادمینی از تیکت {ticket_id} مطلع نشد.")
            for admin in ADMIN_CHAT_IDS:
                send_ble_message(admin, f"{notify_header}\n\n{msg_text or '(بدون توضیح متنی)'}\n\nبرای پاسخ روی /tickets کلیک کنید.", photo=photo_file_id)
            send_ble_message(chat_id, f"✅ پیام شما ثبت شد (تیکت #{ticket_id}). تیم پشتیبانی به زودی پاسخ می‌دهد.\nمی‌توانید وضعیت آن را از «📋 تیکت‌های من» ببینید.")
            return

        if admin_reply_step:
            ticket = get_ticket(admin_reply_step)
            if ticket and ticket.get("ticket_id"):
                now_ts = int(time.time())
                ticket.setdefault("messages", []).append({"from": "admin", "text": text, "timestamp": now_ts})
                ticket["status"] = "answered"
                ticket["updated_at"] = now_ts
                save_ticket(admin_reply_step, ticket)
                user_chat_id = ticket.get("chat_id")
                if user_chat_id:
                    follow_up_kb = {"inline_keyboard": [[{"text": "❌ بستن تیکت", "callback_data": f"close_ticket_{admin_reply_step}"}]]}
                    send_ble_message(user_chat_id, f"📬 پاسخ پشتیبانی (تیکت #{admin_reply_step}):\n\n{text}\n\nاگر مشکل حل نشده، پیام بعدی خود را از منوی «🆘 پشتیبانی» ارسال کنید.", follow_up_kb)
                send_ble_message(chat_id, "پاسخ ارسال شد.")
            else:
                send_ble_message(chat_id, "تیکت یافت نشد.")
            user_data["admin_reply_step"] = None
            redis_save_user(user_id, user_data)
            return

        if admin_dashboard_step and admin_dashboard_step.startswith("view_user_"):
            target_uid = admin_dashboard_step.split("_", 2)[2]
            if text.strip():
                target_data = redis_get_user(target_uid)
                if target_data and target_data.get("chat_id"):
                    send_ble_message(target_data["chat_id"], f"📬 پیام از ادمین:\n\n{text}")
                    send_ble_message(chat_id, "پیام ارسال شد.")
                else:
                    send_ble_message(chat_id, "کاربر چت آی‌دی ندارد.")
            user_data["admin_dashboard_step"] = None
            redis_save_user(user_id, user_data)
            return

        if bank_step == "card":
            if len(text) == 16 and text.isdigit():
                user_data["bank_card"] = text
                user_data["bank_step"] = "sheba"
                redis_save_user(user_id, user_data)
                send_ble_message(chat_id, "شماره شبا را وارد کنید (۲۴ رقم، بدون IR):")
            else:
                send_ble_message(chat_id, "شماره کارت نامعتبر. دوباره وارد کنید:")
            return
        if bank_step == "sheba":
            if len(text) == 24 and text.isdigit():
                user_data["bank_sheba"] = "IR" + text
                user_data["bank_step"] = None
                redis_save_user(user_id, user_data)
                send_ble_message(chat_id, "اطلاعات بانکی ذخیره شد.")
            else:
                send_ble_message(chat_id, "شماره شبا نامعتبر. دوباره وارد کنید:")
            return

        if custom_step and custom_step.startswith("meal_"):
            parts = custom_step.split("_")
            if len(parts) == 3:
                day = int(parts[1])
                meal_type = parts[2]
                save_custom_meal(user_id, day, meal_type, text)
                user_data["custom_step"] = None
                redis_save_user(user_id, user_data)
                send_ble_message(chat_id, f"✅ برنامه {meal_type} روز {day} شخصی‌سازی شد.", get_main_keyboard(True, paid_active))
            return
        elif custom_step and custom_step.startswith("workout_"):
            parts = custom_step.split("_")
            if len(parts) == 3:
                week = int(parts[1])
                session = int(parts[2])
                save_custom_workout(user_id, week, session, text)
                user_data["custom_step"] = None
                redis_save_user(user_id, user_data)
                send_ble_message(chat_id, f"✅ برنامه جلسه {session} هفته {week} شخصی‌سازی شد.", get_main_keyboard(True, paid_active))
            return

        if step == "coupon":
            code = text.upper()
            if code == "SKIP":
                user_data["applied_coupon"] = None
                user_data["step"] = None
                redis_save_user(user_id, user_data)
                process_payment(chat_id, user_id)
                return
            if is_coupon_active(code):
                user_data["applied_coupon"] = code
                user_data["step"] = None
                redis_save_user(user_id, user_data)
                process_payment(chat_id, user_id)
            else:
                skip_kb = {"inline_keyboard": [[{"text": "➡️ ادامه بدون کد تخفیف", "callback_data": "skip_coupon"}]]}
                send_ble_message(chat_id, "کد تخفیف نامعتبر یا منقضی شده. دوباره وارد کنید یا رد کنید:", skip_kb)
            return

        if step == "age":
            age = is_valid_int(text, 10, 80)
            if age is None:
                send_ble_message(chat_id, "❌ سن نامعتبر است. عددی بین 10 تا 80 وارد کنید.")
                return
            user_data["age"] = age
            user_data["step"] = "gender"
            redis_save_user(user_id, user_data)
            show_gender_keyboard(chat_id)
            return
        if step == "weight":
            weight = is_valid_int(text, 30, 300)
            if weight is None:
                send_ble_message(chat_id, "❌ وزن نامعتبر است. عددی بین 30 تا 300 وارد کنید.")
                return
            user_data["weight"] = weight
            user_data["step"] = "height"
            redis_save_user(user_id, user_data)
            send_ble_message(chat_id, "📏 قد خود را وارد کنید (سانتی‌متر، بین 100 تا 250):")
            return
        if step == "height":
            height = is_valid_int(text, 100, 250)
            if height is None:
                send_ble_message(chat_id, "❌ قد نامعتبر است. عددی بین 100 تا 250 وارد کنید.")
                return
            user_data["height"] = height
            user_data["step"] = "goal"
            redis_save_user(user_id, user_data)
            show_goal_keyboard(chat_id)
            return
        send_welcome(chat_id, user_id)
    except Exception as e:
        add_log(f"❌ Handle Message Error: {e}")

def _handle_callback(callback_query):
    try:
        callback_query_id = callback_query.get("id")
        callback_data = callback_query.get("data")
        chat_id = callback_query["message"]["chat"]["id"]
        user_id = callback_query["from"]["id"]
        if callback_query_id:
            answer_callback(callback_query_id)
        add_log(f"callback_data = {callback_data} | user_id = {user_id}")
        user_data = redis_get_user(user_id) or {"chat_id": str(chat_id), "user_id": str(user_id), "paid": False, "start_date": get_today_tehran_date()}
        user_data["chat_id"] = str(chat_id)
        if callback_data == "broadcast_target_all":
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            if redis_available:
                redis_client.hset(f"admin:broadcast:{chat_id}", "target", "all")
                redis_client.hset(f"admin:broadcast:{chat_id}", "step", "content")
            send_ble_message(chat_id, "پیام یا عکس خود را برای ارسال به همه کاربران وارد کنید:")
            return
        elif callback_data == "broadcast_target_finished":
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            if redis_available:
                redis_client.hset(f"admin:broadcast:{chat_id}", "target", "finished")
                redis_client.hset(f"admin:broadcast:{chat_id}", "step", "content")
            send_ble_message(chat_id, "پیام یا عکس خود را برای ارسال به کاربران تکمیل‌شده وارد کنید:")
            return
        elif callback_data == "broadcast_target_all_with_cta":
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            if redis_available:
                redis_client.hset(f"admin:broadcast:{chat_id}", "target", "all_with_cta")
                redis_client.hset(f"admin:broadcast:{chat_id}", "step", "content")
            send_ble_message(chat_id, "پیام یا عکس خود را برای ارسال به همه کاربران وارد کنید (دکمه اشتراک ویژه اضافه خواهد شد):")
            return
        elif callback_data == "broadcast_target_finished_with_cta":
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            if redis_available:
                redis_client.hset(f"admin:broadcast:{chat_id}", "target", "finished_with_cta")
                redis_client.hset(f"admin:broadcast:{chat_id}", "step", "content")
            send_ble_message(chat_id, "پیام یا عکس خود را برای ارسال به کاربران تکمیل‌شده وارد کنید (دکمه اشتراک ویژه اضافه خواهد شد):")
            return
        elif callback_data == "broadcast_cancel":
            if redis_available:
                redis_client.delete(f"admin:broadcast:{chat_id}")
            send_ble_message(chat_id, "لغو شد.")
            return
        elif callback_data.startswith("reply_ticket_"):
            if not is_support_staff(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            ticket_id = callback_data.split("_", 2)[2]
            if not ticket_id:
                send_ble_message(chat_id, "تیکت نامعتبر.")
                return
            ticket = get_ticket(ticket_id)
            if not ticket or not ticket.get("ticket_id"):
                send_ble_message(chat_id, "تیکت یافت نشد.")
                return
            lines = [f"🗂 گفتگوی تیکت #{ticket_id} (کاربر {ticket.get('user_id')}):\n"]
            for m in ticket.get("messages", [])[-10:]:
                who = "👤 کاربر" if m.get("from") == "user" else "🛠 پشتیبانی"
                body = m.get("text") or "(عکس)"
                lines.append(f"{who}: {body}")
            send_ble_message(chat_id, "\n".join(lines))
            user_data["admin_reply_step"] = ticket_id
            clear_flow_flags(user_data, keep="admin_reply_step", chat_id=chat_id)
            redis_save_user(user_id, user_data)
            send_ble_message(chat_id, f"پاسخ خود را برای تیکت #{ticket_id} تایپ کنید:")
            return
        elif callback_data.startswith("close_ticket_"):
            ticket_id = callback_data.split("close_ticket_", 1)[1]
            ticket = get_ticket(ticket_id)
            if not ticket or not ticket.get("ticket_id"):
                send_ble_message(chat_id, "تیکت یافت نشد.")
                return
            is_owner = str(user_id) == str(ticket.get("user_id"))
            if not is_owner and not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            ticket["status"] = "closed"
            ticket["updated_at"] = int(time.time())
            save_ticket(ticket_id, ticket)
            if user_data.get("open_ticket_id") == ticket_id:
                user_data["open_ticket_id"] = None
                redis_save_user(user_id, user_data)
            send_ble_message(chat_id, f"✅ تیکت #{ticket_id} بسته شد.")
            return
        elif callback_data == "support_cancel":
            user_data["support_step"] = None
            redis_save_user(user_id, user_data)
            send_ble_message(chat_id, "لغو شد.")
            return
        elif callback_data == "renew_subscription":
            if not user_profile_completed(user_data):
                send_ble_message(chat_id, "📝 لطفاً ابتدا اطلاعات خود را کامل کنید.")
            else:
                send_payment_offer(chat_id, user_id)
            return
        elif callback_data == "payment_history":
            send_payment_history(chat_id, user_id)
            return
        elif callback_data == "accept_upgrade_offer":
            process_upgrade_payment(chat_id, user_id)
            return
        elif callback_data.startswith("vip_user_"):
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            selected_uid = callback_data.split("_", 2)[2]
            user_data["vip_selected_user"] = selected_uid
            redis_save_user(user_id, user_data)
            keyboard = {"inline_keyboard": [
                [{"text": "ماهانه (۳۰ روز)", "callback_data": "vip_monthly"}],
                [{"text": "۶ ماهه (۱۸۰ روز)", "callback_data": "vip_semester"}],
                [{"text": "سالانه (۳۶۵ روز)", "callback_data": "vip_yearly"}]
            ]}
            send_ble_message(chat_id, f"اشتراک را برای کاربر {selected_uid} انتخاب کنید:", keyboard)
            return
        elif callback_data.startswith("vip_page_"):
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            page = int(callback_data.split("_")[2])
            users = get_all_user_ids()
            per_page = 10
            start = (page - 1) * per_page
            end = start + per_page
            page_users = users[start:end]
            keyboard = {"inline_keyboard": []}
            for uid in page_users:
                u = redis_get_user(uid)
                name = u.get("user_id", uid) if u else uid
                keyboard["inline_keyboard"].append([{"text": f"{name}", "callback_data": f"vip_user_{uid}"}])
            nav = []
            if page > 1:
                nav.append({"text": "⬅️ قبلی", "callback_data": f"vip_page_{page-1}"})
            if end < len(users):
                nav.append({"text": "بعدی ➡️", "callback_data": f"vip_page_{page+1}"})
            if nav:
                keyboard["inline_keyboard"].append(nav)
            send_ble_message(chat_id, f"کاربران (صفحه {page}):", keyboard)
            return
        elif callback_data.startswith("admin_list_"):
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            list_type = callback_data.split("_")[2]
            if list_type == "completed":
                users = [uid for uid in get_all_user_ids() if user_profile_completed(redis_get_user(uid))]
            elif list_type == "paid":
                users = [uid for uid in get_all_user_ids() if is_subscription_active(redis_get_user(uid) or {})]
            else:
                users = get_all_user_ids()
            if not users:
                send_ble_message(chat_id, "کاربری یافت نشد.")
                return
            per_page = 10
            page = 1
            start = (page - 1) * per_page
            end = start + per_page
            page_users = users[start:end]
            keyboard = {"inline_keyboard": []}
            for uid in page_users:
                u = redis_get_user(uid)
                name = u.get("user_id", uid) if u else uid
                keyboard["inline_keyboard"].append([{"text": f"{name}", "callback_data": f"admin_view_user_{uid}"}])
            nav = []
            if page > 1:
                nav.append({"text": "⬅️ قبلی", "callback_data": f"admin_list_page_{list_type}_{page-1}"})
            if end < len(users):
                nav.append({"text": "بعدی ➡️", "callback_data": f"admin_list_page_{list_type}_{page+1}"})
            if nav:
                keyboard["inline_keyboard"].append(nav)
            send_ble_message(chat_id, f"کاربران {list_type} (صفحه {page}):", keyboard)
            return
        elif callback_data == "admin_export_csv":
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            file_path = export_users_csv()
            if not file_path:
                send_ble_message(chat_id, "❌ ساخت فایل CSV با خطا مواجه شد.")
                return
            send_ble_document(chat_id, file_path, caption="📥 خروجی کاربران")
            try:
                os.remove(file_path)
            except Exception:
                pass
            return
        elif callback_data == "admin_conversion_report":
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            send_ble_message(chat_id, generate_conversion_report())
            return
        elif callback_data.startswith("admin_list_page_"):
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            parts = callback_data.split("_")
            list_type = parts[3]
            page = int(parts[4])
            if list_type == "completed":
                users = [uid for uid in get_all_user_ids() if user_profile_completed(redis_get_user(uid))]
            elif list_type == "paid":
                users = [uid for uid in get_all_user_ids() if is_subscription_active(redis_get_user(uid) or {})]
            else:
                users = get_all_user_ids()
            per_page = 10
            start = (page - 1) * per_page
            end = start + per_page
            page_users = users[start:end]
            keyboard = {"inline_keyboard": []}
            for uid in page_users:
                u = redis_get_user(uid)
                name = u.get("user_id", uid) if u else uid
                keyboard["inline_keyboard"].append([{"text": f"{name}", "callback_data": f"admin_view_user_{uid}"}])
            nav = []
            if page > 1:
                nav.append({"text": "⬅️ قبلی", "callback_data": f"admin_list_page_{list_type}_{page-1}"})
            if end < len(users):
                nav.append({"text": "بعدی ➡️", "callback_data": f"admin_list_page_{list_type}_{page+1}"})
            if nav:
                keyboard["inline_keyboard"].append(nav)
            send_ble_message(chat_id, f"کاربران {list_type} (صفحه {page}):", keyboard)
            return
        elif callback_data.startswith("admin_view_user_"):
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            target_uid = callback_data.split("_", 3)[3]
            target_data = redis_get_user(target_uid)
            if not target_data:
                send_ble_message(chat_id, "کاربر یافت نشد.")
                return
            text = (f"👤 پروفایل کاربر {target_uid}:\n"
                    f"🎂 سن: {target_data.get('age', '-')}\n"
                    f"⚧ جنسیت: {target_data.get('gender', '-')}\n"
                    f"⚖️ وزن: {target_data.get('weight', '-')} کیلوگرم\n"
                    f"📏 قد: {target_data.get('height', '-')} سانتی‌متر\n"
                    f"🎯 هدف: {target_data.get('goal', '-')}\n"
                    f"🍽️ رژیم: {target_data.get('diet_type', '-')}\n"
                    f"📊 فعالیت: {target_data.get('activity', '-')}\n"
                    f"🔥 کالری روزانه: {target_data.get('bmr', '-')} کیلوکالری\n"
                    f"💳 پرداخت: {target_data.get('paid', False)}\n"
                    f"📅 تاریخ پرداخت: {target_data.get('paid_date', '-')}\n"
                    f"🆔 چت آی‌دی: {target_data.get('chat_id', '-')}\n"
                    f"🔗 ترک آی‌دی: {target_data.get('track_id', '-')}\n")
            keyboard = {"inline_keyboard": [[{"text": "📨 ارسال پیام", "callback_data": f"admin_message_user_{target_uid}"}]]}
            if is_subscription_active(target_data):
                keyboard["inline_keyboard"].append([{"text": "❌ حذف اشتراک این کاربر", "callback_data": f"admin_revoke_confirm_{target_uid}"}])
            send_ble_message(chat_id, text, keyboard)
            return
        elif callback_data.startswith("admin_revoke_confirm_"):
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            target_uid = callback_data.split("_", 3)[3]
            target_data = redis_get_user(target_uid)
            if not target_data:
                send_ble_message(chat_id, "کاربر یافت نشد.")
                return
            kb = {"inline_keyboard": [
                [{"text": "✅ بله، اشتراک حذف شود", "callback_data": f"admin_revoke_do_{target_uid}"}],
                [{"text": "لغو", "callback_data": f"admin_view_user_{target_uid}"}]
            ]}
            send_ble_message(chat_id, f"⚠️ مطمئنی می‌خوای اشتراک کاربر {target_uid} رو همین حالا حذف کنی؟ این کار قابل بازگشت نیست (باید دوباره پرداخت کنه یا خودت دستی فعالش کنی).", kb)
            return
        elif callback_data.startswith("admin_revoke_do_"):
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            target_uid = callback_data.split("_", 3)[3]
            target_data = redis_get_user(target_uid)
            if not target_data:
                send_ble_message(chat_id, "کاربر یافت نشد.")
                return
            target_data["paid"] = False
            target_data["payment_status"] = "revoked_by_admin"
            redis_save_user(target_uid, target_data)
            add_log(f"🛑 admin {chat_id} revoked subscription for user {target_uid}")
            if target_data.get("chat_id"):
                send_ble_message(target_data["chat_id"], "⚠️ اشتراک شما توسط پشتیبانی غیرفعال شد. برای اطلاعات بیشتر با پشتیبانی در تماس باشید.")
            send_ble_message(chat_id, f"✅ اشتراک کاربر {target_uid} حذف شد.")
            return
        elif callback_data.startswith("admin_message_user_"):
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            target_uid = callback_data.split("_", 3)[3]
            user_data["admin_dashboard_step"] = f"view_user_{target_uid}"
            clear_flow_flags(user_data, keep="admin_dashboard_step", chat_id=chat_id)
            redis_save_user(user_id, user_data)
            send_ble_message(chat_id, "پیام خود را تایپ کنید:")
            return
        elif callback_data in ["vip_monthly", "vip_semester", "vip_yearly"]:
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            selected_uid = user_data.get("vip_selected_user")
            if not selected_uid:
                send_ble_message(chat_id, "کاربر انتخاب نشده.")
                return
            if callback_data == "vip_monthly":
                days = MONTHLY_DAYS
                plan = "ماهانه"
            elif callback_data == "vip_semester":
                days = SEMESTER_DAYS
                plan = "۶ ماهه"
            else:
                days = YEARLY_DAYS
                plan = "سالانه"
            target_data = redis_get_user(selected_uid) or {}
            target_data["paid"] = True
            target_data["payment_status"] = "paid"
            target_data["paid_date"] = datetime.now(pytz.timezone("Asia/Tehran")).strftime("%Y-%m-%d")
            target_data["subscription_days"] = days
            redis_save_user(selected_uid, target_data)
            target_chat_id = target_data.get("chat_id")
            if target_chat_id:
                send_ble_message(target_chat_id, f"🎉 اشتراک {plan} ({days} روزه) توسط ادمین برای شما فعال شد!", get_main_keyboard(user_profile_completed(target_data), True))
                cancel_trial_jobs(selected_uid)
                schedule_weekly_workout_for_paid(selected_uid, target_chat_id)
            send_ble_message(chat_id, f"اشتراک {plan} برای کاربر {selected_uid} اعمال شد.")
            user_data["vip_selected_user"] = None
            redis_save_user(user_id, user_data)
            return
        elif callback_data == "set_bank":
            user_data["bank_step"] = "card"
            clear_flow_flags(user_data, keep="bank_step", chat_id=chat_id)
            redis_save_user(user_id, user_data)
            send_ble_message(chat_id, "شماره کارت بانکی خود را وارد کنید (۱۶ رقم):")
            return
        elif callback_data == "cta_payment":
            send_payment_offer(chat_id, user_id)
            return
        elif callback_data.startswith("custom_meal_day_"):
            day = int(callback_data.split("_")[3])
            select_meal_type(chat_id, day)
            return
        elif callback_data.startswith("custom_meal_type_"):
            parts = callback_data.split("_")
            day = int(parts[3])
            meal_type = parts[4]
            input_custom_meal_text(chat_id, user_id, day, meal_type)
            return
        elif callback_data.startswith("custom_workout_week_"):
            week = int(callback_data.split("_")[3])
            select_session_type(chat_id, week)
            return
        elif callback_data.startswith("custom_workout_session_"):
            parts = callback_data.split("_")
            week = int(parts[3])
            session = int(parts[4])
            input_custom_workout_text(chat_id, user_id, week, session)
            return
        elif callback_data == "custom_meal":
            start_custom_meal(chat_id, user_id)
            return
        elif callback_data == "custom_workout":
            start_custom_workout(chat_id, user_id)
            return
        elif callback_data == "custom_back":
            start_customization(chat_id, user_id)
            return
        elif callback_data.startswith("poll_target_"):
            if not is_admin(chat_id):
                send_ble_message(chat_id, "دسترسی ندارید.")
                return
            parts = callback_data.split("_")
            target = parts[2]
            poll_id = "_".join(parts[3:])
            poll = redis_get_poll(poll_id)
            if not poll:
                send_ble_message(chat_id, "نظرسنجی یافت نشد.")
                return
            if target == "completed":
                targets = [uid for uid in get_all_user_ids() if user_profile_completed(redis_get_user(uid))]
            else:
                targets = get_all_user_ids()
            question = poll["question"]
            options = poll["options"]
            keyboard = {"inline_keyboard": []}
            for i, opt in enumerate(options, 1):
                keyboard["inline_keyboard"].append([{"text": opt, "callback_data": f"poll_vote_{poll_id}_{i}"}])
            total_sent = 0
            for t in targets:
                try:
                    send_ble_message(t, f"📊 نظرسنجی:\n{question}", keyboard)
                    total_sent += 1
                except Exception as e:
                    add_log(f"Poll send failed for {t}: {e}")
            send_ble_message(chat_id, f"نظرسنجی ارسال شد به {total_sent} کاربر. برای مشاهده نتایج: /poll_results {poll_id}")
            user_data["poll_step"] = None
            user_data["current_poll_id"] = None
            redis_save_user(user_id, user_data)
            return
        elif callback_data.startswith("poll_vote_"):
            parts = callback_data.split("_")
            poll_id = parts[2]
            vote = parts[3]
            responses = redis_get_poll_responses(poll_id)
            responses[str(user_id)] = vote
            redis_set_poll_responses(poll_id, responses)
            send_ble_message(chat_id, "✅ پاسخ شما ثبت شد. ممنون!")
            return
        if callback_data == "select_monthly":
            user_data["selected_subscription"] = "monthly"
            increment_counter("selected:monthly")
            redis_save_user(user_id, user_data)
            prompt_coupon_or_pay(chat_id, user_id, user_data)
            return
        elif callback_data == "select_semester":
            user_data["selected_subscription"] = "semester"
            increment_counter("selected:semester")
            redis_save_user(user_id, user_data)
            prompt_coupon_or_pay(chat_id, user_id, user_data)
            return
        elif callback_data == "select_yearly":
            user_data["selected_subscription"] = "yearly"
            increment_counter("selected:yearly")
            redis_save_user(user_id, user_data)
            prompt_coupon_or_pay(chat_id, user_id, user_data)
            return
        elif callback_data == "skip_coupon":
            user_data["applied_coupon"] = None
            user_data["step"] = None
            clear_flow_flags(user_data, keep=None, chat_id=chat_id)
            redis_save_user(user_id, user_data)
            process_payment(chat_id, user_id)
            return
        elif callback_data == "enter_coupon":
            user_data["step"] = "coupon"
            clear_flow_flags(user_data, keep="step", chat_id=chat_id)
            redis_save_user(user_id, user_data)
            send_ble_message(chat_id, "کد تخفیف را وارد کنید:")
            return
        elif callback_data == "gender_male":
            user_data["gender"] = "مرد"
            user_data["step"] = "weight"
            redis_save_user(user_id, user_data)
            send_ble_message(chat_id, "⚖️ وزن خود را وارد کنید (کیلوگرم، بین 30 تا 300):")
            return
        elif callback_data == "gender_female":
            user_data["gender"] = "زن"
            user_data["step"] = "weight"
            redis_save_user(user_id, user_data)
            send_ble_message(chat_id, "⚖️ وزن خود را وارد کنید (کیلوگرم، بین 30 تا 300):")
            return
        elif callback_data == "goal_loss":
            user_data["goal"] = "کاهش وزن"
            user_data["step"] = "diet_type"
            redis_save_user(user_id, user_data)
            show_diet_keyboard(chat_id)
            return
        elif callback_data == "goal_gain":
            user_data["goal"] = "افزایش حجم"
            user_data["step"] = "diet_type"
            redis_save_user(user_id, user_data)
            show_diet_keyboard(chat_id)
            return
        elif callback_data == "goal_keep":
            user_data["goal"] = "حفظ تناسب"
            user_data["step"] = "diet_type"
            redis_save_user(user_id, user_data)
            show_diet_keyboard(chat_id)
            return
        elif callback_data == "diet_normal":
            user_data["diet_type"] = "معمولی"
            user_data["step"] = "activity"
            redis_save_user(user_id, user_data)
            show_activity_keyboard(chat_id)
            return
        elif callback_data == "diet_vegetarian":
            user_data["diet_type"] = "گیاهی"
            user_data["step"] = "activity"
            redis_save_user(user_id, user_data)
            show_activity_keyboard(chat_id)
            return
        elif callback_data == "diet_keto":
            user_data["diet_type"] = "کتو"
            user_data["step"] = "activity"
            redis_save_user(user_id, user_data)
            show_activity_keyboard(chat_id)
            return
        elif callback_data == "diet_mediterranean":
            user_data["diet_type"] = "مدیترانه‌ای"
            user_data["step"] = "activity"
            redis_save_user(user_id, user_data)
            show_activity_keyboard(chat_id)
            return
        elif callback_data == "activity_light":
            user_data["activity"] = "سبک"
            finish_onboarding(chat_id, user_id, user_data)
            return
        elif callback_data == "activity_medium":
            user_data["activity"] = "متوسط"
            finish_onboarding(chat_id, user_id, user_data)
            return
        elif callback_data == "activity_heavy":
            user_data["activity"] = "سنگین"
            finish_onboarding(chat_id, user_id, user_data)
            return
    except Exception as e:
        add_log(f"❌ Handle Callback Error: {e}")

def finish_onboarding(chat_id, user_id, user_data):
    try:
        user_data["step"] = "done"
        user_data["bmr"] = calculate_bmr(user_data)
        if not user_data.get("start_date"):
            user_data["start_date"] = get_today_tehran_date()
        user_data["start_weight"] = user_data.get("weight", 70)
        user_data["chat_id"] = str(user_data.get("chat_id", chat_id))
        user_data["user_id"] = str(user_id)
        redis_save_user(user_id, user_data)

        text = (f"✅ ثبت اطلاعات شما کامل شد.\n\n"
                f"🔥 کالری موردنیاز روزانه شما: {user_data['bmr']} کیلوکالری\n"
                f"🎯 هدف: {user_data.get('goal')}\n"
                f"🍽️ رژیم: {user_data.get('diet_type')}\n\n"
                f"🎁 دوره آزمایشی ۳ روزه رایگان شروع شد! برنامه روز اول و هفته اول تمرین ارسال گردید.\n\n"
                f"⏰ همین امروز ۶۰٪ تخفیف اشتراک ویژه داری - این بیشترین تخفیفیه که می‌گیری و فردا کمتر می‌شه!\n\n"
                f"💳 اشتراک ویژه")
        keyboard = {"inline_keyboard": [[{"text": "💳 اشتراک ویژه تهیه کنید", "callback_data": "renew_subscription"}]]}
        send_ble_message(chat_id, text, keyboard)

        send_daily_plan_with_trial_nudge(chat_id, user_id)
        send_workout_program(chat_id, user_id)

        schedule_trial_jobs(user_id, chat_id)

    except Exception as e:
        add_log(f"❌ finish_onboarding error: {e}")

PLAN_LABELS_FA = {"monthly": "ماهانه", "semester": "۶ ماهه", "yearly": "سالانه", "unknown": "نامشخص"}

def generate_conversion_report():
    offer_views = get_counter("offer_views")
    lines = ["📈 گزارش نرخ تبدیل پلن‌ها\n", f"👁 کل بازدید صفحه اشتراک: {offer_views:,}\n"]
    total_completed = 0
    total_revenue = 0
    for plan in ("monthly", "semester", "yearly"):
        selected = get_counter(f"selected:{plan}")
        initiated = get_counter(f"initiated:{plan}")
        completed = get_counter(f"completed:{plan}")
        revenue = get_counter(f"revenue:{plan}")
        total_completed += completed
        total_revenue += revenue
        conv_from_initiated = f"{(completed / initiated * 100):.0f}%" if initiated else "-"
        conv_from_selected = f"{(completed / selected * 100):.0f}%" if selected else "-"
        avg_order = f"{int(revenue / completed):,}" if completed else "-"
        lines.append(
            f"📅 {PLAN_LABELS_FA.get(plan, plan)}:\n"
            f"   انتخاب‌شده: {selected:,} | شروع پرداخت: {initiated:,} | تکمیل‌شده: {completed:,}\n"
            f"   نرخ تبدیل (تکمیل/شروع پرداخت): {conv_from_initiated} | (تکمیل/انتخاب): {conv_from_selected}\n"
            f"   درآمد: {revenue:,} تومان | میانگین هر خرید: {avg_order} تومان\n"
        )
    overall_conv = f"{(total_completed / offer_views * 100):.1f}%" if offer_views else "-"
    lines.append(f"\n💰 مجموع درآمد ثبت‌شده: {total_revenue:,} تومان")
    lines.append(f"🎯 نرخ تبدیل کلی (بازدید → خرید): {overall_conv}")
    lines.append("\nℹ️ این آمار از زمان دیپلوی این نسخه شمارش می‌شه (شامل خریدهای قدیمی‌تر از قبل این آپدیت نیست).")
    return "\n".join(lines)

def generate_dashboard_report(max_recent=10):
    users = []
    if redis_available:
        try:
            keys = redis_client.keys("user:*")
            for key in keys:
                try:
                    data = redis_client.get(key)
                    if data:
                        u = json.loads(data)
                        users.append(u)
                except Exception:
                    continue
        except Exception as e:
            add_log(f"generate_dashboard_report redis error: {e}")
    else:
        users = list(local_users.values())

    total_users = len(users)
    paid_users = sum(1 for u in users if u.get("paid"))
    active_subs = sum(1 for u in users if is_subscription_active(u))
    completed_profiles = sum(1 for u in users if user_profile_completed(u))

    new_last_7 = 0
    recent_payments = []
    try:
        today = datetime.now(pytz.timezone("Asia/Tehran")).date()
        for u in users:
            sd = u.get("start_date")
            if sd:
                try:
                    d = datetime.strptime(sd, "%Y-%m-%d").date()
                    if (today - d).days <= 7:
                        new_last_7 += 1
                except Exception:
                    pass
            pd = u.get("paid_date")
            if pd:
                try:
                    recent_payments.append({
                        "user_id": u.get("user_id") or u.get("chat_id") or "-",
                        "paid_date": pd,
                        "chat_id": u.get("chat_id", "-"),
                        "track_id": u.get("track_id", "-")
                    })
                except Exception:
                    pass
    except Exception:
        pass

    recent_payments = sorted(recent_payments, key=lambda x: x.get("paid_date",""), reverse=True)[:max_recent]

    lines = [
        f"📊 گزارش مدیریتی ربات",
        f"🔸 کل کاربران: {total_users}",
        f"🔸 کاربران پرداخت‌شده (تاکنون): {paid_users}",
        f"🔸 اشتراک فعال: {active_subs}",
        f"🔸 پروفایل کامل: {completed_profiles}",
        f"🔸 کاربران جدید ۷ روز اخیر: {new_last_7}",
        "",
        "📥 آخرین پرداخت‌ها:"
    ]

    if not recent_payments:
        lines.append("— پرداختی ثبت نشده است.")
    else:
        for p in recent_payments:
            uid = p.get("user_id", "-")
            pd = p.get("paid_date", "-")
            cid = p.get("chat_id", "-")
            tid = p.get("track_id", "-")
            lines.append(f"- {uid} | تاریخ:{pd} | chat:{cid} | track:{tid}")

    lines.append("")
    lines.append("ℹ️ برای جزئیات بیشتر نسخه وب داشبورد را استفاده کنید.")
    return "\n".join(lines)

def export_users_csv():
    """Builds a CSV file of all users in a system temp dir and returns its path, or None."""
    users = []
    if redis_available:
        try:
            keys = redis_client.keys("user:*")
            for key in keys:
                try:
                    data = redis_client.get(key)
                    if data:
                        users.append(json.loads(data))
                except Exception:
                    continue
        except Exception as e:
            add_log(f"export_users_csv redis error: {e}")
            return None
    else:
        users = list(local_users.values())

    fields = ["user_id", "chat_id", "age", "gender", "goal", "diet_type", "activity",
              "paid", "payment_status", "subscription_days", "paid_date", "wallet",
              "referral_total_earned", "referral_paid_count", "points", "level", "start_date"]
    try:
        file_path = os.path.join(tempfile.gettempdir(), f"users_export_{int(time.time())}.csv")
        with open(file_path, "w", newline="", encoding="utf-8-sig") as f:
            writer = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
            writer.writeheader()
            for u in users:
                writer.writerow({k: u.get(k, "") for k in fields})
        return file_path
    except Exception as e:
        add_log(f"export_users_csv write error: {e}")
        return None

def start_broadcast_select_target(chat_id):
    if not is_admin(chat_id):
        send_ble_message(chat_id, "دسترسی ندارید.")
        return
    kb = {"inline_keyboard": [
        [{"text": "ارسال به همه", "callback_data": "broadcast_target_all"}],
        [{"text": "ارسال به تکمیل‌شده‌ها", "callback_data": "broadcast_target_finished"}],
        [{"text": "ارسال به همه با دکمه اشتراک ویژه", "callback_data": "broadcast_target_all_with_cta"}],
        [{"text": "ارسال به تکمیل‌شده‌ها با دکمه اشتراک ویژه", "callback_data": "broadcast_target_finished_with_cta"}],
        [{"text": "لغو", "callback_data": "broadcast_cancel"}],
    ]}
    send_ble_message(chat_id, "مخاطبان مورد نظر برای ارسال را انتخاب کنید (حالا با گزینه CTA اشتراک ویژه):", keyboard=kb)

def broadcast_worker(admin_chat_id, content, target, photo=None):
    cta_keyboard = {"inline_keyboard": [[{"text": "💳 اشتراک ویژه تهیه کنید", "callback_data": "cta_payment"}]]} if "with_cta" in target else None
    if target == "finished" or target == "finished_with_cta":
        targets = [uid for uid in get_all_user_ids() if user_profile_completed(redis_get_user(uid))]
    else:
        targets = get_all_user_ids()
    total = len(targets)
    sent = 0
    failed = 0
    for t in targets:
        try:
            send_ble_message(t, content, keyboard=cta_keyboard, photo=photo)
            sent += 1
        except Exception as e:
            add_log(f"Broadcast failed for {t}: {e}")
            failed += 1
        time.sleep(BROADCAST_DELAY)
    send_ble_message(admin_chat_id, f"ارسال به اتمام رسید.\nکل مخاطبین: {total}\nموفق: {sent}\nناموفق: {failed}")
    if redis_available:
        try:
            redis_client.delete(f"admin:broadcast:{admin_chat_id}")
        except Exception:
            pass

def calculate_bmr(user_data):
    weight = int(user_data.get("weight", 70))
    height = int(user_data.get("height", 170))
    age = int(user_data.get("age", 25))
    gender = user_data.get("gender", "مرد")
    activity = user_data.get("activity", "متوسط")
    goal = user_data.get("goal", "حفظ تناسب")
    base = (10 * weight) + (6.25 * height) - (5 * age)
    bmr = base + 5 if gender == "مرد" else base - 161
    factor_map = {"سبک": 1.2, "متوسط": 1.4, "سنگین": 1.6}
    factor = factor_map.get(activity, 1.4)
    tdee = bmr * factor
    # Adjust maintenance calories (TDEE) for the user's actual goal - previously this
    # function returned plain TDEE regardless of goal, so a "weight loss" user was being
    # given maintenance-level calories every day and would never actually lose weight.
    if "کاهش" in goal:
        target = tdee * 0.80  # ~20% deficit for weight loss
    elif "افزایش" in goal:
        target = tdee * 1.12  # ~12% surplus for weight/muscle gain
    else:
        target = tdee
    return int(target)

def user_profile_completed(user_data):
    required_fields = ["age", "gender", "weight", "height", "goal", "diet_type", "activity", "bmr"]
    return all(user_data.get(field) not in [None, "", 0] for field in required_fields)

@atexit.register
def shutdown_scheduler():
    try:
        if scheduler.running:
            scheduler.shutdown()
    except Exception:
        pass

if __name__ == "__main__":
    port = int(os.getenv("PORT", 8080))
    app.run(host="0.0.0.0", port=port)