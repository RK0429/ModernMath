#!/usr/bin/env python3
"""
Simple test to check if rate limiting returns 429 status code
"""

import requests
import time

# Test the health endpoint which has 100 req/min limit
url = "http://localhost:5001/api/health"

print("Testing rate limit on /api/health endpoint")
print("Making requests until we hit the rate limit...")

for i in range(105):
    response = requests.get(url)

    remaining = response.headers.get('X-RateLimit-Remaining', 'N/A')
    status = response.status_code

    print(f"Request {i+1}: Status={status}, Remaining={remaining}")

    if status == 429:
        print("\nRate limit hit! Got 429 status code.")
        print(f"Response: {response.json()}")
        print(f"Retry-After: {response.headers.get('Retry-After', 'N/A')}")
        break
    elif status != 200:
        print(f"\nUnexpected status code: {status}")
        print(f"Response: {response.text}")

    # When remaining hits 0, the next request should be rate limited
    if remaining == '0':
        print("\nRemaining is 0, next request should be rate limited...")

    time.sleep(0.05)  # Small delay

print("\nNote: If you're seeing 500 errors instead of 429, the API server needs to be restarted.")
