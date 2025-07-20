#!/usr/bin/env python3
"""
Test script to verify API caching functionality
"""

import requests
import time

BASE_URL = "http://localhost:5001/api"


def test_cache():
    """Test that caching is working properly"""

    print("Testing API Cache Implementation")
    print("=" * 50)

    # 1. Test cache stats endpoint
    print("\n1. Testing cache stats endpoint...")
    response = requests.get(f"{BASE_URL}/cache/stats")
    if response.status_code == 200:
        stats = response.json()
        print(f"   ✓ Cache stats: {stats}")
    else:
        print(f"   ✗ Failed to get cache stats: {response.status_code}")

    # 2. Clear cache to start fresh
    print("\n2. Clearing cache...")
    response = requests.post(f"{BASE_URL}/cache/clear")
    if response.status_code == 200:
        print("   ✓ Cache cleared successfully")
    else:
        print(f"   ✗ Failed to clear cache: {response.status_code}")

    # 3. Test a cached endpoint
    print("\n3. Testing cached endpoint (first call)...")
    start_time = time.time()
    response = requests.get(f"{BASE_URL}/nodes/def-group")
    first_call_time = time.time() - start_time

    if response.status_code == 200:
        print(f"   ✓ First call successful (took {first_call_time:.3f}s)")
        first_result = response.json()
    else:
        print(f"   ✗ Failed to get node: {response.status_code}")
        return

    # 4. Test the same endpoint again (should be cached)
    print("\n4. Testing cached endpoint (second call - should be faster)...")
    start_time = time.time()
    response = requests.get(f"{BASE_URL}/nodes/def-group")
    second_call_time = time.time() - start_time

    if response.status_code == 200:
        print(f"   ✓ Second call successful (took {second_call_time:.3f}s)")
        second_result = response.json()

        # Verify results are the same
        if first_result == second_result:
            print("   ✓ Results match between calls")
        else:
            print("   ✗ Results differ between calls!")

        # Check if second call was faster (indicating cache hit)
        if second_call_time < first_call_time:
            speedup = first_call_time / second_call_time
            print(f"   ✓ Second call was {speedup:.1f}x faster (cache hit)")
        else:
            print("   ⚠ Second call was not faster (possible cache miss)")
    else:
        print(f"   ✗ Failed to get node: {response.status_code}")

    # 5. Check cache stats again
    print("\n5. Checking cache stats after calls...")
    response = requests.get(f"{BASE_URL}/cache/stats")
    if response.status_code == 200:
        stats = response.json()
        print(f"   ✓ Cache stats: {stats}")
        if stats["cache_entries"] > 0:
            print(f"   ✓ Cache contains {stats['cache_entries']} entries")
        else:
            print("   ⚠ Cache is empty (unexpected)")
    else:
        print(f"   ✗ Failed to get cache stats: {response.status_code}")

    # 6. Test search endpoint caching
    print("\n6. Testing search endpoint caching...")
    search_term = "group"

    start_time = time.time()
    response = requests.get(f"{BASE_URL}/search", params={"q": search_term})
    first_search_time = time.time() - start_time
    print(f"   First search took {first_search_time:.3f}s")

    start_time = time.time()
    response = requests.get(f"{BASE_URL}/search", params={"q": search_term})
    second_search_time = time.time() - start_time
    print(f"   Second search took {second_search_time:.3f}s")

    if second_search_time < first_search_time:
        speedup = first_search_time / second_search_time
        print(f"   ✓ Search caching working ({speedup:.1f}x faster)")
    else:
        print("   ⚠ Search caching may not be working")

    print("\n" + "=" * 50)
    print("Cache testing complete!")


if __name__ == "__main__":
    try:
        # Check if API is running
        response = requests.get(f"{BASE_URL}/health")
        if response.status_code != 200:
            print("Error: API is not running. Please start the API first.")
            print("Run: cd api && python app.py")
            exit(1)
    except requests.exceptions.ConnectionError:
        print("Error: Cannot connect to API. Please start the API first.")
        print("Run: cd api && python app.py")
        exit(1)

    test_cache()
