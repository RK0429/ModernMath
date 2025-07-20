#!/usr/bin/env python3
"""
Test script for API rate limiting
Tests that rate limits are properly enforced
"""

import requests
import time
import sys


def test_rate_limit(endpoint: str, limit: int, window: str = "minute"):
    """Test rate limiting on a specific endpoint"""
    base_url = "http://localhost:5001"
    url = f"{base_url}{endpoint}"
    
    print(f"\nTesting rate limit on {endpoint}")
    print(f"Expected limit: {limit} per {window}")
    print("-" * 50)
    
    successful_requests = 0
    rate_limited = False
    
    # Make requests until we hit the rate limit
    for i in range(limit + 5):
        try:
            response = requests.get(url)
            
            # Check rate limit headers
            if 'X-RateLimit-Limit' in response.headers:
                print(f"Request {i+1}: Status={response.status_code}, "
                      f"Limit={response.headers.get('X-RateLimit-Limit')}, "
                      f"Remaining={response.headers.get('X-RateLimit-Remaining')}")
            else:
                print(f"Request {i+1}: Status={response.status_code}")
            
            if response.status_code == 200:
                successful_requests += 1
            elif response.status_code == 429:
                rate_limited = True
                retry_after = response.headers.get('Retry-After', 'Unknown')
                print(f"Rate limited! Retry after: {retry_after} seconds")
                print(f"Response: {response.json()}")
                break
                
        except requests.exceptions.ConnectionError:
            print("Error: Could not connect to API. Make sure the API server is running.")
            sys.exit(1)
        except Exception as e:
            print(f"Error: {e}")
            
        # Small delay between requests
        time.sleep(0.1)
    
    print(f"\nResults: {successful_requests} successful requests before rate limit")
    
    if not rate_limited and successful_requests > limit:
        print("WARNING: Rate limit not enforced!")
        return False
    elif rate_limited and successful_requests <= limit:
        print("SUCCESS: Rate limit properly enforced!")
        return True
    else:
        print("UNEXPECTED: Check rate limit configuration")
        return False


def main():
    """Run rate limit tests on various endpoints"""
    print("Math Knowledge Graph API - Rate Limit Testing")
    print("=" * 50)
    
    # Check if API is running
    try:
        response = requests.get("http://localhost:5001/api/health")
        if response.status_code != 200:
            print("API health check failed. Make sure the API server is running.")
            sys.exit(1)
    except:
        print("Could not connect to API at http://localhost:5001")
        print("Please start the API server with: cd api && ./start_api.sh")
        sys.exit(1)
    
    # Test different endpoints
    test_cases = [
        ("/api/health", 100),  # 100 per minute
        ("/api/search?q=group", 20),  # 20 per minute  
        ("/api/nodes", 10),  # 10 per minute
        ("/api/nodes/def-group", 30),  # 30 per minute
    ]
    
    results = []
    for endpoint, limit in test_cases:
        result = test_rate_limit(endpoint, limit)
        results.append((endpoint, result))
        
        # Wait a bit between tests
        if endpoint != test_cases[-1][0]:
            print("\nWaiting before next test...")
            time.sleep(2)
    
    # Summary
    print("\n" + "=" * 50)
    print("Test Summary:")
    print("-" * 50)
    for endpoint, result in results:
        status = "PASSED" if result else "FAILED"
        print(f"{endpoint}: {status}")
    
    all_passed = all(result for _, result in results)
    if all_passed:
        print("\nAll rate limit tests PASSED!")
    else:
        print("\nSome rate limit tests FAILED!")
        sys.exit(1)


if __name__ == "__main__":
    main()