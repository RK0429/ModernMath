"""
Simple in-memory caching module for the Math Knowledge Graph API
Provides time-based caching without external dependencies
"""

import time
import functools
import hashlib
import json
from typing import Callable, Any, Optional, Dict
from threading import Lock


class SimpleCache:
    """Thread-safe in-memory cache with TTL support"""
    
    def __init__(self):
        self._cache: Dict[str, tuple[Any, float]] = {}
        self._lock = Lock()
    
    def get(self, key: str) -> Optional[Any]:
        """Get a value from cache if it exists and hasn't expired"""
        with self._lock:
            if key in self._cache:
                value, expiry = self._cache[key]
                if time.time() < expiry:
                    return value
                else:
                    # Remove expired entry
                    del self._cache[key]
        return None
    
    def set(self, key: str, value: Any, ttl: int = 300):
        """Set a value in cache with TTL (default 5 minutes)"""
        expiry = time.time() + ttl
        with self._lock:
            self._cache[key] = (value, expiry)
    
    def clear(self):
        """Clear all cache entries"""
        with self._lock:
            self._cache.clear()
    
    def remove(self, key: str):
        """Remove a specific key from cache"""
        with self._lock:
            self._cache.pop(key, None)
    
    def cleanup_expired(self):
        """Remove all expired entries"""
        current_time = time.time()
        with self._lock:
            expired_keys = [
                key for key, (_, expiry) in self._cache.items()
                if current_time >= expiry
            ]
            for key in expired_keys:
                del self._cache[key]


# Global cache instance
_cache = SimpleCache()


def cache_key(*args, **kwargs) -> str:
    """Generate a cache key from function arguments"""
    # Convert args and kwargs to a string representation
    key_data = {
        'args': args,
        'kwargs': kwargs
    }
    key_str = json.dumps(key_data, sort_keys=True, default=str)
    # Create a hash of the key string
    return hashlib.md5(key_str.encode()).hexdigest()


def cached(ttl: int = 300):
    """
    Decorator to cache function results
    
    Args:
        ttl: Time to live in seconds (default 5 minutes)
    """
    def decorator(func: Callable) -> Callable:
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            # Generate cache key
            key = f"{func.__name__}:{cache_key(*args, **kwargs)}"
            
            # Try to get from cache
            cached_value = _cache.get(key)
            if cached_value is not None:
                return cached_value
            
            # Call the function and cache the result
            result = func(*args, **kwargs)
            _cache.set(key, result, ttl)
            
            return result
        
        # Add cache management methods to the wrapper
        wrapper.cache_clear = lambda: _cache.clear()
        wrapper.cache_remove = lambda *args, **kwargs: _cache.remove(
            f"{func.__name__}:{cache_key(*args, **kwargs)}"
        )
        
        return wrapper
    return decorator


def api_cache(ttl: int = 300):
    """
    Decorator specifically for Flask API endpoints
    Handles response objects properly
    """
    def decorator(func: Callable) -> Callable:
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            # For API endpoints, we need to be careful with Flask's request context
            from flask import request
            
            # Include request parameters in cache key
            cache_data = {
                'endpoint': request.endpoint,
                'args': args,
                'kwargs': kwargs,
                'params': dict(request.args),
                'method': request.method
            }
            
            key = f"api:{cache_key(cache_data)}"
            
            # Try to get from cache
            cached_value = _cache.get(key)
            if cached_value is not None:
                # Reconstruct the response
                from flask import jsonify
                return jsonify(cached_value)
            
            # Call the function
            response = func(*args, **kwargs)
            
            # Cache only successful JSON responses
            if hasattr(response, 'status_code') and response.status_code == 200:
                # Extract JSON data from response
                if hasattr(response, 'get_json'):
                    json_data = response.get_json()
                    _cache.set(key, json_data, ttl)
            
            return response
        
        return wrapper
    return decorator


# Periodic cleanup function (optional - can be called by a background thread)
def cleanup_cache():
    """Remove expired entries from cache"""
    _cache.cleanup_expired()