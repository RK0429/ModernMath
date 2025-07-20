"""
Monitoring utilities for the Math Knowledge Graph API
Provides logging, metrics collection, and health monitoring
"""

import time
import json
import logging
from datetime import datetime, timedelta
from typing import Dict, Any, Optional, Callable
from collections import defaultdict, deque
from functools import wraps
from flask import request, g
import threading
import os


# Configure structured logging
class StructuredLogger:
    """Structured logging with JSON output for better monitoring"""
    
    def __init__(self, name: str):
        self.logger = logging.getLogger(name)
        handler = logging.StreamHandler()
        formatter = logging.Formatter(
            '{"timestamp": "%(asctime)s", "level": "%(levelname)s", '
            '"module": "%(name)s", "message": "%(message)s"}'
        )
        handler.setFormatter(formatter)
        self.logger.addHandler(handler)
        self.logger.setLevel(logging.INFO)
    
    def log_api_request(self, endpoint: str, method: str, status_code: int, 
                       duration_ms: float, user_ip: str, **kwargs):
        """Log API request with structured data"""
        log_data = {
            "type": "api_request",
            "endpoint": endpoint,
            "method": method,
            "status_code": status_code,
            "duration_ms": round(duration_ms, 2),
            "user_ip": user_ip,
            "timestamp": datetime.utcnow().isoformat(),
            **kwargs
        }
        self.logger.info(json.dumps(log_data))
    
    def log_error(self, error_type: str, error_message: str, **kwargs):
        """Log errors with structured data"""
        log_data = {
            "type": "error",
            "error_type": error_type,
            "error_message": error_message,
            "timestamp": datetime.utcnow().isoformat(),
            **kwargs
        }
        self.logger.error(json.dumps(log_data))
    
    def log_metric(self, metric_name: str, value: Any, **kwargs):
        """Log metrics for monitoring"""
        log_data = {
            "type": "metric",
            "metric_name": metric_name,
            "value": value,
            "timestamp": datetime.utcnow().isoformat(),
            **kwargs
        }
        self.logger.info(json.dumps(log_data))


# Metrics collector
class MetricsCollector:
    """Collect and store application metrics"""
    
    def __init__(self, window_size_minutes: int = 60):
        self.window_size = timedelta(minutes=window_size_minutes)
        self.lock = threading.Lock()
        
        # Request metrics
        self.request_counts = defaultdict(int)
        self.response_times = defaultdict(list)
        self.status_codes = defaultdict(int)
        self.error_counts = defaultdict(int)
        
        # Query metrics
        self.query_counts = defaultdict(int)
        self.query_times = defaultdict(list)
        
        # Time-series data (using deques for efficient sliding windows)
        self.requests_per_minute = deque(maxlen=window_size_minutes)
        self.errors_per_minute = deque(maxlen=window_size_minutes)
        
        # Start metrics cleanup thread
        self._start_cleanup_thread()
    
    def record_request(self, endpoint: str, method: str, status_code: int, 
                      duration_ms: float):
        """Record API request metrics"""
        with self.lock:
            key = f"{method}:{endpoint}"
            self.request_counts[key] += 1
            self.response_times[key].append(duration_ms)
            self.status_codes[str(status_code)] += 1
            
            if status_code >= 400:
                self.error_counts[key] += 1
    
    def record_query(self, query_type: str, duration_ms: float):
        """Record SPARQL query metrics"""
        with self.lock:
            self.query_counts[query_type] += 1
            self.query_times[query_type].append(duration_ms)
    
    def get_metrics_summary(self) -> Dict[str, Any]:
        """Get summary of collected metrics"""
        with self.lock:
            # Calculate response time statistics
            response_stats = {}
            for endpoint, times in self.response_times.items():
                if times:
                    response_stats[endpoint] = {
                        "count": len(times),
                        "avg_ms": round(sum(times) / len(times), 2),
                        "min_ms": round(min(times), 2),
                        "max_ms": round(max(times), 2),
                        "p95_ms": round(self._percentile(times, 95), 2)
                    }
            
            # Calculate query time statistics
            query_stats = {}
            for query_type, times in self.query_times.items():
                if times:
                    query_stats[query_type] = {
                        "count": len(times),
                        "avg_ms": round(sum(times) / len(times), 2),
                        "max_ms": round(max(times), 2)
                    }
            
            return {
                "request_counts": dict(self.request_counts),
                "response_times": response_stats,
                "status_codes": dict(self.status_codes),
                "error_counts": dict(self.error_counts),
                "query_stats": query_stats,
                "total_requests": sum(self.request_counts.values()),
                "total_errors": sum(self.error_counts.values())
            }
    
    def _percentile(self, data: list, percentile: int) -> float:
        """Calculate percentile value"""
        if not data:
            return 0
        sorted_data = sorted(data)
        index = int(len(sorted_data) * (percentile / 100))
        return sorted_data[min(index, len(sorted_data) - 1)]
    
    def _start_cleanup_thread(self):
        """Start thread to periodically clean old metrics"""
        def cleanup_loop():
            while True:
                time.sleep(300)  # Clean every 5 minutes
                self._cleanup_old_metrics()
        
        cleanup_thread = threading.Thread(target=cleanup_loop, daemon=True)
        cleanup_thread.start()
    
    def _cleanup_old_metrics(self):
        """Clean up old metrics to prevent memory growth"""
        with self.lock:
            # Keep only last 1000 response times per endpoint
            for key in self.response_times:
                if len(self.response_times[key]) > 1000:
                    self.response_times[key] = self.response_times[key][-1000:]
            
            # Keep only last 1000 query times per type
            for key in self.query_times:
                if len(self.query_times[key]) > 1000:
                    self.query_times[key] = self.query_times[key][-1000:]


# Global instances
structured_logger = StructuredLogger("math_kg_api")
metrics_collector = MetricsCollector()


# Flask request monitoring decorator
def monitor_request(f: Callable) -> Callable:
    """Decorator to monitor Flask requests"""
    @wraps(f)
    def decorated_function(*args, **kwargs):
        # Record start time
        g.start_time = time.time()
        
        # Execute the request
        try:
            response = f(*args, **kwargs)
            
            # Calculate duration
            duration_ms = (time.time() - g.start_time) * 1000
            
            # Extract status code
            status_code = response[1] if isinstance(response, tuple) else 200
            
            # Record metrics
            metrics_collector.record_request(
                request.endpoint,
                request.method,
                status_code,
                duration_ms
            )
            
            # Log request
            structured_logger.log_api_request(
                endpoint=request.endpoint,
                method=request.method,
                status_code=status_code,
                duration_ms=duration_ms,
                user_ip=request.remote_addr,
                user_agent=request.headers.get('User-Agent', ''),
                query_params=dict(request.args)
            )
            
            return response
            
        except Exception as e:
            # Calculate duration
            duration_ms = (time.time() - g.start_time) * 1000
            
            # Record error
            metrics_collector.record_request(
                request.endpoint,
                request.method,
                500,
                duration_ms
            )
            
            # Log error
            structured_logger.log_error(
                error_type=type(e).__name__,
                error_message=str(e),
                endpoint=request.endpoint,
                method=request.method,
                user_ip=request.remote_addr
            )
            
            raise
    
    return decorated_function


# SPARQL query monitoring
def monitor_sparql_query(query_type: str):
    """Decorator to monitor SPARQL query execution"""
    def decorator(f: Callable) -> Callable:
        @wraps(f)
        def decorated_function(*args, **kwargs):
            start_time = time.time()
            
            try:
                result = f(*args, **kwargs)
                duration_ms = (time.time() - start_time) * 1000
                
                # Record successful query
                metrics_collector.record_query(query_type, duration_ms)
                
                # Log if query is slow
                if duration_ms > 1000:  # Log queries over 1 second
                    structured_logger.log_metric(
                        "slow_query",
                        duration_ms,
                        query_type=query_type
                    )
                
                return result
                
            except Exception as e:
                duration_ms = (time.time() - start_time) * 1000
                
                # Log query error
                structured_logger.log_error(
                    error_type="sparql_error",
                    error_message=str(e),
                    query_type=query_type,
                    duration_ms=duration_ms
                )
                
                raise
        
        return decorated_function
    return decorator


# Health check utilities
class HealthChecker:
    """Check health of various system components"""
    
    @staticmethod
    def check_fuseki_health(endpoint: str) -> Dict[str, Any]:
        """Check if Fuseki endpoint is healthy"""
        try:
            from SPARQLWrapper import SPARQLWrapper, JSON
            start_time = time.time()
            
            sparql = SPARQLWrapper(endpoint)
            sparql.setQuery("SELECT ?s WHERE { ?s ?p ?o } LIMIT 1")
            sparql.setReturnFormat(JSON)
            sparql.setTimeout(5)
            
            result = sparql.query().convert()
            duration_ms = (time.time() - start_time) * 1000
            
            return {
                "status": "healthy",
                "response_time_ms": round(duration_ms, 2)
            }
            
        except Exception as e:
            return {
                "status": "unhealthy",
                "error": str(e)
            }
    
    @staticmethod
    def check_search_index_health(index_dir: str) -> Dict[str, Any]:
        """Check if search index is accessible"""
        try:
            if os.path.exists(index_dir) and os.listdir(index_dir):
                return {"status": "healthy"}
            else:
                return {"status": "unhealthy", "error": "Index directory empty or missing"}
        except Exception as e:
            return {"status": "unhealthy", "error": str(e)}
    
    @staticmethod
    def get_system_health(fuseki_endpoint: str, search_index_dir: str) -> Dict[str, Any]:
        """Get overall system health status"""
        return {
            "timestamp": datetime.utcnow().isoformat(),
            "components": {
                "api": {"status": "healthy"},  # API is healthy if this runs
                "fuseki": HealthChecker.check_fuseki_health(fuseki_endpoint),
                "search_index": HealthChecker.check_search_index_health(search_index_dir)
            },
            "metrics_summary": metrics_collector.get_metrics_summary()
        }


# Export monitoring functions for Flask app
def init_monitoring(app):
    """Initialize monitoring for Flask app"""
    
    @app.before_request
    def before_request():
        g.start_time = time.time()
    
    @app.after_request
    def after_request(response):
        if hasattr(g, 'start_time'):
            duration_ms = (time.time() - g.start_time) * 1000
            
            # Add response time header
            response.headers['X-Response-Time'] = f"{duration_ms:.2f}ms"
            
            # Log request (skip health checks to reduce noise)
            if request.endpoint != 'health_check':
                metrics_collector.record_request(
                    request.endpoint or 'unknown',
                    request.method,
                    response.status_code,
                    duration_ms
                )
        
        return response
    
    # Add monitoring endpoints
    @app.route('/api/metrics', methods=['GET'])
    def get_metrics():
        """Get current metrics"""
        return metrics_collector.get_metrics_summary()
    
    @app.route('/api/health/detailed', methods=['GET'])
    def detailed_health():
        """Get detailed health status"""
        fuseki_endpoint = app.config.get('FUSEKI_ENDPOINT', 'http://localhost:3030/mathwiki/sparql')
        search_index_dir = app.config.get('SEARCH_INDEX_DIR', 'search_index')
        
        return HealthChecker.get_system_health(fuseki_endpoint, search_index_dir)