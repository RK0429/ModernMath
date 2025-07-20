#!/bin/bash
# Build multilingual ModernMath site
# Note: The CI/CD pipeline uses .github/workflows/build.yml for automated builds

echo "Building multilingual ModernMath site..."

# Build English version
echo "Building English version..."
quarto render --profile en

# Build Japanese version
echo "Building Japanese version..."
quarto render --profile ja

# Fix Japanese index page
echo "Fixing Japanese index page..."
poetry run python scripts/fix_japanese_index.py

# Create language detection index.html
echo "Creating language detection page..."
cat > _site/index.html << 'EOF'
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Math Knowledge Graph - 数学知識グラフ</title>
    <style>
        body {
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            height: 100vh;
            margin: 0;
            background-color: #f5f5f5;
        }
        .container {
            text-align: center;
            background: white;
            padding: 3rem;
            border-radius: 10px;
            box-shadow: 0 2px 10px rgba(0, 0, 0, 0.1);
            max-width: 500px;
        }
        h1 {
            margin-bottom: 2rem;
            color: #333;
        }
        .lang-buttons {
            display: flex;
            gap: 2rem;
            justify-content: center;
            margin-top: 2rem;
        }
        .lang-button {
            display: flex;
            flex-direction: column;
            align-items: center;
            text-decoration: none;
            padding: 1.5rem 2rem;
            border: 2px solid #ddd;
            border-radius: 8px;
            transition: all 0.3s ease;
            background: white;
            color: #333;
            min-width: 120px;
        }
        .lang-button:hover {
            border-color: #0366d6;
            box-shadow: 0 4px 12px rgba(3, 102, 214, 0.2);
            transform: translateY(-2px);
        }
        .flag {
            font-size: 3rem;
            margin-bottom: 0.5rem;
        }
        .lang-name {
            font-size: 1.2rem;
            font-weight: 500;
        }
        .loading {
            color: #666;
            font-style: italic;
            margin: 2rem 0;
        }
    </style>
    <script>
        // Check for saved language preference
        const savedLang = localStorage.getItem('preferredLanguage');

        if (savedLang) {
            // Redirect immediately if we have a saved preference
            window.location.href = './' + savedLang + '/index.html';
        } else {
            // Otherwise, detect language and redirect after page loads
            document.addEventListener('DOMContentLoaded', function() {
                const loadingElement = document.getElementById('loading');

                // Auto-detect after a short delay to show the page
                setTimeout(function() {
                    if (loadingElement) {
                        loadingElement.textContent = 'Detecting language...';
                    }

                    const userLang = navigator.language || navigator.userLanguage;
                    const lang = userLang.startsWith('ja') ? 'ja' : 'en';

                    setTimeout(function() {
                        window.location.href = './' + lang + '/index.html';
                    }, 500);
                }, 1000);
            });
        }

        function selectLanguage(lang) {
            // Save preference
            localStorage.setItem('preferredLanguage', lang);
            // Redirect
            window.location.href = './' + lang + '/index.html';
        }
    </script>
</head>
<body>
    <div class="container">
        <h1>Mathematics Knowledge Graph<br>数学知識グラフ</h1>

        <p id="loading" class="loading">Preparing to redirect based on your language preference...</p>

        <div class="lang-buttons">
            <a href="#" onclick="selectLanguage('en'); return false;" class="lang-button">
                <div class="flag">🇬🇧</div>
                <div class="lang-name">English</div>
            </a>
            <a href="#" onclick="selectLanguage('ja'); return false;" class="lang-button">
                <div class="flag">🇯🇵</div>
                <div class="lang-name">日本語</div>
            </a>
        </div>

        <p style="margin-top: 2rem; color: #666; font-size: 0.9rem;">
            Choose your preferred language or wait for automatic detection<br>
            言語を選択するか、自動検出をお待ちください
        </p>
    </div>
</body>
</html>
EOF

# Create .nojekyll file for GitHub Pages
touch _site/.nojekyll

echo "Build complete!"
