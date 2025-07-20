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

# Create root index.html redirect
cat > _site/index.html << 'EOF'
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Math Knowledge Graph - 数学知識グラフ</title>
    <script>
        // Detect user language preference
        const userLang = navigator.language || navigator.userLanguage;
        const lang = userLang.startsWith('ja') ? 'ja' : 'en';
        window.location.href = './' + lang + '/index.html';
    </script>
</head>
<body>
    <p>Redirecting to your preferred language...</p>
    <p>言語設定に基づいてリダイレクトしています...</p>
    <p>
        <a href="./en/index.html">English</a> |
        <a href="./ja/index.html">日本語</a>
    </p>
</body>
</html>
EOF

# Create .nojekyll file for GitHub Pages
touch _site/.nojekyll

echo "Build complete!"
