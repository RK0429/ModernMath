// Dynamic language switcher for ModernMath
// This script updates the language switch link to point to the translated version of the current page

(function() {
    'use strict';

    // Wait for the DOM to be fully loaded
    document.addEventListener('DOMContentLoaded', function() {
        updateLanguageSwitcher();
    });

    // Also update on Quarto page navigation (for SPA-style navigation)
    window.addEventListener('quarto:after-render', function() {
        updateLanguageSwitcher();
    });

    function updateLanguageSwitcher() {
        // Find the language switch link in the navbar
        // Look for links with language emoji or language text
        const allLinks = document.querySelectorAll('.navbar a');
        let langSwitchLink = null;

        // Find the link that contains language switch
        allLinks.forEach(link => {
            const text = link.textContent;
            const href = link.getAttribute('href');

            // Look for language switch patterns
            if (text && href && (
                text.includes('🌐') ||
                text.includes('English') ||
                text.includes('日本語') ||
                (href.includes('/en/') || href.includes('/ja/')) &&
                (text.includes('English') || text.includes('日本語'))
            )) {
                langSwitchLink = link;
            }
        });

        if (!langSwitchLink) {
            console.warn('Language switch link not found in navbar');
            return;
        }

        console.log('Found language switch link:', langSwitchLink.href, langSwitchLink.textContent);

        // Show loading state
        langSwitchLink.style.opacity = '0.7';

        // Try to get translation metadata from the page
        const translationMeta = getTranslationMetadata();

        // Handle results
        if (translationMeta) {
            updateLanguageLink(langSwitchLink, translationMeta);
        } else {
            // No translation metadata found - disable the link
            disableLanguageSwitch(langSwitchLink);
        }
    }

    function getTranslationMetadata() {
        // Method 1: Check for translation data in meta tags (if Quarto exports them)
        const metaTags = document.querySelectorAll('meta[name^="translation-"]');
        const translations = {};

        metaTags.forEach(tag => {
            const name = tag.getAttribute('name');
            const content = tag.getAttribute('content');
            if (name && content) {
                const lang = name.replace('translation-', '');
                translations[lang] = content;
            }
        });

        if (Object.keys(translations).length > 0) {
            return translations;
        }

        // Method 2: Try to extract from the page content
        // Look for translation links in the page (often rendered by Quarto)
        const translationSection = document.querySelector('.translation-links');
        if (translationSection) {
            const links = translationSection.querySelectorAll('a');
            links.forEach(link => {
                const href = link.getAttribute('href');
                const text = link.textContent.toLowerCase();
                if (href) {
                    if (text.includes('english') || text.includes('🇬🇧')) {
                        translations.en = href;
                    } else if (text.includes('日本語') || text.includes('🇯🇵')) {
                        translations.ja = href;
                    }
                }
            });
        }

        // Method 3: Parse from the current URL structure
        // If we can't find metadata, try to construct the translation path
        const currentPath = window.location.pathname;

        // Match language code in path, accounting for GitHub Pages subdirectory
        // Pattern matches /ModernMath/en/... or /ModernMath/ja/... or just /en/... or /ja/...
        const pathMatch = currentPath.match(/^(.*?)\/(en|ja)\/(.*?)$/);

        if (pathMatch) {
            const basePath = pathMatch[1]; // e.g., "/ModernMath" or ""
            const currentLang = pathMatch[2]; // "en" or "ja"
            const pagePath = pathMatch[3]; // rest of the path

            console.log('Detected language path:', { basePath, currentLang, pagePath });

            // Determine target language
            const targetLang = currentLang === 'en' ? 'ja' : 'en';

            // Replace language indicators in the page path as well
            // This handles cases like:
            // - content/ja/algebra/ -> content/en/algebra/
            // - nav/ja/about.html -> nav/en/about.html
            const translatedPagePath = pagePath.replace(
                new RegExp(`(content|nav)/${currentLang}/`, 'g'),
                `$1/${targetLang}/`
            );

            // Construct the translation path
            // This assumes the same file structure in both languages
            const translationPath = `${basePath}/${targetLang}/${translatedPagePath}`;

            console.log('Translation path mapping:', {
                from: currentPath,
                to: translationPath,
                pagePathTransformation: `${pagePath} -> ${translatedPagePath}`
            });

            // For GitHub Pages, we might not be able to check if file exists
            // So let's just assume the translation exists if we have a valid path structure
            // The worst case is a 404 which is acceptable
            translations[targetLang] = translationPath;
            return translations;
        }

        return Object.keys(translations).length > 0 ? translations : null;
    }

    function checkTranslationExists(path) {
        // Use a HEAD request to check if the translation exists
        return fetch(path, { method: 'HEAD' })
            .then(response => response.ok)
            .catch(() => false);
    }

    function updateLanguageLink(linkElement, translations) {
        const currentLang = detectCurrentLanguage();
        const targetLang = currentLang === 'en' ? 'ja' : 'en';

        console.log('Updating language link:', { currentLang, targetLang, translations });

        if (translations[targetLang]) {
            // Update the href to point to the translated version
            linkElement.setAttribute('href', translations[targetLang]);
            linkElement.classList.remove('disabled');
            linkElement.style.opacity = '1';
            linkElement.style.cursor = 'pointer';
            linkElement.removeAttribute('aria-disabled');
            linkElement.removeAttribute('title');

            // Update the text to indicate it's available
            if (targetLang === 'ja') {
                linkElement.innerHTML = '🌐 日本語';
            } else {
                linkElement.innerHTML = '🌐 English';
            }

            // Remove any click handlers that might interfere
            linkElement.onclick = null;

            console.log('Language link updated to:', linkElement.href);
        } else {
            disableLanguageSwitch(linkElement);
        }
    }

    function disableLanguageSwitch(linkElement) {
        const currentLang = detectCurrentLanguage();
        const targetLang = currentLang === 'en' ? 'ja' : 'en';

        // Disable the link
        linkElement.classList.add('disabled');
        linkElement.style.opacity = '0.5';
        linkElement.style.cursor = 'not-allowed';
        linkElement.setAttribute('aria-disabled', 'true');

        // Add tooltip explaining why it's disabled
        const tooltipText = targetLang === 'ja'
            ? 'Japanese translation not available'
            : '英語版は利用できません';
        linkElement.setAttribute('title', tooltipText);

        // Update the text to show it's unavailable
        if (targetLang === 'ja') {
            linkElement.innerHTML = '🌐 <s>日本語</s>';
        } else {
            linkElement.innerHTML = '🌐 <s>English</s>';
        }

        // Prevent click
        linkElement.onclick = function(e) {
            e.preventDefault();
            return false;
        };
    }

    function detectCurrentLanguage() {
        // Detect from URL path
        const path = window.location.pathname;
        if (path.includes('/ja/')) return 'ja';
        if (path.includes('/en/')) return 'en';

        // Detect from HTML lang attribute
        const htmlLang = document.documentElement.getAttribute('lang');
        if (htmlLang) {
            return htmlLang.startsWith('ja') ? 'ja' : 'en';
        }

        // Default to English
        return 'en';
    }

    // Export for debugging
    window.ModernMathLanguageSwitcher = {
        update: updateLanguageSwitcher,
        getTranslationMetadata: getTranslationMetadata,
        detectCurrentLanguage: detectCurrentLanguage
    };

})();
