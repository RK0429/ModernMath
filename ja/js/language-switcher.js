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
        const navLinks = document.querySelectorAll('.navbar-nav .nav-link');
        let langSwitchLink = null;

        // Find the link that contains language switch (looking for ../en/ or ../ja/)
        navLinks.forEach(link => {
            const href = link.getAttribute('href');
            if (href && (href.includes('../en/') || href.includes('../ja/'))) {
                langSwitchLink = link;
            }
        });

        if (!langSwitchLink) {
            console.warn('Language switch link not found in navbar');
            return;
        }

        // Show loading state
        langSwitchLink.style.opacity = '0.7';

        // Try to get translation metadata from the page
        const translationMeta = getTranslationMetadata();

        // Handle both sync and async results
        if (translationMeta && translationMeta.then) {
            // It's a promise - handle async
            translationMeta.then(translations => {
                if (translations) {
                    updateLanguageLink(langSwitchLink, translations);
                } else {
                    disableLanguageSwitch(langSwitchLink);
                }
            }).catch(error => {
                console.error('Error checking translation:', error);
                disableLanguageSwitch(langSwitchLink);
            });
        } else if (translationMeta) {
            // Sync result
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
        const pathMatch = currentPath.match(/\/(en|ja)\/(.*)/);

        if (pathMatch) {
            const currentLang = pathMatch[1];
            const pagePath = pathMatch[2];

            // Determine target language
            const targetLang = currentLang === 'en' ? 'ja' : 'en';

            // Construct the translation path
            // This assumes the same file structure in both languages
            const translationPath = currentPath.replace(`/${currentLang}/`, `/${targetLang}/`);

            // Check if the translation file exists by attempting to fetch it
            return checkTranslationExists(translationPath).then(exists => {
                if (exists) {
                    translations[targetLang] = translationPath;
                    return translations;
                }
                return null;
            });
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
