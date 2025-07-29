// Mobile Footer for ModernMath
// Combines Report Issue, Language Switch, and Buy Me a Coffee buttons in a horizontal footer

(function () {
  "use strict";

  // Configuration
  const GITHUB_REPO = "RK0429/ModernMath";
  const BUYMEACOFFEE_URL = "https://www.buymeacoffee.com/RK0429";

  // Helper function to detect mobile device
  function isMobile() {
    return (
      window.innerWidth <= 768 ||
      /mobile|android|iphone|ipad|phone/i.test(
        navigator.userAgent.toLowerCase(),
      )
    );
  }

  // Helper function to detect current language
  function detectCurrentLanguage() {
    const path = window.location.pathname;
    if (path.includes("/ja/")) return "ja";
    if (path.includes("/en/")) return "en";

    const htmlLang = document.documentElement.getAttribute("lang");
    if (htmlLang) {
      return htmlLang.startsWith("ja") ? "ja" : "en";
    }

    return "en";
  }

  // Helper function to get translation path
  function getTranslationPath() {
    const currentPath = window.location.pathname;
    const pathMatch = currentPath.match(/^(.*?)\/(en|ja)\/(.*?)$/);

    if (pathMatch) {
      const basePath = pathMatch[1];
      const currentLang = pathMatch[2];
      const pagePath = pathMatch[3];

      const targetLang = currentLang === "en" ? "ja" : "en";

      let translatedPagePath = pagePath.replace(
        new RegExp(`(content|nav)/${currentLang}/`, "g"),
        `$1/${targetLang}/`,
      );

      // Special handling for index pages
      if (
        currentLang === "ja" &&
        targetLang === "en" &&
        translatedPagePath === "index-ja.html"
      ) {
        translatedPagePath = "index.html";
      } else if (
        currentLang === "en" &&
        targetLang === "ja" &&
        translatedPagePath === "index.html"
      ) {
        translatedPagePath = "index-ja.html";
      }

      return `${basePath}/${targetLang}/${translatedPagePath}`;
    }

    return null;
  }

  // Helper function to create issue URL
  function createIssueUrl() {
    const baseUrl = `https://github.com/${GITHUB_REPO}/issues/new`;
    const params = new URLSearchParams();

    params.append("template", "page-issue.yml");
    params.append("title", `[Page Issue]: ${document.title || "Unknown Page"}`);
    params.append("page_url", window.location.href);
    params.append("page_title", document.title || "Unknown Page");
    params.append(
      "page_language",
      detectCurrentLanguage() === "ja" ? "Japanese (ja)" : "English (en)",
    );
    params.append("browser", navigator.userAgent);
    params.append("device_type", "Mobile");
    params.append(
      "screen_resolution",
      window.screen.width + "x" + window.screen.height,
    );

    const labels = ["page-issue", "needs-triage", "mobile"];
    params.append("labels", labels.join(","));

    return `${baseUrl}?${params.toString()}`;
  }

  // Create the mobile footer
  function createMobileFooter() {
    const currentLang = detectCurrentLanguage();

    // Create footer container
    const footer = document.createElement("div");
    footer.className = "mobile-footer";
    footer.id = "mobile-footer";

    // Create buttons container
    const buttonsContainer = document.createElement("div");
    buttonsContainer.className = "mobile-footer-buttons";

    // Report Issue button
    const issueButton = document.createElement("a");
    issueButton.className = "mobile-footer-button issue-button-mobile";
    issueButton.href = createIssueUrl();
    issueButton.target = "_blank";
    issueButton.rel = "noopener noreferrer";
    issueButton.innerHTML = `<i class="bi bi-exclamation-circle"></i> <span>${currentLang === "ja" ? "問題を報告" : "Report Issue"}</span>`;
    issueButton.title =
      currentLang === "ja"
        ? "このページに関する問題をGitHubで報告する"
        : "Report an issue with this page on GitHub";

    // Language switch button
    const langButton = document.createElement("a");
    langButton.className = "mobile-footer-button lang-button-mobile";
    const translationPath = getTranslationPath();

    if (translationPath) {
      langButton.href = translationPath;
      langButton.innerHTML = `<i class="bi bi-globe"></i> <span>${currentLang === "en" ? "日本語" : "English"}</span>`;
      langButton.title =
        currentLang === "en" ? "Switch to Japanese" : "Switch to English";
    } else {
      langButton.href = "#";
      langButton.innerHTML = `<i class="bi bi-globe"></i> <span><s>${currentLang === "en" ? "日本語" : "English"}</s></span>`;
      langButton.title =
        currentLang === "en"
          ? "Japanese translation not available"
          : "英語版は利用できません";
      langButton.classList.add("disabled");
      langButton.onclick = function (e) {
        e.preventDefault();
        return false;
      };
    }

    // Buy Me a Coffee button
    const coffeeButton = document.createElement("a");
    coffeeButton.className = "mobile-footer-button coffee-button-mobile";
    coffeeButton.href = BUYMEACOFFEE_URL;
    coffeeButton.target = "_blank";
    coffeeButton.rel = "noopener noreferrer";
    coffeeButton.innerHTML = `<img src="https://cdn.buymeacoffee.com/buttons/v2/default-yellow.png" alt="Buy Me a Coffee"> <span>${currentLang === "ja" ? "コーヒー" : "Coffee"}</span>`;
    coffeeButton.title =
      currentLang === "ja" ? "プロジェクトを支援する" : "Support this project";

    // Add buttons to container
    buttonsContainer.appendChild(issueButton);
    buttonsContainer.appendChild(langButton);
    buttonsContainer.appendChild(coffeeButton);

    footer.appendChild(buttonsContainer);

    return footer;
  }

  // Add styles
  function addStyles() {
    const style = document.createElement("style");
    style.textContent = `
      /* Mobile Footer Styles */
      .mobile-footer {
        display: none;
        position: fixed;
        bottom: 0;
        left: 0;
        right: 0;
        background-color: var(--color-mobile-footer-bg);
        border-top: var(--border-width-thin) solid var(--color-neutral-border);
        box-shadow: 0 -2px 4px rgba(0,0,0,0.1);
        z-index: var(--z-index-mobile-footer);
        padding: var(--space-2);
      }

      .mobile-footer-buttons {
        display: flex;
        justify-content: space-around;
        align-items: center;
        max-width: 500px;
        margin: 0 auto;
      }

      .mobile-footer-button {
        display: flex;
        flex-direction: column;
        align-items: center;
        justify-content: center;
        padding: var(--padding-button-y) var(--padding-button-x);
        border-radius: var(--radius-lg);
        text-decoration: none;
        font-size: var(--font-size-xs);
        font-weight: var(--font-weight-medium);
        transition: all var(--transition-fast);
        min-width: var(--mobile-footer-button-min-width);
        height: var(--mobile-footer-button-height);
        gap: 4px;
      }

      .mobile-footer-button i {
        font-size: 18px;
      }

      .mobile-footer-button img {
        height: 18px;
        width: auto;
      }

      .mobile-footer-button span {
        white-space: nowrap;
      }

      /* Issue button styling */
      .issue-button-mobile {
        background-color: var(--color-issue-button-bg);
        color: var(--color-issue-button-text);
      }

      .issue-button-mobile:hover,
      .issue-button-mobile:active {
        background-color: var(--color-issue-button-hover);
        color: var(--color-issue-button-text);
        text-decoration: none;
      }

      /* Language button styling */
      .lang-button-mobile {
        background-color: var(--color-language-button-bg);
        color: var(--color-language-button-text);
      }

      .lang-button-mobile:hover,
      .lang-button-mobile:active {
        background-color: var(--color-language-button-hover);
        color: var(--color-language-button-text);
        text-decoration: none;
      }

      .lang-button-mobile.disabled {
        background-color: var(--color-language-button-disabled);
        opacity: var(--opacity-disabled);
        cursor: not-allowed;
      }

      /* Coffee button styling */
      .coffee-button-mobile {
        background-color: var(--color-coffee-button-bg);
        color: var(--color-coffee-button-text);
      }

      .coffee-button-mobile:hover,
      .coffee-button-mobile:active {
        background-color: var(--color-coffee-button-hover);
        color: var(--color-coffee-button-text);
        text-decoration: none;
      }

      /* Show mobile footer only on mobile devices */
      @media (max-width: 768px) {
        .mobile-footer {
          display: block;
        }

        /* Hide the original floating buttons on mobile */
        .issue-button,
        .bmc-custom-button {
          display: none !important;
        }

        /* Add padding to the main content to prevent overlap with footer */
        body {
          padding-bottom: 70px;
        }

        /* Adjust Quarto content area */
        .quarto-container,
        main,
        .content {
          margin-bottom: 70px;
        }
      }

      /* Hide on print */
      @media print {
        .mobile-footer {
          display: none;
        }
      }

      /* Dark mode support */
      @media (prefers-color-scheme: dark) {
        .mobile-footer {
          background-color: #1e1e1e;
          border-top-color: #333;
        }
      }

      /* Quarto dark theme support */
      .quarto-dark .mobile-footer {
        background-color: #1e1e1e;
        border-top-color: #333;
      }
    `;
    document.head.appendChild(style);
  }

  // Initialize mobile footer
  function initMobileFooter() {
    // Add styles
    addStyles();

    // Create and add footer
    const footer = createMobileFooter();
    document.body.appendChild(footer);

    // Update on window resize
    let resizeTimer;
    window.addEventListener("resize", function () {
      clearTimeout(resizeTimer);
      resizeTimer = setTimeout(function () {
        const footer = document.getElementById("mobile-footer");
        if (footer) {
          footer.style.display = isMobile() ? "block" : "none";
        }
      }, 250);
    });
  }

  // Wait for DOM to be ready
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", initMobileFooter);
  } else {
    // Also wait for Quarto to finish rendering
    if (window.Quarto && window.Quarto.afterInit) {
      window.Quarto.afterInit(initMobileFooter);
    } else {
      // Fallback: use setTimeout to ensure Quarto has finished
      setTimeout(initMobileFooter, 100);
    }
  }

  // Export for debugging
  window.ModernMathMobileFooter = {
    isMobile: isMobile,
    detectCurrentLanguage: detectCurrentLanguage,
    getTranslationPath: getTranslationPath,
  };
})();
