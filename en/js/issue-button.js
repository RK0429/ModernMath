// Issue Button Integration for ModernMath
// This script adds a "Report Issue" button to each page that creates GitHub issues with context

(function () {
  "use strict";

  // Configuration
  const GITHUB_REPO = "RK0429/ModernMath";
  const ISSUE_LABELS = ["documentation", "content"];

  // Helper function to get page metadata
  function getPageMetadata() {
    const metadata = {
      title: document.title || "Unknown Page",
      url: window.location.href,
      path: window.location.pathname,
      language: "en", // default
      browser: getBrowserInfo(),
      screenResolution: window.screen.width + "x" + window.screen.height,
      deviceType: getDeviceType(),
    };

    // Detect language from path or HTML lang attribute
    if (window.location.pathname.includes("/ja/")) {
      metadata.language = "ja";
    } else if (window.location.pathname.includes("/en/")) {
      metadata.language = "en";
    } else {
      // Fallback to HTML lang attribute
      const htmlLang = document.documentElement.lang;
      if (htmlLang) {
        metadata.language = htmlLang.split("-")[0];
      }
    }

    // Try to get the mathematical concept ID from the page
    const mainHeading = document.querySelector("h1");
    if (mainHeading) {
      const headingId = mainHeading.id;
      if (headingId) {
        metadata.conceptId = headingId;
      }
    }

    // Get the domain from the URL path
    const pathParts = window.location.pathname.split("/");
    const langIndex = pathParts.findIndex(
      (part) => part === "en" || part === "ja",
    );
    if (langIndex >= 0 && langIndex + 1 < pathParts.length) {
      metadata.domain = pathParts[langIndex + 1];
    }

    return metadata;
  }

  // Helper function to get browser information
  function getBrowserInfo() {
    const ua = navigator.userAgent;
    let browser = "Unknown";
    let version = "";

    if (ua.indexOf("Chrome") > -1 && ua.indexOf("Edg") === -1) {
      browser = "Chrome";
      version = ua.match(/Chrome\/(\d+)/)?.[1] || "";
    } else if (ua.indexOf("Safari") > -1 && ua.indexOf("Chrome") === -1) {
      browser = "Safari";
      version = ua.match(/Version\/(\d+)/)?.[1] || "";
    } else if (ua.indexOf("Firefox") > -1) {
      browser = "Firefox";
      version = ua.match(/Firefox\/(\d+)/)?.[1] || "";
    } else if (ua.indexOf("Edg") > -1) {
      browser = "Edge";
      version = ua.match(/Edg\/(\d+)/)?.[1] || "";
    }

    return version ? `${browser} ${version}` : browser;
  }

  // Helper function to detect device type
  function getDeviceType() {
    const userAgent = navigator.userAgent.toLowerCase();
    const isMobile = /mobile|android|iphone|ipad|phone/i.test(userAgent);
    const isTablet = /tablet|ipad/i.test(userAgent);

    if (isTablet) return "Tablet";
    if (isMobile) return "Mobile";
    return "Desktop";
  }

  // Helper function to create the issue URL
  function createIssueUrl(metadata) {
    const baseUrl = `https://github.com/${GITHUB_REPO}/issues/new`;
    const params = new URLSearchParams();

    // Specify the template
    params.append("template", "page-issue.yml");

    // Create issue title
    const title =
      metadata.language === "ja"
        ? `[Page Issue]: ${metadata.title}`
        : `[Page Issue]: ${metadata.title}`;
    params.append("title", title);

    // Add all the form fields based on our template
    params.append("page_url", metadata.url);
    params.append("page_title", metadata.title);
    params.append(
      "page_language",
      metadata.language === "ja" ? "Japanese (ja)" : "English (en)",
    );
    params.append("browser", metadata.browser);
    params.append("device_type", metadata.deviceType);
    params.append("screen_resolution", metadata.screenResolution);

    // Add labels - page-issue is already in the template
    const labels = ["page-issue", "needs-triage", ...ISSUE_LABELS];
    if (metadata.domain) {
      labels.push(metadata.domain);
    }
    params.append("labels", labels.join(","));

    return `${baseUrl}?${params.toString()}`;
  }

  // Helper function to create the issue button
  function createIssueButton() {
    const metadata = getPageMetadata();

    const button = document.createElement("a");
    button.className = "issue-button";
    button.href = createIssueUrl(metadata);
    button.target = "_blank";
    button.rel = "noopener noreferrer";

    // Set button text based on language
    const buttonText =
      metadata.language === "ja" ? "問題を報告" : "Report Issue";
    button.innerHTML = `<i class="bi bi-exclamation-circle"></i> ${buttonText}`;

    // Add tooltip
    const tooltipText =
      metadata.language === "ja"
        ? "このページに関する問題をGitHubで報告する"
        : "Report an issue with this page on GitHub";
    button.title = tooltipText;

    return button;
  }

  // Helper function to add styles
  function addStyles() {
    const style = document.createElement("style");
    style.textContent = `
      .issue-button {
        position: fixed;
        bottom: 70px;
        right: 20px;
        background-color: var(--color-issue-button-bg);
        color: var(--color-issue-button-text);
        padding: var(--padding-button-y) var(--padding-button-x);
        border-radius: var(--radius-lg);
        text-decoration: none;
        font-size: var(--font-size-sm);
        font-weight: var(--font-weight-medium);
        display: inline-flex;
        align-items: center;
        justify-content: center;
        gap: 6px;
        box-shadow: var(--shadow-sm);
        transition: all var(--transition-fast);
        z-index: var(--z-index-issue-button);
        height: var(--button-height-default);
        min-width: var(--button-min-width-default);
      }

      .issue-button:hover {
        background-color: var(--color-issue-button-hover);
        color: var(--color-issue-button-text);
        text-decoration: none;
        transform: translateY(-1px);
        box-shadow: var(--shadow-md);
      }

      .issue-button:active {
        transform: translateY(0);
        box-shadow: var(--shadow-sm);
      }

      .issue-button i {
        font-size: var(--icon-size-sm);
      }

      /* Mobile responsive */
      @media (max-width: 768px) {
        .issue-button {
          bottom: 60px;
          right: 10px;
          padding: var(--padding-button-y) var(--padding-button-x);
          font-size: 13px;
          height: var(--button-height-mobile);
          min-width: var(--button-min-width-mobile);
        }

        .issue-button i {
          font-size: 14px;
        }
      }

      /* Hide on print */
      @media print {
        .issue-button {
          display: none;
        }
      }

      /* Alternative placement in article footer for better integration */
      .article-issue-button {
        margin-top: var(--space-8);
        padding-top: var(--space-8);
        border-top: var(--border-width-thin) solid var(--color-neutral-border);
        text-align: center;
      }

      .article-issue-button .issue-button {
        position: static;
        display: inline-flex;
        box-shadow: none;
      }
    `;
    document.head.appendChild(style);
  }

  // Helper function to check if we should show the button
  function shouldShowButton() {
    // Show the button on all pages
    return true;
  }

  // Initialize the issue button
  function initIssueButton() {
    if (!shouldShowButton()) {
      return;
    }

    // Add styles
    addStyles();

    // Create and add the button
    const button = createIssueButton();

    // Option 1: Floating button (default)
    document.body.appendChild(button);

    // Option 2: Also add to article footer if article element exists
    const article = document.querySelector(
      "main article, .content article, article",
    );
    if (article) {
      const footerSection = document.createElement("div");
      footerSection.className = "article-issue-button";

      const metadata = getPageMetadata();
      const helpText =
        metadata.language === "ja"
          ? "このページに誤りや改善点を見つけましたか？"
          : "Found an error or have a suggestion for this page?";

      footerSection.innerHTML = `<p>${helpText}</p>`;
      footerSection.appendChild(createIssueButton());

      article.appendChild(footerSection);
    }
  }

  // Wait for DOM to be ready
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", initIssueButton);
  } else {
    // Also wait for Quarto to finish rendering
    if (window.Quarto && window.Quarto.afterInit) {
      window.Quarto.afterInit(initIssueButton);
    } else {
      // Fallback: use setTimeout to ensure Quarto has finished
      setTimeout(initIssueButton, 100);
    }
  }

  // Export for debugging
  window.ModernMathIssueButton = {
    getPageMetadata: getPageMetadata,
    createIssueUrl: createIssueUrl,
    shouldShowButton: shouldShowButton,
  };
})();
