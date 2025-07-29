// Buy Me a Coffee Button Integration for ModernMath
// This script adds a "Buy Me a Coffee" button to each page

(function () {
  "use strict";

  // Configuration
  const BUYMEACOFFEE_URL = "https://www.buymeacoffee.com/RK0429";

  // Helper function to create the button
  function createBuyMeCoffeeButton() {
    const button = document.createElement("a");
    button.className = "bmc-custom-button";
    button.href = BUYMEACOFFEE_URL;
    button.target = "_blank";
    button.rel = "noopener noreferrer";

    // Create the coffee icon image
    const img = document.createElement("img");
    img.src = "https://cdn.buymeacoffee.com/buttons/v2/default-yellow.png";
    img.alt = "Buy Me a Coffee";
    img.style.cssText =
      "height: 36px !important; width: auto !important; margin: 0;";

    button.appendChild(img);

    // Add tooltip
    button.title = "Support this project with a coffee";

    return button;
  }

  // Helper function to add styles
  function addStyles() {
    const style = document.createElement("style");
    style.textContent = `
      .bmc-custom-button {
        position: fixed;
        bottom: 20px; /* Positioned above Report Issue button */
        right: 20px;
        background-color: #FFDD00;
        color: #000000;
        border-radius: 6px;
        text-decoration: none;
        font-size: 14px;
        font-weight: 500;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        transition: all 0.2s ease;
        z-index: 999; /* Slightly below Report Issue button */
        height: 44px;
        min-width: 130px;
      }

      .bmc-custom-button:hover {
        background-color: #FFD814;
        transform: translateY(-1px);
        box-shadow: 0 4px 8px rgba(0,0,0,0.15);
        text-decoration: none;
      }

      .bmc-custom-button:active {
        transform: translateY(0);
        box-shadow: 0 2px 4px rgba(0,0,0,0.1);
      }

      .bmc-custom-button img {
        height: 16px !important;
        width: auto !important;
        margin: 0;
      }

      /* Mobile responsive */
      @media (max-width: 768px) {
        .bmc-custom-button {
          bottom: 10px;
          right: 10px;
          font-size: 13px;
          height: 44px;
          min-width: 110px;
        }
      }

      /* Hide on print */
      @media print {
        .bmc-custom-button {
          display: none;
        }
      }
    `;
    document.head.appendChild(style);
  }

  // Helper function to check if we should show the button
  function shouldShowButton() {
    // Show on all pages - you can add exclusions here if needed
    return true;
  }

  // Initialize the Buy Me a Coffee button
  function initBuyMeCoffeeButton() {
    if (!shouldShowButton()) {
      return;
    }

    // Check if button already exists (in case script runs twice)
    if (document.querySelector(".bmc-custom-button")) {
      return;
    }

    // Add styles
    addStyles();

    // Create and add the button
    const button = createBuyMeCoffeeButton();
    document.body.appendChild(button);
  }

  // Wait for DOM to be ready
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", initBuyMeCoffeeButton);
  } else {
    // Also wait for Quarto to finish rendering
    if (window.Quarto && window.Quarto.afterInit) {
      window.Quarto.afterInit(initBuyMeCoffeeButton);
    } else {
      // Fallback: use setTimeout to ensure Quarto has finished
      setTimeout(initBuyMeCoffeeButton, 100);
    }
  }

  // Export for debugging
  window.ModernMathBuyMeCoffeeButton = {
    shouldShowButton: shouldShowButton,
    createBuyMeCoffeeButton: createBuyMeCoffeeButton,
  };
})();
