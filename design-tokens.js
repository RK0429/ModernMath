/**
 * Design Tokens for ModernMath - JavaScript Module
 * Mathematics Knowledge Graph Wiki Design System
 *
 * This file exports design tokens as JavaScript objects for programmatic access.
 * Can be imported in JavaScript files or build tools.
 */

export const designTokens = {
  // Color Tokens
  color: {
    primary: {
      blue: "#0969da",
      blueLight: "#0366d6",
      blueHover: "#0860ca",
      blueBg: "#f0f7ff",
      blueBgLight: "#dbeafe",
      blueText: "#1e40af",
    },

    // Mathematical Content Types
    definition: {
      bg: "#f0f7ff",
      border: "#0969da",
      badgeBg: "#dbeafe",
      badgeText: "#1e40af",
    },

    theorem: {
      bg: "#fff8f0",
      border: "#fb8500",
      badgeBg: "#fed7aa",
      badgeText: "#c2410c",
    },

    example: {
      bg: "#f0fff4",
      border: "#2da44e",
      badgeBg: "#d1fae5",
      badgeText: "#065f46",
    },

    axiom: {
      bg: "#e9d5ff",
      border: "#6b21a8",
      badgeBg: "#e9d5ff",
      badgeText: "#6b21a8",
    },

    // Action Buttons
    button: {
      issue: {
        bg: "#0366d6",
        hover: "#0256c7",
        text: "#ffffff",
      },
      coffee: {
        bg: "#ffdd00",
        hover: "#ffcc00",
        text: "#000000",
      },
      language: {
        bg: "#28a745",
        hover: "#218838",
        disabled: "#6c757d",
        text: "#ffffff",
      },
    },

    // Neutral Colors
    neutral: {
      bg: "#f6f8fa",
      border: "#e0e0e0",
      text: "#24292e",
      textLight: "#586069",
      white: "#ffffff",
      black: "#000000",
    },

    // Interactive States
    link: {
      default: "#0969da",
      hover: "#0860ca",
      visited: "#6f42c1",
    },

    // Translation Status
    translation: {
      pending: {
        bg: "#fff3cd",
        border: "#ffeeba",
      },
      machineTranslated: {
        bg: "#d1ecf1",
        border: "#bee5eb",
      },
    },

    // Language Switcher
    langSwitcher: {
      bg: "rgba(0, 123, 255, 0.1)",
      hover: "rgba(0, 123, 255, 0.2)",
      disabledBg: "rgba(128, 128, 128, 0.1)",
    },
  },

  // Typography Tokens
  typography: {
    fontFamily: {
      base: '-apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif',
      japanese:
        '-apple-system, BlinkMacSystemFont, "Hiragino Kaku Gothic ProN", "Hiragino Sans", Meiryo, sans-serif',
      mono: '"SFMono-Regular", Consolas, "Liberation Mono", Menlo, Courier, monospace',
    },

    fontSize: {
      xs: "0.75rem", // 12px
      sm: "0.875rem", // 14px
      base: "1rem", // 16px
      lg: "1.1rem", // 17.6px
      xl: "1.25rem", // 20px
      "2xl": "1.5rem", // 24px
      "3xl": "2rem", // 32px
    },

    fontWeight: {
      normal: 400,
      medium: 500,
      semibold: 600,
      bold: 700,
    },

    lineHeight: {
      tight: 1,
      normal: 1.5,
      relaxed: 1.6,
      loose: 1.7,
    },
  },

  // Spacing Tokens
  spacing: {
    0: "0",
    1: "0.25rem", // 4px
    2: "0.5rem", // 8px
    3: "0.75rem", // 12px
    4: "1rem", // 16px
    5: "1.25rem", // 20px
    6: "1.5rem", // 24px
    8: "2rem", // 32px
    10: "2.5rem", // 40px
    12: "3rem", // 48px
    16: "4rem", // 64px
  },

  // Component Spacing
  component: {
    button: {
      paddingX: "12px",
      paddingY: "8px",
    },
    section: {
      margin: "1rem",
      marginMobile: "0.75rem",
    },
  },

  // Sizing Tokens
  sizing: {
    button: {
      height: {
        default: "44px",
        mobile: "44px",
      },
      minWidth: {
        default: "130px",
        mobile: "110px",
      },
    },
    icon: {
      sm: "16px",
      md: "20px",
      lg: "24px",
    },
    mobileFooter: {
      height: "60px",
      buttonHeight: "50px",
      buttonMinWidth: "80px",
    },
  },

  // Layout Tokens
  layout: {
    zIndex: {
      dropdown: 100,
      sticky: 200,
      fixed: 500,
      modalBackdrop: 800,
      modal: 900,
      coffeeButton: 999,
      issueButton: 1000,
      mobileFooter: 1100,
      tooltip: 1200,
    },

    borderRadius: {
      sm: "3px",
      md: "5px",
      lg: "6px",
      xl: "8px",
      full: "9999px",
    },

    borderWidth: {
      thin: "1px",
      medium: "2px",
      thick: "4px",
    },
  },

  // Responsive Breakpoints
  breakpoint: {
    xs: "320px",
    sm: "576px",
    md: "768px",
    lg: "992px",
    xl: "1200px",
    "2xl": "1400px",
  },

  // Animation Tokens
  animation: {
    transition: {
      fast: "150ms ease-in-out",
      base: "300ms ease",
      slow: "500ms ease",
    },
    duration: {
      fast: "150ms",
      base: "300ms",
      slow: "500ms",
    },
  },

  // Shadow Tokens
  shadow: {
    sm: "0 1px 2px 0 rgba(0, 0, 0, 0.05)",
    md: "0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06)",
    lg: "0 10px 15px -3px rgba(0, 0, 0, 0.1), 0 4px 6px -2px rgba(0, 0, 0, 0.05)",
    xl: "0 20px 25px -5px rgba(0, 0, 0, 0.1), 0 10px 10px -5px rgba(0, 0, 0, 0.04)",
    hover: "0 0 3px rgba(0, 0, 0, 0.3)",
  },

  // Opacity Tokens
  opacity: {
    0: 0,
    25: 0.25,
    50: 0.5,
    75: 0.75,
    100: 1,
    disabled: 0.5,
  },
};

// Helper function to get CSS custom property value
export function getCSSToken(tokenPath) {
  const propertyName = `--${tokenPath.replace(/\./g, "-")}`;
  return getComputedStyle(document.documentElement)
    .getPropertyValue(propertyName)
    .trim();
}

// Helper function to set CSS custom property value
export function setCSSToken(tokenPath, value) {
  const propertyName = `--${tokenPath.replace(/\./g, "-")}`;
  document.documentElement.style.setProperty(propertyName, value);
}

// Export as default for easier importing
export default designTokens;
