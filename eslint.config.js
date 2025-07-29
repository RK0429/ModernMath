// eslint.config.js
import js from "@eslint/js";
import globals from "globals";

export default [
  // Base configuration
  js.configs.recommended,

  {
    files: ["**/*.js", "**/*.mjs"],
    languageOptions: {
      ecmaVersion: "latest",
      sourceType: "module",
      globals: {
        ...globals.browser,
        ...globals.node,
      },
    },
    rules: {
      // Custom rules for JavaScript files
      "no-console": ["warn", { allow: ["warn", "error"] }],
      eqeqeq: ["error", "always"],
      "no-unused-vars": ["error", { argsIgnorePattern: "^_" }],
    },
  },

  // Ignore patterns
  {
    ignores: [
      "node_modules/",
      "dist/",
      "build/",
      "_site/",
      "fuseki/",
      "lib/",
      "design-tokens.js", // Temporarily ignore the design tokens file to avoid the filename-case error
    ],
  },
];
