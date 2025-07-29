// eslint.config.js
import { defineConfig } from 'eslint/config';
import tsPlugin from '@typescript-eslint/eslint-plugin';
import importPlugin from 'eslint-plugin-import';
import promisePlugin from 'eslint-plugin-promise';
import unicornPlugin from 'eslint-plugin-unicorn';
import sonarjsPlugin from 'eslint-plugin-sonarjs';
import jsxA11yPlugin from 'eslint-plugin-jsx-a11y';
import prettierConfig from 'eslint-config-prettier';

export default defineConfig([
  {
    root: true,
    ignorePatterns: ['node_modules/', 'dist/', 'build/'],

    // Treat warnings as errors
    maxWarnings: 0,

    languageOptions: {
      parser: '@typescript-eslint/parser',
      parserOptions: {
        project: './tsconfig.json',
        ecmaVersion: 'latest',
        sourceType: 'module',
        tsconfigRootDir: __dirname,
      },
      globals: {
        // Define any globals here
      },
    },

    settings: {
      'import/resolver': {
        typescript: {},
      },
    },

    plugins: {
      '@typescript-eslint': tsPlugin,
      import: importPlugin,
      promise: promisePlugin,
      unicorn: unicornPlugin,
      sonarjs: sonarjsPlugin,
      'jsx-a11y': jsxA11yPlugin,
    },

    extends: [
      'eslint:recommended',                                         // Core recommended rules
      'plugin:@typescript-eslint/recommended',                      // TS recommended
      'plugin:@typescript-eslint/recommended-strict',               // TS strict
      'plugin:import/recommended',                                  // Import rules
      'plugin:promise/recommended',                                 // Promise rules
      'plugin:unicorn/recommended',                                 // Unicorn rules
      'plugin:sonarjs/recommended',                                 // SonarJS rules
      'plugin:jsx-a11y/recommended',                                // Accessibility
      'prettier',                                                   // Disable conflicts with Prettier
    ],

    rules: {
      // Override or tighten rules
      '@typescript-eslint/explicit-module-boundary-types': 'error',
      '@typescript-eslint/no-explicit-any': 'error',
      '@typescript-eslint/strict-boolean-expressions': 'error',
      'no-console': ['error', { allow: ['warn', 'error'] }],
      'eqeqeq': ['error', 'always'],
      'complexity': ['error', { max: 10 }],
      'max-lines': ['error', { max: 300, skipBlankLines: true, skipComments: true }],
      'unicorn/filename-case': ['error', { case: 'kebabCase' }],
      'import/order': ['error', {
        groups: [['builtin', 'external'], 'internal', ['parent', 'sibling', 'index']],
        'newlines-between': 'always',
      }],
      'promise/always-return': 'error',
      'promise/no-return-in-finally': 'error',
      'sonarjs/cognitive-complexity': ['error', 15],
      'jsx-a11y/anchor-is-valid': ['error', { components: ['Link'], specialLink: ['hrefLeft', 'hrefRight'] }],
      // Add more project-specific or stricter overrides here
    },
  },
]);
