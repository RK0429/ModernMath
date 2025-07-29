# Issue Reporting System

This document explains the issue reporting system implemented for the ModernMath Knowledge Graph.

## Overview

Every content page in the deployed site includes a "Report Issue" button that allows users to quickly report problems with that specific page. The button automatically collects contextual information about the page and pre-fills a GitHub issue template.

## Components

### 1. Issue Template (`/.github/ISSUE_TEMPLATE/page-issue.yml`)

A structured GitHub issue form template specifically designed for page-related issues. It includes fields for:

- Page URL and title (auto-filled)
- Language version (auto-filled)
- Issue type (dropdown selection)
- Browser and device information (auto-filled)
- Screen resolution (auto-filled)
- Detailed description and screenshots

### 2. JavaScript Integration (`/js/issue-button.js`)

The script automatically:

- Detects page metadata (title, URL, language, domain)
- Collects browser information and device type
- Creates a floating "Report Issue" button on content pages
- Generates GitHub issue URLs with pre-filled parameters

### 3. Configuration

The issue button is loaded on all pages via the Quarto configuration files:

- `_quarto-en.yml` - English site configuration
- `_quarto-ja.yml` - Japanese site configuration

## How It Works

1. When a user visits a content page, the `issue-button.js` script:
   - Checks if it's a content page (not index, search, or navigation pages)
   - Collects page and browser metadata
   - Renders a "Report Issue" button

2. When the button is clicked:
   - A GitHub issue URL is generated with the `page-issue.yml` template
   - All available metadata is passed as URL parameters
   - The user is redirected to GitHub with a pre-filled issue form

3. The user can then:
   - Review the auto-filled information
   - Select the issue type from a dropdown
   - Add a detailed description
   - Attach screenshots if needed
   - Submit the issue

## Testing

To test the issue button locally:

1. Open `test-issue-button.html` in a browser
2. Check the generated metadata and URL
3. Click the generated URL to verify the GitHub form is properly filled

## Customization

### Adding New Issue Types

Edit `/.github/ISSUE_TEMPLATE/page-issue.yml` and add new options to the `issue_type` dropdown field.

### Excluding Pages

Edit the `excludedPages` array in `/js/issue-button.js` to prevent the button from appearing on specific pages.

### Styling

The button styling is defined inline in the JavaScript file. Modify the CSS in the `addStyles()` function to change appearance.
