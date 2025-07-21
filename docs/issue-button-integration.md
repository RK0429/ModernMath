# Issue Button Integration

This document describes the issue button feature that has been integrated into the ModernMath website.

## Overview

The issue button provides a convenient way for readers to report problems or suggest improvements for any content page. It automatically creates GitHub issues with contextual information about the page where the issue was found.

## Features

- **Floating Button**: A "Report Issue" button appears in the bottom-right corner of content pages
- **Article Footer**: An additional issue reporting section is added at the end of articles
- **Multilingual Support**: Button text and issue templates adapt to the page language (English/Japanese)
- **Smart Context**: Automatically captures page title, URL, domain, and concept ID
- **Selective Display**: Only appears on mathematical content pages, not on index or navigation pages

## Technical Implementation

### Files Added/Modified

1. **`js/issue-button.js`**: Main JavaScript file implementing the issue button functionality
2. **`_quarto-en.yml`**: Updated to include Bootstrap Icons CDN and load the issue button script
3. **`_quarto-ja.yml`**: Updated to include Bootstrap Icons CDN and load the issue button script

### How It Works

1. The script detects the current page's metadata (title, URL, language, domain)
2. It checks if the current page is a content page (not index, search, etc.)
3. If appropriate, it adds:
   - A floating button in the bottom-right corner
   - An issue reporting section at the end of the article content
4. Clicking the button opens a new GitHub issue with pre-filled information

### Issue Template

The generated issue includes:

- **Title**: `[Domain] Issue with Page Title` (language-aware)
- **Labels**: `documentation`, `content`, and the mathematical domain
- **Body**: Pre-formatted template with:
  - Page information (title, URL, path, concept ID, domain)
  - Sections for issue description, expected behavior, and actual behavior
  - Space for screenshots

## Configuration

The issue button is configured in `js/issue-button.js`:

```javascript
const GITHUB_REPO = "RK0429/ModernMath";
const ISSUE_LABELS = ["documentation", "content"];
```

## Usage

No additional setup is required. The issue button will automatically appear on all mathematical content pages after building the site with Quarto.

## Testing

A test page is provided at `test-issue-button.html` for verifying the functionality. To test:

1. Open `test-issue-button.html` in a browser
2. Use the test controls to simulate different page contexts
3. Click "Show Debug Info" to see the metadata being captured
4. Click the issue button to see the generated GitHub issue

## Excluded Pages

The issue button does not appear on:

- Index pages
- Search pages
- Visualization pages
- About pages
- Contributing pages

This ensures the button only appears where it's most relevant - on actual mathematical content.
