# Design Tokens Documentation

Design tokens are the visual design atoms of the design system — specifically, they are named entities that store visual design attributes. They help maintain consistency across the ModernMath website.

## Files

- **`design-tokens.css`** - CSS custom properties for use in stylesheets
- **`design-tokens.js`** - JavaScript module for programmatic access

## Usage

### In CSS

Import the design tokens CSS file and use CSS custom properties:

```css
@import "design-tokens.css";

.my-component {
  background-color: var(--color-neutral-bg);
  padding: var(--space-4);
  border-radius: var(--radius-lg);
}
```

### In JavaScript

Import the design tokens module:

```javascript
import { designTokens, getCSSToken, setCSSToken } from "./design-tokens.js";

// Access token values directly
const primaryColor = designTokens.color.primary.blue;

// Get CSS custom property value
const bgColor = getCSSToken("color-neutral-bg");

// Set CSS custom property value dynamically
setCSSToken("color-primary-blue", "#0058cc");
```

## Token Categories

### Colors

#### Primary Colors

- `--color-primary-blue`: Main brand color (#0969da)
- `--color-primary-blue-light`: Lighter variant (#0366d6)
- `--color-primary-blue-hover`: Hover state (#0860ca)
- `--color-primary-blue-bg`: Light background (#f0f7ff)

#### Mathematical Content Types

Each content type has consistent colors:

**Definition**

- `--color-definition-bg`: Background (#f0f7ff)
- `--color-definition-border`: Border (#0969da)
- `--color-definition-badge-bg`: Badge background (#dbeafe)
- `--color-definition-badge-text`: Badge text (#1e40af)

**Theorem**

- `--color-theorem-bg`: Background (#fff8f0)
- `--color-theorem-border`: Border (#fb8500)
- `--color-theorem-badge-bg`: Badge background (#fed7aa)
- `--color-theorem-badge-text`: Badge text (#c2410c)

**Example**

- `--color-example-bg`: Background (#f0fff4)
- `--color-example-border`: Border (#2da44e)
- `--color-example-badge-bg`: Badge background (#d1fae5)
- `--color-example-badge-text`: Badge text (#065f46)

**Axiom**

- `--color-axiom-bg`: Background (#e9d5ff)
- `--color-axiom-border`: Border (#6b21a8)
- `--color-axiom-badge-bg`: Badge background (#e9d5ff)
- `--color-axiom-badge-text`: Badge text (#6b21a8)

#### Action Buttons

- **Issue Button**: `--color-issue-button-bg` (#0366d6)
- **Coffee Button**: `--color-coffee-button-bg` (#ffdd00)
- **Language Button**: `--color-language-button-bg` (#28a745)

### Typography

#### Font Families

- `--font-family-base`: System font stack
- `--font-family-japanese`: Japanese-optimized font stack
- `--font-family-mono`: Monospace font stack

#### Font Sizes

- `--font-size-xs`: 0.75rem (12px)
- `--font-size-sm`: 0.875rem (14px)
- `--font-size-base`: 1rem (16px)
- `--font-size-lg`: 1.1rem (17.6px)
- `--font-size-xl`: 1.25rem (20px)
- `--font-size-2xl`: 1.5rem (24px)
- `--font-size-3xl`: 2rem (32px)

#### Font Weights

- `--font-weight-normal`: 400
- `--font-weight-medium`: 500
- `--font-weight-semibold`: 600
- `--font-weight-bold`: 700

#### Line Heights

- `--line-height-tight`: 1
- `--line-height-normal`: 1.5
- `--line-height-relaxed`: 1.6
- `--line-height-loose`: 1.7

### Spacing

Spacing follows a consistent scale:

- `--space-0`: 0
- `--space-1`: 0.25rem (4px)
- `--space-2`: 0.5rem (8px)
- `--space-3`: 0.75rem (12px)
- `--space-4`: 1rem (16px)
- `--space-5`: 1.25rem (20px)
- `--space-6`: 1.5rem (24px)
- `--space-8`: 2rem (32px)
- `--space-10`: 2.5rem (40px)
- `--space-12`: 3rem (48px)
- `--space-16`: 4rem (64px)

### Layout

#### Z-index Scale

Consistent layering system:

- `--z-index-dropdown`: 100
- `--z-index-sticky`: 200
- `--z-index-fixed`: 500
- `--z-index-modal-backdrop`: 800
- `--z-index-modal`: 900
- `--z-index-coffee-button`: 999
- `--z-index-issue-button`: 1000
- `--z-index-mobile-footer`: 1100
- `--z-index-tooltip`: 1200

#### Border Radius

- `--radius-sm`: 3px
- `--radius-md`: 5px
- `--radius-lg`: 6px
- `--radius-xl`: 8px
- `--radius-full`: 9999px

#### Breakpoints

- `--breakpoint-xs`: 320px
- `--breakpoint-sm`: 576px
- `--breakpoint-md`: 768px
- `--breakpoint-lg`: 992px
- `--breakpoint-xl`: 1200px
- `--breakpoint-2xl`: 1400px

### Animation

#### Transitions

- `--transition-fast`: 150ms ease-in-out
- `--transition-base`: 300ms ease
- `--transition-slow`: 500ms ease

#### Shadows

- `--shadow-sm`: Subtle shadow
- `--shadow-md`: Medium shadow
- `--shadow-lg`: Large shadow
- `--shadow-xl`: Extra large shadow
- `--shadow-hover`: Hover effect shadow

## Best Practices

1. **Always use tokens** instead of hard-coded values
2. **Semantic naming**: Use tokens that describe their purpose
3. **Consistency**: Apply the same tokens for similar UI elements
4. **Responsive design**: Use mobile-specific tokens where provided
5. **Theme support**: Design tokens make it easy to add dark mode in the future

## Examples

### Creating a Card Component

```css
.card {
  background-color: var(--color-neutral-white);
  border: var(--border-width-thin) solid var(--color-neutral-border);
  border-radius: var(--radius-lg);
  padding: var(--space-4);
  margin-bottom: var(--space-4);
  box-shadow: var(--shadow-sm);
  transition: box-shadow var(--transition-fast);
}

.card:hover {
  box-shadow: var(--shadow-md);
}
```

### Mathematical Content Box

```css
.math-box {
  background-color: var(--color-definition-bg);
  border-left: var(--border-width-thick) solid var(--color-definition-border);
  padding: var(--space-4);
  margin: var(--margin-section) 0;
  font-size: var(--font-size-lg);
  line-height: var(--line-height-relaxed);
}
```

### Responsive Button

```css
.action-button {
  background-color: var(--color-primary-blue);
  color: var(--color-neutral-white);
  padding: var(--padding-button-y) var(--padding-button-x);
  border-radius: var(--radius-md);
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-medium);
  min-width: var(--button-min-width-default);
  height: var(--button-height-default);
  transition: background-color var(--transition-fast);
}

.action-button:hover {
  background-color: var(--color-primary-blue-hover);
}

@media (max-width: 768px) {
  .action-button {
    min-width: var(--button-min-width-mobile);
    height: var(--button-height-mobile);
  }
}
```

## Maintenance

When updating design tokens:

1. Update both `design-tokens.css` and `design-tokens.js`
2. Test changes across all pages
3. Check responsive behavior
4. Verify accessibility (contrast ratios)
5. Update this documentation

## Future Enhancements

- Dark mode support via CSS custom property overrides
- Theme switching functionality
- Additional semantic color tokens
- Component-specific token sets
