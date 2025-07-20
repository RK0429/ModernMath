# Quarto Installation Guide

## macOS Installation Options

### Option 1: Using Homebrew (Recommended)

```bash
brew install quarto
```

### Option 2: Direct Download

1. Visit <https://quarto.org/docs/get-started/>
2. Download the macOS installer (.pkg file)
3. Run the installer

### Option 3: Using Conda

```bash
conda install -c conda-forge quarto
```

## Verify Installation

After installation, verify Quarto is working:

```bash
quarto --version
```

## Next Steps

Once Quarto is installed, you can:

1. Preview the site: `quarto preview`
2. Render the site: `quarto render`
3. The output will be in the `_site` directory
