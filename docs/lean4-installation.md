# Installing Lean 4 on macOS

This guide covers the installation of Lean 4 and its toolchain for the Math Knowledge Graph Wiki project.

## Prerequisites

- macOS (10.15 or later recommended)
- Command line tools installed (Xcode or Command Line Tools)
- Git installed (already verified in project)

## Installation Steps

### 1. Install elan (Lean Version Manager)

The recommended way to install Lean 4 is through elan, which manages Lean versions similar to how rustup manages Rust versions.

```bash
# Install elan using the official installer
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Follow the prompts during installation. The installer will:
- Download and install elan
- Set up the latest stable Lean 4 version
- Add elan to your PATH

### 2. Verify Installation

After installation, restart your terminal or run:

```bash
source ~/.profile
```

Then verify the installation:

```bash
# Check elan version
elan --version

# Check Lean version
lean --version

# Check Lake (Lean's build tool) version
lake --version
```

### 3. Install VS Code Extension (Optional but Recommended)

If you use VS Code:

1. Open VS Code
2. Go to Extensions (Cmd+Shift+X)
3. Search for "lean4"
4. Install the "Lean 4" extension by leanprover

## Alternative Installation Methods

### Using Homebrew

If you prefer Homebrew:

```bash
# Install Lean 4 via Homebrew
brew install lean

# Note: This may not always have the latest version
```

### Manual Installation

For manual installation, visit the [Lean 4 releases page](https://github.com/leanprover/lean4/releases) and download the appropriate binary for macOS.

## Next Steps

After installation:

1. Create the Lean project structure in the `formal/` directory
2. Initialize a new Lean project with Lake
3. Add mathlib4 as a dependency
4. Begin formalizing mathematical definitions

## Troubleshooting

### PATH Issues

If `lean` or `lake` commands are not found after installation:

```bash
# Add to ~/.zshrc or ~/.bash_profile
export PATH="$HOME/.elan/bin:$PATH"
```

### Apple Silicon (M1/M2) Compatibility

Lean 4 fully supports Apple Silicon. The elan installer will automatically detect and install the appropriate version.

### Build Tools

Ensure you have Xcode Command Line Tools:

```bash
xcode-select --install
```

## Resources

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Lean 4 Tutorial](https://leanprover.github.io/lean4/doc/tutorial.html)
- [mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/) - Community support
