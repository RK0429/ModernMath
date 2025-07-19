# Java Installation Guide for macOS

Apache Jena Fuseki requires Java to run. Here are the installation options:

## Option 1: Using Homebrew (Recommended)

```bash
# Install OpenJDK
brew install openjdk

# Make sure Java is in your PATH
echo 'export PATH="/opt/homebrew/opt/openjdk/bin:$PATH"' >> ~/.zshrc
source ~/.zshrc
```

## Option 2: Using SDKMAN

```bash
# Install SDKMAN
curl -s "https://get.sdkman.io" | bash
source "$HOME/.sdkman/bin/sdkman-init.sh"

# Install Java
sdk install java
```

## Option 3: Download from Oracle

1. Visit <https://www.oracle.com/java/technologies/downloads/>
2. Download the macOS installer for Java 17 or later
3. Run the installer

## Option 4: Download from Adoptium (OpenJDK)

1. Visit <https://adoptium.net/>
2. Download the macOS installer for OpenJDK 17 or later
3. Run the installer

## Verify Installation

After installation, verify Java is working:

```bash
java -version
```

You should see output similar to:

```text
openjdk version "17.0.x" ...
```

## Next Steps

Once Java is installed, you can start Fuseki:

```bash
cd fuseki/fuseki-server/apache-jena-fuseki-4.10.0
./fuseki-server --config="../../../fuseki/config/mathwiki.ttl"
```
