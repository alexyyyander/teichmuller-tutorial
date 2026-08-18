#!/bin/bash

# Build script for Teichmüller tutorial documents
# This script builds all PDF documents in the project

set -e  # Exit on any error

echo "=== Building Teichmüller Tutorial Documents ==="

# Create build directory if it doesn't exist
mkdir -p build

# Function to build a LaTeX file
build_latex() {
    local file=$1
    local dir=$2
    local name=$3
    
    echo "Building $name..."
    cd "$dir"
    
    # Check if latexmk is available
    if command -v latexmk &> /dev/null; then
        latexmk -xelatex -output-directory=build "$file"
    else
        echo "Error: latexmk not found. Please install TeX Live or MiKTeX."
        exit 1
    fi
    
    cd - > /dev/null
    echo "✓ $name built successfully"
}

# Build Chinese versions
echo ""
echo "=== Building Chinese versions ==="
build_latex "foundations_intro.tex" "docs/tutorial/foundations" "Foundations Introduction (Chinese)"
build_latex "teichmuller_program.tex" "docs/tutorial/advanced" "Teichmüller Program (Chinese)"

# Build English versions
echo ""
echo "=== Building English versions ==="
build_latex "foundations_intro_en.tex" "docs/tutorial/foundations" "Foundations Introduction (English)"
build_latex "teichmuller_program_en.tex" "docs/tutorial/advanced" "Teichmüller Program (English)"

echo ""
echo "=== Build Complete ==="
echo "PDF files are in the docs/tutorial/*/build/ directories"
echo ""
echo "Files built:"
find docs -name "*.pdf" -type f | sort