#!/bin/bash

# Translation helper script for Teichmüller tutorial documents
# This script helps track translation progress

echo "=== Teichmüller Tutorial Translation Status ==="
echo ""

# Check if translation tools are available
check_tools() {
    if command -v diff &> /dev/null; then
        echo "✓ diff available"
    else
        echo "✗ diff not found"
    fi
    
    if command -v wc &> /dev/null; then
        echo "✓ wc available"
    else
        echo "✗ wc not found"
    fi
}

# Compare Chinese and English versions
compare_versions() {
    local chinese_file=$1
    local english_file=$2
    local name=$3
    
    echo ""
    echo "=== $name ==="
    
    if [ -f "$chinese_file" ] && [ -f "$english_file" ]; then
        # Count lines
        chinese_lines=$(wc -l < "$chinese_file")
        english_lines=$(wc -l < "$english_file")
        
        echo "Chinese version: $chinese_lines lines"
        echo "English version: $english_lines lines"
        
        # Simple comparison
        if [ "$chinese_lines" -eq "$english_lines" ]; then
            echo "✓ Line counts match"
        else
            echo "⚠ Line counts differ by $((chinese_lines - english_lines))"
        fi
    else
        echo "✗ Missing file(s)"
        [ ! -f "$chinese_file" ] && echo "  Missing: $chinese_file"
        [ ! -f "$english_file" ] && echo "  Missing: $english_file"
    fi
}

# Main
echo "Checking translation status..."
echo ""

compare_versions "docs/tutorial/foundations/foundations_intro.tex" "docs/tutorial/foundations/foundations_intro_en.tex" "Foundations Introduction"
compare_versions "docs/tutorial/advanced/teichmuller_program.tex" "docs/tutorial/advanced/teichmuller_program_en.tex" "Teichmüller Program"

echo ""
echo "=== Summary ==="
echo ""
echo "To create a new translation:"
echo "1. Copy the Chinese version as a template"
echo "2. Translate the content"
echo "3. Update the LaTeX preamble for English fonts"
echo "4. Test build with: ./scripts/build.sh"
echo ""
echo "For more information, see CONTRIBUTING.md"