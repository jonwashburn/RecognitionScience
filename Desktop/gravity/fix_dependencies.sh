#!/usr/bin/env bash
set -e

echo "Fixing dependency issues..."

# Remove proofwidgets requirement from mathlib
if [ -f .lake/packages/mathlib/lakefile.lean ]; then
    echo "Patching mathlib lakefile to remove proofwidgets..."
    # Create a temporary file without the proofwidgets lines
    grep -v "proofwidgets" .lake/packages/mathlib/lakefile.lean > .lake/packages/mathlib/lakefile.lean.tmp || true
    mv .lake/packages/mathlib/lakefile.lean.tmp .lake/packages/mathlib/lakefile.lean
fi

# Remove proofwidgets directory if it exists
if [ -d .lake/packages/proofwidgets ]; then
    echo "Removing proofwidgets package..."
    rm -rf .lake/packages/proofwidgets
fi

echo "Dependencies fixed!" 