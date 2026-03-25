#!/usr/bin/env bash

set -e

echo "🧹 Cleaning old artifacts..."

find . -type f \( -name "*.vo" -o -name "*.vok" -o -name "*.vos" -o -name "*.glob" \) -delete

echo "📦 Rebuilding only TacticNames.v..."

coqc -Q . Top TacticNames.v

echo "✅ Done!"