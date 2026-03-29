#!/usr/bin/env bash

set -e

echo "🧹 Cleaning old artifacts..."

find . -type f \( -name "*.vo" -o -name "*.vok" -o -name "*.vos" -o -name "*.glob" -o -name *.aux \) -delete

echo "📦 Rebuilding file..."

coqc -Q . Top TacticNames.v
coqc -Q . Top -Q 0_Logic/0_Props Props 0_Logic/0_Props/Task.v
coqc -Q . Top -Q 0_Logic/1_Quantifiers Quantifiers 0_Logic/1_Quantifiers/Task.v

echo "✅ Done!"