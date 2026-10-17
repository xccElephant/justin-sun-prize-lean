#!/usr/bin/env bash
set -euo pipefail
ROOT="/Users/xcc/Project/justin-sun-prize-lean"
TOOLCHAIN="/Users/xcc/.elan/toolchains/leanprover--lean4---v4.33.1"
export PATH="$TOOLCHAIN/bin:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin"
export LEAN_PATH="$ROOT/.lake/packages/Cli/.lake/build/lib/lean:$ROOT/.lake/packages/batteries/.lake/build/lib/lean:$ROOT/.lake/packages/Qq/.lake/build/lib/lean:$ROOT/.lake/packages/aesop/.lake/build/lib/lean:$ROOT/.lake/packages/proofwidgets/.lake/build/lib/lean:$ROOT/.lake/packages/importGraph/.lake/build/lib/lean:$ROOT/.lake/packages/LeanSearchClient/.lake/build/lib/lean:$ROOT/.lake/packages/plausible/.lake/build/lib/lean:$ROOT/.lake/packages/mathlib/.lake/build/lib/lean:$ROOT/.lake/build/lib/lean:$TOOLCHAIN/lib/lean"
exec "$TOOLCHAIN/bin/lean" "$@"
