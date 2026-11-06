#!/usr/bin/env bash
# Check that a muro binary accepts the standard-library smoke book.
#
# The book is written with a quoted heredoc. The release workflow mounts
# this file into the container instead of nesting quotes inside bash -c.
#
# Usage:
#   release-std-smoke.sh MURO
#   release-std-smoke.sh MURO --book PATH
#
# MURO is invoked as `MURO check PATH`. The step fails when PATH is missing
# or empty, when that command fails, or when its stdout does not contain
# the checker's acceptance line.
set -euo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: release-std-smoke.sh MURO [--book PATH]" >&2
  exit 2
fi

bin=$1
shift

book=""
if [ "${1:-}" = "--book" ]; then
  if [ "$#" -ne 2 ]; then
    echo "usage: release-std-smoke.sh MURO --book PATH" >&2
    exit 2
  fi
  book=$2
elif [ "$#" -ne 0 ]; then
  echo "usage: release-std-smoke.sh MURO [--book PATH]" >&2
  exit 2
fi

work=""
if [ -z "$book" ]; then
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  book="$work/use_std.muro"
  cat >"$book" <<'EOF'
import "std:bool.muro"
def n : run Bool := not false
EOF
fi

if [ ! -s "$book" ]; then
  echo "std smoke book is missing: $book" >&2
  exit 1
fi

out=$("$bin" check "$book")
printf '%s\n' "$out"

case "$out" in
  *"All terms check. Evidence never becomes a run."*) ;;
  *)
    echo "std smoke did not accept use_std.muro" >&2
    exit 1
    ;;
esac
