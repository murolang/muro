#!/usr/bin/env bash
# Build the muro archive, install it into a temporary MIX_ARCHIVES, and run
# the tasks from a directory with no mix.exs.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

# grep -q in a pipeline exits 141 under pipefail. Match in the shell instead.
have() {
  case "$1" in
    *"$2"*) ;;
    *)
      echo "missing [$2] in $3" >&2
      printf '%s\n' "$1" >&2
      exit 1
      ;;
  esac
}

version=$(sed -n 's/^[[:space:]]*version: "\([^"]*\)".*/\1/p' mix.exs | head -n 1)
if [ -z "$version" ]; then
  echo "could not read the version from mix.exs" >&2
  exit 1
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

archives="$tmp/archives"
work="$tmp/work"
mkdir -p "$archives" "$work"

export MIX_ENV="${MIX_ENV:-dev}"
mix deps.get
mix archive.build -o "$archives/muro-${version}.ez"

export MIX_ARCHIVES="$archives"
mix archive.install --force "$archives/muro-${version}.ez"

cp "$root/examples/half_ok.muro" "$work/half_ok.muro"
cp "$root/examples/bad_dup.muro" "$work/bad_dup.muro"
cd "$work"

if [ -e mix.exs ]; then
  echo "work directory unexpectedly has a mix.exs" >&2
  exit 1
fi

got=$(mix muro --version)
printf '%s\n' "$got"
if [ "$got" != "Muro v${version}" ]; then
  echo "expected Muro v${version}, got: ${got}" >&2
  exit 1
fi

list=$(mix muro)
have "$list" "Muro v${version}" "mix muro"
have "$list" "mix muro.check" "mix muro"
have "$list" "mix muro.emit" "mix muro"

check_out=$(mix muro.check half_ok.muro)
have "$check_out" "Muro v${version}" "mix muro.check half_ok.muro"
have "$check_out" "All terms check. Evidence never becomes a run." "mix muro.check half_ok.muro"

# The Elixir backend prints the module. Save that text and check it.
mix muro.emit half_ok.muro > half_ok.ex
test -s half_ok.ex
first=$(head -n 1 half_ok.ex)
if [ "$first" != "defmodule HalfOk do" ]; then
  echo "expected half_ok.ex to start with the module, got: ${first}" >&2
  exit 1
fi
grep -q "def plus" half_ok.ex
grep -q "def half" half_ok.ex

set +e
mix muro.check bad_dup.muro >"$tmp/bad.out" 2>"$tmp/bad.err"
bad_status=$?
set -e
if [ "$bad_status" -eq 0 ]; then
  echo "expected mix muro.check to refuse bad_dup.muro" >&2
  cat "$tmp/bad.out" "$tmp/bad.err" >&2
  exit 1
fi
bad_all=$(cat "$tmp/bad.out" "$tmp/bad.err")
have "$bad_all" "Muro v${version}" "refused check"
have "$bad_all" "duplicate name" "refused check"

set +e
mix muro.emit half_ok.muro --backend c >"$tmp/c.out" 2>"$tmp/c.err"
c_status=$?
set -e
if [ "$c_status" -eq 0 ]; then
  echo "expected --backend c to fail without elixir_make" >&2
  cat "$tmp/c.out" "$tmp/c.err" >&2
  exit 1
fi
c_all=$(cat "$tmp/c.out" "$tmp/c.err")
have "$c_all" '{:elixir_make, "~> 0.10", runtime: false}' "backend c"
case "$c_all" in
  *UndefinedFunctionError*)
    echo "backend c raised UndefinedFunctionError" >&2
    printf '%s\n' "$c_all" >&2
    exit 1
    ;;
esac

# The Elixir module is already in half_ok.ex. A refused NIF writes no C.
if [ -e half_ok.c ] || [ -e half_ok.h ] || [ -e half_ok_nif.c ]; then
  echo "backend c wrote files after refusing the NIF" >&2
  ls -la >&2
  exit 1
fi

echo "archive smoke passed (${version})"
