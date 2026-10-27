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

# A project that does not depend on muro keeps the archive. The host is
# neither compiled nor started.
host_parent="$tmp/host-parent"
mkdir -p "$host_parent"
(
  cd "$host_parent"
  mix new host --sup
)

host="$host_parent/host"
app_file="$host/lib/host/application.ex"
if [ ! -f "$app_file" ]; then
  echo "missing $app_file" >&2
  find "$host" -name '*.ex' >&2
  exit 1
fi

app_patched="$tmp/host-application.ex"
if ! awk '
  inserted { print; next }
  /def start\(_type, _args\) do/ {
    print
    print "    IO.puts(\"host application started\")"
    inserted = 1
    next
  }
  { print }
  END {
    if (!inserted) exit 2
  }
' "$app_file" >"$app_patched"; then
  echo "could not patch start/2 in $app_file" >&2
  exit 1
fi
mv "$app_patched" "$app_file"
have "$(cat "$app_file")" 'IO.puts("host application started")' "host application.ex"

cp "$root/examples/half_ok.muro" "$host/half_ok.muro"
(
  cd "$host"
  unset MIX_BUILD_PATH
  rm -rf _build

  set +e
  host_version=$(mix muro --version 2>&1)
  host_version_status=$?
  set -e
  printf '%s\n' "$host_version"
  if [ "$host_version_status" -ne 0 ]; then
    echo "host mix muro --version failed" >&2
    exit 1
  fi
  if [ "$host_version" != "Muro v${version}" ]; then
    echo "expected Muro v${version} inside the host, got: ${host_version}" >&2
    exit 1
  fi
  case "$host_version" in
    *"host application started"*)
      echo "mix muro --version started the host" >&2
      exit 1
      ;;
  esac
  if [ -e _build ]; then
    echo "mix muro --version compiled the host" >&2
    exit 1
  fi

  set +e
  host_check=$(mix muro.check half_ok.muro 2>&1)
  host_check_status=$?
  set -e
  printf '%s\n' "$host_check"
  if [ "$host_check_status" -ne 0 ]; then
    echo "host mix muro.check failed" >&2
    exit 1
  fi
  have "$host_check" "Muro v${version}" "host mix muro.check"
  have "$host_check" "All terms check. Evidence never becomes a run." "host mix muro.check"
  case "$host_check" in
    *"host application started"*)
      echo "mix muro.check started the host" >&2
      exit 1
      ;;
  esac
  if [ -e _build ]; then
    echo "mix muro.check compiled the host" >&2
    exit 1
  fi

  set +e
  mix muro.emit half_ok.muro >half_ok.ex 2>"$tmp/host-emit.err"
  host_emit_status=$?
  set -e
  if [ "$host_emit_status" -ne 0 ]; then
    echo "host mix muro.emit failed" >&2
    cat half_ok.ex "$tmp/host-emit.err" >&2
    exit 1
  fi
  host_emit_err=$(cat "$tmp/host-emit.err")
  case "$host_emit_err" in
    *"host application started"*)
      echo "mix muro.emit started the host" >&2
      exit 1
      ;;
  esac
  case "$(cat half_ok.ex)" in
    *"host application started"*)
      echo "mix muro.emit started the host" >&2
      exit 1
      ;;
  esac
  test -s half_ok.ex
  host_first=$(head -n 1 half_ok.ex)
  if [ "$host_first" != "defmodule HalfOk do" ]; then
    echo "expected half_ok.ex to start with the module, got: ${host_first}" >&2
    exit 1
  fi
  grep -q "def plus" half_ok.ex
  grep -q "def half" half_ok.ex
  if [ -e _build ]; then
    echo "mix muro.emit compiled the host" >&2
    exit 1
  fi
)

echo "archive smoke passed (${version})"
