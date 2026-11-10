#!/usr/bin/env bash
# Smoke Linux muro binaries from release.yml's dist/ directory.
#
# Always runs the binary that matches this machine (linux-x86_64 on
# x86_64, linux-aarch64 on aarch64) with a stripped environment, so a
# host Elixir or Erlang on PATH cannot satisfy the executable.
#
# When docker is available, also runs the Linux x86_64 binary inside a
# fresh ubuntu:24.04 container that must not contain Elixir or Erlang.
# That is the isolation check the hosted-runner workflow used. It is
# skipped on a runner without docker (the self-hosted arm64 image has
# none) rather than emulated: a Burrito executable unpacks a glibc
# ERTS, which qemu-user cannot run here without a foreign-arch sysroot
# we will not install on a persistent shared runner.
#
# Usage: release-linux-smoke.sh DIST_DIR
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: release-linux-smoke.sh DIST_DIR" >&2
  exit 2
fi

dist=$(cd "$1" && pwd)
here=$(cd "$(dirname "$0")" && pwd)

arch=$(uname -m)
case "$arch" in
  x86_64) native_suffix=linux-x86_64 ;;
  aarch64|arm64) native_suffix=linux-aarch64 ;;
  *)
    echo "unsupported runner arch ${arch}" >&2
    exit 1
    ;;
esac

shopt -s nullglob
native_matches=("${dist}"/muro-*-"${native_suffix}")
shopt -u nullglob
if [ "${#native_matches[@]}" -ne 1 ] || [ ! -f "${native_matches[0]}" ]; then
  echo "missing native binary: ${dist}/muro-*-${native_suffix}" >&2
  ls -la "$dist" >&2 || true
  exit 1
fi
native=${native_matches[0]}

smoke_native() {
  local src=$1
  local work
  work=$(mktemp -d)
  # shellcheck disable=SC2064
  trap "rm -rf '$work'" RETURN
  cp "$src" "$work/muro"
  chmod 0755 "$work/muro"
  echo "SMOKE native $(basename "$src") on ${arch} (stripped PATH)"
  env -i PATH="/usr/bin:/bin" HOME="$work" TMPDIR="$work" "$work/muro" --version
  env -i PATH="/usr/bin:/bin" HOME="$work" TMPDIR="$work" "$work/muro" check
  printf '%s\n' 'def one : run Nat := 0' > "$work/one.muro"
  env -i PATH="/usr/bin:/bin" HOME="$work" TMPDIR="$work" \
    "$work/muro" emit "$work/one.muro" --backend rust
  test -f "$work/one.rs"
  env -i PATH="/usr/bin:/bin" HOME="$work" TMPDIR="$work" \
    bash "$here/release-std-smoke.sh" "$work/muro"
}

smoke_native "$native"

if command -v docker >/dev/null 2>&1; then
  shopt -s nullglob
  x86_matches=("${dist}"/muro-*-linux-x86_64)
  shopt -u nullglob
  if [ "${#x86_matches[@]}" -ne 1 ] || [ ! -f "${x86_matches[0]}" ]; then
    echo "missing linux-x86_64 binary for docker smoke" >&2
    ls -la "$dist" >&2 || true
    exit 1
  fi
  echo "SMOKE linux-x86_64 in ubuntu:24.04 via docker"
  docker run --rm -i \
    -v "${dist}:/opt:ro" \
    -v "${here}/release-std-smoke.sh:/release-std-smoke.sh:ro" \
    ubuntu:24.04 /bin/bash -s <<'SCRIPT'
set -euo pipefail
if command -v elixir >/dev/null || command -v erl >/dev/null; then
  echo "the smoke container has Elixir or Erlang" >&2
  exit 1
fi
bin=$(echo /opt/muro-*-linux-x86_64)
cp "$bin" /tmp/muro
chmod 0755 /tmp/muro
/tmp/muro --version
/tmp/muro check
printf '%s\n' 'def one : run Nat := 0' > /tmp/one.muro
/tmp/muro emit /tmp/one.muro --backend rust
test -f /tmp/one.rs
bash /release-std-smoke.sh /tmp/muro
SCRIPT
else
  echo "docker is not available; skipped the ubuntu:24.04 linux-x86_64 isolation smoke"
fi

echo "smoked $(basename "$native") natively on ${arch}"
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  {
    echo "- native: \`$(basename "$native")\` on \`${arch}\` with a stripped PATH"
    if command -v docker >/dev/null 2>&1; then
      echo "- docker: \`linux-x86_64\` in \`ubuntu:24.04\` (no Elixir or Erlang)"
    else
      echo "- docker: skipped (no docker on this runner)"
    fi
  } >> "$GITHUB_STEP_SUMMARY"
fi
