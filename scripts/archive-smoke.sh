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
have "$list" "mix muro.gen" "mix muro"
have "$list" "mix muro.init" "mix muro"
have "$list" "mix muro.deps.get" "mix muro"

check_out=$(mix muro.check half_ok.muro)
have "$check_out" "Muro v${version}" "mix muro.check half_ok.muro"
have "$check_out" "All terms check. Evidence never becomes a run." "mix muro.check half_ok.muro"

cat >"$work/use_std.muro" <<'EOF'
import "std:bool.muro"
def n : run Bool := not false
EOF
std_out=$(mix muro.check use_std.muro)
have "$std_out" "Muro v${version}" "mix muro.check use_std.muro"
have "$std_out" "All terms check. Evidence never becomes a run." "mix muro.check use_std.muro"

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

cp "$root/examples/meet.muro" "$work/meet.muro"
mix muro.emit meet.muro --backend fsm > meet_fsm.ex
test -s meet_fsm.ex
fsm_first=$(head -n 1 meet_fsm.ex)
if [ "$fsm_first" != "defmodule MeetFsm do" ]; then
  echo "expected meet_fsm.ex to start with the module, got: ${fsm_first}" >&2
  exit 1
fi

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
if [ "$c_status" -ne 0 ]; then
  echo "expected --backend c outside a Mix project to write the C files" >&2
  cat "$tmp/c.out" "$tmp/c.err" >&2
  exit 1
fi
c_all=$(cat "$tmp/c.out" "$tmp/c.err")
case "$c_all" in
  *elixir_make*)
    echo "backend c outside a project mentioned elixir_make" >&2
    printf '%s\n' "$c_all" >&2
    exit 1
    ;;
esac
test -s half_ok.h
test -s half_ok.c
# The Elixir module from the earlier emit stays. A NIF would replace it.
if [ "$(head -n 1 half_ok.ex)" != "defmodule HalfOk do" ]; then
  echo "backend c outside a project replaced the Elixir module" >&2
  exit 1
fi
grep -q "def half" half_ok.ex
if [ -e half_ok_nif.c ] || [ -e half_ok_nif.h ] || [ -e half_ok.mk ] || [ -e priv/half_ok.so ]; then
  echo "backend c outside a project wrote a NIF" >&2
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

  # The host is a loaded Mix project and does not depend on elixir_make,
  # so the NIF is refused and no C is written.
  set +e
  mix muro.emit half_ok.muro --backend c >"$tmp/host-c.out" 2>"$tmp/host-c.err"
  host_c_status=$?
  set -e
  if [ "$host_c_status" -eq 0 ]; then
    echo "expected host --backend c to fail without elixir_make" >&2
    cat "$tmp/host-c.out" "$tmp/host-c.err" >&2
    exit 1
  fi
  host_c_all=$(cat "$tmp/host-c.out" "$tmp/host-c.err")
  have "$host_c_all" '{:elixir_make, "~> 0.10", runtime: false}' "host backend c"
  case "$host_c_all" in
    *UndefinedFunctionError*|*host\ application\ started*)
      echo "host backend c raised or started the host" >&2
      printf '%s\n' "$host_c_all" >&2
      exit 1
      ;;
  esac
  if [ -e half_ok.c ] || [ -e half_ok.h ] || [ -e half_ok_nif.c ] || [ -e half_ok.mk ]; then
    echo "host backend c wrote C after refusing the NIF" >&2
    ls -la >&2
    exit 1
  fi
  if [ "$(head -n 1 half_ok.ex)" != "defmodule HalfOk do" ]; then
    echo "host backend c replaced the Elixir module" >&2
    exit 1
  fi
  if [ -e _build ]; then
    echo "mix muro.emit --backend c compiled the host" >&2
    exit 1
  fi

  cat > muro.exs <<EOF
[
  muro: "${version}",
  modules: [
    {"half_ok.muro", Host.HalfOk, "lib/host/half_ok.ex"}
  ]
]
EOF

  set +e
  host_gen=$(mix muro.gen 2>&1)
  host_gen_status=$?
  set -e
  printf '%s\n' "$host_gen"
  if [ "$host_gen_status" -ne 0 ]; then
    echo "host mix muro.gen failed" >&2
    exit 1
  fi
  have "$host_gen" "written lib/host/half_ok.ex" "host mix muro.gen"
  test -s lib/host/half_ok.ex
  grep -q "defmodule Host.HalfOk do" lib/host/half_ok.ex

  set +e
  host_gen_check=$(mix muro.gen --check 2>&1)
  host_gen_check_status=$?
  set -e
  printf '%s\n' "$host_gen_check"
  if [ "$host_gen_check_status" -ne 0 ] || [ "$host_gen_check" != "ok" ]; then
    echo "host mix muro.gen --check did not print ok" >&2
    exit 1
  fi
  case "${host_gen}${host_gen_check}" in
    *"host application started"*)
      echo "mix muro.gen started the host" >&2
      exit 1
      ;;
  esac
  if [ -e _build ]; then
    echo "mix muro.gen compiled the host" >&2
    exit 1
  fi

  cp "$root/examples/meet.muro" meet.muro
  cat > muro.exs <<EOF
[
  muro: "${version}",
  modules: [
    {"half_ok.muro", Host.HalfOk, "lib/host/half_ok.ex"},
    {"meet.muro", Host.MeetFsm, "lib/host/meet_fsm.ex", [kind: :fsm]}
  ]
]
EOF

  set +e
  host_fsm_gen=$(mix muro.gen 2>&1)
  host_fsm_gen_status=$?
  set -e
  printf '%s\n' "$host_fsm_gen"
  if [ "$host_fsm_gen_status" -ne 0 ]; then
    echo "host fsm mix muro.gen failed" >&2
    exit 1
  fi
  have "$host_fsm_gen" "written lib/host/meet_fsm.ex" "host fsm gen"
  test -s lib/host/meet_fsm.ex
  grep -q "defmodule Host.MeetFsm do" lib/host/meet_fsm.ex

  set +e
  host_fsm_check=$(mix muro.gen --check 2>&1)
  host_fsm_check_status=$?
  set -e
  printf '%s\n' "$host_fsm_check"
  if [ "$host_fsm_check_status" -ne 0 ] || [ "$host_fsm_check" != "ok" ]; then
    echo "host fsm mix muro.gen --check did not print ok" >&2
    exit 1
  fi

  cat > fsm_walk.exs <<'EOF'
state = Host.MeetFsm.Ping.init()
{:ok, state} = Host.MeetFsm.Ping.recv(state, 0)
{:ok, state} = Host.MeetFsm.Ping.send(state, 1)
IO.puts("done=#{Host.MeetFsm.Ping.done?(state)}")
IO.inspect(Host.MeetFsm.Ping.recv(state, 9))
EOF

  set +e
  host_fsm_run=$(mix run --no-start fsm_walk.exs 2>&1)
  host_fsm_run_status=$?
  set -e
  printf '%s\n' "$host_fsm_run"
  if [ "$host_fsm_run_status" -ne 0 ]; then
    echo "host fsm walk failed" >&2
    exit 1
  fi
  have "$host_fsm_run" "done=true" "fsm walk"
  have "$host_fsm_run" "meet.muro:4 session ping: end" "fsm refusal"
  case "$host_fsm_run" in
    *"host application started"*)
      echo "fsm walk started the host" >&2
      exit 1
      ;;
  esac
  rm -rf _build

  # CI has git. A checkout without git skips the package case.
  if ! command -v git >/dev/null 2>&1; then
    echo "skip package import smoke: git is not on PATH"
  else
    shared_repo="$tmp/shared-pkg"
    mkdir -p "$shared_repo"
    (
      cd "$shared_repo"
      git -c user.name=t -c user.email=t@t -c commit.gpgsign=false -c init.defaultBranch=main init
      printf '%s\n' 'def shared : run Nat := 0' > shared.muro
      git -c user.name=t -c user.email=t@t -c commit.gpgsign=false -c init.defaultBranch=main add shared.muro
      git -c user.name=t -c user.email=t@t -c commit.gpgsign=false -c init.defaultBranch=main commit -m init
      git -c user.name=t -c user.email=t@t -c commit.gpgsign=false -c init.defaultBranch=main tag v1.0.0
    )

    printf '%s\n' 'import "pkg:shared/shared.muro"' 'def use : run Nat := shared' > book.muro
    cat > muro.exs <<EOF
[
  muro: "${version}",
  muro_deps: [
    shared: {:git, "file://${shared_repo}", tag: "v1.0.0"}
  ],
  modules: [
    {"book.muro", Host.SharedUse, "lib/host/shared_use.ex"}
  ]
]
EOF

    set +e
    pkg_get=$(mix muro.deps.get 2>&1)
    pkg_get_status=$?
    set -e
    printf '%s\n' "$pkg_get"
    if [ "$pkg_get_status" -ne 0 ]; then
      echo "host mix muro.deps.get failed" >&2
      exit 1
    fi
    have "$pkg_get" "fetched shared 1.0.0" "mix muro.deps.get"
    test -f muro.lock
    test -f muro_deps/shared/shared.muro
    case "$pkg_get" in
      *"host application started"*)
        echo "mix muro.deps.get started the host" >&2
        exit 1
        ;;
    esac
    if [ -e _build ]; then
      echo "mix muro.deps.get compiled the host" >&2
      exit 1
    fi

    set +e
    pkg_check=$(mix muro.check book.muro 2>&1)
    pkg_check_status=$?
    set -e
    printf '%s\n' "$pkg_check"
    if [ "$pkg_check_status" -ne 0 ]; then
      echo "host mix muro.check book.muro failed" >&2
      exit 1
    fi
    have "$pkg_check" "conforms to shared 1.0.0 (sha256 " "mix muro.check book.muro"
    case "$pkg_check" in
      *"host application started"*)
        echo "package mix muro.check started the host" >&2
        exit 1
        ;;
    esac

    set +e
    pkg_gen=$(mix muro.gen 2>&1)
    pkg_gen_status=$?
    set -e
    printf '%s\n' "$pkg_gen"
    if [ "$pkg_gen_status" -ne 0 ]; then
      echo "package mix muro.gen failed" >&2
      exit 1
    fi
    test -s lib/host/shared_use.ex
    grep -q "# Conforms to shared 1.0.0" lib/host/shared_use.ex
    if grep -q "$tmp" lib/host/shared_use.ex || grep -q "$host" lib/host/shared_use.ex; then
      echo "package target contains an absolute path" >&2
      exit 1
    fi

    set +e
    pkg_ok=$(mix muro.gen --check 2>&1)
    pkg_ok_status=$?
    set -e
    printf '%s\n' "$pkg_ok"
    if [ "$pkg_ok_status" -ne 0 ] || [ "$pkg_ok" != "ok" ]; then
      echo "package mix muro.gen --check did not print ok" >&2
      exit 1
    fi

    cp muro_deps/shared/shared.muro "$tmp/shared.muro.ok"
    printf '\n-- edited\n' >> muro_deps/shared/shared.muro
    set +e
    pkg_bad=$(mix muro.check book.muro 2>&1)
    pkg_bad_status=$?
    set -e
    printf '%s\n' "$pkg_bad"
    if [ "$pkg_bad_status" -eq 0 ]; then
      echo "expected mix muro.check to refuse a hand-edited package file" >&2
      exit 1
    fi
    have "$pkg_bad" "changed since muro.lock" "hand-edited package file"
    cp "$tmp/shared.muro.ok" muro_deps/shared/shared.muro

    (
      cd "$shared_repo"
      printf '%s\n' 'def shared : run Nat := suc 0' > shared.muro
      git -c user.name=t -c user.email=t@t -c commit.gpgsign=false -c init.defaultBranch=main add shared.muro
      git -c user.name=t -c user.email=t@t -c commit.gpgsign=false -c init.defaultBranch=main commit -m next
      git -c user.name=t -c user.email=t@t -c commit.gpgsign=false -c init.defaultBranch=main tag v1.0.1
    )
    cat > muro.exs <<EOF
[
  muro: "${version}",
  muro_deps: [
    shared: {:git, "file://${shared_repo}", tag: "v1.0.1"}
  ],
  modules: [
    {"book.muro", Host.SharedUse, "lib/host/shared_use.ex"}
  ]
]
EOF

    set +e
    pkg_get2=$(mix muro.deps.get 2>&1)
    pkg_get2_status=$?
    set -e
    printf '%s\n' "$pkg_get2"
    if [ "$pkg_get2_status" -ne 0 ]; then
      echo "host mix muro.deps.get after retag failed" >&2
      exit 1
    fi
    have "$pkg_get2" "changed shared.muro" "mix muro.deps.get retag"

    set +e
    pkg_stale=$(mix muro.gen --check 2>&1)
    pkg_stale_status=$?
    set -e
    printf '%s\n' "$pkg_stale"
    if [ "$pkg_stale_status" -eq 0 ]; then
      echo "expected mix muro.gen --check to fail stale after the package changed" >&2
      exit 1
    fi
    have "$pkg_stale" "stale" "package mix muro.gen --check"
    case "${pkg_get}${pkg_get2}${pkg_check}${pkg_gen}${pkg_ok}${pkg_bad}${pkg_stale}" in
      *"host application started"*)
        echo "package smoke started the host" >&2
        exit 1
        ;;
    esac
    if [ -e _build ]; then
      echo "package smoke compiled the host" >&2
      exit 1
    fi
  fi

  rm -rf book.muro muro_deps muro.lock lib/host/shared_use.ex

  cp "$root/examples/repr.muro" repr.muro
  cp "$root/examples/repr_names.muro" repr_names.muro

  # Closed equations. Round is the file stem, so the suite's default
  # implementation is the emitted module. RoundTest is the .exs mix test
  # loads. RoundSuite is the .ex the compiler checks @behaviour against.
  cat > round.muro <<'EOF'
def round : run Π (n : Nat) → Nat :=
  λ (n : Nat) → n

def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} :=
  refl

def step : run internal Π (n : Nat) → Nat :=
  λ (n : Nat) → suc n

def step-ok : evidence {step 0 ≡ suc 0 : Nat} :=
  refl
EOF

  cat > muro.exs <<EOF
[
  muro: "${version}",
  modules: [
    {"half_ok.muro", Host.HalfOk, "lib/host/half_ok.ex"},
    {"repr.muro", Host.Repr, "lib/host/repr.ex"},
    {"repr_names.muro", Host.ReprNames, "lib/host/repr_names.ex"},
    {"round.muro", Round, "lib/round.ex"},
    {"round.muro", RoundTest, "test/round_test.exs", [kind: :exunit]},
    {"round.muro", RoundSuite, "test/support/round_suite.ex", [kind: :exunit]}
  ]
]
EOF

  mix_patched="$tmp/host-mix.exs"
  if ! awk '
    {
      lines[NR] = $0
    }
    /deps: deps\(\)/ && !done {
      lines[NR] = "        elixirc_paths: elixirc_paths(Mix.env()),\n        deps: deps()"
      done = 1
    }
    $0 == "end" { last = NR }
    END {
      if (!done || last == 0) exit 2
      for (i = 1; i <= NR; i++) {
        if (i == last) {
          print "  defp elixirc_paths(:test), do: [\"lib\", \"test/support\"]"
          print "  defp elixirc_paths(_), do: [\"lib\"]"
          print ""
        }
        print lines[i]
      }
    }
  ' mix.exs >"$mix_patched"; then
    echo "could not patch elixirc_paths in mix.exs" >&2
    exit 1
  fi
  mv "$mix_patched" mix.exs

  mkdir -p test/support
  cat > test/support/good_round.ex <<'EOF'
defmodule GoodRound do
  @behaviour RoundSuite.Behaviour
  def round(n), do: n
end
EOF
  cat > test/support/bad_round.ex <<'EOF'
defmodule IncompleteRound do
  @behaviour RoundSuite.Behaviour
end
EOF
  cat > test/support/wrong_round.ex <<'EOF'
defmodule BadRound do
  def round(_), do: 0
end
EOF

  set +e
  host_exunit_gen=$(mix muro.gen 2>&1)
  host_exunit_gen_status=$?
  set -e
  printf '%s\n' "$host_exunit_gen"
  if [ "$host_exunit_gen_status" -ne 0 ]; then
    echo "host mix muro.gen for the suite failed" >&2
    exit 1
  fi
  have "$host_exunit_gen" "written lib/round.ex" "host exunit gen"
  have "$host_exunit_gen" "written lib/host/repr.ex" "host exunit gen"
  have "$host_exunit_gen" "written lib/host/repr_names.ex" "host exunit gen"
  have "$host_exunit_gen" "written test/round_test.exs" "host exunit gen"
  have "$host_exunit_gen" "written test/support/round_suite.ex" "host exunit gen"
  have "$host_exunit_gen" "skipped test/round_test.exs: step-ok (round.muro:" "host exunit gen"
  have "$host_exunit_gen" "step is run internal and is not exported" "host exunit gen"
  test -s lib/round.ex
  test -s test/round_test.exs
  test -s test/support/round_suite.ex
  if grep -F "$host" lib/round.ex test/round_test.exs test/support/round_suite.ex >/dev/null; then
    echo "generated file contains an absolute path" >&2
    exit 1
  fi

  set +e
  host_exunit_check=$(mix muro.gen --check 2>&1)
  host_exunit_check_status=$?
  set -e
  printf '%s\n' "$host_exunit_check"
  if [ "$host_exunit_check_status" -ne 0 ] || [ "$host_exunit_check" != "ok" ]; then
    echo "host mix muro.gen --check after the suite did not print ok" >&2
    exit 1
  fi
  if [ -e _build ]; then
    echo "mix muro.gen compiled the host" >&2
    exit 1
  fi

  set +e
  host_exunit_test=$(MIX_ENV=test mix test --trace 2>&1)
  host_exunit_test_status=$?
  set -e
  printf '%s\n' "$host_exunit_test"
  if [ "$host_exunit_test_status" -ne 0 ]; then
    echo "host mix test did not pass the suite" >&2
    exit 1
  fi
  have "$host_exunit_test" "round.muro round-ok" "host mix test"
  if ! printf '%s\n' "$host_exunit_test" | grep -Eq '(^|[^0-9])0 failures|^Result: [0-9]+ passed'; then
    echo "missing a passing summary in host mix test" >&2
    exit 1
  fi
  if printf '%s\n' "$host_exunit_test" | grep -Eq '^Failed: |[1-9][0-9]* failures'; then
    echo "host mix test reported failures" >&2
    exit 1
  fi
  have "$host_exunit_test" "function round/1 required by behaviour RoundSuite.Behaviour is not implemented" "host mix test"
  have "$host_exunit_test" "IncompleteRound" "host mix test"

  cp test/test_helper.exs "$tmp/host-test-helper.exs"
  cat >> test/test_helper.exs <<'EOF'
Application.put_env(:muro, RoundTest, BadRound)
EOF

  set +e
  host_exunit_bad=$(MIX_ENV=test mix test --trace 2>&1)
  host_exunit_bad_status=$?
  set -e
  printf '%s\n' "$host_exunit_bad"
  if [ "$host_exunit_bad_status" -eq 0 ]; then
    echo "expected mix test to fail against BadRound" >&2
    exit 1
  fi
  have "$host_exunit_bad" "round.muro round-ok" "wrong adapter"
  mv "$tmp/host-test-helper.exs" test/test_helper.exs

  # A param library is the suite. Elixir emit still refuses it. The
  # exunit entry does not. The adapter is selected per test module.
  cat > kit.muro <<'EOF'
data Key : Type where
  k0 : Key
  k1 : Key

data Answer : Type where
  yes : Answer
  no : Answer

def rule : run Π (k : Key) → Answer :=
  λ (k : Key) →
    match k motive (λ _ → Answer)
      | k0 => yes
      | k1 => yes

param decide : run Π (k : Key) → Answer
param decide-is : evidence Π (k : Key) → {decide k ≡ rule k : Answer}

def golden : run Key := k0

def golden-k0 : evidence {decide golden ≡ yes : Answer} :=
  rewrite (decide-is golden) motive (λ z → {z ≡ yes : Answer}) in refl

def k0-yes : evidence {decide k0 ≡ yes : Answer} :=
  rewrite (decide-is k0) motive (λ z → {z ≡ yes : Answer}) in refl

def k1-yes : evidence {decide k1 ≡ yes : Answer} :=
  rewrite (decide-is k1) motive (λ z → {z ≡ yes : Answer}) in refl

def wrap : run Π (k : Key) → Answer :=
  λ (k : Key) → decide k

def through : evidence {wrap k0 ≡ yes : Answer} :=
  rewrite (decide-is k0) motive (λ z → {z ≡ yes : Answer}) in refl
EOF

  set +e
  kit_elixir=$(mix muro.emit kit.muro 2>&1)
  kit_elixir_status=$?
  set -e
  printf '%s\n' "$kit_elixir"
  if [ "$kit_elixir_status" -eq 0 ]; then
    echo "expected mix muro.emit to refuse an unsupplied param library" >&2
    exit 1
  fi
  have "$kit_elixir" "is supplied by a file that imports this one" "elixir emit of kit.muro"

  cat > muro.exs <<EOF
[
  muro: "${version}",
  modules: [
    {"half_ok.muro", Host.HalfOk, "lib/host/half_ok.ex"},
    {"repr.muro", Host.Repr, "lib/host/repr.ex"},
    {"repr_names.muro", Host.ReprNames, "lib/host/repr_names.ex"},
    {"round.muro", Round, "lib/round.ex"},
    {"round.muro", RoundTest, "test/round_test.exs", [kind: :exunit]},
    {"round.muro", RoundSuite, "test/support/round_suite.ex", [kind: :exunit]},
    {"kit.muro", KitTest, "test/kit_test.exs", [kind: :exunit]}
  ]
]
EOF

  set +e
  kit_gen=$(mix muro.gen 2>&1)
  kit_gen_status=$?
  set -e
  printf '%s\n' "$kit_gen"
  if [ "$kit_gen_status" -ne 0 ]; then
    echo "host mix muro.gen for the param library failed" >&2
    exit 1
  fi
  have "$kit_gen" "written test/kit_test.exs" "kit gen"
  have "$kit_gen" "skipped test/kit_test.exs: through (kit.muro:" "kit gen"
  have "$kit_gen" "calls param decide through wrap" "kit gen"
  test -s test/kit_test.exs
  if grep -F "$host" test/kit_test.exs >/dev/null; then
    echo "generated kit suite contains an absolute path" >&2
    exit 1
  fi

  set +e
  kit_check=$(mix muro.gen --check 2>&1)
  kit_check_status=$?
  set -e
  printf '%s\n' "$kit_check"
  if [ "$kit_check_status" -ne 0 ] || [ "$kit_check" != "ok" ]; then
    echo "host mix muro.gen --check after the param library did not print ok" >&2
    exit 1
  fi

  cat > test/support/good_kit.ex <<'EOF'
defmodule GoodKit do
  @behaviour KitTest.Behaviour

  def decide(:k0), do: :yes
  def decide(:k1), do: :yes
end
EOF
  cat > test/support/bad_kit.ex <<'EOF'
defmodule BadKit do
  @behaviour KitTest.Behaviour

  def decide(:k0), do: :no
  def decide(:k1), do: :yes
end
EOF

  cp test/test_helper.exs "$tmp/host-test-helper.exs"
  cat >> test/test_helper.exs <<'EOF'
Application.put_env(:muro, KitTest, GoodKit)
EOF

  set +e
  kit_test=$(MIX_ENV=test mix test --trace 2>&1)
  kit_test_status=$?
  set -e
  printf '%s\n' "$kit_test"
  if [ "$kit_test_status" -ne 0 ]; then
    echo "host mix test did not pass the param library" >&2
    exit 1
  fi
  have "$kit_test" "kit.muro golden-k0" "kit mix test"
  if ! printf '%s\n' "$kit_test" | grep -Eq '(^|[^0-9])0 failures|^Result: [0-9]+ passed'; then
    echo "missing a passing summary in the param library mix test" >&2
    exit 1
  fi
  if printf '%s\n' "$kit_test" | grep -Eq '^Failed: |[1-9][0-9]* failures'; then
    echo "param library mix test reported failures" >&2
    exit 1
  fi

  cp "$tmp/host-test-helper.exs" test/test_helper.exs
  cat >> test/test_helper.exs <<'EOF'
Application.put_env(:muro, KitTest, BadKit)
EOF

  set +e
  kit_bad=$(MIX_ENV=test mix test --trace 2>&1)
  kit_bad_status=$?
  set -e
  printf '%s\n' "$kit_bad"
  if [ "$kit_bad_status" -eq 0 ]; then
    echo "expected mix test to fail against BadKit" >&2
    exit 1
  fi
  have "$kit_bad" "kit.muro golden-k0" "mutant adapter"
  have "$kit_bad" "kit.muro:" "mutant adapter file and line"
  mv "$tmp/host-test-helper.exs" test/test_helper.exs

  test -s lib/host/repr.ex
  test -s lib/host/repr_names.ex
  grep -q "def decode_entry" lib/host/repr.ex
  grep -q "def toggle" lib/host/repr.ex
  grep -q "def decode_template" lib/host/repr_names.ex
  grep -q "def muro_repr_table_new" lib/host/repr_names.ex

  set +e
  repr_check=$(mix muro.gen --check 2>&1)
  repr_check_status=$?
  set -e
  printf '%s\n' "$repr_check"
  if [ "$repr_check_status" -ne 0 ] || [ "$repr_check" != "ok" ]; then
    echo "host mix muro.gen --check did not print ok for repr.muro" >&2
    exit 1
  fi

  cat > repr_call.exs <<'EOF'
{:ok, v, table} = Host.Repr.decode_entry(%{"id" => 3, "enabled" => true})
enc = Host.Repr.encode_entry(Host.Repr.toggle(v), table)
bad = Host.Repr.decode_entry(%{"id" => 3, "enabled" => 1})
IO.puts("REPR_ENC #{inspect(enc)}")
IO.puts("REPR_BAD #{inspect(bad)}")
EOF

  set +e
  repr_run=$(mix run repr_call.exs 2>&1)
  repr_run_status=$?
  set -e
  printf '%s\n' "$repr_run"
  if [ "$repr_run_status" -ne 0 ]; then
    echo "host mix run of the repr codec failed" >&2
    exit 1
  fi
  have "$repr_run" "REPR_ENC" "repr encode"
  have "$repr_run" "\"id\" => 3" "repr encode id"
  have "$repr_run" "\"enabled\" => false" "repr encode enabled"
  have "$repr_run" "REPR_BAD {:error, {[\"enabled\"], {:not_boolean, 1}}}" "repr strict failure"

  cat > repr_names_call.exs <<'EOF'
wire = %{
  "*" => [%{"relation" => "*", "read" => true}],
  "auth" => [%{"relation" => "token", "read" => false}]
}
{:ok, v, table} = Host.ReprNames.decode_template(wire)
IO.puts("NAMES #{inspect(Host.ReprNames.muro_repr_table_names(table))}")
IO.puts("NAMES_ENC #{inspect(Host.ReprNames.encode_template(v, table))}")
IO.puts("NAMES_OFF #{inspect(Host.ReprNames.encode_template(Host.ReprNames.reads_off(v), table))}")
IO.puts("NAMES_COUNT #{inspect(Host.ReprNames.count_entries(v))}")
EOF

  set +e
  names_run=$(mix run repr_names_call.exs 2>&1)
  names_run_status=$?
  set -e
  printf '%s\n' "$names_run"
  if [ "$names_run_status" -ne 0 ]; then
    echo "host mix run of the names codec failed" >&2
    exit 1
  fi
  have "$names_run" 'NAMES ["auth", "token"]' "repr names table"
  have "$names_run" '"relation" => "*"' "repr names wild relation"
  have "$names_run" '"relation" => "token"' "repr names token relation"
  have "$names_run" '"read" => true' "repr names read true"
  have "$names_run" '"read" => false' "repr names read false"
  have "$names_run" 'NAMES_COUNT {:suc, {:suc, 0}}' "repr names count"

  cat > bad_repr.muro <<'EOF'
data E : Type where
  a : E
  b : E
repr E := a => nil | b => nil
EOF

  set +e
  bad_repr=$(mix muro.check bad_repr.muro 2>&1)
  bad_repr_status=$?
  set -e
  printf '%s\n' "$bad_repr"
  if [ "$bad_repr_status" -eq 0 ]; then
    echo "expected mix muro.check to refuse an ambiguous repr" >&2
    exit 1
  fi
  have "$bad_repr" "constructors a and b share a host shape (nil)" "ambiguous repr"
)

# From an empty directory: init, generate, check, then the two drift failures.
gen="$tmp/gen"
mkdir -p "$gen"
cd "$gen"

mix muro.init --ci github >"$tmp/init.out"
init_out=$(cat "$tmp/init.out")
have "$init_out" "created muro.exs" "mix muro.init"
have "$init_out" "created priv/muro/" "mix muro.init"
have "$init_out" "created .github/workflows/muro.yml" "mix muro.init"
have "$init_out" "Generated files are not edited by hand. The .muro file is the source. Run mix muro.gen after changing it." "mix muro.init"
if [ -e AGENTS.md ]; then
  echo "mix muro.init wrote AGENTS.md" >&2
  exit 1
fi

set +e
mix muro.init >"$tmp/init2.out" 2>"$tmp/init2.err"
init2_status=$?
set -e
if [ "$init2_status" -eq 0 ]; then
  echo "expected mix muro.init to refuse an existing manifest" >&2
  cat "$tmp/init2.out" "$tmp/init2.err" >&2
  exit 1
fi
have "$(cat "$tmp/init2.out" "$tmp/init2.err")" "refusing to overwrite an existing manifest: muro.exs" "mix muro.init again"

cp "$root/examples/using_prelude.muro" priv/muro/using_prelude.muro
cat > muro.exs <<EOF
[
  muro: "${version}",
  modules: [
    {"priv/muro/using_prelude.muro", Smoke.Before, "lib/smoke/before.ex"}
  ]
]
EOF

gen_out=$(mix muro.gen)
have "$gen_out" "written lib/smoke/before.ex" "mix muro.gen"
test -s lib/smoke/before.ex
grep -q "defmodule Smoke.Before do" lib/smoke/before.ex
if grep -q "defmodule UsingPrelude do" lib/smoke/before.ex; then
  echo "module name came from the file stem" >&2
  exit 1
fi
grep -q "Generated by Muro ${version} from priv/muro/using_prelude.muro" lib/smoke/before.ex
if grep -F "$gen" lib/smoke/before.ex >/dev/null; then
  echo "generated file contains an absolute path" >&2
  exit 1
fi

check_out=$(mix muro.gen --check)
if [ "$check_out" != "ok" ]; then
  echo "expected mix muro.gen --check to print ok, got:" >&2
  printf '%s\n' "$check_out" >&2
  exit 1
fi

cp lib/smoke/before.ex "$tmp/before.ex"
gen2=$(mix muro.gen)
have "$gen2" "unchanged lib/smoke/before.ex" "second mix muro.gen"
cmp lib/smoke/before.ex "$tmp/before.ex"

workflow=$(cat .github/workflows/muro.yml)
have "$workflow" "mix archive.install hex muro ${version} --force" "workflow"
have "$workflow" "mix muro.gen --check" "workflow"
case "$workflow" in
  *archive.install\ github*)
    echo "workflow installs from GitHub" >&2
    exit 1
    ;;
esac

printf '\n# hand\n' >> lib/smoke/before.ex
set +e
mix muro.gen --check >"$tmp/hand.out" 2>"$tmp/hand.err"
hand_status=$?
set -e
if [ "$hand_status" -eq 0 ]; then
  echo "expected mix muro.gen --check to fail after a hand edit" >&2
  exit 1
fi
hand_all=$(cat "$tmp/hand.out" "$tmp/hand.err")
have "$hand_all" "lib/smoke/before.ex: hand-edited target; priv/muro/using_prelude.muro is unchanged" "hand edit"

printf '\n-- smoke\n' >> priv/muro/using_prelude.muro
set +e
mix muro.gen --check >"$tmp/stale.out" 2>"$tmp/stale.err"
stale_status=$?
set -e
if [ "$stale_status" -eq 0 ]; then
  echo "expected mix muro.gen --check to fail after a book edit" >&2
  exit 1
fi
stale_all=$(cat "$tmp/stale.out" "$tmp/stale.err")
have "$stale_all" "lib/smoke/before.ex: stale target; priv/muro/using_prelude.muro changed" "stale book"
case "$stale_all" in
  *hand-edited*)
    echo "a book edit was reported as a hand edit" >&2
    printf '%s\n' "$stale_all" >&2
    exit 1
    ;;
esac

# The published package must compile. manual/for-agents.md is read
# while compiling Muro.Skills, so a tarball that omits it fails here.
hex_dir="$tmp/hex-unpacked"
hex_app="$tmp/hex-app"
hex_archives="$tmp/hex-archives"
mkdir -p "$hex_dir" "$hex_app" "$hex_archives"
(
  cd "$root"
  # The smoke installs the archive into an empty MIX_ARCHIVES. Hex lives
  # in the default archives, and hex.build needs it to load the project.
  env -u MIX_ARCHIVES mix hex.build --output "$tmp/muro-${version}.tar"
)
tar -xf "$tmp/muro-${version}.tar" -C "$hex_dir"
# A Hex tarball is CHECKSUM, VERSION, metadata.config, and contents.tar.gz.
pkg="$hex_dir/src"
mkdir -p "$pkg"
tar -xzf "$hex_dir/contents.tar.gz" -C "$pkg"
test -f "$pkg/manual/for-agents.md"
test -f "$pkg/lib/muro/skills.ex"
if grep -q burrito "$hex_dir/metadata.config"; then
  echo "the hex package lists burrito" >&2
  exit 1
fi

cat >"$hex_app/mix.exs" <<EOF
defmodule HexApp.MixProject do
  use Mix.Project

  def project do
    [
      app: :hex_app,
      version: "0.1.0",
      elixir: "~> 1.15",
      deps: [{:muro, path: "${pkg}"}]
    ]
  end

  def application do
    [extra_applications: [:logger]]
  end
end
EOF

(
  cd "$hex_app"
  unset MIX_BUILD_PATH
  unset MIX_ARCHIVES
  mix deps.get
  mix compile
  block=$(mix run -e 'IO.write(Muro.Skills.block(nil))')
  printf '%s\n' "$block"
  have "$block" "<!-- muro:begin -->" "packaged skills block"
  have "$block" "<!-- muro:end -->" "packaged skills block"
  have "$block" "muro check" "packaged skills block"
  # Archive the beams compiled from the package, not the checkout.
  mix archive.build -i "_build/${MIX_ENV}/lib/muro" -o "$hex_archives/muro-${version}.ez"
)

MIX_ARCHIVES="$hex_archives" mix archive.install --force "$hex_archives/muro-${version}.ez"

hex_work="$tmp/hex-work"
mkdir -p "$hex_work"
(
  cd "$hex_work"
  got=$(MIX_ARCHIVES="$hex_archives" mix muro --version)
  printf '%s\n' "$got"
  if [ "$got" != "Muro v${version}" ]; then
    echo "expected Muro v${version} from the packaged archive, got: ${got}" >&2
    exit 1
  fi
  cat > use_std.muro <<'EOF'
import "std:bool.muro"
def n : run Bool := not false
EOF
  std_out=$(MIX_ARCHIVES="$hex_archives" mix muro.check use_std.muro)
  printf '%s\n' "$std_out"
  have "$std_out" "All terms check. Evidence never becomes a run." "packaged archive std import"
)

echo "archive smoke passed (${version})"
