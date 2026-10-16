#!/usr/bin/env bash
# Install the paper's toolchain under tools/ (everything here except this
# script and cvc5_dafny.sh is gitignored).
#
#   tools/dafny/       Dafny 4.11.0 release (the last 4.11 release; the paper's
#                      fork reports 4.11.1 as its development version). Enough
#                      for every probe; only the AST mapping step needs the fork.
#   tools/z3/          Z3 4.12.1, the solver the Dafny probes run with.
#   tools/dafny-fork/  with --fork: the Dafny fork (marchiesa/dafny, branch
#                      proof-lifting, commit 06ff43f7c) built from source. It
#                      adds `dafny verify --ast-mapping <file>`, a JSON mapping
#                      from Dafny source constructs to Boogie that the
#                      classifier uses to read the types of equality operands.
#   tools/verus/       symlink to a Verus 0.2026.02.22 install (see below).
#   tools/cvc5/        symlink to a cvc5 1.1.2 install (see below).
#
# Usage: tools/setup_toolchain.sh [--fork] [--verus DIR] [--cvc5 DIR]
#
# Verus and cvc5 are not downloaded. Pass the directories of existing
# installs, or symlink them yourself:
#   Verus 0.2026.02.22: https://github.com/verus-lang/verus/releases/tag/release/0.2026.02.22
#     (unpack; the directory holds `verus` and its bundled `z3`)
#   cvc5 1.1.2:         https://github.com/cvc5/cvc5/releases/tag/cvc5-1.1.2
#     (unpack; the directory holds `bin/cvc5`)
# The pipeline reads every binary location from solver_needs/config.py, which
# looks under tools/ unless SOLVER_NEEDS_DAFNY_DLL, SOLVER_NEEDS_Z3,
# SOLVER_NEEDS_VERUS or SOLVER_NEEDS_CVC5 name another path.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
DAFNY_VERSION=4.11.0
Z3_VERSION=4.12.1
FORK_REPO=https://github.com/marchiesa/dafny.git
FORK_BRANCH=proof-lifting
FORK_COMMIT=06ff43f7c913bd935178a56abedc5a398b8d2a00
JDK_URL_BASE=https://api.adoptium.net/v3/binary/latest/21/ga

BUILD_FORK=0
VERUS_DIR=""
CVC5_DIR=""
while [ $# -gt 0 ]; do
  case "$1" in
    --fork) BUILD_FORK=1 ;;
    --verus) VERUS_DIR="$2"; shift ;;
    --cvc5) CVC5_DIR="$2"; shift ;;
    *) echo "unknown option: $1" >&2; exit 2 ;;
  esac
  shift
done

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    DAFNY_ASSET="dafny-${DAFNY_VERSION}-arm64-macos-13.zip"
    Z3_ASSET="z3-${Z3_VERSION}-arm64-osx-11.0.zip"
    JDK_URL="${JDK_URL_BASE}/mac/aarch64/jdk/hotspot/normal/eclipse"
    JDK_HOME_SUFFIX="Contents/Home" ;;
  Linux-x86_64)
    DAFNY_ASSET="dafny-${DAFNY_VERSION}-x64-ubuntu-22.04.zip"
    Z3_ASSET="z3-${Z3_VERSION}-x64-glibc-2.35.zip"
    JDK_URL="${JDK_URL_BASE}/linux/x64/jdk/hotspot/normal/eclipse"
    JDK_HOME_SUFFIX="" ;;
  *) echo "unsupported platform: $(uname -s)-$(uname -m) (macOS arm64 and Linux x86_64 are supported)" >&2; exit 1 ;;
esac

mkdir -p "$HERE/downloads"
fetch() {  # fetch URL FILE
  if [ ! -f "$HERE/downloads/$2" ]; then
    echo "downloading $2"
    curl -sSL -o "$HERE/downloads/$2" "$1"
  fi
}

# --- Dafny release
if [ ! -f "$HERE/dafny/dafny/Dafny.dll" ]; then
  fetch "https://github.com/dafny-lang/dafny/releases/download/v${DAFNY_VERSION}/${DAFNY_ASSET}" "$DAFNY_ASSET"
  rm -rf "$HERE/dafny" && mkdir -p "$HERE/dafny"
  unzip -q "$HERE/downloads/$DAFNY_ASSET" -d "$HERE/dafny"
fi
echo "dafny:  $(dotnet "$HERE/dafny/dafny/Dafny.dll" --version)"

# --- Z3
if [ ! -x "$HERE/z3/bin/z3" ]; then
  fetch "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${Z3_ASSET}" "$Z3_ASSET"
  rm -rf "$HERE/z3" "$HERE/z3-unpack" && mkdir -p "$HERE/z3-unpack"
  unzip -q "$HERE/downloads/$Z3_ASSET" -d "$HERE/z3-unpack"
  mv "$HERE/z3-unpack"/z3-* "$HERE/z3" && rm -rf "$HERE/z3-unpack"
fi
echo "z3:     $("$HERE/z3/bin/z3" --version)"

# --- Verus and cvc5
if [ -n "$VERUS_DIR" ]; then
  rm -rf "$HERE/verus"; ln -s "$(cd "$VERUS_DIR" && pwd)" "$HERE/verus"
fi
if [ -x "$HERE/verus/verus" ]; then
  echo "verus:  $("$HERE/verus/verus" --version | tr '\n' ' ')"
else
  echo "verus:  not installed. Download Verus 0.2026.02.22 from"
  echo "        https://github.com/verus-lang/verus/releases/tag/release/0.2026.02.22"
  echo "        and rerun with --verus <unpacked directory> (or set SOLVER_NEEDS_VERUS)."
fi
if [ -n "$CVC5_DIR" ]; then
  rm -rf "$HERE/cvc5"; ln -s "$(cd "$CVC5_DIR" && pwd)" "$HERE/cvc5"
fi
if [ -x "$HERE/cvc5/bin/cvc5" ]; then
  echo "cvc5:   $("$HERE/cvc5/bin/cvc5" --version | head -1)"
else
  echo "cvc5:   not installed. Download cvc5 1.1.2 from"
  echo "        https://github.com/cvc5/cvc5/releases/tag/cvc5-1.1.2"
  echo "        and rerun with --cvc5 <unpacked directory> (or set SOLVER_NEEDS_CVC5)."
fi

# --- the Dafny fork (AST mapping step)
if [ "$BUILD_FORK" = 1 ]; then
  if [ ! -d "$HERE/dafny-fork/.git" ]; then
    git clone -q -b "$FORK_BRANCH" "$FORK_REPO" "$HERE/dafny-fork"
  fi
  git -C "$HERE/dafny-fork" checkout -q "$FORK_COMMIT"
  # The build embeds a Java runtime jar, so it needs a JDK; a self-contained
  # one is fetched into tools/jdk when none is on PATH.
  if ! command -v java >/dev/null 2>&1; then
    if [ ! -d "$HERE/jdk" ]; then
      fetch "$JDK_URL" jdk.tar.gz
      mkdir -p "$HERE/jdk" && tar -xzf "$HERE/downloads/jdk.tar.gz" -C "$HERE/jdk" --strip-components=1
    fi
    export JAVA_HOME="$HERE/jdk/${JDK_HOME_SUFFIX}"
    export PATH="$JAVA_HOME/bin:$PATH"
  fi
  echo "building the Dafny fork at $FORK_COMMIT (a few minutes)"
  (cd "$HERE/dafny-fork" && dotnet build Source/Dafny/Dafny.csproj)
  echo "fork:   $(dotnet "$HERE/dafny-fork/Binaries/Dafny.dll" --version)"
else
  echo "fork:   not built (rerun with --fork to clone and build it; needed only for the AST mapping step)"
fi
