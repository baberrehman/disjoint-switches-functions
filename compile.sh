#!/bin/bash
# Compile all Coq developments (Coq 8.13 + TLC + Metalib).
# Prefers the artifact Docker image when the daemon is available.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
IMAGE="${SWITCHES_IMAGE:-disjoint-switches-functions}"

compile_dir() {
  local dir="$1"
  echo "===== $dir ====="
  if command -v coqc >/dev/null 2>&1 && coqc --version | grep -q '8.13'; then
    (cd "$ROOT/code/$dir" && make)
  else
    docker run --rm \
      -v "$ROOT/code/$dir:/src" \
      -w /tmp/build \
      "$IMAGE" \
      bash -lc "eval \$(opam env); mkdir -p /tmp/build && cp /src/*.v /src/Makefile /src/_CoqProject /tmp/build/ 2>/dev/null; cp -r /src/_build /tmp/build/_build 2>/dev/null || true; cd /tmp/build && make && cp -f *.vo /src/ 2>/dev/null || true"
  fi
}

compile_dir section3
compile_dir section3_domain
compile_dir section4
compile_dir section51
compile_dir section52
echo "===== ALL OK ====="
