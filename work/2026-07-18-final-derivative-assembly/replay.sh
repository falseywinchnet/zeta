#!/bin/sh
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
lake_bin=${LAKE_BIN:-"${ELAN_HOME:-$HOME/.elan}/bin/lake"}
if [ -n "${PF4_MODULE_DIR:-}" ]; then
  module_dir=$PF4_MODULE_DIR
  mkdir -p "$module_dir"
else
  module_dir=$(mktemp -d "${TMPDIR:-/tmp}/pf4-final-assembly.XXXXXX")
  trap 'rm -rf "$module_dir"' EXIT
fi

cd "$repo_root/proof/formal"
"$lake_bin" env lean -R "$repo_root/work/2026-07-18-coordinate-sign-bridge" \
  -o "$module_dir/CoordinateSignBridge.olean" \
  "$repo_root/work/2026-07-18-coordinate-sign-bridge/CoordinateSignBridge.lean"
"$lake_bin" env lean -R "$repo_root/work/2026-07-18-central-transport-identity" \
  -o "$module_dir/CentralTransportIdentity.olean" \
  "$repo_root/work/2026-07-18-central-transport-identity/CentralTransportIdentity.lean"
"$lake_bin" env lean -R "$repo_root/work/2026-07-18-c4-curvature-identity" \
  -o "$module_dir/C4CurvatureIdentity.olean" \
  "$repo_root/work/2026-07-18-c4-curvature-identity/C4CurvatureIdentity.lean"
LEAN_PATH="$module_dir${LEAN_PATH:+:$LEAN_PATH}" "$lake_bin" env lean \
  "$repo_root/work/2026-07-18-final-derivative-assembly/FinalDerivativeAssembly.lean"
