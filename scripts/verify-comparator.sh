#!/usr/bin/env bash
set -euo pipefail

# Judge Solution against Challenge the way Palomar does: with the `lake
# comparator` that ships in this project's own toolchain, replaying the proof
# through Lean's kernel and the toolchain's bundled independent kernels
# (NanoDa and con-ron). Nothing is built from a pin; everything that judges
# comes from `lean-toolchain`, which Palomar requires to be v4.35.0-rc2 or
# later.
#
# Adapted from PalomarRegistry/PalomarTemplate (Apache-2.0). Local addition: with
# COMPARATOR_NO_SANDBOX=1 the check runs without the bwrap sandbox (for machines
# without bubblewrap, e.g. macOS). That is weaker than Palomar's check and is
# meant only for a trusted local checkout; CI always runs with the sandbox.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

sandbox_flag=()
required_commands=(bwrap lake lean python3)
if [ "${COMPARATOR_NO_SANDBOX:-0}" = "1" ]; then
  echo "warning: running lake comparator WITHOUT its sandbox (COMPARATOR_NO_SANDBOX=1)" >&2
  sandbox_flag=(--inadvisably-no-sandbox)
  required_commands=(lake lean python3)
fi

for required_command in "${required_commands[@]}"; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

# Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted
# comparator.json: it registers the toolchain's bundled kernels itself. This
# generated copy does the same, so the local check judges as the registry does.
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels is not a submitter field; Palomar rejects it", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

lake exe cache get
lake comparator --config "$config" ${sandbox_flag[@]+"${sandbox_flag[@]}"}
