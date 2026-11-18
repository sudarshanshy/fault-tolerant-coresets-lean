#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build
audit_output="$(mktemp)"
trap 'rm -f -- "$audit_output"' EXIT
lake env lean -j1 FaultTolerantCoresets/Audit.lean | tee "$audit_output"
python3 scripts/check_axioms.py "$audit_output"
lake env lean -j1 --run FaultTolerantCoresets/Executable/Demo.lean
lake env lean -j1 --run FaultTolerantCoresets/Hardness/Demo.lean
echo 'Build, axiom audit, and executable demos passed.'
