"""Reject missing audits and nonstandard transitive axioms."""
from pathlib import Path
import re, sys
root = Path(__file__).resolve().parents[1]
expected = set(re.findall(r"^#print axioms (\S+)", (root/'FaultTolerantCoresets/Audit.lean').read_text(), re.M))
output = Path(sys.argv[1]).read_text()
found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output):
    found[name] = set(filter(None, re.split(r"[,\s]+", axioms.strip())))
for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
    found[name] = set()
assert expected and expected == found.keys(), f"Audit mismatch: missing={expected-found.keys()}, extra={found.keys()-expected}"
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in found.items():
    assert axioms <= allowed, f"{name}: unexpected axioms {axioms-allowed}"
print(f'All {len(found)} audited declarations use only standard logical axioms.')
