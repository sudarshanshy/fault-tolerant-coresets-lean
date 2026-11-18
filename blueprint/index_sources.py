#!/usr/bin/env python3
"""Index explicitly named declarations; compiled Lean is authoritative for names."""
from pathlib import Path
import json, re

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'blueprint'
declaration = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(theorem|lemma|def|abbrev|structure|inductive)\s+([\w.\u0080-\uffff]+)')
records = {}
for file in sorted((ROOT/'FaultTolerantCoresets').rglob('*.lean')):
    if file.name in {'Audit.lean', 'Demo.lean'}: continue
    lines = file.read_text().splitlines()
    stack, starts = [], []
    for i, line in enumerate(lines):
        match = re.match(r'^\s*namespace\s+([\w.]+)', line)
        if match:
            stack.append(match.group(1))
            continue
        if re.match(r'^\s*section(?:\s|$)', line):
            stack.append('')
            continue
        if re.match(r'^\s*end(?:\s|$)', line):
            if stack: stack.pop()
            continue
        match = declaration.match(line)
        if match:
            kind, name = match.groups()
            namespace = '.'.join(n for n in stack if n)
            qualified = name if name.startswith('FTC.') else namespace+'.'+name
            starts.append((i, qualified, kind))
    for j, (i, name, kind) in enumerate(starts):
        stop = starts[j+1][0] if j+1<len(starts) else len(lines)
        records[name] = {'file':str(file.relative_to(ROOT)), 'line':i+1,
                         'kind':kind, 'source':'\n'.join(lines[i:stop]).strip()}
(HERE/'source_index.json').write_text(json.dumps(records,ensure_ascii=False,indent=2))
(HERE/'source_names.txt').write_text('\n'.join(sorted(records))+'\n')
print(f'Indexed {len(records)} source declarations.')
