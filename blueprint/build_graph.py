#!/usr/bin/env python3
"""Generate a self-contained PFR-style blueprint from compiled Lean dependencies.

Run from the project root after `lake env lean blueprint/Extract.lean`.
Graphviz is the only external rendering dependency. No browser/network is needed.
"""
from pathlib import Path
import argparse, collections, html, json, re, subprocess, textwrap

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'blueprint'
OUT = HERE / 'generated'
OUT.mkdir(exist_ok=True)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--overview-only', action='store_true', help='Rebuild the overview while retaining existing detailed views.')
args = parser.parse_args()
raw = {r['name']: r for r in json.loads((HERE/'compiled_dependencies.json').read_text())}
source = json.loads((HERE/'source_index.json').read_text())
missing = set(source) - raw.keys()
assert not missing, f'Source declarations missing from compiled environment: {sorted(missing)}'
records = {n: dict(raw[n], **source[n]) for n in source}
raw_deps = {n: [d for d in r['used'] if d in raw and d != n] for n,r in raw.items()}

# These labels are exposition only. Every edge below is obtained from Lean expressions.
friendly = {
 'theorem_3_1': 'Theorem 3.1 · Fault-tolerant sampling',
 'theorem_A_1': 'Theorem A.1 · Proxy-score sampling',
 'LowerBound.theorem_3_4_of_support': 'Theorem 3.4 · Support lower bound',
 'FiniteMetric.estimate_approximates_sensitivity': 'Theorem 4.1 · Sensitivity reduction',
 'Hardness.theorem_4_2_full_matrix': 'Theorem 4.2 · Conditional hardness',
 'lemma_3_2': 'Lemma 3.2 · Per-copy contribution',
 'clean_core_bounds': 'Clean-core invariant',
 'filtering_decoder_correct': 'Filtering decoder correctness',
 'Probability.iid_coreset_success_of_sampleSize': 'IID coreset success bound',
 'Probability.sensitivitySampling_fault_tolerant_rounded': 'Explicit IID fault-tolerant sampler',
 'LowerBound.weight_preservation': 'Claim A.2 · Weight preservation',
 'Hardness.weighted_sensitivity_formula': 'Exact hardness-instance sensitivity',
 'Hardness.Encoding.fullReductionCode_cost_size': 'Polynomial construction cost and size',
 'Counterexample.appendix_A1_counterexample': 'Appendix A.1 · Metric counterexample',
}
full = lambda n: "FTC."+n
overview_names = [full(n) for n in ['theorem_3_1', 'theorem_A_1', 'LowerBound.theorem_3_4_of_support', 'FiniteMetric.estimate_approximates_sensitivity', 'Hardness.theorem_4_2_full_matrix', 'lemma_3_2', 'clean_core_bounds', 'filtering_decoder_correct', 'Probability.iid_coreset_success_of_sampleSize', 'Probability.sensitivitySampling_fault_tolerant_rounded', 'LowerBound.weight_preservation', 'Hardness.weighted_sensitivity_formula', 'Hardness.Encoding.fullReductionCode_cost_size', 'Counterexample.appendix_A1_counterexample']]
assert all(n in records for n in overview_names), set(overview_names)-records.keys()
mains = {full(n) for n in ['theorem_3_1', 'theorem_A_1', 'LowerBound.theorem_3_4_of_support', 'FiniteMetric.estimate_approximates_sensitivity', 'Hardness.theorem_4_2_full_matrix']}

def displayed_dependencies(selected):
    """Nearest displayed dependencies, traversing omitted compiled helper constants."""
    selected = set(selected)
    edges, witnesses = set(), {}
    for target in sorted(selected):
        queue = collections.deque((d,[target,d]) for d in raw_deps.get(target,[]))
        seen = {target}
        while queue:
            dep,path = queue.popleft()
            if dep in seen: continue
            seen.add(dep)
            if dep in selected:
                edges.add((dep,target)); witnesses[(dep,target)] = list(reversed(path))
            else:
                queue.extend((d,path+[d]) for d in raw_deps.get(dep,[]) if d not in seen)
    return edges,witnesses

def reach(start,adj,skip=None):
    seen=set(); todo=[start]
    while todo:
        x=todo.pop()
        for y in adj.get(x,[]):
            if (x,y)==skip or y in seen: continue
            seen.add(y); todo.append(y)
    return seen

def reduce_edges(nodes,edges):
    """Remove redundant transitive arrows only for an acyclic displayed graph."""
    adj={n:[] for n in nodes}; indeg={n:0 for n in nodes}
    for a,b in edges: adj[a].append(b); indeg[b]+=1
    todo=[n for n in nodes if indeg[n]==0]; visited=0
    while todo:
        n=todo.pop(); visited+=1
        for b in adj[n]:
            indeg[b]-=1
            if not indeg[b]:todo.append(b)
    if visited!=len(nodes): return edges,False
    return {e for e in edges if e[1] not in reach(e[0],adj,skip=e)},True

node_ids={n:'decl_'+str(i) for i,n in enumerate(sorted(records))}
nodes={}
summaries = json.loads((HERE/'descriptions.json').read_text())
for n, r in records.items():
    summaries.setdefault(n, 'Declaration in '+r['file']+'. See the Lean statement and proof below.')
assert records.keys() <= summaries.keys(), 'Missing node descriptions'
for n,r in records.items():
    short=n.removeprefix('FTC.')
    nodes[node_ids[n]]={
      'id':node_ids[n], 'name':n, 'label':friendly.get(short,short),
      'kind':'theorem' if raw[n]['kind']=='theorem' else 'definition',
      'summary':summaries[n],
      'statement':raw[n]['statement'], 'file':r['file'], 'line':r['line'],
      'source':r['source'], 'checked':True,
    }

views={
 'overview': ('Main results and ingredients', overview_names),
 'sampling': ('Sampling and decoding', [n for n,r in records.items() if '/Probability/' in r['file'] or Path(r['file']).stem in {'Sampling','SamplingWeights','Decoder','Basic'}]),
 'lower': ('Lower bound', [n for n,r in records.items() if '/LowerBound/' in r['file']]),
 'hardness': ('Conditional hardness', [n for n,r in records.items() if '/Hardness/' in r['file']]),
 'full': ('All source-named declarations', sorted(records)),
}
graph_data=json.loads((OUT/'graph_data.json').read_text())['views'] if args.overview_only else {}
for key,(title,chosen) in views.items():
    if args.overview_only and key != 'overview': continue
    edges,paths=displayed_dependencies(chosen)
    edges,acyclic=reduce_edges(chosen,edges)
    edge_list=[{'from':node_ids[a],'to':node_ids[b],'path':paths[(a,b)]} for a,b in sorted(edges)]
    lines=['digraph proof {',
      'graph [pack=true,packmode="array3",rankdir=TB,bgcolor="white",pad="0.22",nodesep="0.24",ranksep="0.55",splines=polyline,outputorder=edgesfirst];',
      'node [fontname="DejaVu Sans",fontsize=10,style=filled,fillcolor="#b9e5b2",color="#23823c",fontcolor="#133b1e",penwidth=1.3,margin="0.13,0.08"];',
      'edge [color="#748076",arrowsize=0.65,penwidth=0.8];']
    for n in sorted(chosen):
        d=nodes[node_ids[n]]
        label=d['label'] if key=='overview' else n.removeprefix('FTC.')
        label='\n'.join('\n'.join(textwrap.wrap(part,width=35,break_long_words=True,break_on_hyphens=False)) for part in label.split('\n'))
        attrs={'id':d['id'],'label':label,'shape':'ellipse' if d['kind']=='theorem' else 'box',
          'tooltip':n+' — Lean-checked'}
        if n in mains: attrs.update(penwidth='2.5',peripheries='2',fillcolor='#8fd18b',fontsize='12')
        lines.append(json.dumps(n)+' ['+','.join(k+'='+json.dumps(v,ensure_ascii=False) for k,v in attrs.items())+'];')
    for a,b in sorted(edges): lines.append(json.dumps(a)+' -> '+json.dumps(b)+';')
    lines.append('}')
    dot=OUT/(key+'.dot');dot.write_text('\n'.join(lines))
    svg=OUT/(key+'.svg')
    subprocess.run(['dot','-Tsvg',str(dot),'-o',str(svg)],check=True)
    graph_data[key]={'title':title,'nodes':[node_ids[n] for n in sorted(chosen)],'edges':edge_list,
      'acyclic':acyclic,'svg':re.sub(r'^.*?(?=<svg\s)','',svg.read_text(),flags=re.S)}

data={'nodes':nodes,'views':graph_data,'main':[node_ids[n] for n in sorted(mains)],
      'audit_count':(ROOT/'FaultTolerantCoresets/Audit.lean').read_text().count('#print axioms'),
      'extraction':'Lean 4.31.0 compiled ConstantInfo types and values; omitted helper constants traversed; transitive redundant arrows removed when acyclic.',
      'raw_declaration_count':len(raw),'source_declaration_count':len(records),
      'foundational_axioms':['propext','Classical.choice','Quot.sound'],
      'inspiration':'https://teorth.github.io/pfr/blueprint/dep_graph_document.html'}
(OUT/'graph_data.json').write_text(json.dumps(data,ensure_ascii=False,indent=2))
template=(HERE/'template.html').read_text()
payload=json.dumps(data,ensure_ascii=False).replace('</','<\\/')
(OUT/'Fault_Tolerant_Coresets_Blueprint.html').write_text(template.replace('__GRAPH_DATA__',payload))
subprocess.run(['dot','-Tpdf',str(OUT/'overview.dot'),'-o',str(OUT/'Fault_Tolerant_Coresets_Dependency_Graph.pdf')],check=True)
subprocess.run(['dot','-Tpng','-Gdpi=110',str(OUT/'overview.dot'),'-o',str(OUT/'Fault_Tolerant_Coresets_Dependency_Graph.png')],check=True)
(OUT/'Fault_Tolerant_Coresets_Dependency_Graph.svg').write_text((OUT/'overview.svg').read_text())
print(json.dumps({'source_nodes':len(records),'overview_nodes':len(overview_names),
 'views':{k:{'nodes':len(v['nodes']),'edges':len(v['edges']),'acyclic':v['acyclic']} for k,v in graph_data.items()}},indent=2))
