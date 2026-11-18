# Fault-tolerant coresets proof graph

Open `generated/Fault_Tolerant_Coresets_Blueprint.html` locally. The graph is
self-contained, with overview, sampling, lower-bound, hardness, and full views.
Click declarations for their compiled Lean types and source proofs.

After installing Graphviz and building the pinned Lean environment, regenerate:

```sh
python3 blueprint/index_sources.py
lake env lean blueprint/Extract.lean
python3 blueprint/build_graph.py
```

Arrows are derived from compiled declaration types and proof terms. Paths
through omitted helpers are collapsed; redundant transitive edges are removed
for acyclic views. `generated/graph_data.json` records a compiled witness path
for every displayed edge. The full view includes indexed source declarations,
not every compiler-generated helper. Standard logical axioms are permitted;
checked proofs may still have explicit mathematical hypotheses, particularly
the conditional hardness result. See `FORMALIZATION.md` for scope.

The renderer is adapted from the online-carpooling-lean repository.
GitHub renders the SVG preview; the interactive HTML must be downloaded or
served. A repository administrator can enable GitHub Pages with GitHub Actions
and run the included Pages workflow to host it.

The overview has 14 nodes; the full view has 737 indexed declarations.
Some overview nodes are disconnected because the compiled proof does not
reference another displayed declaration; no expository arrows are invented.
