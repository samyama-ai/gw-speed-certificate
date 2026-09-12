#!/usr/bin/env python3
"""Finer certification near the end of the range: K = 2000, cells of width 0.005 on [1.73, 1.80],
unchanged functions from rigorous_crude.py. Overlaps the K = 1000 run on [1.73, 1.74]."""
import json
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rigorous_crude as rc  # noqa: E402

rc.K = 2000
edges = [Fr(173, 100) + Fr(i, 200) for i in range(15)]
env = {lam: rc.envelopes(lam) for lam in edges}
rows, run_end = [], edges[0]
for la, lb in zip(edges, edges[1:]):
    r = rc.certify(la, lb, env[la], env[lb])
    rows.append(r)
    if r["certified"] and run_end == la:
        run_end = lb
    print(f"[{float(la):.3f}, {float(lb):.3f}]  margin {r['margin']:+.5f}  {'CERTIFIED' if r['certified'] else 'no'}", flush=True)
print(f"K=2000 edge run: certified from 1.73 to {float(run_end)} = {run_end}")
json.dump({"K": 2000, "edges": [str(e) for e in edges], "run_end": str(run_end), "rows": rows,
           "exact_decisions": int(sum(e["exact_decisions"] for e in env.values()))},
          open("rigorous_crude_edge_K2000.json", "w"), indent=1)
