#!/usr/bin/env python3
"""Figure 1: certified margin per λ-cell (lower bound of RHS minus upper bound of LHS)."""
import json
from fractions import Fraction as Fr

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

main = json.load(open("rigorous_crude.json"))["rows"]
edge = json.load(open("rigorous_crude_edge_K2000.json"))["rows"]
fig, ax = plt.subplots(figsize=(6.4, 3.4))
for rows, lab, mk in ((main, "K = 1000, cells 0.01", "o"), (edge, "K = 2000, cells 0.005", "s")):
    x = [float((Fr(r["la"]) + Fr(r["lb"])) / 2) for r in rows]
    y = [r["margin"] for r in rows]
    ax.plot(x, y, mk, ms=3.5, label=lab)
ax.axhline(0.0, color="k", lw=0.8)
ax.axvline(2 / (1 + 0.5 ** 0.5), color="0.5", ls="--", lw=0.8)
ax.text(2 / (1 + 0.5 ** 0.5) + 0.006, 0.02, "known bound\n$2/(1+\\sqrt{1/2})$", fontsize=8, color="0.3", va="bottom")
ax.set_xlabel("$\\lambda$ (cell midpoint)")
ax.set_ylabel("certified margin")
ax.legend(fontsize=8, loc="upper right")
fig.tight_layout()
fig.savefig("fig1_margin.png", dpi=200)
fig.savefig("fig1_margin.pdf")
print("wrote fig1_margin.png / .pdf")
