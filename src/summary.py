#!/usr/bin/env python3
"""Collect every number the paper quotes into results/certificate_summary.json."""
import json
from fractions import Fraction as Fr

main = json.load(open("rigorous_crude.json"))
edge = json.load(open("rigorous_crude_edge_K2000.json"))
chk = json.load(open("independent_check_K150.json"))


def cell(rows, la, lb):
    return next(r for r in rows if Fr(r["la"]) == Fr(la) and Fr(r["lb"]) == Fr(lb))


m = main["rows"]
e = edge["rows"]
lam_main = Fr(main["lambda_star"])
lam_edge = Fr(edge["run_end"])
combined = lam_edge if lam_edge > lam_main and Fr(edge["edges"][0]) <= lam_main else lam_main
s = {
    "K_main": main["K"], "K_edge": edge["K"], "K_check": chk["K"], "EPS": main["EPS"],
    "lambda_star_main": float(lam_main), "lambda_star_combined": float(combined),
    "lambda_star_combined_fraction": str(combined),
    "cells_certified_main": sum(1 for r in m if r["certified"] and Fr(r["lb"]) <= lam_main),
    "exact_decisions_main": main["exact_decisions"], "exact_decisions_edge": edge["exact_decisions"],
    "margin_1_17": cell(m, "117/100", "59/50")["margin"],
    "margin_1_40": cell(m, "7/5", "141/100")["margin"],
    "margin_1_60": cell(m, "8/5", "161/100")["margin"],
    "margin_1_73": cell(m, "173/100", "87/50")["margin"],
    "margin_1_74_fail": cell(m, "87/50", "7/4")["margin"],
    "margin_edge_last": cell(e, "7/4", "351/200")["margin"],
    "margin_edge_fail": cell(e, "351/200", "44/25")["margin"],
    "check_margin_1_17": chk["cells"][0]["margin"], "check_margin_1_40": chk["cells"][1]["margin"],
    "check_margin_1_60": chk["cells"][2]["margin"],
    "check_all_certified": all(c["certified"] for c in chk["cells"]),
}
json.dump(s, open("certificate_summary.json", "w"), indent=1)
print(json.dumps(s, indent=1))
