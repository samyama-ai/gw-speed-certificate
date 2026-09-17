#!/usr/bin/env python3
"""Independent checker for rigorous_crude.py. Shares NO code with it or with pilot/.

mpmath interval arithmetic (outward rounding, 80-bit precision) at coarse K, on spot cells.
Re-derives every step from ../PROOF.md:
  - index maps are interval-conservative: the upper envelope sends mass at s to ⌈upper end of
    (t−a)/h⌉, the lower envelope to ⌊lower end⌋ (no exact fallback needed);
  - each envelope is a concrete law defined by its CDF values G_j (exact binary numbers);
    after a step the new CDF is the conservative endpoint of the interval CDF (lower end for the
    upper envelope, upper end for the lower envelope), then made monotone with G_K = 1 (L2);
  - masses used in sums are the intervals G_j − G_{j−1}, which contain the exact masses;
  - all expectations, the R bracket and the L7–L8 criterion are computed as intervals;
  - corner conditions of L8 recomputed with exact Fractions.
At coarse K the brackets are wider than in the main certifier, so margins shrink; the point is to
confirm the logic on cells that the main certifier passes with room.
"""
import json
import sys
import time
from fractions import Fraction as Fr

from mpmath import iv, mp

iv.prec = 80
K = int(sys.argv[1]) if len(sys.argv) > 1 else 150
ITERS = int(sys.argv[2]) if len(sys.argv) > 2 else 90
HALF = iv.mpf(1) / 2


def I(q):
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def geometry(lam):
    a, b = 1 - lam / 2, 1 - lam / 3
    h = (b - a) / K
    A, Hh = I(a), I(h)
    return a, h, A, Hh, [A + Hh * j for j in range(K + 1)]


def maps(lam, nu, A, Hh):
    L = I(lam)
    up, dn = [], []
    for i in range(nu * K + 1):
        s = nu * A + Hh * i
        x = (s / (L + s) - A) / Hh
        up.append(min(K, max(0, int(mp.ceil(x.b)))))
        dn.append(min(K, max(0, int(mp.floor(x.a)))))
    return up, dn


def masses(G):
    return [iv.mpf(G[0])] + [iv.mpf(G[j]) - iv.mpf(G[j - 1]) for j in range(1, len(G))]


def conv(p, q):
    r = [iv.mpf(0)] * (len(p) + len(q) - 1)
    for i, pi in enumerate(p):
        if pi.b == 0:
            continue
        for j, qj in enumerate(q):
            if qj.b == 0:
                continue
            r[i + j] += pi * qj
    return r


def cdf_from(m, upper):
    """Interval masses -> conservative concrete CDF (list of mpf), last value 1."""
    G, acc, prev = [], iv.mpf(0), mp.mpf(0)
    for k, mk in enumerate(m):
        acc = acc + mk
        g = acc.a if upper else acc.b
        g = min(mp.mpf(1), max(mp.mpf(0), g))
        g = max(g, prev)
        G.append(g)
        prev = g
    G[-1] = mp.mpf(1)
    return G


def envelope(lam, upper):
    a, h, A, Hh, X = geometry(lam)
    m2 = maps(lam, 2, A, Hh)
    m3 = maps(lam, 3, A, Hh)
    j2, j3 = (m2[0], m3[0]) if upper else (m2[1], m3[1])
    G = [mp.mpf(0)] * K + [mp.mpf(1)] if upper else [mp.mpf(1)] * (K + 1)
    for _ in range(ITERS):
        u = masses(G)
        s2 = conv(u, u)
        s3 = conv(s2, u)
        out = [iv.mpf(0)] * (K + 1)
        for i, v in enumerate(s2):
            out[j2[i]] += v * HALF
        for i, v in enumerate(s3):
            out[j3[i]] += v * HALF
        G = cdf_from(out, upper)
    return X, G, A, Hh


def T_law(G, nu, upper, A, Hh):
    u = masses(G)
    t = u
    for _ in range(nu - 1):
        t = conv(t, u)
    Gt = cdf_from(t, upper)
    return [nu * A + Hh * j for j in range(len(Gt))], masses(Gt)


def esum(p, X, q, T, F):
    tot = iv.mpf(0)
    for pi, xi in zip(p, X):
        if pi.b == 0:
            continue
        row = iv.mpf(0)
        for qj, tj in zip(q, T):
            if qj.b == 0:
                continue
            row += qj * F(xi, tj)
        tot += pi * row
    return tot


def corner_checks(la, lb):
    cb, ca = 1 / (2 - lb), 1 / (2 - la)
    kap = 1 - cb * (lb - la)
    A, B = 1 - lb / 2, 1 - la / 3
    al = la - 1
    return all([kap > 0, la - 1 + 2 * A > 0, ca * 3 * A - 1 > 0, al + kap * (3 * A - B) > 0,
                cb * al + cb * kap * A - cb * kap * 3 * B + 2 * kap > 0, al + kap * (2 * A - B) > 0,
                cb * al + cb * kap * B - cb * kap * 2 * A - 2 * kap - 2 * kap * cb * (lb - 1) < 0])


def check_cell(la, lb):
    Xa, Ga, Aa, Ha = envelope(la, True)
    Xb, Gb, Ab, Hb = envelope(lb, False)
    Ua, Lb = masses(Ga), masses(Gb)
    La_, Lb_ = I(la), I(lb)
    E = {}
    for nu in (2, 3):
        TU, qU = T_law(Ga, nu, True, Aa, Ha)
        TL, qL = T_law(Gb, nu, False, Ab, Hb)
        E[(nu, "hi")] = esum(Ua, Xa, qL, TL, lambda x, t: x / (La_ - 1 + x + t)).b
        E[(nu, "lo")] = esum(Lb, Xb, qU, TU, lambda x, t: x / (Lb_ - 1 + x + t)).a
    E2h, E2l, E3h, E3l = (iv.mpf(E[k]) for k in ((2, "hi"), (2, "lo"), (3, "hi"), (3, "lo")))
    R_lo = (2 + E3l / (E2h + E3l)).a
    R_hi = min((2 + E3h / (E2l + E3h)).b, mp.mpf(5) / 2)
    rhs_lo = (iv.mpf(R_lo) / Lb_ * (E2l + E3l) / 2).a
    c = 1 / (2 - Lb_)
    kap = 1 - c * (Lb_ - La_)
    TU3, qU3 = T_law(Ga, 3, True, Aa, Ha)
    H3 = esum(Ua, Xa, qU3, TU3, lambda x, t: x * (c * t - 1) / (La_ - 1 + kap * (x + t)) ** 2).b
    TL2, qL2 = T_law(Gb, 2, False, Ab, Hb)
    H2 = esum(Ua, Xa, qL2, TL2, lambda x, t: x * (1 + c * (Lb_ - 1 + t)) / (La_ - 1 + kap * (x + t)) ** 2).b
    lhs_hi = ((3 - iv.mpf(R_lo)) / 2 * H3 + (iv.mpf(R_hi) - 2) / 2 * H2).b
    ok = corner_checks(la, lb) and R_lo > 2 and R_hi < 3
    return {"cell": [str(la), str(lb)], "R_lo": float(R_lo), "R_hi": float(R_hi), "lhs_hi": float(lhs_hi),
            "rhs_lo": float(rhs_lo), "margin": float((iv.mpf(rhs_lo) - iv.mpf(lhs_hi)).a),  # conservative lower end
            "certified": bool(ok and lhs_hi < rhs_lo)}


def main():
    # optional cells after K and ITERS, as decimal "la:lb" pairs, e.g. 1.750:1.755
    if len(sys.argv) > 3:
        cells = [tuple(Fr(x) for x in arg.split(":")) for arg in sys.argv[3:]]
        tag = "_" + "_".join(f"{float(la):.3f}-{float(lb):.3f}" for la, lb in cells)
    else:
        cells = [(Fr(117, 100), Fr(118, 100)), (Fr(140, 100), Fr(141, 100)), (Fr(160, 100), Fr(161, 100))]
        tag = ""
    out = []
    for la, lb in cells:
        t0 = time.time()
        r = check_cell(la, lb)
        r["seconds"] = round(time.time() - t0, 1)
        out.append(r)
        print(f"[{float(la):.2f},{float(lb):.2f}] K={K}: R∈[{r['R_lo']:.4f},{r['R_hi']:.4f}] lhs≤{r['lhs_hi']:+.5f} "
              f"rhs≥{r['rhs_lo']:+.5f} margin {r['margin']:+.5f} {'CERTIFIED' if r['certified'] else 'no'} ({r['seconds']}s)",
              flush=True)
    json.dump({"K": K, "iters": ITERS, "cells": out}, open(f"independent_check_K{K}{tag}.json", "w"), indent=1)


if __name__ == "__main__":
    main()
