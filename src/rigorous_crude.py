#!/usr/bin/env python3
"""Milestone 3: rigorous cell certificates, crude-bound route, ν uniform on {2,3}.

Claim certified per cell [λa, λb] (with the lemmas in ../PROOF.md): x(λ) = R(λ)/λ, hence the speed
v = (R−λ)/(R+λ), is strictly decreasing on the cell. Difference-quotient criterion (PROOF.md L7), so
no differentiability of β is used: for λ1 < λ2 in the cell,
    x(λ2) < x(λ1)  ⇔  E[(ν − R1) Δf0/Δλ] < (R1/λ1) E[f0(λ2)],
and the left side is bounded pathwise by the mean value theorem plus the Lipschitz bound
0 ≤ β(λ1) − β(λ2) ≤ Δλ·c·β(λ1), c = 1/(2 − λb) (PROOF.md L5).

Conservative ingredients:
  * λ, a = 1 − λ/2, b = 1 − λ/3, h = λ/(6K) are exact Fractions; floats are only images.
  * index maps ⌈(t−a)/h⌉ / ⌊(t−a)/h⌋, t = s/(λ+s), s = νa + ih: float, with an exact-Fraction decision
    whenever the float value is within 1e-9 of an integer (count reported).
  * envelope masses by direct convolution; after every step the CDF is moved by relative EPS = 1e-10
    (far above the accumulated float error, about 1e-12 at K = 1000): upper envelopes get a lower CDF
    (stochastically larger), lower envelopes a higher CDF. Every iterate is a valid envelope (L2).
  * expectation double sums have nonnegative integrands; each is widened by relative EPS.
  * monotonicity of every integrand (needed for the stochastic-order bounds) is checked by exact
    Fraction inequalities at the worst corner of the union support (PROOF.md L8).
  * the final scalar algebra (R bracket, criterion) is exact Fraction arithmetic.
"""
import json
import math
import time
from fractions import Fraction as Fr

import numpy as np

K = 1000
EPS = 1e-10


def params(lam):
    a = 1 - lam / 2
    b = 1 - lam / 3
    return a, b, (b - a) / K


def index_map(lam, nu, up):
    a, b, h = params(lam)
    af, hf, lf = float(a), float(h), float(lam)
    i = np.arange(nu * K + 1)
    s = nu * af + hf * i
    x = (s / (lf + s) - af) / hf
    j = np.ceil(x) if up else np.floor(x)
    near = np.nonzero(np.abs(x - np.round(x)) < 1e-9)[0]
    for k in near:
        sF = nu * a + h * int(k)
        xF = (sF / (lam + sF) - a) / h
        j[k] = math.ceil(xF) if up else math.floor(xF)
    return np.clip(j, 0, K).astype(np.int64), len(near)


def upper_env(m):
    C = np.clip(np.cumsum(m) * (1 - EPS), 0.0, 1.0)
    C[-1] = 1.0
    return np.diff(np.maximum.accumulate(C), prepend=0.0)


def lower_env(m):
    C = np.clip(np.cumsum(m) * (1 + EPS) + EPS, 0.0, 1.0)
    C[-1] = 1.0
    return np.diff(np.maximum.accumulate(C), prepend=0.0)


def step(u, j2, j3):
    s2 = np.convolve(u, u)
    s3 = np.convolve(s2, u)
    return 0.5 * np.bincount(j2, weights=s2, minlength=K + 1) + 0.5 * np.bincount(j3, weights=s3, minlength=K + 1)


def envelopes(lam, iters=400):
    jm = {(nu, up): index_map(lam, nu, up) for nu in (2, 3) for up in (True, False)}
    U = np.zeros(K + 1); U[K] = 1.0
    L = np.zeros(K + 1); L[0] = 1.0
    for it in range(1, iters + 1):
        U2 = upper_env(step(U, jm[(2, True)][0], jm[(3, True)][0]))
        L2 = lower_env(step(L, jm[(2, False)][0], jm[(3, False)][0]))
        d = max(np.abs(np.cumsum(U2 - U)).max(), np.abs(np.cumsum(L2 - L)).max())
        U, L = U2, L2
        if d < 1e-13:
            break
    a, _, h = params(lam)
    x = float(a) + float(h) * np.arange(K + 1)
    return {"x": x, "U": U, "L": L, "iters": it, "exact_decisions": sum(v[1] for v in jm.values())}


def T_env(x, m, nu, upper):
    a, h = x[0], x[1] - x[0]
    t = m.copy()
    for _ in range(nu - 1):
        t = np.convolve(t, m)
    t = upper_env(t) if upper else lower_env(t)
    return nu * a + h * np.arange(len(t)), t


def esum(p, xv, q, Tv, F):
    return float(p @ F(xv[:, None], Tv[None, :]) @ q)


def certify(la, lb, ea, eb):
    xa, Ua = ea["x"], ea["U"]
    xb, Lb = eb["x"], eb["L"]
    laf, lbf = float(la), float(lb)
    cb = 1 / (2 - lb)
    ca = 1 / (2 - la)
    kap = 1 - cb * (lb - la)
    A, B = 1 - lb / 2, 1 - la / 3
    al = la - 1
    checks = {
        "kappa_pos": kap > 0,
        "f0_inc_b0": la - 1 + 2 * A > 0,
        "h3_pos": ca * 3 * A - 1 > 0,
        "h3_inc_b0": al + kap * (3 * A - B) > 0,
        "h3_inc_T": cb * al + cb * kap * A - cb * kap * 3 * B + 2 * kap > 0,
        "h2_inc_b0": al + kap * (2 * A - B) > 0,
        "h2_dec_T": cb * al + cb * kap * B - cb * kap * 2 * A - 2 * kap - 2 * kap * cb * (lb - 1) < 0,
    }
    E = {}
    for nu in (2, 3):
        TxU, TU = T_env(xa, Ua, nu, True)
        TxL, TL = T_env(xb, Lb, nu, False)
        E[(nu, "hi")] = Fr(esum(Ua, xa, TL, TxL, lambda b0, T: b0 / (laf - 1 + b0 + T)) * (1 + EPS))
        E[(nu, "lo")] = Fr(esum(Lb, xb, TU, TxU, lambda b0, T: b0 / (lbf - 1 + b0 + T)) * (1 - EPS))
    E2h, E2l, E3h, E3l = E[(2, "hi")], E[(2, "lo")], E[(3, "hi")], E[(3, "lo")]
    R_lo = 2 + E3l / (E2h + E3l)
    R_hi = min(2 + E3h / (E2l + E3h), Fr(5, 2))
    rhs_lo = R_lo / lb * (E2l + E3l) / 2
    cbf, kapf = float(cb), float(kap)
    TxU3, TU3 = T_env(xa, Ua, 3, True)
    H3 = Fr(esum(Ua, xa, TU3, TxU3, lambda b0, T: b0 * (cbf * T - 1.0) / (laf - 1 + kapf * (b0 + T)) ** 2) * (1 + EPS))
    TxL2, TL2 = T_env(xb, Lb, 2, False)
    H2 = Fr(esum(Ua, xa, TL2, TxL2, lambda b0, T: b0 * (1.0 + cbf * (lbf - 1 + T)) / (laf - 1 + kapf * (b0 + T)) ** 2) * (1 + EPS))
    lhs_hi = (3 - R_lo) / 2 * H3 + (R_hi - 2) / 2 * H2
    ok = all(checks.values()) and 2 < R_lo and R_hi < 3
    return {"la": str(la), "lb": str(lb), "R_lo": float(R_lo), "R_hi": float(R_hi), "lhs_hi": float(lhs_hi),
            "rhs_lo": float(rhs_lo), "margin": float(rhs_lo - lhs_hi), "checks": {k: bool(v) for k, v in checks.items()},
            "certified": bool(ok and lhs_hi < rhs_lo)}


def main():
    t0 = time.time()
    edges = [Fr(117, 100) + Fr(i, 100) for i in range(64)]          # 1.17 .. 1.80
    env = {}
    for lam in edges:
        env[lam] = envelopes(lam)
    print(f"envelopes for {len(edges)} λ in {time.time() - t0:.0f}s; exact index decisions: "
          f"{sum(e['exact_decisions'] for e in env.values())}; max iters {max(e['iters'] for e in env.values())}", flush=True)
    rows, run_end = [], edges[0]
    for la, lb in zip(edges, edges[1:]):
        r = certify(la, lb, env[la], env[lb])
        rows.append(r)
        if r["certified"] and run_end == la:
            run_end = lb
        print(f"[{float(la):.2f}, {float(lb):.2f}]  R∈[{r['R_lo']:.4f},{r['R_hi']:.4f}]  lhs≤{r['lhs_hi']:+.5f}  "
              f"rhs≥{r['rhs_lo']:+.5f}  margin {r['margin']:+.5f}  {'CERTIFIED' if r['certified'] else 'no'}"
              f"{'' if all(r['checks'].values()) else '  CHECK FAILED: ' + str([k for k, v in r['checks'].items() if not v])}",
              flush=True)
    print(f"RIGOROUS λ* (contiguous from 1.17, K={K}, cells 0.01): {float(run_end)} = {run_end}")
    json.dump({"K": K, "EPS": EPS, "lambda_star": str(run_end), "rows": rows,
               "exact_decisions": int(sum(e["exact_decisions"] for e in env.values())),
               "max_iters": int(max(e["iters"] for e in env.values()))},
              open("rigorous_crude.json", "w"), indent=1)


if __name__ == "__main__":
    main()
