# gw-speed-certificate

Computer-assisted certificates that the speed of the λ-biased random walk on a Galton–Watson tree
with offspring uniform on {2,3} is **strictly decreasing on [0, 1.755]**.

The previously published range for this law is λ ≤ 2/(1+√(1/2)) ≈ 1.1716 (Song, Wang, Xiang,
J. Appl. Probab. 62(3), 2025). The certificates here cover [1.17, 1.755]; together they give
[0, 1.755]. This is a partial result: the conjecture concerns all of [0, 2.5).

## Reproduce

```bash
./run.sh
```

Creates a local virtual environment (numpy, mpmath, matplotlib), then writes to `results/`:

| File | What it is |
|---|---|
| `rigorous_crude.json` | one certificate per λ-cell of width 0.01 on [1.17, 1.80], K = 1000 |
| `rigorous_crude_edge_K2000.json` | cells of width 0.005 on [1.73, 1.80], K = 2000 |
| `independent_check_K150.json` | independent interval-arithmetic re-check of three cells |
| `certificate_summary.json` | every number quoted in the paper |
| `fig1_margin.png` | certified margin per cell (Figure 1) |

## What the computer checks, per λ-cell [λa, λb]

1. Upper and lower bounds (in the stochastic order) on the law of the conductance β: a monotone
   sandwich of discretised laws on the invariant interval [1 − λ/2, 1 − λ/3], with rounding and a
   CDF adjustment that keep each bound on the safe side.
2. From these, an upper bound on the left side and a lower bound on the right side of a
   difference-quotient inequality that implies R(λ)/λ, hence the speed, is strictly decreasing on
   the cell.
3. Exact rational checks of the positivity and monotonicity conditions the bounds rely on.
4. The final strict inequality, in exact rational arithmetic.

Floating-point work is bounded explicitly (all accumulated relative error below 1e-12, widened by
1e-10). `src/independent_check.py` repeats the whole computation with mpmath interval arithmetic and
shares no code with `src/rigorous_crude.py`.

## What is proved by hand

The reduction from the monotonicity of the speed to the per-cell inequality (support bounds for β,
monotonicity in λ, a pathwise Lipschitz bound, the difference-quotient criterion, and the
mean-value bookkeeping). See the paper.

## Licence

Code: Apache-2.0.
