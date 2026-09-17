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
| `independent_check_K1000_1.730-1.735.json` | the same check at K = 1000 on [1.730, 1.735] (`CHECK_EDGE=1`, 48 min) |
| `independent_check_K2000_1.750-1.755.json` | the same check at K = 2000 on the last cell, [1.750, 1.755] (`CHECK_EDGE=1`, 3 h) |
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

Floating-point work is bounded explicitly. Accumulated relative error is below 2e-12 and underflow
error below 1e-300 absolute; every distribution function is moved by 1e-10 relative plus 1e-10
absolute in the safe direction. `src/independent_check.py` repeats the whole computation with mpmath
interval arithmetic and shares no code with `src/rigorous_crude.py`. It takes the grid size, the
iteration count and optional cells:

```bash
cd results && ../.venv/bin/python ../src/independent_check.py 2000 90 1.750:1.755
```

## What is proved by hand

The reduction from the monotonicity of the speed to the per-cell inequality (support bounds for β,
monotonicity in λ, a pathwise Lipschitz bound, the difference-quotient criterion, and the
mean-value bookkeeping). See the paper.

## Licence

Code: Apache-2.0.
