# gw-speed-certificate

Computer-assisted and formally verified (Lean 4) certificates that the speed of the λ-biased random
walk on a Galton–Watson tree with offspring uniform on {2,3} is **strictly decreasing on [0, 1.755]**.

The previously published range for this law is λ ≤ 2/(1+√(1/2)) ≈ 1.1716 (Song, Wang, Xiang,
J. Appl. Probab. 62(3), 2025). The certificates here cover [1.17, 1.755]; together they give
[0, 1.755]. This is a partial result: the conjecture concerns all of [0, 2.5).

## Reproduce (Python certificates & Figure 1)

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

## Formal verification in Lean 4 (`lean/`)

All analytical reduction lemmas and an exact-integer certificate covering `[1.17, 1.755]` (`117/100`
to `351/200` across 34 contiguous rational cells) are formally verified in Lean 4 (`v4.35.0`,
`mathlib4 v4.35.0`) with zero `sorry`, zero floating-point axioms, and zero `native_decide`
(`Lean.ofReduceBool`):

| Module | Contents |
|---|---|
| `lean/GWSpeedCertificate/TreeConductance.lean` | Infinite `{2,3}` trees, conductance recursion, uniform contraction, support bounds (`1 - λ/2 ≤ β ≤ 1 - λ/3`), monotonicity in `λ`, and pathwise Lipschitz bound `0 ≤ β(λ₁) - β(λ₂) ≤ (λ₂ - λ₁) β(λ₁) / (2 - λ₂)` (Lemmas 4.1–4.3) |
| `lean/GWSpeedCertificate/Criterion.lean` | Speed-to-`R/λ` reduction, difference-quotient criterion, segment MVT worst-case bounds (`h₂`, `h₃`), corner monotonicity conditions, and interval gluing (Lemmas 3.1, 3.2, 6.1) |
| `lean/GWSpeedCertificate/StochasticOrder.lean` | Galton–Watson `{2,3}` root-splitting interface (`IsGWTree23`), 1-step post-fixpoint integer envelope checkers (`checkUpperEnv`, `checkLowerEnv`), Abel summation dominance, and soundness (`upperEnv_sound`, `lowerEnv_sound`; Lemma 5.1) |
| `lean/GWSpeedCertificate/CellVerifier.lean` | Pure natural-number cell verifier (`checkCell`) and soundness proof (`checkCell_sound`; Proposition 6.2) |
| `lean/GWSpeedCertificate/Certs/Batch01..14.lean`, `AllCells.lean` | 34 contiguous rational cell certificates verified in the Lean kernel via `Eq.refl true` (`r_div_lam_strictAntiOn_117_to_1755`) |
| `lean/GWSpeedCertificate/MainTheorem.lean` | Literature hypothesis structure `GWSpeedModel` (packaging Aïdékon's 2014 speed formula and Song–Wang–Xiang's 2025 monotonicity on `[0, 1.17]`) and `speed_strictAntiOn_zero_to_1755` |

### Reproduce the Lean 4 build and axiom check

```bash
# Optional: regenerate lean/GWSpeedCertificate/Certs/*.lean from scratch (~35 s)
python3 src/export_lean_certificates.py

# Fetch precompiled mathlib4 cache and verify all proofs in the Lean 4 kernel (~3 min)
cd lean
lake exe cache get
lake build
lake env lean --stdin << 'EOF'
import GWSpeedCertificate
#print axioms GWSpeedCertificate.speed_strictAntiOn_zero_to_1755
EOF
```

Expected output:
```text
'GWSpeedCertificate.speed_strictAntiOn_zero_to_1755' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What the computer checks, per λ-cell [λa, λb]

1. Upper and lower bounds (in the stochastic order) on the law of the conductance β: a monotone
   sandwich of discretised laws on the invariant interval [1 − λ/2, 1 − λ/3], with rounding and a
   CDF adjustment that keep each bound on the safe side (iterated in Python with explicit IEEE-754
   error bounds, and verified in Lean 4 as exact integer 1-step post-fixpoints of the RDE operator).
2. From these, an upper bound on the left side and a lower bound on the right side of a
   difference-quotient inequality that implies R(λ)/λ, hence the speed, is strictly decreasing on
   the cell.
3. Exact rational/integer checks of the positivity and monotonicity conditions the bounds rely on.
4. The final strict inequality, in exact rational/integer arithmetic.

In the Python certifier (`src/rigorous_crude.py`), floating-point work is bounded explicitly.
Accumulated relative error is below 2e-12 and underflow error below 1e-300 absolute; every
distribution function is moved by 1e-10 relative plus 1e-10 absolute in the safe direction.
`src/independent_check.py` repeats the whole computation with mpmath interval arithmetic and shares
no code with `src/rigorous_crude.py`. It takes the grid size, the iteration count and optional cells:

```bash
cd results && ../.venv/bin/python ../src/independent_check.py 2000 90 1.750:1.755
```

## External theorems assumed as hypotheses

In both the paper and `GWSpeedModel` (`lean/GWSpeedCertificate/MainTheorem.lean`), two external
results from the probability literature are taken as hypotheses rather than re-proved from scratch:
Aïdékon's speed formula (Probab. Theory Related Fields 159, 2014, Theorem 1.1) together with the
Galton–Watson root-splitting law, and Song, Wang and Xiang's monotonicity theorem on `[0, 1.17]`
(J. Appl. Probab. 62(3), 2025, Theorem 1.2). Every reduction from those hypotheses to `[0, 1.755]`
is proved both in the paper and in Lean 4.

## Licence

Code: Apache-2.0.
