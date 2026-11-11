import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Sections 3, 6 & 7: Difference-Quotient Criterion, Cell Bounds & Interval Gluing (`Criterion.lean`)

Proves with zero `sorry` and zero floating-point assumptions:
- **Lemma 3.1 (`lemma_3_1_speed_formula`, `lemma_3_1_strictAntiOn`)**: `v = (R - λ)/(R + λ)` is strictly decreasing iff `R/λ` is.
- **Lemma 3.2 (`lemma_3_2_diff_quotient`)**: Exact difference-quotient equivalence for `R(λ₂)/λ₂ < R(λ₁)/λ₁`.
- **Chebyshev Cap (`R_bounds_of_E2_E3`)**: `E₃ ≤ E₂ ⟹ 2 < 2 + E₃/(E₂ + E₃) ≤ 5/2`.
- **Lemma 6.1 (`lemma_6_1_nu3`, `lemma_6_1_nu2`)**: Pointwise bounds by `h₃` and `h₂` via exact
  cross-multiplication factoring of `Δf₀`.
- **Corner Monotonicity (`h3Func_mono_box`, `h2Func_mono_anti_box`, `f0Func_mono_y0`, `f0Func_anti_t`, `f0Func_anti_lam`)**:
  The affine corner inequalities imply monotonicity of `h₃`, `h₂`, and `f₀` across `[A, B] × [νA, νB]`.
- **Interval-Chain Gluing (`strictAntiOn_Icc_glue`, `strictAntiOn_chain`)**: Strict decrease on adjacent
  closed intervals glues to strict decrease on `[0, 351/200]`.
-/

namespace GWSpeedCertificate

/-- Pointwise conductance ratio functional `f₀(λ, y₀, S) = y₀ / (λ - 1 + y₀ + S)`. -/
noncomputable def f0Func (lam y0 s : ℝ) : ℝ :=
  y0 / (lam - 1 + y0 + s)

/-- Upper-bound kernel `h₃` for `ν = 3` on a cell `[λa, λb]` (`Eq. 4` in Paper 24). -/
noncomputable def h3Func (la lb y t : ℝ) : ℝ :=
  y * ((1 / (2 - lb)) * t - 1) / ((la - 1) + (1 - (1 / (2 - lb)) * (lb - la)) * (y + t)) ^ 2

/-- Upper-bound kernel `h₂` for `ν = 2` on a cell `[λa, λb]` (`Eq. 4` in Paper 24). -/
noncomputable def h2Func (la lb y t : ℝ) : ℝ :=
  y * (1 + (1 / (2 - lb)) * (lb - 1 + t)) / ((la - 1) + (1 - (1 / (2 - lb)) * (lb - la)) * (y + t)) ^ 2

/-- **Lemma 3.1a**: Algebraic identity `(N - λM) / (N + λM) = (R - λ) / (R + λ)` when `R = N / M`. -/
theorem lemma_3_1_speed_formula {N M lam : ℝ} (hM : M ≠ 0) :
    (N - lam * M) / (N + lam * M) = (N / M - lam) / (N / M + lam) := by
  have h1 : N - lam * M = M * (N / M - lam) := by field_simp [hM]
  have h2 : N + lam * M = M * (N / M + lam) := by field_simp [hM]
  rw [h1, h2, mul_div_mul_left _ _ hM]

/-- **Lemma 3.1b (`lem:R`)**: For `R > 0` and `λ > 0`, `(R - λ)/(R + λ)` decreases iff `R/λ` decreases. -/
theorem lemma_3_1_strictAntiOn {R : ℝ → ℝ} {S : Set ℝ}
    (hlam : ∀ l ∈ S, 0 < l) (hR : ∀ l ∈ S, 0 < R l) :
    StrictAntiOn (fun l => (R l - l) / (R l + l)) S ↔
      StrictAntiOn (fun l => R l / l) S := by
  constructor <;> intro h l1 hl1 l2 hl2 hlt
  · have hstep := h hl1 hl2 hlt
    have d1 : 0 < R l1 + l1 := by linarith [hlam l1 hl1, hR l1 hl1]
    have d2 : 0 < R l2 + l2 := by linarith [hlam l2 hl2, hR l2 hl2]
    have p1 : 0 < l1 := hlam l1 hl1
    have p2 : 0 < l2 := hlam l2 hl2
    rw [div_lt_div_iff₀ d2 d1] at hstep
    rw [div_lt_div_iff₀ p2 p1]
    nlinarith
  · have hstep := h hl1 hl2 hlt
    have d1 : 0 < R l1 + l1 := by linarith [hlam l1 hl1, hR l1 hl1]
    have d2 : 0 < R l2 + l2 := by linarith [hlam l2 hl2, hR l2 hl2]
    have p1 : 0 < l1 := hlam l1 hl1
    have p2 : 0 < l2 := hlam l2 hl2
    rw [div_lt_div_iff₀ p2 p1] at hstep
    rw [div_lt_div_iff₀ d2 d1]
    nlinarith

/-- **Lemma 3.2 (`lem:dq`)**: Difference-quotient criterion at two biases `0 < λ₁ < λ₂`. -/
theorem lemma_3_2_diff_quotient {lam1 lam2 N1 M1 N2 M2 : ℝ}
    (hlam1 : 0 < lam1) (hlt : lam1 < lam2) (hM1 : 0 < M1) (hM2 : 0 < M2) :
    let R1 := N1 / M1
    let R2 := N2 / M2
    (R2 / lam2 < R1 / lam1) ↔
      ((N2 - N1) - R1 * (M2 - M1)) / (lam2 - lam1) < (R1 / lam1) * M2 := by
  intro R1 R2
  have hlam2 : 0 < lam2 := by linarith
  have hdl : 0 < lam2 - lam1 := by linarith
  have hident : (N2 - N1) - R1 * (M2 - M1) = M2 * (R2 - R1) := by
    unfold R1 R2
    field_simp [ne_of_gt hM1, ne_of_gt hM2]
    try ring
  rw [hident, div_lt_iff₀ hdl]
  unfold R1 R2
  rw [div_lt_div_iff₀ hlam2 hlam1]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [div_lt_div_iff₀ hM2 hM1]
  have heq : M2 * (N2 / M2 - N1 / M1) - N1 / M1 / lam1 * M2 * (lam2 - lam1) =
      (N2 * lam1 * M1 - N1 * lam2 * M2) / (M1 * lam1) := by
    field_simp [ne_of_gt hM1, ne_of_gt hM2, ne_of_gt hlam1]
    try ring
  constructor <;> intro h
  · have hm : (N2 * lam1 * M1 - N1 * lam2 * M2) / (M1 * lam1) < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) (by positivity)
    linarith
  · have hneg : (N2 * lam1 * M1 - N1 * lam2 * M2) / (M1 * lam1) < 0 := by linarith
    have hnum_neg : N2 * lam1 * M1 - N1 * lam2 * M2 < 0 := by
      by_contra hge
      have hpos : 0 ≤ (N2 * lam1 * M1 - N1 * lam2 * M2) / (M1 * lam1) :=
        div_nonneg (not_lt.mp hge) (by positivity)
      linarith
    nlinarith

/-- **Chebyshev Cap**: Since `f₀` is nonincreasing in `ν` (`E₃ ≤ E₂` with `0 < E₂, 0 < E₃`),
    `R = 2 + E₃ / (E₂ + E₃) ≤ 5/2` and `2 < R`. -/
theorem R_bounds_of_E2_E3 {E2 E3 : ℝ} (hE2 : 0 < E2) (hE3 : 0 < E3) (hle : E3 ≤ E2) :
    let R := 2 + E3 / (E2 + E3)
    2 < R ∧ R ≤ 5 / 2 := by
  intro R
  have hden : 0 < E2 + E3 := by linarith
  constructor
  · unfold R; linarith [div_pos hE3 hden]
  · unfold R
    have hdiv : E3 / (E2 + E3) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hden (by norm_num)]
      linarith
    linarith

/-- Exact cross-multiplication identity for `f₀(λ₂, y₀', S') - f₀(λ₁, y₀, S)`. -/
lemma f0Func_diff_ident {lam1 lam2 y0 y0' s s' : ℝ}
    (hd1 : lam1 - 1 + y0 + s ≠ 0) (hd2 : lam2 - 1 + y0' + s' ≠ 0) :
    f0Func lam2 y0' s' - f0Func lam1 y0 s =
      ((y0' - y0) * (lam1 - 1 + s) + y0 * ((s - s') - (lam2 - lam1))) /
        ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s')) := by
  unfold f0Func
  field_simp [hd1, hd2]
  try ring

/-- **Lemma 6.1 (`ν = 3`)**: Pointwise upper bound `(3 - R₁) * Δf₀ / Δλ ≤ (3 - R₁) * h₃(y₀, S)`. -/
theorem lemma_6_1_nu3 {la lb lam1 lam2 R1 y0 y0' s s' : ℝ}
    (hla1 : 1 < la) (hlb2 : lb < 2)
    (h1 : la ≤ lam1) (hlt : lam1 < lam2) (h2 : lam2 ≤ lb)
    (hR1 : R1 < 3)
    (hy0_pos : 0 < y0) (hs_lo : 3 * (1 - lb / 2) ≤ s)
    (hy0_dec : y0' ≤ y0) (hy0_lip : (1 - (1 / (2 - lb)) * (lb - la)) * y0 ≤ y0')
    (hs_lip_up : s - s' ≤ (lam2 - lam1) * (1 / (2 - lb)) * s)
    (hs_lip_lo : (1 - (1 / (2 - lb)) * (lb - la)) * s ≤ s')
    (hkap : 0 < 1 - (1 / (2 - lb)) * (lb - la)) :
    (3 - R1) * ((f0Func lam2 y0' s' - f0Func lam1 y0 s) / (lam2 - lam1)) ≤
      (3 - R1) * h3Func la lb y0 s := by
  set c := 1 / (2 - lb)
  set kap := 1 - c * (lb - la)
  set al := la - 1
  have hc_pos : 0 < c := by unfold c; positivity
  have hal_pos : 0 < al := by unfold al; linarith
  have hs_pos : 0 < s := by linarith
  have hd_lo : 0 < al + kap * (y0 + s) := by positivity
  have hkap_le1 : kap ≤ 1 := by
    have : 0 ≤ c * (lb - la) := mul_nonneg (le_of_lt hc_pos) (by linarith)
    linarith [show kap = 1 - c * (lb - la) from rfl]
  have hd1_ge : al + kap * (y0 + s) ≤ lam1 - 1 + y0 + s := by
    have : kap * (y0 + s) ≤ 1 * (y0 + s) := mul_le_mul_of_nonneg_right hkap_le1 (by linarith)
    linarith [show al = la - 1 from rfl]
  have hd2_ge : al + kap * (y0 + s) ≤ lam2 - 1 + y0' + s' := by
    linarith [show al = la - 1 from rfl, hy0_lip, hs_lip_lo]
  have hd1_pos : 0 < lam1 - 1 + y0 + s := lt_of_lt_of_le hd_lo hd1_ge
  have hd2_pos : 0 < lam2 - 1 + y0' + s' := lt_of_lt_of_le hd_lo hd2_ge
  have hdl_pos : 0 < lam2 - lam1 := by linarith
  have hcs : 0 < c * s - 1 := by
    have h32 : c * (3 * (1 - lb / 2)) = 3 / 2 := by
      unfold c; field_simp [show 2 - lb ≠ 0 by linarith]
    have hmul : c * (3 * (1 - lb / 2)) ≤ c * s := mul_le_mul_of_nonneg_left hs_lo (le_of_lt hc_pos)
    linarith
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  rw [f0Func_diff_ident (ne_of_gt hd1_pos) (ne_of_gt hd2_pos), div_div]
  change ((y0' - y0) * (lam1 - 1 + s) + y0 * (s - s' - (lam2 - lam1))) /
      ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s') * (lam2 - lam1)) ≤
      y0 * (c * s - 1) / (al + kap * (y0 + s)) ^ 2
  have hnum : (y0' - y0) * (lam1 - 1 + s) + y0 * (s - s' - (lam2 - lam1)) ≤
      (lam2 - lam1) * (y0 * (c * s - 1)) := by
    have ht1 : (y0' - y0) * (lam1 - 1 + s) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have ht2 : y0 * (s - s' - (lam2 - lam1)) ≤ y0 * ((lam2 - lam1) * c * s - (lam2 - lam1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hy0_pos)
    have hid : y0 * ((lam2 - lam1) * c * s - (lam2 - lam1)) = (lam2 - lam1) * (y0 * (c * s - 1)) := by ring
    linarith
  calc ((y0' - y0) * (lam1 - 1 + s) + y0 * (s - s' - (lam2 - lam1))) /
        ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s') * (lam2 - lam1))
      ≤ ((lam2 - lam1) * (y0 * (c * s - 1))) /
        ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s') * (lam2 - lam1)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
    _ = (y0 * (c * s - 1)) / ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s')) := by
          have : (lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s') * (lam2 - lam1) =
              (lam2 - lam1) * ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s')) := by ring
          rw [this, mul_div_mul_left _ _ (ne_of_gt hdl_pos)]
    _ ≤ (y0 * (c * s - 1)) / (al + kap * (y0 + s)) ^ 2 := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          rw [sq]
          exact mul_le_mul hd1_ge hd2_ge (le_of_lt hd_lo) (le_of_lt hd1_pos)

/-- **Lemma 6.1 (`ν = 2`)**: Pointwise upper bound `(2 - R₁) * Δf₀ / Δλ ≤ (R₁ - 2) * h₂(y₀, S)`. -/
theorem lemma_6_1_nu2 {la lb lam1 lam2 R1 y0 y0' s s' : ℝ}
    (hla1 : 1 < la) (hlb2 : lb < 2)
    (h1 : la ≤ lam1) (hlt : lam1 < lam2) (h2 : lam2 ≤ lb)
    (hR1 : 2 < R1)
    (hy0_pos : 0 < y0) (hs_pos : 0 < s)
    (hy0_lip_up : y0 - y0' ≤ (lam2 - lam1) * (1 / (2 - lb)) * y0)
    (hy0_lip_lo : (1 - (1 / (2 - lb)) * (lb - la)) * y0 ≤ y0')
    (hs_dec : s' ≤ s)
    (hs_lip_lo : (1 - (1 / (2 - lb)) * (lb - la)) * s ≤ s')
    (hkap : 0 < 1 - (1 / (2 - lb)) * (lb - la)) :
    (2 - R1) * ((f0Func lam2 y0' s' - f0Func lam1 y0 s) / (lam2 - lam1)) ≤
      (R1 - 2) * h2Func la lb y0 s := by
  set c := 1 / (2 - lb)
  set kap := 1 - c * (lb - la)
  set al := la - 1
  have hc_pos : 0 < c := by unfold c; positivity
  have hal_pos : 0 < al := by unfold al; linarith
  have hd_lo : 0 < al + kap * (y0 + s) := by positivity
  have hkap_le1 : kap ≤ 1 := by
    have : 0 ≤ c * (lb - la) := mul_nonneg (le_of_lt hc_pos) (by linarith)
    linarith [show kap = 1 - c * (lb - la) from rfl]
  have hd1_ge : al + kap * (y0 + s) ≤ lam1 - 1 + y0 + s := by
    have : kap * (y0 + s) ≤ 1 * (y0 + s) := mul_le_mul_of_nonneg_right hkap_le1 (by linarith)
    linarith [show al = la - 1 from rfl]
  have hd2_ge : al + kap * (y0 + s) ≤ lam2 - 1 + y0' + s' := by
    linarith [show al = la - 1 from rfl, hy0_lip_lo, hs_lip_lo]
  have hd1_pos : 0 < lam1 - 1 + y0 + s := lt_of_lt_of_le hd_lo hd1_ge
  have hd2_pos : 0 < lam2 - 1 + y0' + s' := lt_of_lt_of_le hd_lo hd2_ge
  have hdl_pos : 0 < lam2 - lam1 := by linarith
  have hrew : (2 - R1) * ((f0Func lam2 y0' s' - f0Func lam1 y0 s) / (lam2 - lam1)) =
      (R1 - 2) * ((f0Func lam1 y0 s - f0Func lam2 y0' s') / (lam2 - lam1)) := by ring
  rw [hrew]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  have hneg_diff : f0Func lam1 y0 s - f0Func lam2 y0' s' =
      ((y0 - y0') * (lam1 - 1 + s) + y0 * ((lam2 - lam1) - (s - s'))) /
        ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s')) := by
    unfold f0Func; field_simp [ne_of_gt hd1_pos, ne_of_gt hd2_pos]; try ring
  rw [hneg_diff, div_div]
  change ((y0 - y0') * (lam1 - 1 + s) + y0 * ((lam2 - lam1) - (s - s'))) /
      ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s') * (lam2 - lam1)) ≤
      y0 * (1 + c * (lb - 1 + s)) / (al + kap * (y0 + s)) ^ 2
  have hlb1s_pos : 0 < lb - 1 + s := by linarith
  have hnum_pos : 0 ≤ y0 * (1 + c * (lb - 1 + s)) := by positivity
  have hnum : (y0 - y0') * (lam1 - 1 + s) + y0 * ((lam2 - lam1) - (s - s')) ≤
      (lam2 - lam1) * (y0 * (1 + c * (lb - 1 + s))) := by
    have h1s_pos : 0 < lam1 - 1 + s := by linarith
    have h1s_le : lam1 - 1 + s ≤ lb - 1 + s := by linarith
    have ht1 : (y0 - y0') * (lam1 - 1 + s) ≤ ((lam2 - lam1) * c * y0) * (lb - 1 + s) := by
      calc (y0 - y0') * (lam1 - 1 + s)
          ≤ ((lam2 - lam1) * c * y0) * (lam1 - 1 + s) :=
            mul_le_mul_of_nonneg_right hy0_lip_up (le_of_lt h1s_pos)
        _ ≤ ((lam2 - lam1) * c * y0) * (lb - 1 + s) :=
            mul_le_mul_of_nonneg_left h1s_le (by positivity)
    have ht2 : 0 ≤ y0 * (s - s') := mul_nonneg (le_of_lt hy0_pos) (by linarith)
    have hid : ((lam2 - lam1) * c * y0) * (lb - 1 + s) + y0 * (lam2 - lam1) =
        (lam2 - lam1) * (y0 * (1 + c * (lb - 1 + s))) := by ring
    linarith
  calc ((y0 - y0') * (lam1 - 1 + s) + y0 * ((lam2 - lam1) - (s - s'))) /
        ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s') * (lam2 - lam1))
      ≤ ((lam2 - lam1) * (y0 * (1 + c * (lb - 1 + s)))) /
        ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s') * (lam2 - lam1)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
    _ = (y0 * (1 + c * (lb - 1 + s))) / ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s')) := by
          have : (lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s') * (lam2 - lam1) =
              (lam2 - lam1) * ((lam1 - 1 + y0 + s) * (lam2 - 1 + y0' + s')) := by ring
          rw [this, mul_div_mul_left _ _ (ne_of_gt hdl_pos)]
    _ ≤ (y0 * (1 + c * (lb - 1 + s))) / (al + kap * (y0 + s)) ^ 2 := by
          refine div_le_div_of_nonneg_left hnum_pos (by positivity) ?_
          rw [sq]
          exact mul_le_mul hd1_ge hd2_ge (le_of_lt hd_lo) (le_of_lt hd1_pos)

/-- Universal rational monotonicity lemma for `u ↦ u / (P + k * u)^2`:
    nondecreasing when `P ≥ k * max(u₁, u₂)` and nonincreasing when `P ≤ k * min(u₁, u₂)`. -/
lemma rat_quad_mono {P k u1 u2 : ℝ}
    (hk : 0 ≤ k) (hu1 : 0 ≤ u1) (hle : u1 ≤ u2)
    (hd1 : 0 < P + k * u1) (hd2 : 0 < P + k * u2)
    (hcorner : k * u2 ≤ P) :
    u1 / (P + k * u1) ^ 2 ≤ u2 / (P + k * u2) ^ 2 := by
  rw [div_le_div_iff₀ (pow_pos hd1 2) (pow_pos hd2 2)]
  have hfact : u2 * (P + k * u1) ^ 2 - u1 * (P + k * u2) ^ 2 =
      (u2 - u1) * (P ^ 2 - (k * u1) * (k * u2)) := by ring
  have hku1 : 0 ≤ k * u1 := mul_nonneg hk hu1
  have hku12 : k * u1 ≤ k * u2 := mul_le_mul_of_nonneg_left hle hk
  have hku1P : k * u1 ≤ P := hku12.trans hcorner
  have hsq : (k * u1) * (k * u2) ≤ P ^ 2 := by
    rw [sq]
    exact mul_le_mul hku1P hcorner (mul_nonneg hk (hu1.trans hle)) (hku1.trans hku1P)
  have hprod : 0 ≤ (u2 - u1) * (P ^ 2 - (k * u1) * (k * u2)) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

lemma rat_quad_anti {P k u1 u2 : ℝ}
    (hk : 0 ≤ k) (_hu1 : 0 ≤ u1) (hle : u1 ≤ u2)
    (hd1 : 0 < P + k * u1) (hd2 : 0 < P + k * u2)
    (hcorner : P ≤ k * u1) :
    u2 / (P + k * u2) ^ 2 ≤ u1 / (P + k * u1) ^ 2 := by
  rw [div_le_div_iff₀ (pow_pos hd2 2) (pow_pos hd1 2)]
  have hfact : u1 * (P + k * u2) ^ 2 - u2 * (P + k * u1) ^ 2 =
      (u2 - u1) * ((k * u1) * (k * u2) - P ^ 2) := by ring
  have h1 : -(k * u1) < P := by linarith
  have h2 : k * u1 ≤ k * u2 := mul_le_mul_of_nonneg_left hle hk
  have hsq : P ^ 2 ≤ (k * u1) * (k * u2) := by nlinarith
  have hprod : 0 ≤ (u2 - u1) * ((k * u1) * (k * u2) - P ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- Monotonicity of `f₀(λ, y₀, t)` in `y₀`, `t`, and `λ`. -/
theorem f0Func_mono_y0 {lam y1 y2 t : ℝ}
    (hy1 : 0 ≤ y1) (hy : y1 ≤ y2) (hlt : 0 < lam - 1 + t) :
    f0Func lam y1 t ≤ f0Func lam y2 t := by
  unfold f0Func
  have hd1 : 0 < lam - 1 + y1 + t := by linarith
  have hd2 : 0 < lam - 1 + y2 + t := by linarith
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith

theorem f0Func_anti_t {lam y0 t1 t2 : ℝ}
    (hy0 : 0 ≤ y0) (ht : t1 ≤ t2) (hd1 : 0 < lam - 1 + y0 + t1) :
    f0Func lam y0 t2 ≤ f0Func lam y0 t1 := by
  unfold f0Func
  exact div_le_div_of_nonneg_left hy0 hd1 (by linarith)

theorem f0Func_anti_lam {lam1 lam2 y0 t : ℝ}
    (hy0 : 0 ≤ y0) (hl : lam1 ≤ lam2) (hd1 : 0 < lam1 - 1 + y0 + t) :
    f0Func lam2 y0 t ≤ f0Func lam1 y0 t := by
  unfold f0Func
  exact div_le_div_of_nonneg_left hy0 hd1 (by linarith)

/-- **Corner Monotonicity of `h₃(y, t)`**: On `y ∈ [A, B]`, `t ∈ [3A, 3B]`, the affine corner conditions
    imply `h₃(y₁, t₁) ≤ h₃(y₂, t₂)` for `y₁ ≤ y₂` and `t₁ ≤ t₂`. -/
theorem h3Func_mono_box {la lb A B y1 y2 t1 t2 : ℝ}
    (hla1 : 1 < la) (hlb2 : lb < 2) (hA : 0 < A)
    (hy1 : A ≤ y1) (hy12 : y1 ≤ y2) (hy2 : y2 ≤ B)
    (ht1 : 3 * A ≤ t1) (ht12 : t1 ≤ t2) (ht2 : t2 ≤ 3 * B)
    (hkap : 0 < 1 - (1 / (2 - lb)) * (lb - la))
    (h_pos_t : 0 ≤ (1 / (2 - lb)) * t1 - 1)
    (h_inc_y : 0 < (la - 1) + (1 - (1 / (2 - lb)) * (lb - la)) * (3 * A - B))
    (h_inc_t : 0 < (1 / (2 - lb)) * (la - 1) +
        (1 / (2 - lb)) * (1 - (1 / (2 - lb)) * (lb - la)) * A -
        (1 / (2 - lb)) * (1 - (1 / (2 - lb)) * (lb - la)) * (3 * B) +
        2 * (1 - (1 / (2 - lb)) * (lb - la))) :
    h3Func la lb y1 t1 ≤ h3Func la lb y2 t2 := by
  set c := 1 / (2 - lb)
  set kap := 1 - c * (lb - la)
  set al := la - 1
  have hc : 0 < c := by unfold c; positivity
  have hal : 0 < al := by unfold al; linarith
  have hckap : 0 < c * kap := mul_pos hc hkap
  have hd_y1t1 : 0 < al + kap * (y1 + t1) := by
    have : 0 < y1 + t1 := by linarith
    positivity
  have hd_y2t1 : 0 < al + kap * (y2 + t1) := by
    have : 0 < y2 + t1 := by linarith
    positivity
  have hd_y2t2 : 0 < al + kap * (y2 + t2) := by
    have : 0 < y2 + t2 := by linarith
    positivity
  -- Step 1: `h3(y1, t1) ≤ h3(y2, t1)`
  have hstep1 : h3Func la lb y1 t1 ≤ h3Func la lb y2 t1 := by
    change y1 * (c * t1 - 1) / (al + kap * (y1 + t1)) ^ 2 ≤
      y2 * (c * t1 - 1) / (al + kap * (y2 + t1)) ^ 2
    have hf1 : y1 * (c * t1 - 1) / (al + kap * (y1 + t1)) ^ 2 =
        (c * t1 - 1) * (y1 / ((al + kap * t1) + kap * y1) ^ 2) := by ring
    have hf2 : y2 * (c * t1 - 1) / (al + kap * (y2 + t1)) ^ 2 =
        (c * t1 - 1) * (y2 / ((al + kap * t1) + kap * y2) ^ 2) := by ring
    rw [hf1, hf2]
    refine mul_le_mul_of_nonneg_left ?_ h_pos_t
    have hd1' : 0 < (al + kap * t1) + kap * y1 := by linarith [show (al + kap * t1) + kap * y1 = al + kap * (y1 + t1) by ring]
    have hd2' : 0 < (al + kap * t1) + kap * y2 := by linarith [show (al + kap * t1) + kap * y2 = al + kap * (y2 + t1) by ring]
    refine rat_quad_mono (le_of_lt hkap) (by linarith) hy12 hd1' hd2' ?_
    have hk1 : kap * (3 * A) ≤ kap * t1 := mul_le_mul_of_nonneg_left ht1 (le_of_lt hkap)
    have hk2 : kap * y2 ≤ kap * B := mul_le_mul_of_nonneg_left hy2 (le_of_lt hkap)
    have hk3 : al + kap * (3 * A - B) = al + kap * (3 * A) - kap * B := by ring
    linarith [h_inc_y]
  -- Step 2: `h3(y2, t1) ≤ h3(y2, t2)` via `u = c * t - 1`
  have hstep2 : h3Func la lb y2 t1 ≤ h3Func la lb y2 t2 := by
    change y2 * (c * t1 - 1) / (al + kap * (y2 + t1)) ^ 2 ≤
      y2 * (c * t2 - 1) / (al + kap * (y2 + t2)) ^ 2
    set P := al + kap * y2 + kap / c
    have hc_ne : c ≠ 0 := ne_of_gt hc
    have hid1 : al + kap * (y2 + t1) = P + (kap / c) * (c * t1 - 1) := by
      unfold P; field_simp [hc_ne]; try ring
    have hid2 : al + kap * (y2 + t2) = P + (kap / c) * (c * t2 - 1) := by
      unfold P; field_simp [hc_ne]; try ring
    rw [hid1, hid2, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have hd1 : 0 < P + (kap / c) * (c * t1 - 1) := by rw [← hid1]; exact hd_y2t1
    have hd2 : 0 < P + (kap / c) * (c * t2 - 1) := by rw [← hid2]; exact hd_y2t2
    have hu12 : c * t1 - 1 ≤ c * t2 - 1 := by
      have : c * t1 ≤ c * t2 := mul_le_mul_of_nonneg_left ht12 (le_of_lt hc)
      linarith
    refine rat_quad_mono (div_nonneg (le_of_lt hkap) (le_of_lt hc)) h_pos_t hu12 hd1 hd2 ?_
    have hmul : 0 ≤ c * (P - (kap / c) * (c * t2 - 1)) := by
      have heq : c * (P - (kap / c) * (c * t2 - 1)) =
          c * al + (c * kap) * y2 - (c * kap) * t2 + 2 * kap := by
        unfold P; field_simp [hc_ne]; try ring
      rw [heq]
      have hm1 : (c * kap) * A ≤ (c * kap) * y2 := mul_le_mul_of_nonneg_left (hy1.trans hy12) (le_of_lt hckap)
      have hm2 : (c * kap) * t2 ≤ (c * kap) * (3 * B) := mul_le_mul_of_nonneg_left ht2 (le_of_lt hckap)
      linarith [h_inc_t]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hmul hc)
  exact hstep1.trans hstep2

/-- **Corner Monotonicity of `h₂(y, t)`**: Increasing in `y ∈ [A, B]` and decreasing in `t ∈ [2A, 2B]`. -/
theorem h2Func_mono_anti_box {la lb A B y1 y2 t1 t2 : ℝ}
    (hla1 : 1 < la) (hlb2 : lb < 2) (hlalb : la ≤ lb) (hA : 0 < A)
    (hy1 : A ≤ y1) (hy12 : y1 ≤ y2) (hy2 : y2 ≤ B)
    (ht1 : 2 * A ≤ t2) (ht21 : t2 ≤ t1) (_ht2 : t1 ≤ 2 * B)
    (hkap : 0 < 1 - (1 / (2 - lb)) * (lb - la))
    (h_inc_y : 0 < (la - 1) + (1 - (1 / (2 - lb)) * (lb - la)) * (2 * A - B))
    (h_dec_t : (1 / (2 - lb)) * (la - 1) +
        (1 / (2 - lb)) * (1 - (1 / (2 - lb)) * (lb - la)) * B -
        (1 / (2 - lb)) * (1 - (1 / (2 - lb)) * (lb - la)) * (2 * A) -
        2 * (1 - (1 / (2 - lb)) * (lb - la)) -
        2 * (1 - (1 / (2 - lb)) * (lb - la)) * (1 / (2 - lb)) * (lb - 1) < 0) :
    h2Func la lb y1 t1 ≤ h2Func la lb y2 t2 := by
  set c := 1 / (2 - lb)
  set kap := 1 - c * (lb - la)
  set al := la - 1
  have hc : 0 < c := by unfold c; positivity
  have hal : 0 < al := by unfold al; linarith
  have hckap : 0 < c * kap := mul_pos hc hkap
  have hv1_pos : 0 ≤ 1 + c * (lb - 1 + t1) := by
    have : 0 ≤ lb - 1 + t1 := by linarith
    positivity
  have hv2_pos : 0 ≤ 1 + c * (lb - 1 + t2) := by
    have : 0 ≤ lb - 1 + t2 := by linarith
    positivity
  have hd_y1t1 : 0 < al + kap * (y1 + t1) := by
    have : 0 < y1 + t1 := by linarith
    positivity
  have hd_y2t1 : 0 < al + kap * (y2 + t1) := by
    have : 0 < y2 + t1 := by linarith
    positivity
  have hd_y2t2 : 0 < al + kap * (y2 + t2) := by
    have : 0 < y2 + t2 := by linarith
    positivity
  -- Step 1: `h2(y1, t1) ≤ h2(y2, t1)`
  have hstep1 : h2Func la lb y1 t1 ≤ h2Func la lb y2 t1 := by
    change y1 * (1 + c * (lb - 1 + t1)) / (al + kap * (y1 + t1)) ^ 2 ≤
      y2 * (1 + c * (lb - 1 + t1)) / (al + kap * (y2 + t1)) ^ 2
    have hf1 : y1 * (1 + c * (lb - 1 + t1)) / (al + kap * (y1 + t1)) ^ 2 =
        (1 + c * (lb - 1 + t1)) * (y1 / ((al + kap * t1) + kap * y1) ^ 2) := by ring
    have hf2 : y2 * (1 + c * (lb - 1 + t1)) / (al + kap * (y2 + t1)) ^ 2 =
        (1 + c * (lb - 1 + t1)) * (y2 / ((al + kap * t1) + kap * y2) ^ 2) := by ring
    rw [hf1, hf2]
    refine mul_le_mul_of_nonneg_left ?_ hv1_pos
    have hd1' : 0 < (al + kap * t1) + kap * y1 := by linarith [show (al + kap * t1) + kap * y1 = al + kap * (y1 + t1) by ring]
    have hd2' : 0 < (al + kap * t1) + kap * y2 := by linarith [show (al + kap * t1) + kap * y2 = al + kap * (y2 + t1) by ring]
    refine rat_quad_mono (le_of_lt hkap) (by linarith) hy12 hd1' hd2' ?_
    have hk1 : kap * (2 * A) ≤ kap * t1 := mul_le_mul_of_nonneg_left (ht1.trans ht21) (le_of_lt hkap)
    have hk2 : kap * y2 ≤ kap * B := mul_le_mul_of_nonneg_left hy2 (le_of_lt hkap)
    have hk3 : al + kap * (2 * A - B) = al + kap * (2 * A) - kap * B := by ring
    linarith [h_inc_y]
  -- Step 2: `h2(y2, t1) ≤ h2(y2, t2)` (since `t2 ≤ t1`) via `v = 1 + c * (lb - 1 + t)`
  have hstep2 : h2Func la lb y2 t1 ≤ h2Func la lb y2 t2 := by
    change y2 * (1 + c * (lb - 1 + t1)) / (al + kap * (y2 + t1)) ^ 2 ≤
      y2 * (1 + c * (lb - 1 + t2)) / (al + kap * (y2 + t2)) ^ 2
    set Q := al + kap * y2 - kap * (lb - 1) - kap / c
    have hc_ne : c ≠ 0 := ne_of_gt hc
    have hid1 : al + kap * (y2 + t1) = Q + (kap / c) * (1 + c * (lb - 1 + t1)) := by
      unfold Q; field_simp [hc_ne]; try ring
    have hid2 : al + kap * (y2 + t2) = Q + (kap / c) * (1 + c * (lb - 1 + t2)) := by
      unfold Q; field_simp [hc_ne]; try ring
    rw [hid1, hid2, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have hd1 : 0 < Q + (kap / c) * (1 + c * (lb - 1 + t1)) := by rw [← hid1]; exact hd_y2t1
    have hd2 : 0 < Q + (kap / c) * (1 + c * (lb - 1 + t2)) := by rw [← hid2]; exact hd_y2t2
    have hv21 : 1 + c * (lb - 1 + t2) ≤ 1 + c * (lb - 1 + t1) := by
      have : c * (lb - 1 + t2) ≤ c * (lb - 1 + t1) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hc)
      linarith
    refine rat_quad_anti (div_nonneg (le_of_lt hkap) (le_of_lt hc)) hv2_pos hv21 hd2 hd1 ?_
    have hmul : c * (Q - (kap / c) * (1 + c * (lb - 1 + t2))) ≤ 0 := by
      have heq : c * (Q - (kap / c) * (1 + c * (lb - 1 + t2))) =
          c * al + (c * kap) * y2 - (c * kap) * t2 - 2 * kap - 2 * kap * c * (lb - 1) := by
        unfold Q; field_simp [hc_ne]; try ring
      rw [heq]
      have hm1 : (c * kap) * y2 ≤ (c * kap) * B := mul_le_mul_of_nonneg_left hy2 (le_of_lt hckap)
      have hm2 : (c * kap) * (2 * A) ≤ (c * kap) * t2 := mul_le_mul_of_nonneg_left ht1 (le_of_lt hckap)
      linarith [h_dec_t]
    have hle0 : Q - (kap / c) * (1 + c * (lb - 1 + t2)) ≤ 0 := by
      by_contra hgt
      linarith [mul_pos hc (not_le.mp hgt)]
    linarith
  exact hstep1.trans hstep2

/-- **Gluing Lemma (`Proof of Theorem 1`)**: If `v` is strictly decreasing on `[a, b]` and on `[b, c]`
    (with `a ≤ b ≤ c`), then `v` is strictly decreasing on `[a, c]`. -/
theorem strictAntiOn_Icc_glue {v : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : StrictAntiOn v (Set.Icc a b)) (h2 : StrictAntiOn v (Set.Icc b c)) :
    StrictAntiOn v (Set.Icc a c) := by
  intro x hx y hy hxy
  rcases le_or_gt y b with hyb | hby
  · exact h1 ⟨hx.1, hyb.trans' (le_of_lt hxy)⟩ ⟨hx.1.trans (le_of_lt hxy), hyb⟩ hxy
  · rcases le_or_gt b x with hbx | hxb
    · exact h2 ⟨hbx, hx.2⟩ ⟨hbx.trans (le_of_lt hxy), hy.2⟩ hxy
    · have h1' : v b < v x := h1 ⟨hx.1, le_of_lt hxb⟩ ⟨hab, le_rfl⟩ hxb
      have h2' : v y < v b := h2 ⟨le_rfl, hbc⟩ ⟨le_of_lt hby, hy.2⟩ hby
      exact lt_trans h2' h1'

/-- Recursive nondecreasing chain predicate on `x0 :: pts`. -/
def IsSortedChain : ℝ → List ℝ → Prop
  | _, [] => True
  | x, y :: rest => x ≤ y ∧ IsSortedChain y rest

lemma isSortedChain_le_getLast :
    ∀ (rest : List ℝ) (y : ℝ),
      IsSortedChain y rest → y ≤ (y :: rest).getLast (List.cons_ne_nil _ _)
  | [], y, _ => by simp
  | z :: zs, y, ⟨hyz, hzs⟩ => le_trans hyz (isSortedChain_le_getLast zs z hzs)

/-- Inductive gluing of `StrictAntiOn v` across a list of contiguous closed intervals. -/
theorem strictAntiOn_chain {v : ℝ → ℝ} :
    ∀ (pts : List ℝ) (x0 : ℝ),
      IsSortedChain x0 pts →
      (∀ p ∈ List.zip (x0 :: pts) pts, StrictAntiOn v (Set.Icc p.1 p.2)) →
      StrictAntiOn v (Set.Icc x0 ((x0 :: pts).getLast (List.cons_ne_nil _ _)))
  | [], x0, _, _ => by
      intro a ha b hb hab
      simp only [List.getLast_singleton, Set.mem_Icc] at ha hb
      linarith
  | y :: rest, x0, ⟨hxy, hrest⟩, hall => by
      have hfirst : StrictAntiOn v (Set.Icc x0 y) :=
        hall (x0, y) (by simp)
      have htail : StrictAntiOn v (Set.Icc y ((y :: rest).getLast (List.cons_ne_nil _ _))) :=
        strictAntiOn_chain rest y hrest (fun p hp => hall p (by simp [hp]))
      have hlast_ge : y ≤ (y :: rest).getLast (List.cons_ne_nil _ _) :=
        isSortedChain_le_getLast rest y hrest
      simpa using strictAntiOn_Icc_glue hxy hlast_ge hfirst htail

end GWSpeedCertificate
