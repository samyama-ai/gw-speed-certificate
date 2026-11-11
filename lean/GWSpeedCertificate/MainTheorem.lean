import GWSpeedCertificate.Certs.AllCells

/-!
# Main Theorem: Speed Monotonicity of Biased Random Walk on `[0, 1.755]` (`MainTheorem.lean`)

Combines:
- **Layer A (`GWSpeedModel`)**: Explicit literature hypotheses packaging
  1. Aïdékon's speed formula for biased random walk on a Galton–Watson tree
     (E. Aïdékon, *Probab. Theory Relat. Fields* 159 (2014), Theorem 1.1; specialized to
     `Offspring(p₂ = p₃ = 1/2)` in Section 3, Eq. (1)),
  2. the Galton–Watson `Offspring(p₂ = p₃ = 1/2)` root-splitting law (`IsGWTree23`), and
  3. Song–Wang–Xiang's analytical speed monotonicity theorem on `[0, 1.17]`
     (H. Song, H. Wang, and K. Xiang, *J. Appl. Probab.* 62 (2025), Theorem 1.2).
- **Layer B (`TreeConductance`, `Criterion`, `StochasticOrder`)**: Machine-checked analytical
  reductions (Lemmas 3.1, 3.2, 4.1, 4.2, 4.3, 5.2, and 6.1) with zero `sorry`.
- **Layer C (`CellVerifier`, `Certs.AllCells`)**: Exact integer stochastic-order and
  difference-quotient verification across 34 contiguous rational cells covering `[1.17, 1.755]`
  (`117/100` to `351/200`) via pure Lean 4 kernel reduction (`Eq.refl true`).
-/

namespace GWSpeedCertificate

open MeasureTheory

/-- **Layer A Model (`GWSpeedModel`)**: Packages the Galton–Watson `Offspring(p₂ = p₃ = 1/2)`
    tree measure `mu`, the asymptotic speed function `v : ℝ → ℝ`, Aïdékon's speed formula on
    `λ ∈ (0, 2)`, and Song–Wang–Xiang's monotonicity result on `[0, 117/100]`. -/
structure GWSpeedModel where
  /-- Asymptotic speed `v(λ)` of the `λ`-biased random walk on a `GW(p₂ = p₃ = 1/2)` tree. -/
  v : ℝ → ℝ
  /-- Galton–Watson `Offspring(p₂ = p₃ = 1/2)` probability measure on `InfTree23`. -/
  mu : Measure InfTree23
  /-- Law of `mu` satisfies the `GW(p₂ = p₃ = 1/2)` root-splitting isomorphism (`IsGWTree23`). -/
  instGW : IsGWTree23 mu
  /-- **Aïdékon's Speed Formula** (Aïdékon, *Probab. Theory Relat. Fields* 159 (2014), Theorem 1.1;
      specialized to `p₂ = p₃ = 1/2` in Eq. (1)):
      for every `λ ∈ (0, 2)`,
      `v(λ) = (½ (2 E₂(λ) + 3 E₃(λ)) - λ · ½ (E₂(λ) + E₃(λ))) / (½ (2 E₂(λ) + 3 E₃(λ)) + λ · ½ (E₂(λ) + E₃(λ)))`. -/
  aidekon_speed : ∀ lam ∈ Set.Ioo (0 : ℝ) 2,
    v lam =
      ((1 / 2 : ℝ) * (2 * E2Expect mu lam + 3 * E3Expect mu lam) -
        lam * ((1 / 2 : ℝ) * (E2Expect mu lam + E3Expect mu lam))) /
      ((1 / 2 : ℝ) * (2 * E2Expect mu lam + 3 * E3Expect mu lam) +
        lam * ((1 / 2 : ℝ) * (E2Expect mu lam + E3Expect mu lam)))
  /-- **Song–Wang–Xiang Monotonicity on `[0, 1.17]`** (Song, Wang, and Xiang,
      *J. Appl. Probab.* 62 (2025), Theorem 1.2): `v(λ)` is strictly decreasing on `[0, 117/100]`. -/
  swx_zero_to_117 : StrictAntiOn v (Set.Icc (0 : ℝ) (117 / 100 : ℝ))

attribute [instance] GWSpeedModel.instGW

/-- **Lemma 3.1 Specialization (`speed_eq_R_formula`)**: Under Aïdékon's speed formula on
    `Offspring(p₂ = p₃ = 1/2)`, `v(λ) = (R(λ) - λ) / (R(λ) + λ)` for all `λ ∈ (0, 2)`. -/
theorem speed_eq_R_formula (M : GWSpeedModel) {lam : ℝ} (hlam : lam ∈ Set.Ioo (0 : ℝ) 2) :
    M.v lam = (RFunc M.mu lam - lam) / (RFunc M.mu lam + lam) := by
  rw [M.aidekon_speed lam hlam]
  set E2 : ℝ := E2Expect M.mu lam
  set E3 : ℝ := E3Expect M.mu lam
  have hM_pos : 0 < E2 + E3 :=
    add_pos (E2Expect_pos (mu := M.mu) hlam.1 hlam.2) (E3Expect_pos (mu := M.mu) hlam.1 hlam.2)
  have hhalf :
      ((1 / 2 : ℝ) * (2 * E2 + 3 * E3) - lam * ((1 / 2 : ℝ) * (E2 + E3))) /
        ((1 / 2 : ℝ) * (2 * E2 + 3 * E3) + lam * ((1 / 2 : ℝ) * (E2 + E3))) =
      ((2 * E2 + 3 * E3) - lam * (E2 + E3)) /
        ((2 * E2 + 3 * E3) + lam * (E2 + E3)) := by
    have hnum : (1 / 2 : ℝ) * (2 * E2 + 3 * E3) - lam * ((1 / 2 : ℝ) * (E2 + E3)) =
        (1 / 2 : ℝ) * ((2 * E2 + 3 * E3) - lam * (E2 + E3)) := by ring
    have hden : (1 / 2 : ℝ) * (2 * E2 + 3 * E3) + lam * ((1 / 2 : ℝ) * (E2 + E3)) =
        (1 / 2 : ℝ) * ((2 * E2 + 3 * E3) + lam * (E2 + E3)) := by ring
    rw [hnum, hden, mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [hhalf, lemma_3_1_speed_formula (ne_of_gt hM_pos)]
  rfl

/-- **Certified Extension Theorem (`speed_strictAntiOn_117_to_1755`)**:
    The asymptotic speed `v(λ)` is strictly decreasing across the certified interval
    `[1.17, 1.755]` (`[117/100, 351/200]`). -/
theorem speed_strictAntiOn_117_to_1755 (M : GWSpeedModel) :
    StrictAntiOn M.v (Set.Icc (117 / 100 : ℝ) (351 / 200 : ℝ)) := by
  have hR_anti : StrictAntiOn (fun l => (RFunc M.mu l - l) / (RFunc M.mu l + l))
      (Set.Icc (117 / 100 : ℝ) (351 / 200 : ℝ)) := by
    rw [lemma_3_1_strictAntiOn
      (fun l hl => by linarith [hl.1])
      (fun l hl => by
        have hl0 : 0 < l := by linarith [hl.1]
        have hl2 : l < 2 := by linarith [hl.2]
        linarith [(RFunc_bounds (mu := M.mu) hl0 hl2).1])]
    exact Certs.r_div_lam_strictAntiOn_117_to_1755 (mu := M.mu)
  intro l1 hl1 l2 hl2 hlt
  have h1 : l1 ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hl1.1], by linarith [hl1.2]⟩
  have h2 : l2 ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hl2.1], by linarith [hl2.2]⟩
  rw [speed_eq_R_formula M h2, speed_eq_R_formula M h1]
  exact hR_anti hl1 hl2 hlt

/-- **Theorem 1.1 (`speed_strictAntiOn_zero_to_1755`)**:
    For the biased random walk `BRW_λ` on a Galton–Watson tree with offspring distribution
    `p₂ = p₃ = 1/2`, the asymptotic speed `v(λ)` is strictly decreasing on `[0, 1.755]`
    (`[0, 351/200]`). -/
theorem speed_strictAntiOn_zero_to_1755 (M : GWSpeedModel) :
    StrictAntiOn M.v (Set.Icc (0 : ℝ) (351 / 200 : ℝ)) :=
  strictAntiOn_Icc_glue (by norm_num) (by norm_num)
    M.swx_zero_to_117 (speed_strictAntiOn_117_to_1755 M)

end GWSpeedCertificate
