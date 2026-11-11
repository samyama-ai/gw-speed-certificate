import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Section 4: Finite-Depth & Infinite-Tree Conductance Bounds (`TreeConductance.lean`)

Formalizes leafless `{2,3}`-trees (`InfTree23`), the finite-depth conductance recursion
`betaAtInit` / `betaAt`, the infinite-depth conductance `beta`, and proves from first principles:
- **Lemma 4.1 (`lemma_4_1_support`)**: `1 - λ/2 ≤ β(λ) ≤ 1 - λ/3` for `0 < λ < 2`.
- **Lemma 4.2 (`lemma_4_2_mono`)**: Pathwise monotonicity `β(λ₂) ≤ β(λ₁)` for `0 < λ₁ ≤ λ₂ < 2`.
- **Lemma 4.3 (`lemma_4_3_lipschitz`)**: Pathwise Lipschitz bound
  `0 ≤ β(λ₁) - β(λ₂) ≤ (λ₂ - λ₁) * β(λ₁) / (2 - λ₂)` for `0 < λ₁ < λ₂ < 2` (proved directly by
  algebraic finite-difference induction on tree depth, avoiding differentiation/integration).
- **Contraction Uniqueness (`betaAtInit_uniform_approx`)**: Uniform `(λ/2)^n` convergence of
  depth-`n` conductances started from any constant in `[1 - λ/2, 1 - λ/3]` to `β(λ)`.
-/

namespace GWSpeedCertificate

/-- An infinite leafless rooted tree where every vertex `v : List (Fin 3)` has either
    2 children (`T v = true`, children `0, 1`) or 3 children (`T v = false`, children `0, 1, 2`). -/
abbrev InfTree23 : Type := List (Fin 3) → Bool

/-- Subtree rooted at vertex `p`. -/
def shiftTree (T : InfTree23) (p : List (Fin 3)) : InfTree23 :=
  fun w => T (p ++ w)

@[simp]
lemma shiftTree_nil (T : InfTree23) : shiftTree T [] = T := by
  funext w; simp [shiftTree]

/-- One-step rational conductance map `g_λ(S) = S / (λ + S)`. -/
noncomputable def condStep (lam s : ℝ) : ℝ := s / (lam + s)

/-- Depth-`n` conductance at vertex `v` on tree `T` with bias `lam` and depth-`n` boundary `init`. -/
noncomputable def betaAtInit (T : InfTree23) (lam : ℝ) (init : List (Fin 3) → ℝ) :
    ℕ → List (Fin 3) → ℝ
  | 0, v => init v
  | n + 1, v =>
      let b0 := betaAtInit T lam init n (v ++ [0])
      let b1 := betaAtInit T lam init n (v ++ [1])
      let s := if T v then b0 + b1 else b0 + b1 + betaAtInit T lam init n (v ++ [2])
      condStep lam s

/-- Standard depth-`n` conductance started from constant boundary `1` (Aïdékon 2014, §4). -/
noncomputable def betaAt (T : InfTree23) (lam : ℝ) (n : ℕ) (v : List (Fin 3)) : ℝ :=
  betaAtInit T lam (fun _ => 1) n v

/-- Infinite-tree root conductance `β(T, λ) = inf_n β_n(T, λ)`. -/
noncomputable def beta (T : InfTree23) (lam : ℝ) : ℝ :=
  ⨅ n : ℕ, betaAt T lam n []

lemma condStep_mono {lam s1 s2 : ℝ} (hlam : 0 < lam) (hs1 : 0 ≤ s1) (hle : s1 ≤ s2) :
    condStep lam s1 ≤ condStep lam s2 := by
  unfold condStep
  have hd1 : 0 < lam + s1 := by linarith
  have hd2 : 0 < lam + s2 := by linarith
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith

lemma condStep_anti_lam {lam1 lam2 s : ℝ} (hlam1 : 0 < lam1) (hl : lam1 ≤ lam2) (hs : 0 ≤ s) :
    condStep lam2 s ≤ condStep lam1 s := by
  unfold condStep
  have hd1 : 0 < lam1 + s := by linarith
  have hd2 : 0 < lam2 + s := by linarith
  rw [div_le_div_iff₀ hd2 hd1]
  nlinarith

lemma betaAtInit_shift (T : InfTree23) (lam : ℝ) (init : List (Fin 3) → ℝ) (n : ℕ)
    (p v : List (Fin 3)) :
    betaAtInit (shiftTree T p) lam (fun w => init (p ++ w)) n v =
      betaAtInit T lam init n (p ++ v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      dsimp only [betaAtInit]
      rw [ih (v ++ [0]), ih (v ++ [1]), ih (v ++ [2])]
      have hsh : shiftTree T p v = T (p ++ v) := rfl
      rw [hsh]
      cases T (p ++ v) <;> simp [List.append_assoc]

lemma betaAtInit_comp (T : InfTree23) (lam : ℝ) (init : List (Fin 3) → ℝ) (n m : ℕ)
    (v : List (Fin 3)) :
    betaAtInit T lam init (n + m) v =
      betaAtInit T lam (fun w => betaAtInit T lam init m w) n v := by
  induction n generalizing v with
  | zero => simp [betaAtInit]
  | succ n ih =>
      simp only [Nat.succ_add, betaAtInit]
      rw [ih (v ++ [0]), ih (v ++ [1]), ih (v ++ [2])]

lemma betaAtInit_mono_init (T : InfTree23) {lam : ℝ} (hlam : 0 < lam)
    {init1 init2 : List (Fin 3) → ℝ}
    (hpos : ∀ w, 0 ≤ init1 w) (hle : ∀ w, init1 w ≤ init2 w) :
    ∀ n v, 0 ≤ betaAtInit T lam init1 n v ∧ betaAtInit T lam init1 n v ≤ betaAtInit T lam init2 n v := by
  intro n
  induction n with
  | zero => intro v; exact ⟨hpos v, hle v⟩
  | succ n ih =>
      intro v
      obtain ⟨hp0, hl0⟩ := ih (v ++ [0])
      obtain ⟨hp1, hl1⟩ := ih (v ++ [1])
      obtain ⟨hp2, hl2⟩ := ih (v ++ [2])
      simp only [betaAtInit]
      split_ifs with hT
      · refine ⟨?_, condStep_mono hlam (by linarith) (by linarith)⟩
        unfold condStep
        exact div_nonneg (by linarith) (by linarith)
      · refine ⟨?_, condStep_mono hlam (by linarith) (by linarith)⟩
        unfold condStep
        exact div_nonneg (by linarith) (by linarith)

/-- Lower bound `1 - λ/2` and upper bound `1` for `betaAt` at every depth `n`. -/
lemma betaAt_bounds (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) :
    ∀ n v, 1 - lam / 2 ≤ betaAt T lam n v ∧ betaAt T lam n v ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro v
      simp only [betaAt, betaAtInit]
      constructor <;> linarith
  | succ n ih =>
      intro v
      obtain ⟨h0l, h0u⟩ := ih (v ++ [0])
      obtain ⟨h1l, h1u⟩ := ih (v ++ [1])
      obtain ⟨h2l, h2u⟩ := ih (v ++ [2])
      simp only [betaAt, betaAtInit] at *
      split_ifs with hT
      · have hs_lo : 2 - lam ≤ betaAtInit T lam (fun _ => 1) n (v ++ [0]) +
            betaAtInit T lam (fun _ => 1) n (v ++ [1]) := by linarith
        have hstep_lo : condStep lam (2 - lam) ≤
            condStep lam (betaAtInit T lam (fun _ => 1) n (v ++ [0]) +
              betaAtInit T lam (fun _ => 1) n (v ++ [1])) :=
          condStep_mono hlam0 (by linarith) hs_lo
        have hfix2 : condStep lam (2 - lam) = 1 - lam / 2 := by
          unfold condStep; ring
        constructor
        · linarith
        · unfold condStep
          rw [div_le_one (by linarith)]
          linarith
      · have hs_lo : 2 - lam ≤ betaAtInit T lam (fun _ => 1) n (v ++ [0]) +
            betaAtInit T lam (fun _ => 1) n (v ++ [1]) +
            betaAtInit T lam (fun _ => 1) n (v ++ [2]) := by linarith
        have hstep_lo : condStep lam (2 - lam) ≤
            condStep lam (betaAtInit T lam (fun _ => 1) n (v ++ [0]) +
              betaAtInit T lam (fun _ => 1) n (v ++ [1]) +
              betaAtInit T lam (fun _ => 1) n (v ++ [2])) :=
          condStep_mono hlam0 (by linarith) hs_lo
        have hfix2 : condStep lam (2 - lam) = 1 - lam / 2 := by
          unfold condStep; ring
        constructor
        · linarith
        · unfold condStep
          rw [div_le_one (by linarith)]
          linarith

/-- `betaAt T lam n v` is antitone (nonincreasing) in depth `n`. -/
lemma betaAt_antitone (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) (v : List (Fin 3)) :
    Antitone (fun n => betaAt T lam n v) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  unfold betaAt
  rw [betaAtInit_comp T lam (fun _ => 1) n 1 v]
  refine (betaAtInit_mono_init T hlam0 (fun w => ?_) (fun w => ?_) n v).2
  · have hb := (betaAt_bounds T hlam0 hlam2 1 w).1
    unfold betaAt at hb
    linarith
  · exact (betaAt_bounds T hlam0 hlam2 1 w).2

lemma betaAt_bddBelow (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) (v : List (Fin 3)) :
    BddBelow (Set.range (fun n => betaAt T lam n v)) := by
  refine ⟨1 - lam / 2, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (betaAt_bounds T hlam0 hlam2 n v).1

lemma tendsto_betaAt (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) :
    Filter.Tendsto (fun n => betaAt T lam n []) Filter.atTop (nhds (beta T lam)) :=
  tendsto_atTop_ciInf (betaAt_antitone T hlam0 hlam2 []) (betaAt_bddBelow T hlam0 hlam2 [])

/-- Closed-form ternary tree depth-`n` sequence `y_n = (1 - q) / (1 - q^(n+1))` with `q = λ/3`. -/
noncomputable def ternarySeq (lam : ℝ) (n : ℕ) : ℝ :=
  (1 - lam / 3) / (1 - (lam / 3) ^ (n + 1))

lemma ternarySeq_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) (n : ℕ) :
    0 < ternarySeq lam n := by
  unfold ternarySeq
  have hq0 : 0 < lam / 3 := by linarith
  have hq1 : lam / 3 < 1 := by linarith
  have hpow : (lam / 3) ^ (n + 1) < 1 := pow_lt_one₀ (le_of_lt hq0) hq1 (Nat.succ_ne_zero n)
  exact div_pos (by linarith) (by linarith)

lemma ternarySeq_step {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) (n : ℕ) :
    condStep lam (3 * ternarySeq lam n) = ternarySeq lam (n + 1) := by
  unfold condStep ternarySeq
  have hq0 : 0 < lam / 3 := by linarith
  have hq1 : lam / 3 < 1 := by linarith
  have hd1 : 1 - (lam / 3) ^ (n + 1) ≠ 0 := by
    have hp : (lam / 3) ^ (n + 1) < 1 := pow_lt_one₀ (le_of_lt hq0) hq1 (Nat.succ_ne_zero n)
    linarith
  have hd2 : 1 - (lam / 3) ^ (n + 2) ≠ 0 := by
    have hp : (lam / 3) ^ (n + 2) < 1 := pow_lt_one₀ (le_of_lt hq0) hq1 (by omega)
    linarith
  have hden : lam + 3 * ((1 - lam / 3) / (1 - (lam / 3) ^ (n + 1))) ≠ 0 := by
    have hp := ternarySeq_pos hlam0 hlam2 n
    unfold ternarySeq at hp
    linarith
  have hp2 : (lam / 3) ^ (n + 2) = (lam / 3) ^ (n + 1) * (lam / 3) := pow_succ (lam / 3) (n + 1)
  rw [hp2] at hd2 ⊢
  field_simp [hd1, hd2, hden]
  ring

lemma betaAt_le_ternarySeq (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) :
    ∀ n v, betaAt T lam n v ≤ ternarySeq lam n := by
  intro n
  induction n with
  | zero =>
      intro v
      unfold betaAt betaAtInit ternarySeq
      have hne : (1 : ℝ) - lam / 3 ≠ 0 := by linarith
      have hp1 : (lam / 3) ^ (0 + 1) = lam / 3 := by ring
      rw [hp1, div_self hne]
  | succ n ih =>
      intro v
      have h0 := ih (v ++ [0])
      have h1 := ih (v ++ [1])
      have h2 := ih (v ++ [2])
      have hb0 : 0 ≤ betaAt T lam n (v ++ [0]) := by
        have := (betaAt_bounds T hlam0 hlam2 n (v ++ [0])).1; linarith
      have hb1 : 0 ≤ betaAt T lam n (v ++ [1]) := by
        have := (betaAt_bounds T hlam0 hlam2 n (v ++ [1])).1; linarith
      have hb2 : 0 ≤ betaAt T lam n (v ++ [2]) := by
        have := (betaAt_bounds T hlam0 hlam2 n (v ++ [2])).1; linarith
      have htpos := le_of_lt (ternarySeq_pos hlam0 hlam2 n)
      simp only [betaAt, betaAtInit] at *
      rw [← ternarySeq_step hlam0 hlam2 n]
      split_ifs with hT
      · exact condStep_mono hlam0 (by linarith) (by linarith)
      · exact condStep_mono hlam0 (by linarith) (by linarith)

/-- **Lemma 4.1 (`lem:support`)**: For `0 < λ < 2`, `1 - λ/2 ≤ β(T, λ) ≤ 1 - λ/3` on every `{2,3}` tree. -/
theorem lemma_4_1_support (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) :
    1 - lam / 2 ≤ beta T lam ∧ beta T lam ≤ 1 - lam / 3 := by
  constructor
  · exact le_ciInf (fun n => (betaAt_bounds T hlam0 hlam2 n []).1)
  · have hq0 : 0 ≤ lam / 3 := by linarith
    have hq1 : lam / 3 < 1 := by linarith
    have hpow : Filter.Tendsto (fun n : ℕ => (lam / 3) ^ (n + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp (Filter.tendsto_add_atTop_nat 1)
    have hsub : Filter.Tendsto (fun n : ℕ => 1 - (lam / 3) ^ (n + 1)) Filter.atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hpow
    have htern : Filter.Tendsto (ternarySeq lam) Filter.atTop (nhds ((1 - lam / 3) / (1 - 0))) := by
      unfold ternarySeq
      exact Filter.Tendsto.div tendsto_const_nhds hsub (by norm_num)
    have htern' : Filter.Tendsto (ternarySeq lam) Filter.atTop (nhds (1 - lam / 3)) := by
      simpa using htern
    exact le_of_tendsto_of_tendsto (tendsto_betaAt T hlam0 hlam2) htern'
      (Filter.Eventually.of_forall (fun n => betaAt_le_ternarySeq T hlam0 hlam2 n []))

lemma betaAt_anti_lam (T : InfTree23) {lam1 lam2 : ℝ}
    (hlam1 : 0 < lam1) (hle : lam1 ≤ lam2) (hlam2 : lam2 < 2) :
    ∀ n v, betaAt T lam2 n v ≤ betaAt T lam1 n v := by
  intro n
  induction n with
  | zero => intro v; simp [betaAt, betaAtInit]
  | succ n ih =>
      intro v
      have h0 := ih (v ++ [0])
      have h1 := ih (v ++ [1])
      have h2 := ih (v ++ [2])
      have p0 : 0 ≤ betaAt T lam2 n (v ++ [0]) := by
        have := (betaAt_bounds T (by linarith) hlam2 n (v ++ [0])).1; linarith
      have p1 : 0 ≤ betaAt T lam2 n (v ++ [1]) := by
        have := (betaAt_bounds T (by linarith) hlam2 n (v ++ [1])).1; linarith
      have p2 : 0 ≤ betaAt T lam2 n (v ++ [2]) := by
        have := (betaAt_bounds T (by linarith) hlam2 n (v ++ [2])).1; linarith
      simp only [betaAt, betaAtInit] at *
      split_ifs with hT
      · exact (condStep_anti_lam hlam1 hle (by linarith)).trans
          (condStep_mono hlam1 (by linarith) (by linarith))
      · exact (condStep_anti_lam hlam1 hle (by linarith)).trans
          (condStep_mono hlam1 (by linarith) (by linarith))

/-- **Lemma 4.2 (`lem:mono`)**: On every `{2,3}` tree, `λ ↦ β(T, λ)` is nonincreasing on `(0, 2)`. -/
theorem lemma_4_2_mono (T : InfTree23) {lam1 lam2 : ℝ}
    (hlam1 : 0 < lam1) (hle : lam1 ≤ lam2) (hlam2 : lam2 < 2) :
    beta T lam2 ≤ beta T lam1 := by
  exact le_of_tendsto_of_tendsto (tendsto_betaAt T (by linarith) hlam2)
    (tendsto_betaAt T hlam1 (by linarith))
    (Filter.Eventually.of_forall (fun n => betaAt_anti_lam T hlam1 hle hlam2 n []))

/-- Core algebraic step for Lemma 4.3: one-step Lipschitz preservation without calculus. -/
lemma condStep_lipschitz_step {lam1 lam2 s1 s2 : ℝ}
    (hlam1 : 0 < lam1) (hlt : lam1 < lam2) (hlam2 : lam2 < 2)
    (hs1 : 0 ≤ s1) (hs2_lo : 2 - lam2 ≤ s2)
    (hdiff : s1 - s2 ≤ (lam2 - lam1) / (2 - lam2) * s1) :
    condStep lam1 s1 - condStep lam2 s2 ≤
      (lam2 - lam1) / (2 - lam2) * condStep lam1 s1 := by
  unfold condStep
  have hd1 : 0 < lam1 + s1 := by linarith
  have hd2 : 0 < lam2 + s2 := by linarith
  have hc : 0 < 2 - lam2 := by linarith
  have hden2 : 2 ≤ lam2 + s2 := by linarith
  have h_ident : s1 / (lam1 + s1) - s2 / (lam2 + s2) =
      (s1 * (lam2 - lam1) + lam1 * (s1 - s2)) / ((lam1 + s1) * (lam2 + s2)) := by
    field_simp [ne_of_gt hd1, ne_of_gt hd2]
    ring
  rw [h_ident]
  have hnum_le : s1 * (lam2 - lam1) + lam1 * (s1 - s2) ≤
      s1 * (lam2 - lam1) * (1 + lam2 / (2 - lam2)) := by
    have h1 : lam1 * (s1 - s2) ≤ lam1 * ((lam2 - lam1) / (2 - lam2) * s1) :=
      mul_le_mul_of_nonneg_left hdiff (le_of_lt hlam1)
    have hnonneg : 0 ≤ (lam2 - lam1) / (2 - lam2) * s1 :=
      mul_nonneg (div_nonneg (by linarith) (le_of_lt hc)) hs1
    have h2 : lam1 * ((lam2 - lam1) / (2 - lam2) * s1) ≤
        lam2 * ((lam2 - lam1) / (2 - lam2) * s1) :=
      mul_le_mul_of_nonneg_right (le_of_lt hlt) hnonneg
    have h3 : s1 * (lam2 - lam1) + lam2 * ((lam2 - lam1) / (2 - lam2) * s1) =
        s1 * (lam2 - lam1) * (1 + lam2 / (2 - lam2)) := by ring
    linarith
  have h1plus : 1 + lam2 / (2 - lam2) = 2 / (2 - lam2) := by
    field_simp [ne_of_gt hc]; ring
  rw [h1plus] at hnum_le
  calc (s1 * (lam2 - lam1) + lam1 * (s1 - s2)) / ((lam1 + s1) * (lam2 + s2))
      ≤ (s1 * (lam2 - lam1) * (2 / (2 - lam2))) / ((lam1 + s1) * (lam2 + s2)) := by
          exact div_le_div_of_nonneg_right hnum_le (by positivity)
    _ ≤ (s1 * (lam2 - lam1) * (2 / (2 - lam2))) / ((lam1 + s1) * 2) := by
          have hnum_nonneg : 0 ≤ s1 * (lam2 - lam1) * (2 / (2 - lam2)) := by
            positivity
          exact div_le_div_of_nonneg_left hnum_nonneg (by positivity)
            (mul_le_mul_of_nonneg_left hden2 (le_of_lt hd1))
    _ = (lam2 - lam1) / (2 - lam2) * (s1 / (lam1 + s1)) := by
          field_simp [ne_of_gt hd1, ne_of_gt hc]

lemma betaAt_lipschitz (T : InfTree23) {lam1 lam2 : ℝ}
    (hlam1 : 0 < lam1) (hlt : lam1 < lam2) (hlam2 : lam2 < 2) :
    ∀ n v, betaAt T lam1 n v - betaAt T lam2 n v ≤
      (lam2 - lam1) / (2 - lam2) * betaAt T lam1 n v := by
  intro n
  induction n with
  | zero =>
      intro v
      simp only [betaAt, betaAtInit, sub_self, mul_one]
      exact div_nonneg (by linarith) (by linarith)
  | succ n ih =>
      intro v
      have h0 := ih (v ++ [0])
      have h1 := ih (v ++ [1])
      have h2 := ih (v ++ [2])
      have b1_0 := (betaAt_bounds T hlam1 (by linarith) n (v ++ [0])).1
      have b1_1 := (betaAt_bounds T hlam1 (by linarith) n (v ++ [1])).1
      have b1_2 := (betaAt_bounds T hlam1 (by linarith) n (v ++ [2])).1
      have b2_0 := (betaAt_bounds T (by linarith) hlam2 n (v ++ [0])).1
      have b2_1 := (betaAt_bounds T (by linarith) hlam2 n (v ++ [1])).1
      have b2_2 := (betaAt_bounds T (by linarith) hlam2 n (v ++ [2])).1
      simp only [betaAt, betaAtInit] at *
      have h_add2 : (betaAtInit T lam1 (fun _ => 1) n (v ++ [0]) + betaAtInit T lam1 (fun _ => 1) n (v ++ [1])) -
          (betaAtInit T lam2 (fun _ => 1) n (v ++ [0]) + betaAtInit T lam2 (fun _ => 1) n (v ++ [1])) ≤
          (lam2 - lam1) / (2 - lam2) * (betaAtInit T lam1 (fun _ => 1) n (v ++ [0]) + betaAtInit T lam1 (fun _ => 1) n (v ++ [1])) := by
        linarith
      have h_add3 : (betaAtInit T lam1 (fun _ => 1) n (v ++ [0]) + betaAtInit T lam1 (fun _ => 1) n (v ++ [1]) + betaAtInit T lam1 (fun _ => 1) n (v ++ [2])) -
          (betaAtInit T lam2 (fun _ => 1) n (v ++ [0]) + betaAtInit T lam2 (fun _ => 1) n (v ++ [1]) + betaAtInit T lam2 (fun _ => 1) n (v ++ [2])) ≤
          (lam2 - lam1) / (2 - lam2) * (betaAtInit T lam1 (fun _ => 1) n (v ++ [0]) + betaAtInit T lam1 (fun _ => 1) n (v ++ [1]) + betaAtInit T lam1 (fun _ => 1) n (v ++ [2])) := by
        linarith
      split_ifs with hT
      · exact condStep_lipschitz_step hlam1 hlt hlam2 (by linarith) (by linarith) h_add2
      · exact condStep_lipschitz_step hlam1 hlt hlam2 (by linarith) (by linarith) h_add3

/-- **Lemma 4.3 (`lem:lip`)**: Pathwise Lipschitz bound on `β(T, λ)` for `0 < λ₁ < λ₂ < 2`. -/
theorem lemma_4_3_lipschitz (T : InfTree23) {lam1 lam2 : ℝ}
    (hlam1 : 0 < lam1) (hlt : lam1 < lam2) (hlam2 : lam2 < 2) :
    0 ≤ beta T lam1 - beta T lam2 ∧
      beta T lam1 - beta T lam2 ≤ (lam2 - lam1) * beta T lam1 / (2 - lam2) := by
  refine ⟨sub_nonneg.mpr (lemma_4_2_mono T hlam1 (le_of_lt hlt) hlam2), ?_⟩
  have ht1 := tendsto_betaAt T hlam1 (by linarith)
  have ht2 := tendsto_betaAt T (by linarith) hlam2
  have hsub := ht1.sub ht2
  have hrhs : Filter.Tendsto (fun n => (lam2 - lam1) / (2 - lam2) * betaAt T lam1 n [])
      Filter.atTop (nhds ((lam2 - lam1) / (2 - lam2) * beta T lam1)) :=
    tendsto_const_nhds.mul ht1
  have hle := le_of_tendsto_of_tendsto hsub hrhs
    (Filter.Eventually.of_forall (fun n => betaAt_lipschitz T hlam1 hlt hlam2 n []))
  have heq : (lam2 - lam1) / (2 - lam2) * beta T lam1 = (lam2 - lam1) * beta T lam1 / (2 - lam2) := by
    ring
  linarith

/-- Invariance of `[1 - λ/2, 1 - λ/3]` under `betaAtInit`. -/
lemma betaAtInit_in_interval (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2)
    {init : List (Fin 3) → ℝ}
    (hinit : ∀ w, 1 - lam / 2 ≤ init w ∧ init w ≤ 1 - lam / 3) :
    ∀ n v, 1 - lam / 2 ≤ betaAtInit T lam init n v ∧ betaAtInit T lam init n v ≤ 1 - lam / 3 := by
  intro n
  induction n with
  | zero => intro v; exact hinit v
  | succ n ih =>
      intro v
      obtain ⟨l0, u0⟩ := ih (v ++ [0])
      obtain ⟨l1, u1⟩ := ih (v ++ [1])
      obtain ⟨l2, u2⟩ := ih (v ++ [2])
      have hfix2 : condStep lam (2 * (1 - lam / 2)) = 1 - lam / 2 := by
        unfold condStep; ring
      have hfix3 : condStep lam (3 * (1 - lam / 3)) = 1 - lam / 3 := by
        unfold condStep; ring
      simp only [betaAtInit]
      split_ifs with hT
      · constructor
        · rw [← hfix2]; exact condStep_mono hlam0 (by linarith) (by linarith)
        · rw [← hfix3]; exact condStep_mono hlam0 (by linarith) (by linarith)
      · constructor
        · rw [← hfix2]; exact condStep_mono hlam0 (by linarith) (by linarith)
        · rw [← hfix3]; exact condStep_mono hlam0 (by linarith) (by linarith)

/-- Exact fixed-point equation for `beta` at the root. -/
lemma beta_fixed_point (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) :
    beta T lam =
      let b0 := beta (shiftTree T [0]) lam
      let b1 := beta (shiftTree T [1]) lam
      let s := if T [] then b0 + b1 else b0 + b1 + beta (shiftTree T [2]) lam
      condStep lam s := by
  have ht0 := tendsto_betaAt (shiftTree T [0]) hlam0 hlam2
  have ht1 := tendsto_betaAt (shiftTree T [1]) hlam0 hlam2
  have ht2 := tendsto_betaAt (shiftTree T [2]) hlam0 hlam2
  have hshift : ∀ (c : Fin 3) (n : ℕ), betaAt (shiftTree T [c]) lam n [] = betaAt T lam n [c] := by
    intro c n
    unfold betaAt
    simpa using betaAtInit_shift T lam (fun _ => 1) n [c] []
  simp_rw [hshift] at ht0 ht1 ht2
  have hstep_seq : ∀ n, betaAt T lam (n + 1) [] =
      condStep lam (if T [] then betaAt T lam n [0] + betaAt T lam n [1]
        else betaAt T lam n [0] + betaAt T lam n [1] + betaAt T lam n [2]) := fun _ => rfl
  have hlhs : Filter.Tendsto (fun n => betaAt T lam (n + 1) []) Filter.atTop (nhds (beta T lam)) :=
    (tendsto_betaAt T hlam0 hlam2).comp (Filter.tendsto_add_atTop_nat 1)
  cases hT : T []
  · have hstep_f : ∀ n, betaAt T lam (n + 1) [] =
        condStep lam (betaAt T lam n [0] + betaAt T lam n [1] + betaAt T lam n [2]) := by
      intro n; simp [hstep_seq, hT]
    have hs : Filter.Tendsto (fun n => betaAt T lam n [0] + betaAt T lam n [1] + betaAt T lam n [2])
        Filter.atTop (nhds (beta (shiftTree T [0]) lam + beta (shiftTree T [1]) lam + beta (shiftTree T [2]) lam)) :=
      (ht0.add ht1).add ht2
    have hden : lam + (beta (shiftTree T [0]) lam + beta (shiftTree T [1]) lam + beta (shiftTree T [2]) lam) ≠ 0 := by
      have s0 := (lemma_4_1_support (shiftTree T [0]) hlam0 hlam2).1
      have s1 := (lemma_4_1_support (shiftTree T [1]) hlam0 hlam2).1
      have s2 := (lemma_4_1_support (shiftTree T [2]) hlam0 hlam2).1
      linarith
    have hrhs : Filter.Tendsto (fun n => condStep lam (betaAt T lam n [0] + betaAt T lam n [1] + betaAt T lam n [2]))
        Filter.atTop (nhds (condStep lam (beta (shiftTree T [0]) lam + beta (shiftTree T [1]) lam + beta (shiftTree T [2]) lam))) := by
      unfold condStep
      exact hs.div (tendsto_const_nhds.add hs) hden
    simp_rw [← hstep_f] at hrhs
    have heq := tendsto_nhds_unique hlhs hrhs
    simpa [hT] using heq
  · have hstep_t : ∀ n, betaAt T lam (n + 1) [] =
        condStep lam (betaAt T lam n [0] + betaAt T lam n [1]) := by
      intro n; simp [hstep_seq, hT]
    have hs : Filter.Tendsto (fun n => betaAt T lam n [0] + betaAt T lam n [1])
        Filter.atTop (nhds (beta (shiftTree T [0]) lam + beta (shiftTree T [1]) lam)) :=
      ht0.add ht1
    have hden : lam + (beta (shiftTree T [0]) lam + beta (shiftTree T [1]) lam) ≠ 0 := by
      have s0 := (lemma_4_1_support (shiftTree T [0]) hlam0 hlam2).1
      have s1 := (lemma_4_1_support (shiftTree T [1]) hlam0 hlam2).1
      linarith
    have hrhs : Filter.Tendsto (fun n => condStep lam (betaAt T lam n [0] + betaAt T lam n [1]))
        Filter.atTop (nhds (condStep lam (beta (shiftTree T [0]) lam + beta (shiftTree T [1]) lam))) := by
      unfold condStep
      exact hs.div (tendsto_const_nhds.add hs) hden
    simp_rw [← hstep_t] at hrhs
    have heq := tendsto_nhds_unique hlhs hrhs
    simpa [hT] using heq

lemma beta_eq_betaAtInit_shift (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) :
    ∀ n v, beta (shiftTree T v) lam =
      betaAtInit T lam (fun w => beta (shiftTree T w) lam) n v := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
      intro v
      have hfp := beta_fixed_point (shiftTree T v) hlam0 hlam2
      have hsh : ∀ c : Fin 3, shiftTree (shiftTree T v) [c] = shiftTree T (v ++ [c]) := by
        intro c; funext w; simp [shiftTree, List.append_assoc]
      have ht : shiftTree T v [] = T v := by simp [shiftTree]
      simp only [hsh, ht] at hfp
      rw [hfp, ih (v ++ [0]), ih (v ++ [1]), ih (v ++ [2])]
      rfl

/-- One-step multiplicative contraction of `g_λ(S) = S/(λ+S)`:
    if `0 < sz`, `2 - λ ≤ sz`, `0 ≤ δ`, and `sy ≤ (1 + δ) * sz`, then
    `condStep λ sy ≤ (1 + (λ/2) * δ) * condStep λ sz`. -/
lemma condStep_ratio_contraction {lam sy sz delta : ℝ}
    (hlam0 : 0 < lam) (_hlam2 : lam < 2)
    (hsz_pos : 0 < sz) (hsz_lo : 2 - lam ≤ sz)
    (hdelta : 0 ≤ delta) (hsy_pos : 0 ≤ sy) (hsy : sy ≤ (1 + delta) * sz) :
    condStep lam sy ≤ (1 + (lam / 2) * delta) * condStep lam sz := by
  have hmono : condStep lam sy ≤ condStep lam ((1 + delta) * sz) :=
    condStep_mono hlam0 hsy_pos hsy
  refine hmono.trans ?_
  unfold condStep
  have hd1 : 0 < lam + (1 + delta) * sz := by nlinarith
  have hd2 : 0 < lam + sz := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ hd1 hd2]
  have hsum2 : 2 ≤ lam + (1 + delta) * sz := by nlinarith
  have hdiff : (1 + lam / 2 * delta) * sz * (lam + (1 + delta) * sz) -
      (1 + delta) * sz * (lam + sz) =
      (delta * sz) * ((lam / 2) * (lam + (1 + delta) * sz) - lam) := by ring
  have hfactor1 : 0 ≤ delta * sz := mul_nonneg hdelta (le_of_lt hsz_pos)
  have hfactor2 : 0 ≤ (lam / 2) * (lam + (1 + delta) * sz) - lam := by nlinarith
  have hprod : 0 ≤ (delta * sz) * ((lam / 2) * (lam + (1 + delta) * sz) - lam) :=
    mul_nonneg hfactor1 hfactor2
  linarith

/-- Uniform `(λ/2)^n` multiplicative contraction between any two boundary assignments in `[1-λ/2, 1-λ/3]`. -/
lemma betaAtInit_ratio_contraction (T : InfTree23) {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2)
    {init1 init2 : List (Fin 3) → ℝ}
    (h1 : ∀ w, 1 - lam / 2 ≤ init1 w ∧ init1 w ≤ 1 - lam / 3)
    (h2 : ∀ w, 1 - lam / 2 ≤ init2 w ∧ init2 w ≤ 1 - lam / 3) :
    let a := 1 - lam / 2
    let b := 1 - lam / 3
    let delta0 := (b - a) / a
    ∀ n v, betaAtInit T lam init1 n v ≤
      (1 + (lam / 2) ^ n * delta0) * betaAtInit T lam init2 n v := by
  intro a b delta0 n
  have ha : 0 < a := by unfold a; linarith
  have hb_pos : 0 < b := by unfold b; linarith
  have hba : 0 ≤ b - a := by unfold a b; linarith
  have hd0 : 0 ≤ delta0 := div_nonneg hba (le_of_lt ha)
  induction n with
  | zero =>
      intro v
      simp only [betaAtInit, pow_zero, one_mul]
      have h1u := (h1 v).2
      have h2l := (h2 v).1
      have h1plus : 1 + delta0 = b / a := by unfold delta0; field_simp [ne_of_gt ha]; ring
      rw [h1plus]
      calc init1 v ≤ b := h1u
        _ = (b / a) * a := by field_simp [ne_of_gt ha]
        _ ≤ (b / a) * init2 v := mul_le_mul_of_nonneg_left h2l (div_nonneg (le_of_lt hb_pos) (le_of_lt ha))
  | succ n ih =>
      intro v
      have ih0 := ih (v ++ [0])
      have ih1 := ih (v ++ [1])
      have ih2 := ih (v ++ [2])
      have b2_0 := (betaAtInit_in_interval T hlam0 hlam2 h2 n (v ++ [0])).1
      have b2_1 := (betaAtInit_in_interval T hlam0 hlam2 h2 n (v ++ [1])).1
      have b2_2 := (betaAtInit_in_interval T hlam0 hlam2 h2 n (v ++ [2])).1
      have b1_0 := (betaAtInit_in_interval T hlam0 hlam2 h1 n (v ++ [0])).1
      have b1_1 := (betaAtInit_in_interval T hlam0 hlam2 h1 n (v ++ [1])).1
      have b1_2 := (betaAtInit_in_interval T hlam0 hlam2 h1 n (v ++ [2])).1
      have hdn : 0 ≤ (lam / 2) ^ n * delta0 := mul_nonneg (pow_nonneg (by linarith) n) hd0
      simp only [betaAtInit, pow_succ']
      rw [mul_assoc]
      split_ifs with hT
      · exact condStep_ratio_contraction hlam0 hlam2 (by linarith) (by linarith) hdn (by linarith) (by linarith)
      · exact condStep_ratio_contraction hlam0 hlam2 (by linarith) (by linarith) hdn (by linarith) (by linarith)

/-- **Uniform Contraction Theorem**: Starting depth-`n` recursion from any constant `c ∈ [1-λ/2, 1-λ/3]`
    approximates the true infinite-tree conductance `beta T lam` uniformly across ALL trees `T`
    within `(λ/2)^n * ((b - a) / a) * b`. -/
theorem betaAtInit_uniform_approx (T : InfTree23) {lam c : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 2)
    (hc : 1 - lam / 2 ≤ c ∧ c ≤ 1 - lam / 3) (n : ℕ) :
    let a := 1 - lam / 2
    let b := 1 - lam / 3
    |betaAtInit T lam (fun _ => c) n [] - beta T lam| ≤
      (lam / 2) ^ n * ((b - a) / a) * b := by
  intro a b
  have hbeta_eq : beta T lam = betaAtInit T lam (fun w => beta (shiftTree T w) lam) n [] := by
    have h := beta_eq_betaAtInit_shift T hlam0 hlam2 n []
    rwa [shiftTree_nil] at h
  rw [hbeta_eq]
  have hinit_c : ∀ w : List (Fin 3), 1 - lam / 2 ≤ c ∧ c ≤ 1 - lam / 3 := fun _ => hc
  have hinit_b : ∀ w : List (Fin 3), 1 - lam / 2 ≤ beta (shiftTree T w) lam ∧ beta (shiftTree T w) lam ≤ 1 - lam / 3 :=
    fun w => lemma_4_1_support (shiftTree T w) hlam0 hlam2
  have h_le1 := betaAtInit_ratio_contraction T hlam0 hlam2 hinit_c hinit_b n []
  have h_le2 := betaAtInit_ratio_contraction T hlam0 hlam2 hinit_b hinit_c n []
  have hb_c := betaAtInit_in_interval T hlam0 hlam2 hinit_c n []
  have hb_b := betaAtInit_in_interval T hlam0 hlam2 hinit_b n []
  have hnonneg : 0 ≤ (lam / 2) ^ n * ((b - a) / a) := by
    have ha : 0 < a := by unfold a; linarith
    have hba : 0 ≤ b - a := by unfold a b; linarith
    exact mul_nonneg (pow_nonneg (by linarith) n) (div_nonneg hba (le_of_lt ha))
  change |betaAtInit T lam (fun _ => c) n [] - betaAtInit T lam (fun w => beta (shiftTree T w) lam) n []| ≤ _
  have hsub1 : betaAtInit T lam (fun _ => c) n [] - betaAtInit T lam (fun w => beta (shiftTree T w) lam) n [] ≤
      ((lam / 2) ^ n * ((b - a) / a)) * b := by
    have h1 : betaAtInit T lam (fun _ => c) n [] - betaAtInit T lam (fun w => beta (shiftTree T w) lam) n [] ≤
        ((lam / 2) ^ n * ((b - a) / a)) * betaAtInit T lam (fun w => beta (shiftTree T w) lam) n [] := by
      unfold a b; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left hb_b.2 hnonneg)
  have hsub2 : betaAtInit T lam (fun w => beta (shiftTree T w) lam) n [] - betaAtInit T lam (fun _ => c) n [] ≤
      ((lam / 2) ^ n * ((b - a) / a)) * b := by
    have h2 : betaAtInit T lam (fun w => beta (shiftTree T w) lam) n [] - betaAtInit T lam (fun _ => c) n [] ≤
        ((lam / 2) ^ n * ((b - a) / a)) * betaAtInit T lam (fun _ => c) n [] := by
      unfold a b; linarith
    exact h2.trans (mul_le_mul_of_nonneg_left hb_c.2 hnonneg)
  rw [abs_sub_le_iff]
  exact ⟨hsub1, hsub2⟩

end GWSpeedCertificate
