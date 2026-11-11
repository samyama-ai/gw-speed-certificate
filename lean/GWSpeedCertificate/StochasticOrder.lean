import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import GWSpeedCertificate.TreeConductance

/-!
# Section 5: Discrete RDE Envelopes, Abel Stochastic Dominance & Multi-Tree Bounds (`StochasticOrder.lean`)

Proves with zero `sorry` and zero floating-point assumptions:
- **Measurability on `InfTree23`**: `betaAtInit`, `betaAt`, and `beta` are measurable on `InfTree23`.
- **Abel Summation Stochastic Dominance (`evalGrid_le_of_checkCdfLe`)**: Exact `List ℕ` cumulative-sum
  dominance implies expectation inequalities for all monotone functions.
- **Exact Polynomial Convolution (`polyMul`) & Linear Bucketing (`bucketSorted`)**: Kernel-friendly
  `List ℕ` operations with zero array-indexing overhead and exact generating-sum soundness theorems.
- **1-Step Post-Fixpoint Envelope Theorems (`upperEnv_sound`, `lowerEnv_sound`)**:
  Verified integer 1-step post-fixpoints `T_up(U) ≤_st U` and `L ≤_st T_dn(L)` bound `∫ T, g(β(T, λ)) ∂μ`
  via GW root branching induction on depth `n` + uniform contraction (`betaAtInit_uniform_approx`) +
  dominated convergence as `n → ∞`.
-/

namespace GWSpeedCertificate

open MeasureTheory

/-! ## 1. Interval Clamping & Measurability on `InfTree23` -/

/-- Clamp `x : ℝ` into `[a, b]` via `max a (min b x)`. -/
noncomputable def clampIcc (a b x : ℝ) : ℝ :=
  max a (min b x)

lemma clampIcc_mem_Icc {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    clampIcc a b x ∈ Set.Icc a b := by
  unfold clampIcc
  refine ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

lemma clampIcc_eq_self {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    clampIcc a b x = x := by
  unfold clampIcc
  rw [min_eq_right hx.2, max_eq_right hx.1]

lemma continuous_clampIcc (a b : ℝ) : Continuous (clampIcc a b) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma monotone_clampIcc (a b : ℝ) : Monotone (clampIcc a b) := by
  intro x y hxy
  unfold clampIcc
  exact max_le_max_left a (min_le_min_left b hxy)

lemma measurable_tree_apply (v : List (Fin 3)) : Measurable (fun T : InfTree23 => T v) :=
  measurable_pi_apply v

lemma measurable_shiftTree (p : List (Fin 3)) : Measurable (fun T : InfTree23 => shiftTree T p) :=
  Measurable.of_eval (fun w => measurable_pi_apply (p ++ w))

lemma measurable_betaAtInit (lam c : ℝ) :
    ∀ (n : ℕ) (v : List (Fin 3)), Measurable (fun T : InfTree23 => betaAtInit T lam (fun _ => c) n v)
  | 0, _ => measurable_const
  | n + 1, v => by
      have m0 := measurable_betaAtInit lam c n (v ++ [0])
      have m1 := measurable_betaAtInit lam c n (v ++ [1])
      have m2 := measurable_betaAtInit lam c n (v ++ [2])
      have msum : Measurable (fun T : InfTree23 =>
          if T v then betaAtInit T lam (fun _ => c) n (v ++ [0]) + betaAtInit T lam (fun _ => c) n (v ++ [1])
          else betaAtInit T lam (fun _ => c) n (v ++ [0]) + betaAtInit T lam (fun _ => c) n (v ++ [1]) +
            betaAtInit T lam (fun _ => c) n (v ++ [2])) := by
        refine Measurable.ite ?_ (m0.add m1) ((m0.add m1).add m2)
        exact (measurable_tree_apply v) (measurableSet_singleton true)
      change Measurable (fun T => condStep lam _)
      unfold condStep
      exact msum.div (measurable_const.add msum)

lemma measurable_betaAt (lam : ℝ) (n : ℕ) (v : List (Fin 3)) :
    Measurable (fun T : InfTree23 => betaAt T lam n v) :=
  measurable_betaAtInit lam 1 n v

lemma measurable_beta (lam : ℝ) : Measurable (fun T : InfTree23 => beta T lam) := by
  unfold beta
  exact Measurable.iInf (fun n => measurable_betaAt lam n [])

lemma integrable_of_measurable_bounded {α : Type*} [MeasurableSpace α]
    {mu : Measure α} [IsFiniteMeasure mu] {f : α → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f mu := by
  refine Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable C ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

/-! ## 2. Galton–Watson `Offspring(p₂ = p₃ = 1/2)` Tree Law Interface -/

/-- Probability law `mu` on `InfTree23` satisfying the recursive Galton–Watson branching equation
    at the root (`P(deg = 2) = P(deg = 3) = 1/2`, with i.i.d. child subtrees of law `mu`). -/
class IsGWTree23 (mu : Measure InfTree23) : Prop where
  isProb : IsProbabilityMeasure mu
  branching :
    ∀ (φ : InfTree23 → ℝ) (G2 : ℝ × ℝ → ℝ) (G3 : ℝ × ℝ × ℝ → ℝ),
      Measurable φ → (∃ C, ∀ T, |φ T| ≤ C) →
      Continuous G2 → Continuous G3 →
      (∫ T, (if T [] then G2 (φ (shiftTree T [0]), φ (shiftTree T [1]))
             else G3 (φ (shiftTree T [0]), φ (shiftTree T [1]), φ (shiftTree T [2]))) ∂mu) =
        (1 / 2 : ℝ) * (∫ T0, ∫ T1, G2 (φ T0, φ T1) ∂mu ∂mu) +
        (1 / 2 : ℝ) * (∫ T0, ∫ T1, ∫ T2, G3 (φ T0, φ T1, φ T2) ∂mu ∂mu ∂mu)

attribute [instance] IsGWTree23.isProb

/-! ## 3. Pure `List ℕ` Grid Evaluation, Convolution, Bucketing & Abel Dominance -/

/-- Evaluate `∑_{k} w_k * g(x0 + k * h)` along a list of integer weights. -/
noncomputable def evalGrid (x0 h : ℝ) (g : ℝ → ℝ) : List ℕ → ℝ
  | [] => 0
  | w :: ws => (w : ℝ) * g x0 + evalGrid (x0 + h) h g ws

/-- Pointwise addition of two `List ℕ`s (zero-padded at the end). -/
def addLists : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addLists xs ys

/-- Multiply every entry of a `List ℕ` by `c : ℕ`. -/
def scaleList (c : ℕ) : List ℕ → List ℕ
  | [] => []
  | y :: ys => (c * y) :: scaleList c ys

/-- Exact discrete convolution (polynomial multiplication) of two `List ℕ`s.
    Automatically skips zero entries in the first list for sparse kernel speed. -/
def polyMul : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | 0 :: xs, ys => 0 :: polyMul xs ys
  | x :: xs, ys => addLists (scaleList x ys) (0 :: polyMul xs ys)

lemma grid_pt_mem_Icc {a b h : ℝ} (hh : 0 ≤ h) {K j : ℕ}
    (hj : j < K + 1) (hlast : a + (K : ℝ) * h ≤ b) :
    a + (j : ℝ) * h ∈ Set.Icc a b := by
  have hj_le : (j : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr (Nat.lt_succ_iff.mp hj)
  have h1 : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh
  have h2 : (j : ℝ) * h ≤ (K : ℝ) * h := mul_le_mul_of_nonneg_right hj_le hh
  exact ⟨by linarith, by linarith⟩

lemma evalGrid_congr {x0 h : ℝ} {g1 g2 : ℝ → ℝ} :
    ∀ (ws : List ℕ) (k : ℕ),
      (∀ j, k ≤ j → j < k + ws.length → g1 (x0 + (j - k : ℕ) * h) = g2 (x0 + (j - k : ℕ) * h)) →
      evalGrid x0 h g1 ws = evalGrid x0 h g2 ws
  | [], _, _ => rfl
  | w :: ws, k, hfg => by
      simp only [evalGrid]
      have h0 : g1 x0 = g2 x0 := by
        have := hfg k (le_rfl) (by simp)
        simpa using this
      have hrest : evalGrid (x0 + h) h g1 ws = evalGrid (x0 + h) h g2 ws := by
        refine evalGrid_congr ws (k + 1) (fun j hlo hhi => ?_)
        have hj := hfg j (by omega) (by simp [List.length_cons]; omega)
        have hshift : (x0 + h) + ((j - (k + 1) : ℕ) : ℝ) * h = x0 + ((j - k : ℕ) : ℝ) * h := by
          have hnat : (j - k : ℕ) = (j - (k + 1)) + 1 := by omega
          push_cast [hnat]
          ring
        rwa [hshift]
      rw [h0, hrest]

lemma evalGrid_mono_pts {h : ℝ} {g1 g2 : ℝ → ℝ} :
    ∀ (ws : List ℕ) (x0 : ℝ),
      (∀ j < ws.length, g1 (x0 + (j : ℝ) * h) ≤ g2 (x0 + (j : ℝ) * h)) →
      evalGrid x0 h g1 ws ≤ evalGrid x0 h g2 ws
  | [], _, _ => le_rfl
  | w :: ws, x0, hle => by
      simp only [evalGrid]
      have h0 : (w : ℝ) * g1 x0 ≤ (w : ℝ) * g2 x0 := by
        have := hle 0 (by simp)
        simp only [Nat.cast_zero, zero_mul, add_zero] at this
        exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg w)
      have htail : evalGrid (x0 + h) h g1 ws ≤ evalGrid (x0 + h) h g2 ws := by
        refine evalGrid_mono_pts ws (x0 + h) (fun j hj => ?_)
        have hj' := hle (j + 1) (by simp [List.length_cons]; omega)
        have hsh : (x0 + h) + (j : ℝ) * h = x0 + ((j + 1 : ℕ) : ℝ) * h := by push_cast; ring
        rwa [hsh]
      linarith

lemma evalGrid_add_func (x0 h : ℝ) (g1 g2 : ℝ → ℝ) :
    ∀ ws : List ℕ, evalGrid x0 h (fun x => g1 x + g2 x) ws =
      evalGrid x0 h g1 ws + evalGrid x0 h g2 ws
  | [] => by simp [evalGrid]
  | w :: ws => by simp only [evalGrid, evalGrid_add_func _ _ _ _ ws]; ring

lemma evalGrid_const_mul (x0 h c : ℝ) (g : ℝ → ℝ) :
    ∀ ws : List ℕ, evalGrid x0 h (fun x => c * g x) ws = c * evalGrid x0 h g ws
  | [] => by simp [evalGrid]
  | w :: ws => by simp only [evalGrid, evalGrid_const_mul _ _ _ _ ws]; ring

lemma evalGrid_const (x0 h c : ℝ) :
    ∀ ws : List ℕ, evalGrid x0 h (fun _ => c) ws = (ws.sum : ℝ) * c
  | [] => by simp [evalGrid]
  | w :: ws => by
      simp only [evalGrid, List.sum_cons, Nat.cast_add, evalGrid_const _ _ _ ws]
      ring

lemma evalGrid_addLists (h : ℝ) (g : ℝ → ℝ) :
    ∀ (xs ys : List ℕ) (x0 : ℝ),
      evalGrid x0 h g (addLists xs ys) = evalGrid x0 h g xs + evalGrid x0 h g ys
  | [], ys, x0 => by simp [addLists, evalGrid]
  | x :: xs, [], x0 => by simp [addLists, evalGrid]
  | x :: xs, y :: ys, x0 => by
      simp only [addLists, evalGrid, Nat.cast_add, evalGrid_addLists h g xs ys (x0 + h)]
      ring

lemma evalGrid_scaleList (c : ℕ) (h : ℝ) (g : ℝ → ℝ) :
    ∀ (ys : List ℕ) (x0 : ℝ),
      evalGrid x0 h g (scaleList c ys) = (c : ℝ) * evalGrid x0 h g ys
  | [], _ => by simp [scaleList, evalGrid]
  | y :: ys, x0 => by
      simp only [scaleList, evalGrid, Nat.cast_mul, evalGrid_scaleList c h g ys (x0 + h)]
      ring

lemma evalGrid_shift (h : ℝ) (g : ℝ → ℝ) :
    ∀ (ys : List ℕ) (x0 y0 : ℝ),
      evalGrid (x0 + y0) h g ys = evalGrid y0 h (fun y => g (x0 + y)) ys
  | [], _, _ => rfl
  | y :: ys, x0, y0 => by
      simp only [evalGrid]
      have h1 : (x0 + y0) + h = x0 + (y0 + h) := by ring
      rw [h1, evalGrid_shift h g ys x0 (y0 + h)]

/-- **Exact Convolution Evaluation Theorem**: `polyMul xs ys` evaluates bilinear expectations
    `∑_i ∑_j xs[i] * ys[j] * g((x0 + i*h) + (y0 + j*h))` with zero loss. -/
theorem evalGrid_polyMul (h : ℝ) (g : ℝ → ℝ) :
    ∀ (xs : List ℕ) (x0 y0 : ℝ) (ys : List ℕ),
      evalGrid (x0 + y0) h g (polyMul xs ys) =
        evalGrid x0 h (fun x => evalGrid y0 h (fun y => g (x + y)) ys) xs
  | [], _, _, _ => by simp [polyMul, evalGrid]
  | 0 :: xs, x0, y0, ys => by
      simp only [polyMul, evalGrid, Nat.cast_zero, zero_mul, zero_add]
      have h1 : (x0 + y0) + h = (x0 + h) + y0 := by ring
      rw [h1, evalGrid_polyMul h g xs (x0 + h) y0 ys]
  | (x + 1) :: xs, x0, y0, ys => by
      simp only [polyMul]
      rw [evalGrid_addLists, evalGrid_scaleList, evalGrid_shift]
      simp only [evalGrid, Nat.cast_zero, zero_mul, zero_add]
      have h1 : (x0 + y0) + h = (x0 + h) + y0 := by ring
      rw [h1, evalGrid_polyMul h g xs (x0 + h) y0 ys]

/-- Prefix-dominance and equal-sum check on two `List ℕ`s:
    returns `true` iff `ps.length = qs.length`, `cp + sum(ps) = cq + sum(qs)`,
    and at every step `cp + partial_sum(ps) ≤ cq + partial_sum(qs)`. -/
def checkCdfLe : ℕ → ℕ → List ℕ → List ℕ → Bool
  | cp, cq, [], [] => cp == cq
  | cp, cq, p :: ps, q :: qs =>
      let cp' := cp + p
      let cq' := cq + q
      (cp' ≤ cq') && checkCdfLe cp' cq' ps qs
  | _, _, _, _ => false

/-- **Abel Summation Stochastic Dominance Theorem** on `List ℕ`:
    if `cp ≤ cq`, `0 ≤ h`, `g` is `Monotone`, and `checkCdfLe cp cq ps qs = true`, then
    `(cq - cp) * g(x0) + evalGrid x0 h g qs ≤ evalGrid x0 h g ps`. -/
lemma evalGrid_le_of_checkCdfLe_aux {h : ℝ} (hh : 0 ≤ h) {g : ℝ → ℝ} (hg : Monotone g) :
    ∀ (ps qs : List ℕ) (cp cq : ℕ) (x0 : ℝ),
      cp ≤ cq →
      checkCdfLe cp cq ps qs = true →
      ((cq : ℝ) - (cp : ℝ)) * g x0 + evalGrid x0 h g qs ≤ evalGrid x0 h g ps
  | [], [], cp, cq, x0, _, hchk => by
      simp only [checkCdfLe, beq_iff_eq] at hchk
      subst hchk
      simp [evalGrid]
  | [], _ :: _, _, _, _, _, hchk => by simp [checkCdfLe] at hchk
  | _ :: _, [], _, _, _, _, hchk => by simp [checkCdfLe] at hchk
  | p :: ps, q :: qs, cp, cq, x0, _, hchk => by
      simp only [checkCdfLe, Bool.and_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨hle', hrest⟩ := hchk
      have ih := evalGrid_le_of_checkCdfLe_aux hh hg ps qs (cp + p) (cq + q) (x0 + h) hle' hrest
      have hg_step : g x0 ≤ g (x0 + h) := hg (by linarith)
      have hdiff_nonneg : (0 : ℝ) ≤ ((cq + q : ℕ) : ℝ) - ((cp + p : ℕ) : ℝ) :=
        sub_nonneg.mpr (Nat.cast_le.mpr hle')
      have hstep_mul : (((cq + q : ℕ) : ℝ) - ((cp + p : ℕ) : ℝ)) * g x0 ≤
          (((cq + q : ℕ) : ℝ) - ((cp + p : ℕ) : ℝ)) * g (x0 + h) :=
        mul_le_mul_of_nonneg_left hg_step hdiff_nonneg
      simp only [evalGrid]
      push_cast at hstep_mul ih
      linarith

theorem evalGrid_le_of_checkCdfLe {x0 h : ℝ} (hh : 0 ≤ h) {g : ℝ → ℝ} (hg : Monotone g)
    {ps qs : List ℕ} (hchk : checkCdfLe 0 0 ps qs = true) :
    evalGrid x0 h g qs ≤ evalGrid x0 h g ps := by
  have h0 := evalGrid_le_of_checkCdfLe_aux hh hg ps qs 0 0 x0 (le_rfl) hchk
  simpa using h0

/-- Consume all leading `(j, w)` pairs with `j ≤ curK`, accumulating weights into `acc`.
    Purely structural on `List (ℕ × ℕ)` so it reduces directly in the Lean kernel (`Eq.refl true`). -/
def takeBin (curK : ℕ) : ℕ → List (ℕ × ℕ) → ℕ × List (ℕ × ℕ)
  | acc, [] => (acc, [])
  | acc, (j, w) :: rest =>
      if j ≤ curK then
        takeBin curK (acc + w) rest
      else
        (acc, (j, w) :: rest)

/-- Linear-time bucketing of sorted `(bin_index, weight)` pairs into `rem` bins starting at `curK`.
    Purely structural on `rem : ℕ` (no `WellFounded.fix`) for fast Lean kernel reduction. -/
def bucketSorted : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List ℕ
  | _, 0, _, _ => []
  | curK, rem + 1, acc, pairs =>
      let res := takeBin curK acc pairs
      res.1 :: bucketSorted (curK + 1) rem 0 res.2

/-- Evaluate `(j, w)` pairs at grid points `baseX + j * h`. -/
noncomputable def evalPairs (baseX h : ℝ) (g : ℝ → ℝ) : List (ℕ × ℕ) → ℝ
  | [] => 0
  | (j, w) :: rest => (w : ℝ) * g (baseX + (j : ℝ) * h) + evalPairs baseX h g rest

/-- Predicate asserting that `pairs` has nondecreasing indices in `[lo, hi)`. -/
def SortedInRange : ℕ → ℕ → List (ℕ × ℕ) → Prop
  | lo, hi, [] => lo < hi
  | lo, hi, (j, _) :: rest => lo ≤ j ∧ j < hi ∧ SortedInRange j hi rest

lemma takeBin_spec (baseX h : ℝ) (g : ℝ → ℝ) (curK hi : ℕ) :
    ∀ (pairs : List (ℕ × ℕ)) (acc : ℕ),
      SortedInRange curK hi pairs →
      ((takeBin curK acc pairs).2 = [] ∨
        (curK + 1 < hi ∧ SortedInRange (curK + 1) hi (takeBin curK acc pairs).2)) ∧
      (((takeBin curK acc pairs).1 : ℝ) * g (baseX + (curK : ℝ) * h) +
          evalPairs baseX h g (takeBin curK acc pairs).2 =
        (acc : ℝ) * g (baseX + (curK : ℝ) * h) + evalPairs baseX h g pairs)
  | [], acc, _ => ⟨Or.inl rfl, rfl⟩
  | (j, w) :: rest, acc, ⟨hlo, hhi, hrest⟩ => by
      simp only [takeBin]
      split_ifs with hj
      · have hjeq : j = curK := le_antisymm hj hlo
        subst hjeq
        obtain ⟨h1, h2⟩ := takeBin_spec baseX h g j hi rest (acc + w) hrest
        refine ⟨h1, ?_⟩
        rw [h2]
        simp only [evalPairs, Nat.cast_add]
        ring
      · have hjgt : curK + 1 ≤ j := Nat.succ_le_of_lt (lt_of_not_ge hj)
        exact ⟨Or.inr ⟨by omega, ⟨hjgt, hhi, hrest⟩⟩, rfl⟩

lemma evalGrid_bucketSorted (baseX h : ℝ) (g : ℝ → ℝ) :
    ∀ (curK rem acc : ℕ) (pairs : List (ℕ × ℕ)),
      0 < rem →
      SortedInRange curK (curK + rem) pairs →
      evalGrid (baseX + (curK : ℝ) * h) h g (bucketSorted curK rem acc pairs) =
        (acc : ℝ) * g (baseX + (curK : ℝ) * h) + evalPairs baseX h g pairs
  | _, 0, _, _, hrem, _ => absurd hrem (lt_irrefl 0)
  | curK, 1, acc, pairs, _, hsr => by
      obtain ⟨h1, h2⟩ := takeBin_spec baseX h g curK (curK + 1) pairs acc hsr
      have hempty : (takeBin curK acc pairs).2 = [] := by
        rcases h1 with hnil | ⟨hlt, _⟩
        · exact hnil
        · omega
      simp only [bucketSorted, evalGrid, add_zero]
      rw [← h2, hempty, evalPairs, add_zero]
  | curK, rem + 2, acc, pairs, _, hsr => by
      obtain ⟨h1, h2⟩ := takeBin_spec baseX h g curK (curK + (rem + 2)) pairs acc hsr
      have hsr_next : SortedInRange (curK + 1) ((curK + 1) + (rem + 1)) (takeBin curK acc pairs).2 := by
        rcases h1 with hnil | ⟨_, hsr'⟩
        · rw [hnil]; simp only [SortedInRange]; omega
        · rwa [show (curK + 1) + (rem + 1) = curK + (rem + 2) by omega]
      change ((takeBin curK acc pairs).1 : ℝ) * g (baseX + (curK : ℝ) * h) +
          evalGrid ((baseX + (curK : ℝ) * h) + h) h g
            (bucketSorted (curK + 1) (rem + 1) 0 (takeBin curK acc pairs).2) =
        (acc : ℝ) * g (baseX + (curK : ℝ) * h) + evalPairs baseX h g pairs
      have hshift : (baseX + (curK : ℝ) * h) + h = baseX + ((curK + 1 : ℕ) : ℝ) * h := by
        push_cast; ring
      have hrec := evalGrid_bucketSorted baseX h g (curK + 1) (rem + 1) 0
        (takeBin curK acc pairs).2 (Nat.succ_pos rem) hsr_next
      rw [hshift, hrec]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      exact h2

/-! ## 4. Exact Integer Index-Map & 1-Step Post-Fixpoint Checkers -/

/-- Check that `js` is nondecreasing in `[prevJ, K]` and satisfies the exact integer upper bound
    `condStep (ln/ld) (nu * a + curI * h) ≤ a + j * h` via `D * Ds ≤ Dxj * (Dlam + Ds)` with `D = 6*ld*K`. -/
def checkIndexUpper (ln ld K nu : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | curI, prevJ, j :: rest =>
      let D := 6 * ld * K
      let Da := 3 * K * (2 * ld - ln)
      let Dlam := 6 * K * ln
      let Ds := nu * Da + curI * ln
      let Dxj := Da + j * ln
      (prevJ ≤ j) && (j ≤ K) && (D * Ds ≤ Dxj * (Dlam + Ds)) &&
        checkIndexUpper ln ld K nu (curI + 1) j rest

/-- Check that `js` is nondecreasing in `[prevJ, K]` and satisfies the exact integer lower bound
    `a + j * h ≤ condStep (ln/ld) (nu * a + curI * h)` via `Dxj * (Dlam + Ds) ≤ D * Ds`. -/
def checkIndexLower (ln ld K nu : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | curI, prevJ, j :: rest =>
      let D := 6 * ld * K
      let Da := 3 * K * (2 * ld - ln)
      let Dlam := 6 * K * ln
      let Ds := nu * Da + curI * ln
      let Dxj := Da + j * ln
      (prevJ ≤ j) && (j ≤ K) && (Dxj * (Dlam + Ds) ≤ D * Ds) &&
        checkIndexLower ln ld K nu (curI + 1) j rest

/-- Pure `Bool` checker for a 1-step upper envelope `u` at `λ = ln / ld`. -/
def checkUpperEnv (ln ld K M : ℕ) (u j2u j3u : List ℕ) : Bool :=
  (0 < ln) && (ln < 2 * ld) && (0 < K) && (0 < M) &&
  (u.length == K + 1) && (u.sum == M) &&
  (j2u.length == (polyMul u u).length) && (j3u.length == (polyMul (polyMul u u) u).length) &&
  checkIndexUpper ln ld K 2 0 0 j2u &&
  checkIndexUpper ln ld K 3 0 0 j3u &&
  checkCdfLe 0 0 (scaleList (2 * M * M) u)
    (addLists (scaleList M (bucketSorted 0 (K + 1) 0 (List.zip j2u (polyMul u u))))
      (bucketSorted 0 (K + 1) 0 (List.zip j3u (polyMul (polyMul u u) u))))

/-- Pure `Bool` checker for a 1-step lower envelope `l` at `λ = ln / ld`. -/
def checkLowerEnv (ln ld K M : ℕ) (l j2l j3l : List ℕ) : Bool :=
  (0 < ln) && (ln < 2 * ld) && (0 < K) && (0 < M) &&
  (l.length == K + 1) && (l.sum == M) &&
  (j2l.length == (polyMul l l).length) && (j3l.length == (polyMul (polyMul l l) l).length) &&
  checkIndexLower ln ld K 2 0 0 j2l &&
  checkIndexLower ln ld K 3 0 0 j3l &&
  checkCdfLe 0 0
    (addLists (scaleList M (bucketSorted 0 (K + 1) 0 (List.zip j2l (polyMul l l))))
      (bucketSorted 0 (K + 1) 0 (List.zip j3l (polyMul (polyMul l l) l))))
    (scaleList (2 * M * M) l)

/-! ## 5. Soundness of `checkIndexUpper` & `checkIndexLower` -/

lemma grid_identities {ln ld K : ℕ} (hld : 0 < ld) (hln2 : ln < 2 * ld) (hK : 0 < K) :
    let lam : ℝ := (ln : ℝ) / (ld : ℝ)
    let a : ℝ := 1 - lam / 2
    let b : ℝ := 1 - lam / 3
    let h : ℝ := (b - a) / (K : ℝ)
    let D : ℝ := (6 * ld * K : ℕ)
    0 < D ∧
    D * lam = ((6 * K * ln : ℕ) : ℝ) ∧
    D * a = ((3 * K * (2 * ld - ln) : ℕ) : ℝ) ∧
    D * h = (ln : ℝ) := by
  intro lam a b h D
  have hld_ne : (ld : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hld)
  have hK_ne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hK)
  have hD_pos : 0 < D := by
    change (0 : ℝ) < ((6 * ld * K : ℕ) : ℝ)
    exact Nat.cast_pos.mpr (by positivity)
  have hsub : ((2 * ld - ln : ℕ) : ℝ) = 2 * (ld : ℝ) - (ln : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hln2), Nat.cast_mul, Nat.cast_ofNat]
  refine ⟨hD_pos, ?_, ?_, ?_⟩
  · change ((6 * ld * K : ℕ) : ℝ) * ((ln : ℝ) / (ld : ℝ)) = ((6 * K * ln : ℕ) : ℝ)
    push_cast; field_simp [hld_ne]
  · change ((6 * ld * K : ℕ) : ℝ) * (1 - ((ln : ℝ) / (ld : ℝ)) / 2) = ((3 * K * (2 * ld - ln) : ℕ) : ℝ)
    rw [Nat.cast_mul (3 * K) (2 * ld - ln), hsub]
    push_cast; field_simp [hld_ne]; ring
  · change ((6 * ld * K : ℕ) : ℝ) * (((1 - ((ln : ℝ) / (ld : ℝ)) / 3) - (1 - ((ln : ℝ) / (ld : ℝ)) / 2)) / (K : ℝ)) = (ln : ℝ)
    push_cast; field_simp [hld_ne, hK_ne]; ring

lemma checkIndexUpper_sound {ln ld K nu : ℕ}
    (hln : 0 < ln) (hln2 : ln < 2 * ld) (hK : 0 < K) (hnu : 0 < nu)
    {g : ℝ → ℝ} (hg : Monotone g) :
    let lam : ℝ := (ln : ℝ) / (ld : ℝ)
    let a : ℝ := 1 - lam / 2
    let b : ℝ := 1 - lam / 3
    let h : ℝ := (b - a) / (K : ℝ)
    ∀ (js ws : List ℕ) (curI prevJ : ℕ),
      js.length = ws.length →
      prevJ ≤ K →
      checkIndexUpper ln ld K nu curI prevJ js = true →
      SortedInRange prevJ (K + 1) (List.zip js ws) ∧
        evalGrid ((nu : ℝ) * a + (curI : ℝ) * h) h (fun s => g (condStep lam s)) ws ≤
          evalPairs a h g (List.zip js ws) := by
  intro lam a b h
  have hld : 0 < ld := by omega
  obtain ⟨hD_pos, hDlam, hDa, hDh⟩ := grid_identities hld hln2 hK
  set D : ℝ := ((6 * ld * K : ℕ) : ℝ)
  intro js
  induction js with
  | nil =>
      intro ws curI prevJ hlen _ _
      cases ws with
      | nil => exact ⟨by simp [SortedInRange]; omega, by simp [evalGrid, evalPairs]⟩
      | cons _ _ => simp at hlen
  | cons j js ih =>
      intro ws curI prevJ hlen _ hchk
      cases ws with
      | nil => simp at hlen
      | cons w ws =>
          simp only [checkIndexUpper, Bool.and_eq_true, decide_eq_true_eq] at hchk
          obtain ⟨⟨⟨hpj, hjK⟩, hineq⟩, hrest⟩ := hchk
          obtain ⟨hsr, heval⟩ := ih ws (curI + 1) j (by simpa using hlen) hjK hrest
          refine ⟨⟨hpj, by omega, hsr⟩, ?_⟩
          set s : ℝ := (nu : ℝ) * a + (curI : ℝ) * h
          set xj : ℝ := a + (j : ℝ) * h
          have hDs : D * s = ((nu * (3 * K * (2 * ld - ln)) + curI * ln : ℕ) : ℝ) := by
            unfold s
            have : D * ((nu : ℝ) * a + (curI : ℝ) * h) = (nu : ℝ) * (D * a) + (curI : ℝ) * (D * h) := by ring
            rw [this, hDa, hDh]; push_cast; ring
          have hDxj : D * xj = ((3 * K * (2 * ld - ln) + j * ln : ℕ) : ℝ) := by
            unfold xj
            have : D * (a + (j : ℝ) * h) = D * a + (j : ℝ) * (D * h) := by ring
            rw [this, hDa, hDh]; push_cast; ring
          have hineq_real : D * (D * s) ≤ (D * xj) * (D * lam + D * s) := by
            rw [hDs, hDxj, hDlam]; unfold D
            exact_mod_cast hineq
          have hDlam_pos : 0 < D * lam := by
            rw [hDlam]; exact Nat.cast_pos.mpr (by positivity)
          have hDs_pos : 0 < D * s := by
            rw [hDs]; exact Nat.cast_pos.mpr (by
              have : 0 < 2 * ld - ln := by omega
              positivity)
          have hls_pos : 0 < lam + s := by
            have : 0 < D * (lam + s) := by linarith
            exact pos_of_mul_pos_right this (le_of_lt hD_pos)
          have hstep_le : condStep lam s ≤ xj := by
            unfold condStep
            rw [div_le_iff₀ hls_pos]
            have : D ^ 2 * (s - xj * (lam + s)) = D * (D * s) - (D * xj) * (D * lam + D * s) := by ring
            have hnonpos : D ^ 2 * (s - xj * (lam + s)) ≤ 0 := by linarith
            have hD2 : 0 < D ^ 2 := pow_pos hD_pos 2
            have : s - xj * (lam + s) ≤ 0 := nonpos_of_mul_nonpos_right hnonpos hD2
            linarith
          have hg_le : (w : ℝ) * g (condStep lam s) ≤ (w : ℝ) * g xj :=
            mul_le_mul_of_nonneg_left (hg hstep_le) (Nat.cast_nonneg w)
          simp only [List.zip_cons_cons, evalGrid, evalPairs]
          have hshift : s + h = (nu : ℝ) * a + ((curI + 1 : ℕ) : ℝ) * h := by
            unfold s; push_cast; ring
          rw [hshift]
          linarith

lemma checkIndexLower_sound {ln ld K nu : ℕ}
    (hln : 0 < ln) (hln2 : ln < 2 * ld) (hK : 0 < K) (hnu : 0 < nu)
    {g : ℝ → ℝ} (hg : Monotone g) :
    let lam : ℝ := (ln : ℝ) / (ld : ℝ)
    let a : ℝ := 1 - lam / 2
    let b : ℝ := 1 - lam / 3
    let h : ℝ := (b - a) / (K : ℝ)
    ∀ (js ws : List ℕ) (curI prevJ : ℕ),
      js.length = ws.length →
      prevJ ≤ K →
      checkIndexLower ln ld K nu curI prevJ js = true →
      SortedInRange prevJ (K + 1) (List.zip js ws) ∧
        evalPairs a h g (List.zip js ws) ≤
          evalGrid ((nu : ℝ) * a + (curI : ℝ) * h) h (fun s => g (condStep lam s)) ws := by
  intro lam a b h
  have hld : 0 < ld := by omega
  obtain ⟨hD_pos, hDlam, hDa, hDh⟩ := grid_identities hld hln2 hK
  set D : ℝ := ((6 * ld * K : ℕ) : ℝ)
  intro js
  induction js with
  | nil =>
      intro ws curI prevJ hlen _ _
      cases ws with
      | nil => exact ⟨by simp [SortedInRange]; omega, by simp [evalGrid, evalPairs]⟩
      | cons _ _ => simp at hlen
  | cons j js ih =>
      intro ws curI prevJ hlen _ hchk
      cases ws with
      | nil => simp at hlen
      | cons w ws =>
          simp only [checkIndexLower, Bool.and_eq_true, decide_eq_true_eq] at hchk
          obtain ⟨⟨⟨hpj, hjK⟩, hineq⟩, hrest⟩ := hchk
          obtain ⟨hsr, heval⟩ := ih ws (curI + 1) j (by simpa using hlen) hjK hrest
          refine ⟨⟨hpj, by omega, hsr⟩, ?_⟩
          set s : ℝ := (nu : ℝ) * a + (curI : ℝ) * h
          set xj : ℝ := a + (j : ℝ) * h
          have hDs : D * s = ((nu * (3 * K * (2 * ld - ln)) + curI * ln : ℕ) : ℝ) := by
            unfold s
            have : D * ((nu : ℝ) * a + (curI : ℝ) * h) = (nu : ℝ) * (D * a) + (curI : ℝ) * (D * h) := by ring
            rw [this, hDa, hDh]; push_cast; ring
          have hDxj : D * xj = ((3 * K * (2 * ld - ln) + j * ln : ℕ) : ℝ) := by
            unfold xj
            have : D * (a + (j : ℝ) * h) = D * a + (j : ℝ) * (D * h) := by ring
            rw [this, hDa, hDh]; push_cast; ring
          have hineq_real : (D * xj) * (D * lam + D * s) ≤ D * (D * s) := by
            rw [hDs, hDxj, hDlam]; unfold D
            exact_mod_cast hineq
          have hDlam_pos : 0 < D * lam := by
            rw [hDlam]; exact Nat.cast_pos.mpr (by positivity)
          have hDs_pos : 0 < D * s := by
            rw [hDs]; exact Nat.cast_pos.mpr (by
              have : 0 < 2 * ld - ln := by omega
              positivity)
          have hls_pos : 0 < lam + s := by
            have : 0 < D * (lam + s) := by linarith
            exact pos_of_mul_pos_right this (le_of_lt hD_pos)
          have hstep_ge : xj ≤ condStep lam s := by
            unfold condStep
            rw [le_div_iff₀ hls_pos]
            have : D ^ 2 * (xj * (lam + s) - s) = (D * xj) * (D * lam + D * s) - D * (D * s) := by ring
            have hnonpos : D ^ 2 * (xj * (lam + s) - s) ≤ 0 := by linarith
            have hD2 : 0 < D ^ 2 := pow_pos hD_pos 2
            have : xj * (lam + s) - s ≤ 0 := nonpos_of_mul_nonpos_right hnonpos hD2
            linarith
          have hg_ge : (w : ℝ) * g xj ≤ (w : ℝ) * g (condStep lam s) :=
            mul_le_mul_of_nonneg_left (hg hstep_ge) (Nat.cast_nonneg w)
          simp only [List.zip_cons_cons, evalGrid, evalPairs]
          have hshift : s + h = (nu : ℝ) * a + ((curI + 1 : ℕ) : ℝ) * h := by
            unfold s; push_cast; ring
          rw [hshift]
          linarith

/-! ## 6. 1-Step Post-Fixpoint Envelope Theorems (`upperEnv_sound`, `lowerEnv_sound`) -/

/-- One-step GW root recursion for `∫ T, g(betaAtInit T lam (const c) (n+1) []) ∂mu`. -/
lemma gw_step_expect {mu : Measure InfTree23} [IsGWTree23 mu]
    {lam c : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2)
    (hc : 1 - lam / 2 ≤ c ∧ c ≤ 1 - lam / 3)
    {g : ℝ → ℝ} (hg_cont : Continuous g) (n : ℕ) :
    let φ : InfTree23 → ℝ := fun T => betaAtInit T lam (fun _ => c) n []
    (∫ T, g (betaAtInit T lam (fun _ => c) (n + 1) []) ∂mu) =
      (1 / 2 : ℝ) * (∫ T0, ∫ T1, g (condStep lam (φ T0 + φ T1)) ∂mu ∂mu) +
      (1 / 2 : ℝ) * (∫ T0, ∫ T1, ∫ T2, g (condStep lam (φ T0 + φ T1 + φ T2)) ∂mu ∂mu ∂mu) := by
  intro φ
  set a := 1 - lam / 2
  set b := 1 - lam / 3
  have hab : a ≤ b := by unfold a b; linarith
  have hφ_mem : ∀ T : InfTree23, φ T ∈ Set.Icc a b :=
    fun T => betaAtInit_in_interval T hlam0 hlam2 (fun _ => hc) n []
  have hφ_meas : Measurable φ := measurable_betaAtInit lam c n []
  have hφ_bdd : ∃ C, ∀ T, |φ T| ≤ C := by
    refine ⟨b, fun T => ?_⟩
    rw [abs_of_nonneg (by have := (hφ_mem T).1; unfold a at this; linarith)]
    exact (hφ_mem T).2
  set G2 : ℝ × ℝ → ℝ := fun p => g (condStep lam (clampIcc a b p.1 + clampIcc a b p.2))
  set G3 : ℝ × ℝ × ℝ → ℝ := fun p => g (condStep lam (clampIcc a b p.1 + clampIcc a b p.2.1 + clampIcc a b p.2.2))
  have hG2_cont : Continuous G2 := by
    unfold G2 condStep
    have hs : Continuous (fun p : ℝ × ℝ => clampIcc a b p.1 + clampIcc a b p.2) :=
      ((continuous_clampIcc a b).comp continuous_fst).add ((continuous_clampIcc a b).comp continuous_snd)
    refine hg_cont.comp (hs.div (continuous_const.add hs) (fun p => ?_))
    have h1 := (clampIcc_mem_Icc hab p.1).1
    have h2 := (clampIcc_mem_Icc hab p.2).1
    unfold a at h1 h2; linarith
  have hG3_cont : Continuous G3 := by
    unfold G3 condStep
    have hs : Continuous (fun p : ℝ × ℝ × ℝ => clampIcc a b p.1 + clampIcc a b p.2.1 + clampIcc a b p.2.2) :=
      (((continuous_clampIcc a b).comp continuous_fst).add
        ((continuous_clampIcc a b).comp (continuous_fst.comp continuous_snd))).add
        ((continuous_clampIcc a b).comp (continuous_snd.comp continuous_snd))
    refine hg_cont.comp (hs.div (continuous_const.add hs) (fun p => ?_))
    have h1 := (clampIcc_mem_Icc hab p.1).1
    have h2 := (clampIcc_mem_Icc hab p.2.1).1
    have h3 := (clampIcc_mem_Icc hab p.2.2).1
    unfold a at h1 h2 h3; linarith
  have hbr := IsGWTree23.branching (mu := mu) φ G2 G3 hφ_meas hφ_bdd hG2_cont hG3_cont
  have hlhs : ∀ T : InfTree23,
      g (betaAtInit T lam (fun _ => c) (n + 1) []) =
        (if T [] then G2 (φ (shiftTree T [0]), φ (shiftTree T [1]))
         else G3 (φ (shiftTree T [0]), φ (shiftTree T [1]), φ (shiftTree T [2]))) := by
    intro T
    have hs0 : φ (shiftTree T [0]) = betaAtInit T lam (fun _ => c) n [0] := by
      simpa using betaAtInit_shift T lam (fun _ => c) n [0] []
    have hs1 : φ (shiftTree T [1]) = betaAtInit T lam (fun _ => c) n [1] := by
      simpa using betaAtInit_shift T lam (fun _ => c) n [1] []
    have hs2 : φ (shiftTree T [2]) = betaAtInit T lam (fun _ => c) n [2] := by
      simpa using betaAtInit_shift T lam (fun _ => c) n [2] []
    have hc0 : clampIcc a b (φ (shiftTree T [0])) = φ (shiftTree T [0]) := clampIcc_eq_self (hφ_mem _)
    have hc1 : clampIcc a b (φ (shiftTree T [1])) = φ (shiftTree T [1]) := clampIcc_eq_self (hφ_mem _)
    have hc2 : clampIcc a b (φ (shiftTree T [2])) = φ (shiftTree T [2]) := clampIcc_eq_self (hφ_mem _)
    cases hT : T []
    · simp only [betaAtInit, hT, Bool.false_eq_true, ↓reduceIte, G3]
      rw [hc0, hc1, hc2, hs0, hs1, hs2]; rfl
    · simp only [betaAtInit, hT, ↓reduceIte, G2]
      rw [hc0, hc1, hs0, hs1]; rfl
  have hrhs2 : ∀ T0 T1 : InfTree23, G2 (φ T0, φ T1) = g (condStep lam (φ T0 + φ T1)) := by
    intro T0 T1; simp [G2, clampIcc_eq_self (hφ_mem T0), clampIcc_eq_self (hφ_mem T1)]
  have hrhs3 : ∀ T0 T1 T2 : InfTree23, G3 (φ T0, φ T1, φ T2) = g (condStep lam (φ T0 + φ T1 + φ T2)) := by
    intro T0 T1 T2; simp [G3, clampIcc_eq_self (hφ_mem T0), clampIcc_eq_self (hφ_mem T1), clampIcc_eq_self (hφ_mem T2)]
  simp_rw [hlhs, ← hrhs2, ← hrhs3]
  exact hbr

lemma evalGrid_ge_head {h : ℝ} (hh : 0 ≤ h) {g : ℝ → ℝ} (hg : Monotone g) :
    ∀ (ws : List ℕ) (x0 : ℝ), (ws.sum : ℝ) * g x0 ≤ evalGrid x0 h g ws
  | [], _ => by simp [evalGrid]
  | w :: ws, x0 => by
      simp only [List.sum_cons, Nat.cast_add, evalGrid, add_mul]
      have h1 : (ws.sum : ℝ) * g x0 ≤ (ws.sum : ℝ) * g (x0 + h) :=
        mul_le_mul_of_nonneg_left (hg (by linarith)) (Nat.cast_nonneg _)
      have h2 := evalGrid_ge_head hh hg ws (x0 + h)
      linarith

lemma evalGrid_le_last {h : ℝ} {g : ℝ → ℝ} (hg : Monotone g) :
    ∀ (ws : List ℕ) (x0 b : ℝ),
      (∀ j < ws.length, x0 + (j : ℝ) * h ≤ b) →
      evalGrid x0 h g ws ≤ (ws.sum : ℝ) * g b
  | [], _, _, _ => by simp [evalGrid]
  | w :: ws, x0, b, hpts => by
      simp only [evalGrid, List.sum_cons, Nat.cast_add, add_mul]
      have hx0 : x0 ≤ b := by
        have := hpts 0 (by simp)
        simpa using this
      have hhead : (w : ℝ) * g x0 ≤ (w : ℝ) * g b :=
        mul_le_mul_of_nonneg_left (hg hx0) (Nat.cast_nonneg w)
      have htail : evalGrid (x0 + h) h g ws ≤ (ws.sum : ℝ) * g b := by
        refine evalGrid_le_last hg ws (x0 + h) b (fun j hj => ?_)
        have hj' := hpts (j + 1) (by simp [List.length_cons]; omega)
        have hsh : (x0 + h) + (j : ℝ) * h = x0 + ((j + 1 : ℕ) : ℝ) * h := by push_cast; ring
        rwa [hsh]
      linarith

lemma evalGrid_integrable {α : Type*} [MeasurableSpace α] {mu : Measure α} [IsFiniteMeasure mu] :
    ∀ (ws : List ℕ) (x0 h : ℝ) (f : ℝ → α → ℝ),
      (∀ x, Integrable (f x) mu) →
      Integrable (fun ω => evalGrid x0 h (fun x => f x ω) ws) mu ∧
        (∫ ω, evalGrid x0 h (fun x => f x ω) ws ∂mu) =
          evalGrid x0 h (fun x => ∫ ω, f x ω ∂mu) ws
  | [], _, _, _, _ => ⟨integrable_zero _ _ _, by simp [evalGrid]⟩
  | w :: ws, x0, h, f, hf => by
      obtain ⟨hint, heq⟩ := evalGrid_integrable ws (x0 + h) h f hf
      have hw : Integrable (fun ω => (w : ℝ) * f x0 ω) mu := (hf x0).const_mul (w : ℝ)
      refine ⟨hw.add hint, ?_⟩
      simp only [evalGrid]
      rw [integral_add hw hint, integral_const_mul, heq]

/-- Helper for clamping `condStep lam` so it is globally `Continuous` and `Monotone` in each variable. -/
noncomputable def clampedStep2 (lam a b x0 x1 : ℝ) : ℝ :=
  condStep lam (clampIcc a b x0 + clampIcc a b x1)

noncomputable def clampedStep3 (lam a b x0 x1 x2 : ℝ) : ℝ :=
  condStep lam (clampIcc a b x0 + clampIcc a b x1 + clampIcc a b x2)

lemma clampedStep2_props {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) :
    let a := 1 - lam / 2
    let b := 1 - lam / 3
    Continuous (fun p : ℝ × ℝ => clampedStep2 lam a b p.1 p.2) ∧
    (∀ x0, Monotone (fun x1 => clampedStep2 lam a b x0 x1)) ∧
    (∀ x1, Monotone (fun x0 => clampedStep2 lam a b x0 x1)) ∧
    (∀ x0 x1, clampedStep2 lam a b x0 x1 ∈ Set.Icc a b) := by
  intro a b
  have hab : a ≤ b := by unfold a b; linarith
  have hs_cont : Continuous (fun p : ℝ × ℝ => clampIcc a b p.1 + clampIcc a b p.2) :=
    ((continuous_clampIcc a b).comp continuous_fst).add ((continuous_clampIcc a b).comp continuous_snd)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold clampedStep2 condStep
    refine hs_cont.div (continuous_const.add hs_cont) (fun p => ?_)
    have h1 := (clampIcc_mem_Icc hab p.1).1
    have h2 := (clampIcc_mem_Icc hab p.2).1
    unfold a at h1 h2; linarith
  · intro x0 u v huv
    unfold clampedStep2
    have h1 := (clampIcc_mem_Icc hab x0).1
    have h2 := (clampIcc_mem_Icc hab u).1
    exact condStep_mono hlam0 (by unfold a at h1 h2; linarith)
      (by linarith [monotone_clampIcc a b huv])
  · intro x1 u v huv
    unfold clampedStep2
    have h1 := (clampIcc_mem_Icc hab u).1
    have h2 := (clampIcc_mem_Icc hab x1).1
    exact condStep_mono hlam0 (by unfold a at h1 h2; linarith)
      (by linarith [monotone_clampIcc a b huv])
  · intro x0 x1
    unfold clampedStep2
    have m0 := clampIcc_mem_Icc hab x0
    have m1 := clampIcc_mem_Icc hab x1
    have hlo : condStep lam (2 * a) ≤ condStep lam (clampIcc a b x0 + clampIcc a b x1) :=
      condStep_mono hlam0 (by unfold a; linarith) (by linarith [m0.1, m1.1])
    have hhi : condStep lam (clampIcc a b x0 + clampIcc a b x1) ≤ condStep lam (3 * b) :=
      condStep_mono hlam0 (by unfold a at m0 m1; linarith [m0.1, m1.1]) (by unfold a b at *; linarith [m0.2, m1.2])
    have ha_fix : condStep lam (2 * a) = a := by unfold condStep a; ring
    have hb_fix : condStep lam (3 * b) = b := by unfold condStep b; ring
    exact ⟨by linarith, by linarith⟩

lemma clampedStep3_props {lam : ℝ} (hlam0 : 0 < lam) (hlam2 : lam < 2) :
    let a := 1 - lam / 2
    let b := 1 - lam / 3
    Continuous (fun p : ℝ × ℝ × ℝ => clampedStep3 lam a b p.1 p.2.1 p.2.2) ∧
    (∀ x0 x1, Monotone (fun x2 => clampedStep3 lam a b x0 x1 x2)) ∧
    (∀ x0 x2, Monotone (fun x1 => clampedStep3 lam a b x0 x1 x2)) ∧
    (∀ x1 x2, Monotone (fun x0 => clampedStep3 lam a b x0 x1 x2)) ∧
    (∀ x0 x1 x2, clampedStep3 lam a b x0 x1 x2 ∈ Set.Icc a b) := by
  intro a b
  have hab : a ≤ b := by unfold a b; linarith
  have hs_cont : Continuous (fun p : ℝ × ℝ × ℝ => clampIcc a b p.1 + clampIcc a b p.2.1 + clampIcc a b p.2.2) :=
    (((continuous_clampIcc a b).comp continuous_fst).add
      ((continuous_clampIcc a b).comp (continuous_fst.comp continuous_snd))).add
      ((continuous_clampIcc a b).comp (continuous_snd.comp continuous_snd))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold clampedStep3 condStep
    refine hs_cont.div (continuous_const.add hs_cont) (fun p => ?_)
    have h1 := (clampIcc_mem_Icc hab p.1).1
    have h2 := (clampIcc_mem_Icc hab p.2.1).1
    have h3 := (clampIcc_mem_Icc hab p.2.2).1
    unfold a at h1 h2 h3; linarith
  · intro x0 x1 u v huv
    unfold clampedStep3
    have h1 := (clampIcc_mem_Icc hab x0).1
    have h2 := (clampIcc_mem_Icc hab x1).1
    have h3 := (clampIcc_mem_Icc hab u).1
    exact condStep_mono hlam0 (by unfold a at h1 h2 h3; linarith)
      (by linarith [monotone_clampIcc a b huv])
  · intro x0 x2 u v huv
    unfold clampedStep3
    have h1 := (clampIcc_mem_Icc hab x0).1
    have h2 := (clampIcc_mem_Icc hab u).1
    have h3 := (clampIcc_mem_Icc hab x2).1
    exact condStep_mono hlam0 (by unfold a at h1 h2 h3; linarith)
      (by linarith [monotone_clampIcc a b huv])
  · intro x1 x2 u v huv
    unfold clampedStep3
    have h1 := (clampIcc_mem_Icc hab u).1
    have h2 := (clampIcc_mem_Icc hab x1).1
    have h3 := (clampIcc_mem_Icc hab x2).1
    exact condStep_mono hlam0 (by unfold a at h1 h2 h3; linarith)
      (by linarith [monotone_clampIcc a b huv])
  · intro x0 x1 x2
    unfold clampedStep3
    have m0 := clampIcc_mem_Icc hab x0
    have m1 := clampIcc_mem_Icc hab x1
    have m2 := clampIcc_mem_Icc hab x2
    have hlo : condStep lam (2 * a) ≤ condStep lam (clampIcc a b x0 + clampIcc a b x1 + clampIcc a b x2) :=
      condStep_mono hlam0 (by unfold a; linarith) (by unfold a at *; linarith [m0.1, m1.1, m2.1])
    have hhi : condStep lam (clampIcc a b x0 + clampIcc a b x1 + clampIcc a b x2) ≤ condStep lam (3 * b) :=
      condStep_mono hlam0 (by unfold a at *; linarith [m0.1, m1.1, m2.1]) (by linarith [m0.2, m1.2, m2.2])
    have ha_fix : condStep lam (2 * a) = a := by unfold condStep a; ring
    have hb_fix : condStep lam (3 * b) = b := by unfold condStep b; ring
    exact ⟨by linarith, by linarith⟩

lemma integrable_clamped_mono {α : Type*} [MeasurableSpace α] {mu : Measure α} [IsFiniteMeasure mu]
    {a b : ℝ} (_hab : a ≤ b) {g : ℝ → ℝ} (hg_cont : Continuous g) (hg_mono : Monotone g)
    {Y : α → ℝ} (hY_meas : Measurable Y) (hY_mem : ∀ ω, Y ω ∈ Set.Icc a b) :
    Integrable (fun ω => g (Y ω)) mu := by
  refine integrable_of_measurable_bounded (hg_cont.measurable.comp hY_meas) (C := max |g a| |g b|) (fun ω => ?_)
  have hga : g a ≤ g (Y ω) := hg_mono (hY_mem ω).1
  have hgb : g (Y ω) ≤ g b := hg_mono (hY_mem ω).2
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have := neg_abs_le (g a); linarith [le_max_left |g a| |g b|]
  · have := le_abs_self (g b); linarith [le_max_right |g a| |g b|]

/-- **1-Step Upper Envelope Theorem (`upperEnv_sound`)**:
    If `checkUpperEnv ln ld K M u j2u j3u = true`, then for every `g : ℝ → ℝ` that is
    continuous and nondecreasing on `[a, b] = [1 - λ/2, 1 - λ/3]`,
    `∫ T, g(beta T λ) ∂mu ≤ (1 / M) * evalGrid a h g u`. -/
theorem upperEnv_sound {mu : Measure InfTree23} [IsGWTree23 mu]
    {ln ld K M : ℕ} {u j2u j3u : List ℕ}
    (hchk : checkUpperEnv ln ld K M u j2u j3u = true) :
    let lam : ℝ := (ln : ℝ) / (ld : ℝ)
    let a : ℝ := 1 - lam / 2
    let b : ℝ := 1 - lam / 3
    let h : ℝ := (b - a) / (K : ℝ)
    ∀ {g : ℝ → ℝ}, ContinuousOn g (Set.Icc a b) → MonotoneOn g (Set.Icc a b) →
      (∫ T, g (beta T lam) ∂mu) ≤ (1 / (M : ℝ)) * evalGrid a h g u := by
  simp only [checkUpperEnv, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hchk
  rcases hchk with ⟨hln, hln2, hK, hM, hlen_u, hsum_u, hlen_j2, hlen_j3, hidx2, hidx3, hcdf⟩
  intro lam a b h g hg_cont_on hg_mono_on
  have hld : 0 < ld := by omega
  have hlam0 : 0 < lam := div_pos (Nat.cast_pos.mpr hln) (Nat.cast_pos.mpr hld)
  have hlam2 : lam < 2 := by
    unfold lam
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]
    exact_mod_cast hln2
  have hab : a ≤ b := by unfold a b; linarith
  have hh_pos : 0 < h := div_pos (by unfold a b; linarith) (Nat.cast_pos.mpr hK)
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  set gc : ℝ → ℝ := fun x => g (clampIcc a b x)
  have hgc_cont : Continuous gc := hg_cont_on.comp_continuous (continuous_clampIcc a b) (clampIcc_mem_Icc hab)
  have hgc_mono : Monotone gc := fun x y hxy =>
    hg_mono_on (clampIcc_mem_Icc hab x) (clampIcc_mem_Icc hab y) (monotone_clampIcc a b hxy)
  have hu_last : a + (K : ℝ) * h ≤ b := by
    unfold h
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt hK))]
    linarith
  have hdepth : ∀ (n : ℕ) (f : ℝ → ℝ), Continuous f → Monotone f →
      (∫ T, f (betaAtInit T lam (fun _ => a) n []) ∂mu) ≤ (1 / (M : ℝ)) * evalGrid a h f u := by
    intro n
    induction n with
    | zero =>
        intro f _ hf_mono
        simp only [betaAtInit, integral_const, probReal_univ, one_smul]
        have hge := evalGrid_ge_head (le_of_lt hh_pos) hf_mono u a
        rw [hsum_u] at hge
        rw [one_div, le_inv_mul_iff₀ hM_pos]
        exact hge
    | succ n ih =>
        intro f hf_cont hf_mono
        have ha_mem : 1 - lam / 2 ≤ a ∧ a ≤ 1 - lam / 3 := ⟨le_rfl, hab⟩
        rw [gw_step_expect hlam0 hlam2 ha_mem hf_cont n]
        set φ : InfTree23 → ℝ := fun T => betaAtInit T lam (fun _ => a) n []
        have hφ_mem : ∀ T, φ T ∈ Set.Icc a b :=
          fun T => betaAtInit_in_interval T hlam0 hlam2 (fun _ => ha_mem) n []
        have hφ_meas : Measurable φ := measurable_betaAtInit lam a n []
        obtain ⟨hc2_cont, hc2_m1, hc2_m0, hc2_mem⟩ := clampedStep2_props hlam0 hlam2
        obtain ⟨hc3_cont, hc3_m2, hc3_m1, hc3_m0, hc3_mem⟩ := clampedStep3_props hlam0 hlam2
        have hI2 : (∫ T0, ∫ T1, f (condStep lam (φ T0 + φ T1)) ∂mu ∂mu) ≤
            (1 / (M : ℝ) ^ 2) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul u u) := by
          have heq2 : ∀ T0 T1, f (condStep lam (φ T0 + φ T1)) = f (clampedStep2 lam a b (φ T0) (φ T1)) := by
            intro T0 T1; unfold clampedStep2; rw [clampIcc_eq_self (hφ_mem T0), clampIcc_eq_self (hφ_mem T1)]
          simp_rw [heq2]
          have hstep_T1 : ∀ x0 : ℝ,
              (∫ T1, f (clampedStep2 lam a b x0 (φ T1)) ∂mu) ≤
                (1 / (M : ℝ)) * evalGrid a h (fun x1 => f (clampedStep2 lam a b x0 x1)) u := by
            intro x0
            exact ih (fun x1 => f (clampedStep2 lam a b x0 x1))
              (hf_cont.comp (hc2_cont.comp (continuous_const.prodMk continuous_id)))
              (fun y1 y2 hy => hf_mono (hc2_m1 x0 hy))
          have hint_lhs : Integrable (fun T0 => ∫ T1, f (clampedStep2 lam a b (φ T0) (φ T1)) ∂mu) mu := by
            have hjoint : StronglyMeasurable (Function.uncurry (fun T0 T1 => f (clampedStep2 lam a b (φ T0) (φ T1)))) :=
              ((hf_cont.comp hc2_cont).measurable.comp ((hφ_meas.comp measurable_fst).prodMk (hφ_meas.comp measurable_snd))).stronglyMeasurable
            refine Integrable.of_bound hjoint.integral_prod_right.aestronglyMeasurable (max |f a| |f b|) ?_
            filter_upwards with T0
            have hpt : ∀ᵐ T1 ∂mu, ‖f (clampedStep2 lam a b (φ T0) (φ T1))‖ ≤ max |f a| |f b| := by
              filter_upwards with T1
              rw [Real.norm_eq_abs, abs_le]
              have hm := hc2_mem (φ T0) (φ T1)
              exact ⟨by have := neg_abs_le (f a); linarith [hf_mono hm.1, le_max_left |f a| |f b|],
                     by have := le_abs_self (f b); linarith [hf_mono hm.2, le_max_right |f a| |f b|]⟩
            simpa using norm_integral_le_of_norm_le_const hpt
          have hint_each : ∀ x1 : ℝ, Integrable (fun T0 => f (clampedStep2 lam a b (φ T0) x1)) mu := by
            intro x1
            exact integrable_clamped_mono hab hf_cont hf_mono
              (hc2_cont.measurable.comp (hφ_meas.prodMk measurable_const)) (fun T0 => hc2_mem (φ T0) x1)
          obtain ⟨hint_grid, heq_grid⟩ := evalGrid_integrable u a h (fun x1 T0 => f (clampedStep2 lam a b (φ T0) x1)) hint_each
          have hmono_T0 : (∫ T0, ∫ T1, f (clampedStep2 lam a b (φ T0) (φ T1)) ∂mu ∂mu) ≤
              (1 / (M : ℝ)) * evalGrid a h (fun x1 => ∫ T0, f (clampedStep2 lam a b (φ T0) x1) ∂mu) u := by
            calc (∫ T0, ∫ T1, f (clampedStep2 lam a b (φ T0) (φ T1)) ∂mu ∂mu)
                ≤ ∫ T0, (1 / (M : ℝ)) * evalGrid a h (fun x1 => f (clampedStep2 lam a b (φ T0) x1)) u ∂mu :=
                  integral_mono hint_lhs (hint_grid.const_mul _) (fun T0 => hstep_T1 (φ T0))
              _ = (1 / (M : ℝ)) * evalGrid a h (fun x1 => ∫ T0, f (clampedStep2 lam a b (φ T0) x1) ∂mu) u := by
                  rw [integral_const_mul, heq_grid]
          have hstep_T0 : evalGrid a h (fun x1 => ∫ T0, f (clampedStep2 lam a b (φ T0) x1) ∂mu) u ≤
              evalGrid a h (fun x1 => (1 / (M : ℝ)) * evalGrid a h (fun x0 => f (clampedStep2 lam a b x0 x1)) u) u := by
            refine evalGrid_mono_pts u a (fun j1 _ => ?_)
            exact ih (fun x0 => f (clampedStep2 lam a b x0 (a + (j1 : ℝ) * h)))
              (hf_cont.comp (hc2_cont.comp (continuous_id.prodMk continuous_const)))
              (fun y1 y2 hy => hf_mono (hc2_m0 _ hy))
          have hunclamp : evalGrid a h (fun x1 => evalGrid a h (fun x0 => f (clampedStep2 lam a b x0 x1)) u) u =
              evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul u u) := by
            have h2a : 2 * a = a + a := by ring
            rw [h2a, evalGrid_polyMul h (fun s => f (condStep lam s)) u a a u]
            refine evalGrid_congr u 0 (fun j1 _ hj1 => ?_)
            simp only [Nat.sub_zero]
            refine evalGrid_congr u 0 (fun j0 _ hj0 => ?_)
            simp only [Nat.sub_zero]
            have hx1 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j1) (by omega) hu_last
            have hx0 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j0) (by omega) hu_last
            unfold clampedStep2
            rw [clampIcc_eq_self hx0, clampIcc_eq_self hx1, add_comm (a + (j0 : ℝ) * h)]
          rw [evalGrid_const_mul] at hstep_T0
          calc (∫ T0, ∫ T1, f (clampedStep2 lam a b (φ T0) (φ T1)) ∂mu ∂mu)
              ≤ (1 / (M : ℝ)) * ((1 / (M : ℝ)) * evalGrid a h (fun x1 => evalGrid a h (fun x0 => f (clampedStep2 lam a b x0 x1)) u) u) :=
                hmono_T0.trans (mul_le_mul_of_nonneg_left hstep_T0 (by positivity))
            _ = (1 / (M : ℝ) ^ 2) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul u u) := by
                rw [hunclamp]; ring
        have hI3 : (∫ T0, ∫ T1, ∫ T2, f (condStep lam (φ T0 + φ T1 + φ T2)) ∂mu ∂mu ∂mu) ≤
            (1 / (M : ℝ) ^ 3) * evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul u u) u) := by
          have heq3 : ∀ T0 T1 T2, f (condStep lam (φ T0 + φ T1 + φ T2)) = f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) := by
            intro T0 T1 T2; unfold clampedStep3; rw [clampIcc_eq_self (hφ_mem T0), clampIcc_eq_self (hφ_mem T1), clampIcc_eq_self (hφ_mem T2)]
          simp_rw [heq3]
          have hstep_T2 : ∀ x0 x1 : ℝ,
              (∫ T2, f (clampedStep3 lam a b x0 x1 (φ T2)) ∂mu) ≤
                (1 / (M : ℝ)) * evalGrid a h (fun x2 => f (clampedStep3 lam a b x0 x1 x2)) u := by
            intro x0 x1
            exact ih (fun x2 => f (clampedStep3 lam a b x0 x1 x2))
              (hf_cont.comp (hc3_cont.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))))
              (fun y1 y2 hy => hf_mono (hc3_m2 x0 x1 hy))
          have hstep_T12 : ∀ x0 : ℝ,
              (∫ T1, ∫ T2, f (clampedStep3 lam a b x0 (φ T1) (φ T2)) ∂mu ∂mu) ≤
                (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => f (clampedStep3 lam a b x0 x1 x2)) u) u := by
            intro x0
            have hint_lhs1 : Integrable (fun T1 => ∫ T2, f (clampedStep3 lam a b x0 (φ T1) (φ T2)) ∂mu) mu := by
              have hjoint : StronglyMeasurable (Function.uncurry (fun T1 T2 => f (clampedStep3 lam a b x0 (φ T1) (φ T2)))) :=
                ((hf_cont.comp hc3_cont).measurable.comp (measurable_const.prodMk ((hφ_meas.comp measurable_fst).prodMk (hφ_meas.comp measurable_snd)))).stronglyMeasurable
              refine Integrable.of_bound hjoint.integral_prod_right.aestronglyMeasurable (max |f a| |f b|) ?_
              filter_upwards with T1
              have hpt : ∀ᵐ T2 ∂mu, ‖f (clampedStep3 lam a b x0 (φ T1) (φ T2))‖ ≤ max |f a| |f b| := by
                filter_upwards with T2
                rw [Real.norm_eq_abs, abs_le]
                have hm := hc3_mem x0 (φ T1) (φ T2)
                exact ⟨by have := neg_abs_le (f a); linarith [hf_mono hm.1, le_max_left |f a| |f b|],
                       by have := le_abs_self (f b); linarith [hf_mono hm.2, le_max_right |f a| |f b|]⟩
              simpa using norm_integral_le_of_norm_le_const hpt
            have hint_each1 : ∀ x2 : ℝ, Integrable (fun T1 => f (clampedStep3 lam a b x0 (φ T1) x2)) mu := by
              intro x2
              exact integrable_clamped_mono hab hf_cont hf_mono
                (hc3_cont.measurable.comp (measurable_const.prodMk (hφ_meas.prodMk measurable_const)))
                (fun T1 => hc3_mem x0 (φ T1) x2)
            obtain ⟨hint_g1, heq_g1⟩ := evalGrid_integrable u a h (fun x2 T1 => f (clampedStep3 lam a b x0 (φ T1) x2)) hint_each1
            have hm1 : (∫ T1, ∫ T2, f (clampedStep3 lam a b x0 (φ T1) (φ T2)) ∂mu ∂mu) ≤
                (1 / (M : ℝ)) * evalGrid a h (fun x2 => ∫ T1, f (clampedStep3 lam a b x0 (φ T1) x2) ∂mu) u := by
              calc (∫ T1, ∫ T2, f (clampedStep3 lam a b x0 (φ T1) (φ T2)) ∂mu ∂mu)
                  ≤ ∫ T1, (1 / (M : ℝ)) * evalGrid a h (fun x2 => f (clampedStep3 lam a b x0 (φ T1) x2)) u ∂mu :=
                    integral_mono hint_lhs1 (hint_g1.const_mul _) (fun T1 => hstep_T2 x0 (φ T1))
                _ = (1 / (M : ℝ)) * evalGrid a h (fun x2 => ∫ T1, f (clampedStep3 lam a b x0 (φ T1) x2) ∂mu) u := by
                    rw [integral_const_mul, heq_g1]
            have hm2 : evalGrid a h (fun x2 => ∫ T1, f (clampedStep3 lam a b x0 (φ T1) x2) ∂mu) u ≤
                evalGrid a h (fun x2 => (1 / (M : ℝ)) * evalGrid a h (fun x1 => f (clampedStep3 lam a b x0 x1 x2)) u) u := by
              refine evalGrid_mono_pts u a (fun j2 _ => ?_)
              exact ih (fun x1 => f (clampedStep3 lam a b x0 x1 (a + (j2 : ℝ) * h)))
                (hf_cont.comp (hc3_cont.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))))
                (fun y1 y2 hy => hf_mono (hc3_m1 x0 _ hy))
            rw [evalGrid_const_mul] at hm2
            calc (∫ T1, ∫ T2, f (clampedStep3 lam a b x0 (φ T1) (φ T2)) ∂mu ∂mu)
                ≤ (1 / (M : ℝ)) * ((1 / (M : ℝ)) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => f (clampedStep3 lam a b x0 x1 x2)) u) u) :=
                  hm1.trans (mul_le_mul_of_nonneg_left hm2 (by positivity))
              _ = _ := by ring
          have hint_lhs0 : Integrable (fun T0 => ∫ T1, ∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu ∂mu) mu := by
            have hjoint2 : StronglyMeasurable (Function.uncurry (fun (p : InfTree23 × InfTree23) (T2 : InfTree23) =>
                f (clampedStep3 lam a b (φ p.1) (φ p.2) (φ T2)))) :=
              ((hf_cont.comp hc3_cont).measurable.comp ((hφ_meas.comp (measurable_fst.comp measurable_fst)).prodMk
                ((hφ_meas.comp (measurable_snd.comp measurable_fst)).prodMk (hφ_meas.comp measurable_snd)))).stronglyMeasurable
            have hinner_sm : StronglyMeasurable (Function.uncurry (fun T0 T1 =>
                ∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu)) :=
              hjoint2.integral_prod_right
            refine Integrable.of_bound hinner_sm.integral_prod_right.aestronglyMeasurable (max |f a| |f b|) ?_
            filter_upwards with T0
            have hpt1 : ∀ᵐ T1 ∂mu, ‖∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu‖ ≤ max |f a| |f b| := by
              filter_upwards with T1
              have hpt2 : ∀ᵐ T2 ∂mu, ‖f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2))‖ ≤ max |f a| |f b| := by
                filter_upwards with T2
                rw [Real.norm_eq_abs, abs_le]
                have hm := hc3_mem (φ T0) (φ T1) (φ T2)
                exact ⟨by have := neg_abs_le (f a); linarith [hf_mono hm.1, le_max_left |f a| |f b|],
                       by have := le_abs_self (f b); linarith [hf_mono hm.2, le_max_right |f a| |f b|]⟩
              simpa using norm_integral_le_of_norm_le_const hpt2
            simpa using norm_integral_le_of_norm_le_const hpt1
          have hint_each0 : ∀ x2 : ℝ, Integrable (fun T0 => evalGrid a h (fun x1 => f (clampedStep3 lam a b (φ T0) x1 x2)) u) mu := by
            intro x2
            refine (evalGrid_integrable u a h (fun x1 T0 => f (clampedStep3 lam a b (φ T0) x1 x2)) (fun x1 => ?_)).1
            exact integrable_clamped_mono hab hf_cont hf_mono
              (hc3_cont.measurable.comp (hφ_meas.prodMk (measurable_const.prodMk measurable_const)))
              (fun T0 => hc3_mem (φ T0) x1 x2)
          obtain ⟨hint_g0, heq_g0⟩ := evalGrid_integrable u a h
            (fun x2 T0 => evalGrid a h (fun x1 => f (clampedStep3 lam a b (φ T0) x1 x2)) u) hint_each0
          have hm0 : (∫ T0, ∫ T1, ∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu ∂mu ∂mu) ≤
              (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => ∫ T0, f (clampedStep3 lam a b (φ T0) x1 x2) ∂mu) u) u := by
            calc (∫ T0, ∫ T1, ∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu ∂mu ∂mu)
                ≤ ∫ T0, (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => f (clampedStep3 lam a b (φ T0) x1 x2)) u) u ∂mu :=
                  integral_mono hint_lhs0 (hint_g0.const_mul _) (fun T0 => hstep_T12 (φ T0))
              _ = (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => ∫ T0, f (clampedStep3 lam a b (φ T0) x1 x2) ∂mu) u) u := by
                  rw [integral_const_mul, heq_g0]
                  congr 1
                  refine evalGrid_congr u 0 (fun j2 _ _ => ?_)
                  simp only [Nat.sub_zero]
                  exact (evalGrid_integrable u a h (fun x1 T0 => f (clampedStep3 lam a b (φ T0) x1 (a + (j2 : ℝ) * h))) (fun x1 =>
                    integrable_clamped_mono hab hf_cont hf_mono
                      (hc3_cont.measurable.comp (hφ_meas.prodMk (measurable_const.prodMk measurable_const)))
                      (fun T0 => hc3_mem (φ T0) x1 _))).2
          have hm0_ih : evalGrid a h (fun x2 => evalGrid a h (fun x1 => ∫ T0, f (clampedStep3 lam a b (φ T0) x1 x2) ∂mu) u) u ≤
              evalGrid a h (fun x2 => evalGrid a h (fun x1 => (1 / (M : ℝ)) * evalGrid a h (fun x0 => f (clampedStep3 lam a b x0 x1 x2)) u) u) u := by
            refine evalGrid_mono_pts u a (fun j2 _ => ?_)
            refine evalGrid_mono_pts u a (fun j1 _ => ?_)
            exact ih (fun x0 => f (clampedStep3 lam a b x0 (a + (j1 : ℝ) * h) (a + (j2 : ℝ) * h)))
              (hf_cont.comp (hc3_cont.comp (continuous_id.prodMk (continuous_const.prodMk continuous_const))))
              (fun y1 y2 hy => hf_mono (hc3_m0 _ _ hy))
          have hpull : evalGrid a h (fun x2 => evalGrid a h (fun x1 => (1 / (M : ℝ)) * evalGrid a h (fun x0 => f (clampedStep3 lam a b x0 x1 x2)) u) u) u =
              (1 / (M : ℝ)) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => evalGrid a h (fun x0 => f (clampedStep3 lam a b x0 x1 x2)) u) u) u := by
            simp_rw [evalGrid_const_mul]
          have hunclamp3 : evalGrid a h (fun x2 => evalGrid a h (fun x1 => evalGrid a h (fun x0 => f (clampedStep3 lam a b x0 x1 x2)) u) u) u =
              evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul u u) u) := by
            have h3a : 3 * a = (a + a) + a := by ring
            rw [h3a, evalGrid_polyMul h (fun s => f (condStep lam s)) (polyMul u u) (a + a) a u]
            have hcomm : ∀ (F : ℝ → ℝ → ℝ) (xs ys : List ℕ) (x0 y0 : ℝ),
                evalGrid x0 h (fun x => evalGrid y0 h (fun y => F x y) ys) xs =
                  evalGrid y0 h (fun y => evalGrid x0 h (fun x => F x y) xs) ys := by
              intro F xs
              induction xs with
              | nil => intro ys x0 y0; simp [evalGrid, evalGrid_const]
              | cons w ws ihx =>
                  intro ys x0 y0
                  simp only [evalGrid]
                  rw [ihx ys (x0 + h) y0, ← evalGrid_const_mul, ← evalGrid_add_func]
            rw [hcomm (fun s12 x2 => f (condStep lam (s12 + x2))) (polyMul u u) u (a + a) a]
            refine evalGrid_congr u 0 (fun j2 _ hj2 => ?_)
            simp only [Nat.sub_zero]
            rw [evalGrid_polyMul h (fun s12 => f (condStep lam (s12 + (a + (j2 : ℝ) * h)))) u a a u]
            refine evalGrid_congr u 0 (fun j1 _ hj1 => ?_)
            simp only [Nat.sub_zero]
            refine evalGrid_congr u 0 (fun j0 _ hj0 => ?_)
            simp only [Nat.sub_zero]
            have hx2 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j2) (by omega) hu_last
            have hx1 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j1) (by omega) hu_last
            have hx0 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j0) (by omega) hu_last
            unfold clampedStep3
            rw [clampIcc_eq_self hx0, clampIcc_eq_self hx1, clampIcc_eq_self hx2]
            congr 2; ring
          rw [hpull, hunclamp3] at hm0_ih
          calc (∫ T0, ∫ T1, ∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu ∂mu ∂mu)
              ≤ (1 / (M : ℝ) ^ 2) * ((1 / (M : ℝ)) * evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul u u) u)) :=
                hm0.trans (mul_le_mul_of_nonneg_left hm0_ih (by positivity))
            _ = _ := by ring
        obtain ⟨hsr2, hev2⟩ := checkIndexUpper_sound hln hln2 hK (by norm_num : 0 < 2) hf_mono j2u (polyMul u u) 0 0 hlen_j2 (Nat.zero_le K) hidx2
        obtain ⟨hsr3, hev3⟩ := checkIndexUpper_sound hln hln2 hK (by norm_num : 0 < 3) hf_mono j3u (polyMul (polyMul u u) u) 0 0 hlen_j3 (Nat.zero_le K) hidx3
        simp only [Nat.cast_ofNat, Nat.cast_zero, zero_mul, add_zero] at hev2 hev3
        have hb2 := evalGrid_bucketSorted a h f 0 (K + 1) 0 (List.zip j2u (polyMul u u)) (Nat.succ_pos K) (by simpa using hsr2)
        have hb3 := evalGrid_bucketSorted a h f 0 (K + 1) 0 (List.zip j3u (polyMul (polyMul u u) u)) (Nat.succ_pos K) (by simpa using hsr3)
        simp only [Nat.cast_zero, zero_mul, add_zero] at hb2 hb3
        set push := addLists (scaleList M (bucketSorted 0 (K + 1) 0 (List.zip j2u (polyMul u u))))
          (bucketSorted 0 (K + 1) 0 (List.zip j3u (polyMul (polyMul u u) u)))
        have hpush_eval : evalGrid a h f push =
            (M : ℝ) * evalPairs a h f (List.zip j2u (polyMul u u)) +
              evalPairs a h f (List.zip j3u (polyMul (polyMul u u) u)) := by
          unfold push
          rw [evalGrid_addLists, evalGrid_scaleList, hb2, hb3]; ring
        have habel := evalGrid_le_of_checkCdfLe (x0 := a) (le_of_lt hh_pos) hf_mono hcdf
        rw [evalGrid_scaleList, hpush_eval] at habel
        push_cast at habel
        have hM3_pos : (0 : ℝ) < 2 * (M : ℝ) ^ 3 := by positivity
        have hcomb : (1 / 2 : ℝ) * ((1 / (M : ℝ) ^ 2) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul u u)) +
            (1 / 2 : ℝ) * ((1 / (M : ℝ) ^ 3) * evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul u u) u)) ≤
            (1 / (M : ℝ)) * evalGrid a h f u := by
          have hstep_sum : (M : ℝ) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul u u) +
              evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul u u) u) ≤
              (2 * (M : ℝ) * (M : ℝ)) * evalGrid a h f u := by
            have := mul_le_mul_of_nonneg_left hev2 (le_of_lt hM_pos)
            linarith
          have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_pos
          rw [show (1 / 2 : ℝ) * ((1 / (M : ℝ) ^ 2) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul u u)) +
              (1 / 2 : ℝ) * ((1 / (M : ℝ) ^ 3) * evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul u u) u)) =
              ((M : ℝ) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul u u) +
                evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul u u) u)) / (2 * (M : ℝ) ^ 3) by
                field_simp [hM_ne]]
          rw [div_le_iff₀ hM3_pos]
          have hrhs : (1 / (M : ℝ)) * evalGrid a h f u * (2 * (M : ℝ) ^ 3) =
              (2 * (M : ℝ) * (M : ℝ)) * evalGrid a h f u := by
            field_simp [hM_ne]
          linarith
        linarith
  have hlim_pt : ∀ T : InfTree23,
      Filter.Tendsto (fun n => gc (betaAtInit T lam (fun _ => a) n [])) Filter.atTop (nhds (gc (beta T lam))) := by
    intro T
    refine (hgc_cont.tendsto _).comp ?_
    rw [Metric.tendsto_atTop]
    intro eps heps
    have hq0 : 0 ≤ lam / 2 := by linarith
    have hq1 : lam / 2 < 1 := by linarith
    have hpow : Filter.Tendsto (fun n : ℕ => (lam / 2) ^ n * ((b - a) / a) * b) Filter.atTop (nhds 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ((b - a) / a)).mul_const b
    rw [Metric.tendsto_atTop] at hpow
    obtain ⟨N, hN⟩ := hpow eps heps
    refine ⟨N, fun n hn => ?_⟩
    have happrox := betaAtInit_uniform_approx T hlam0 hlam2 ⟨le_rfl, hab⟩ n
    have hN' := hN n hn
    rw [Real.dist_eq, sub_zero] at hN'
    rw [Real.dist_eq]
    exact lt_of_le_of_lt happrox (lt_of_le_of_lt (le_abs_self _) hN')
  have hdom : Filter.Tendsto (fun n => ∫ T, gc (betaAtInit T lam (fun _ => a) n []) ∂mu)
      Filter.atTop (nhds (∫ T, gc (beta T lam) ∂mu)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => max |gc a| |gc b|)
      (fun n => (hgc_cont.measurable.comp (measurable_betaAtInit lam a n [])).stronglyMeasurable.aestronglyMeasurable)
      (integrable_const _) (fun n => ?_) (Filter.Eventually.of_forall hlim_pt)
    filter_upwards with T
    rw [Real.norm_eq_abs, abs_le]
    have hm := betaAtInit_in_interval T hlam0 hlam2 (fun _ => ⟨le_rfl, hab⟩) n []
    exact ⟨by have := neg_abs_le (gc a); linarith [hgc_mono hm.1, le_max_left |gc a| |gc b|],
           by have := le_abs_self (gc b); linarith [hgc_mono hm.2, le_max_right |gc a| |gc b|]⟩
  have hgc_lim : (∫ T, gc (beta T lam) ∂mu) ≤ (1 / (M : ℝ)) * evalGrid a h gc u :=
    le_of_tendsto_of_tendsto hdom tendsto_const_nhds (Filter.Eventually.of_forall (fun n => hdepth n gc hgc_cont hgc_mono))
  have hlhs_eq : (∫ T, g (beta T lam) ∂mu) = (∫ T, gc (beta T lam) ∂mu) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun T => ?_))
    exact (congrArg g (clampIcc_eq_self (lemma_4_1_support T hlam0 hlam2))).symm
  have hrhs_eq : evalGrid a h gc u = evalGrid a h g u := by
    refine evalGrid_congr u 0 (fun j _ hj => ?_)
    simp only [Nat.sub_zero]
    have hxj := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j) (by omega) hu_last
    exact congrArg g (clampIcc_eq_self hxj)
  rw [hlhs_eq, ← hrhs_eq]
  exact hgc_lim

/-- **1-Step Lower Envelope Theorem (`lowerEnv_sound`)**:
    If `checkLowerEnv ln ld K M l j2l j3l = true`, then for every `g : ℝ → ℝ` that is
    continuous and nondecreasing on `[a, b] = [1 - λ/2, 1 - λ/3]`,
    `(1 / M) * evalGrid a h g l ≤ ∫ T, g(beta T λ) ∂mu`. -/
theorem lowerEnv_sound {mu : Measure InfTree23} [IsGWTree23 mu]
    {ln ld K M : ℕ} {l j2l j3l : List ℕ}
    (hchk : checkLowerEnv ln ld K M l j2l j3l = true) :
    let lam : ℝ := (ln : ℝ) / (ld : ℝ)
    let a : ℝ := 1 - lam / 2
    let b : ℝ := 1 - lam / 3
    let h : ℝ := (b - a) / (K : ℝ)
    ∀ {g : ℝ → ℝ}, ContinuousOn g (Set.Icc a b) → MonotoneOn g (Set.Icc a b) →
      (1 / (M : ℝ)) * evalGrid a h g l ≤ (∫ T, g (beta T lam) ∂mu) := by
  simp only [checkLowerEnv, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hchk
  rcases hchk with ⟨hln, hln2, hK, hM, hlen_l, hsum_l, hlen_j2, hlen_j3, hidx2, hidx3, hcdf⟩
  intro lam a b h g hg_cont_on hg_mono_on
  have hld : 0 < ld := by omega
  have hlam0 : 0 < lam := div_pos (Nat.cast_pos.mpr hln) (Nat.cast_pos.mpr hld)
  have hlam2 : lam < 2 := by
    unfold lam
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]
    exact_mod_cast hln2
  have hab : a ≤ b := by unfold a b; linarith
  have hh_pos : 0 < h := div_pos (by unfold a b; linarith) (Nat.cast_pos.mpr hK)
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  set gc : ℝ → ℝ := fun x => g (clampIcc a b x)
  have hgc_cont : Continuous gc := hg_cont_on.comp_continuous (continuous_clampIcc a b) (clampIcc_mem_Icc hab)
  have hgc_mono : Monotone gc := fun x y hxy =>
    hg_mono_on (clampIcc_mem_Icc hab x) (clampIcc_mem_Icc hab y) (monotone_clampIcc a b hxy)
  have hl_last : a + (K : ℝ) * h ≤ b := by
    unfold h
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt hK))]
    linarith
  have hdepth : ∀ (n : ℕ) (f : ℝ → ℝ), Continuous f → Monotone f →
      (1 / (M : ℝ)) * evalGrid a h f l ≤ (∫ T, f (betaAtInit T lam (fun _ => b) n []) ∂mu) := by
    intro n
    induction n with
    | zero =>
        intro f _ hf_mono
        simp only [betaAtInit, integral_const, probReal_univ, one_smul]
        have hle := evalGrid_le_last (h := h) hf_mono l a b (fun j hj =>
          (grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j) (by omega) hl_last).2)
        rw [hsum_l] at hle
        rw [one_div, inv_mul_le_iff₀ hM_pos]
        exact hle
    | succ n ih =>
        intro f hf_cont hf_mono
        have hb_mem : 1 - lam / 2 ≤ b ∧ b ≤ 1 - lam / 3 := ⟨hab, le_rfl⟩
        rw [gw_step_expect hlam0 hlam2 hb_mem hf_cont n]
        set φ : InfTree23 → ℝ := fun T => betaAtInit T lam (fun _ => b) n []
        have hφ_mem : ∀ T, φ T ∈ Set.Icc a b :=
          fun T => betaAtInit_in_interval T hlam0 hlam2 (fun _ => hb_mem) n []
        have hφ_meas : Measurable φ := measurable_betaAtInit lam b n []
        obtain ⟨hc2_cont, hc2_m1, hc2_m0, hc2_mem⟩ := clampedStep2_props hlam0 hlam2
        obtain ⟨hc3_cont, hc3_m2, hc3_m1, hc3_m0, hc3_mem⟩ := clampedStep3_props hlam0 hlam2
        have hI2 : (1 / (M : ℝ) ^ 2) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul l l) ≤
            (∫ T0, ∫ T1, f (condStep lam (φ T0 + φ T1)) ∂mu ∂mu) := by
          have heq2 : ∀ T0 T1, f (condStep lam (φ T0 + φ T1)) = f (clampedStep2 lam a b (φ T0) (φ T1)) := by
            intro T0 T1; unfold clampedStep2; rw [clampIcc_eq_self (hφ_mem T0), clampIcc_eq_self (hφ_mem T1)]
          simp_rw [heq2]
          have hstep_T1 : ∀ x0 : ℝ,
              (1 / (M : ℝ)) * evalGrid a h (fun x1 => f (clampedStep2 lam a b x0 x1)) l ≤
                (∫ T1, f (clampedStep2 lam a b x0 (φ T1)) ∂mu) := by
            intro x0
            exact ih (fun x1 => f (clampedStep2 lam a b x0 x1))
              (hf_cont.comp (hc2_cont.comp (continuous_const.prodMk continuous_id)))
              (fun y1 y2 hy => hf_mono (hc2_m1 x0 hy))
          have hint_rhs : Integrable (fun T0 => ∫ T1, f (clampedStep2 lam a b (φ T0) (φ T1)) ∂mu) mu := by
            have hjoint : StronglyMeasurable (Function.uncurry (fun T0 T1 => f (clampedStep2 lam a b (φ T0) (φ T1)))) :=
              ((hf_cont.comp hc2_cont).measurable.comp ((hφ_meas.comp measurable_fst).prodMk (hφ_meas.comp measurable_snd))).stronglyMeasurable
            refine Integrable.of_bound hjoint.integral_prod_right.aestronglyMeasurable (max |f a| |f b|) ?_
            filter_upwards with T0
            have hpt : ∀ᵐ T1 ∂mu, ‖f (clampedStep2 lam a b (φ T0) (φ T1))‖ ≤ max |f a| |f b| := by
              filter_upwards with T1
              rw [Real.norm_eq_abs, abs_le]
              have hm := hc2_mem (φ T0) (φ T1)
              exact ⟨by have := neg_abs_le (f a); linarith [hf_mono hm.1, le_max_left |f a| |f b|],
                     by have := le_abs_self (f b); linarith [hf_mono hm.2, le_max_right |f a| |f b|]⟩
            simpa using norm_integral_le_of_norm_le_const hpt
          have hint_each : ∀ x1 : ℝ, Integrable (fun T0 => f (clampedStep2 lam a b (φ T0) x1)) mu := by
            intro x1
            exact integrable_clamped_mono hab hf_cont hf_mono
              (hc2_cont.measurable.comp (hφ_meas.prodMk measurable_const)) (fun T0 => hc2_mem (φ T0) x1)
          obtain ⟨hint_grid, heq_grid⟩ := evalGrid_integrable l a h (fun x1 T0 => f (clampedStep2 lam a b (φ T0) x1)) hint_each
          have hmono_T0 : (1 / (M : ℝ)) * evalGrid a h (fun x1 => ∫ T0, f (clampedStep2 lam a b (φ T0) x1) ∂mu) l ≤
              (∫ T0, ∫ T1, f (clampedStep2 lam a b (φ T0) (φ T1)) ∂mu ∂mu) := by
            calc (1 / (M : ℝ)) * evalGrid a h (fun x1 => ∫ T0, f (clampedStep2 lam a b (φ T0) x1) ∂mu) l
                = ∫ T0, (1 / (M : ℝ)) * evalGrid a h (fun x1 => f (clampedStep2 lam a b (φ T0) x1)) l ∂mu := by
                  rw [integral_const_mul, heq_grid]
              _ ≤ (∫ T0, ∫ T1, f (clampedStep2 lam a b (φ T0) (φ T1)) ∂mu ∂mu) :=
                  integral_mono (hint_grid.const_mul _) hint_rhs (fun T0 => hstep_T1 (φ T0))
          have hstep_T0 : evalGrid a h (fun x1 => (1 / (M : ℝ)) * evalGrid a h (fun x0 => f (clampedStep2 lam a b x0 x1)) l) l ≤
              evalGrid a h (fun x1 => ∫ T0, f (clampedStep2 lam a b (φ T0) x1) ∂mu) l := by
            refine evalGrid_mono_pts l a (fun j1 _ => ?_)
            exact ih (fun x0 => f (clampedStep2 lam a b x0 (a + (j1 : ℝ) * h)))
              (hf_cont.comp (hc2_cont.comp (continuous_id.prodMk continuous_const)))
              (fun y1 y2 hy => hf_mono (hc2_m0 _ hy))
          have hunclamp : evalGrid a h (fun x1 => evalGrid a h (fun x0 => f (clampedStep2 lam a b x0 x1)) l) l =
              evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul l l) := by
            have h2a : 2 * a = a + a := by ring
            rw [h2a, evalGrid_polyMul h (fun s => f (condStep lam s)) l a a l]
            refine evalGrid_congr l 0 (fun j1 _ hj1 => ?_)
            simp only [Nat.sub_zero]
            refine evalGrid_congr l 0 (fun j0 _ hj0 => ?_)
            simp only [Nat.sub_zero]
            have hx1 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j1) (by omega) hl_last
            have hx0 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j0) (by omega) hl_last
            unfold clampedStep2
            rw [clampIcc_eq_self hx0, clampIcc_eq_self hx1, add_comm (a + (j0 : ℝ) * h)]
          rw [evalGrid_const_mul, hunclamp] at hstep_T0
          calc (1 / (M : ℝ) ^ 2) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul l l)
              = (1 / (M : ℝ)) * ((1 / (M : ℝ)) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul l l)) := by ring
            _ ≤ (1 / (M : ℝ)) * evalGrid a h (fun x1 => ∫ T0, f (clampedStep2 lam a b (φ T0) x1) ∂mu) l :=
                mul_le_mul_of_nonneg_left hstep_T0 (by positivity)
            _ ≤ _ := hmono_T0
        have hI3 : (1 / (M : ℝ) ^ 3) * evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul l l) l) ≤
            (∫ T0, ∫ T1, ∫ T2, f (condStep lam (φ T0 + φ T1 + φ T2)) ∂mu ∂mu ∂mu) := by
          have heq3 : ∀ T0 T1 T2, f (condStep lam (φ T0 + φ T1 + φ T2)) = f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) := by
            intro T0 T1 T2; unfold clampedStep3; rw [clampIcc_eq_self (hφ_mem T0), clampIcc_eq_self (hφ_mem T1), clampIcc_eq_self (hφ_mem T2)]
          simp_rw [heq3]
          have hstep_T2 : ∀ x0 x1 : ℝ,
              (1 / (M : ℝ)) * evalGrid a h (fun x2 => f (clampedStep3 lam a b x0 x1 x2)) l ≤
                (∫ T2, f (clampedStep3 lam a b x0 x1 (φ T2)) ∂mu) := by
            intro x0 x1
            exact ih (fun x2 => f (clampedStep3 lam a b x0 x1 x2))
              (hf_cont.comp (hc3_cont.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))))
              (fun y1 y2 hy => hf_mono (hc3_m2 x0 x1 hy))
          have hstep_T12 : ∀ x0 : ℝ,
              (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => f (clampedStep3 lam a b x0 x1 x2)) l) l ≤
                (∫ T1, ∫ T2, f (clampedStep3 lam a b x0 (φ T1) (φ T2)) ∂mu ∂mu) := by
            intro x0
            have hint_rhs1 : Integrable (fun T1 => ∫ T2, f (clampedStep3 lam a b x0 (φ T1) (φ T2)) ∂mu) mu := by
              have hjoint : StronglyMeasurable (Function.uncurry (fun T1 T2 => f (clampedStep3 lam a b x0 (φ T1) (φ T2)))) :=
                ((hf_cont.comp hc3_cont).measurable.comp (measurable_const.prodMk ((hφ_meas.comp measurable_fst).prodMk (hφ_meas.comp measurable_snd)))).stronglyMeasurable
              refine Integrable.of_bound hjoint.integral_prod_right.aestronglyMeasurable (max |f a| |f b|) ?_
              filter_upwards with T1
              have hpt : ∀ᵐ T2 ∂mu, ‖f (clampedStep3 lam a b x0 (φ T1) (φ T2))‖ ≤ max |f a| |f b| := by
                filter_upwards with T2
                rw [Real.norm_eq_abs, abs_le]
                have hm := hc3_mem x0 (φ T1) (φ T2)
                exact ⟨by have := neg_abs_le (f a); linarith [hf_mono hm.1, le_max_left |f a| |f b|],
                       by have := le_abs_self (f b); linarith [hf_mono hm.2, le_max_right |f a| |f b|]⟩
              simpa using norm_integral_le_of_norm_le_const hpt
            have hint_each1 : ∀ x2 : ℝ, Integrable (fun T1 => f (clampedStep3 lam a b x0 (φ T1) x2)) mu := by
              intro x2
              exact integrable_clamped_mono hab hf_cont hf_mono
                (hc3_cont.measurable.comp (measurable_const.prodMk (hφ_meas.prodMk measurable_const)))
                (fun T1 => hc3_mem x0 (φ T1) x2)
            obtain ⟨hint_g1, heq_g1⟩ := evalGrid_integrable l a h (fun x2 T1 => f (clampedStep3 lam a b x0 (φ T1) x2)) hint_each1
            have hm1 : (1 / (M : ℝ)) * evalGrid a h (fun x2 => ∫ T1, f (clampedStep3 lam a b x0 (φ T1) x2) ∂mu) l ≤
                (∫ T1, ∫ T2, f (clampedStep3 lam a b x0 (φ T1) (φ T2)) ∂mu ∂mu) := by
              calc (1 / (M : ℝ)) * evalGrid a h (fun x2 => ∫ T1, f (clampedStep3 lam a b x0 (φ T1) x2) ∂mu) l
                  = ∫ T1, (1 / (M : ℝ)) * evalGrid a h (fun x2 => f (clampedStep3 lam a b x0 (φ T1) x2)) l ∂mu := by
                    rw [integral_const_mul, heq_g1]
                _ ≤ _ := integral_mono (hint_g1.const_mul _) hint_rhs1 (fun T1 => hstep_T2 x0 (φ T1))
            have hm2 : evalGrid a h (fun x2 => (1 / (M : ℝ)) * evalGrid a h (fun x1 => f (clampedStep3 lam a b x0 x1 x2)) l) l ≤
                evalGrid a h (fun x2 => ∫ T1, f (clampedStep3 lam a b x0 (φ T1) x2) ∂mu) l := by
              refine evalGrid_mono_pts l a (fun j2 _ => ?_)
              exact ih (fun x1 => f (clampedStep3 lam a b x0 x1 (a + (j2 : ℝ) * h)))
                (hf_cont.comp (hc3_cont.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))))
                (fun y1 y2 hy => hf_mono (hc3_m1 x0 _ hy))
            rw [evalGrid_const_mul] at hm2
            calc (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => f (clampedStep3 lam a b x0 x1 x2)) l) l
                = (1 / (M : ℝ)) * ((1 / (M : ℝ)) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => f (clampedStep3 lam a b x0 x1 x2)) l) l) := by ring
              _ ≤ (1 / (M : ℝ)) * evalGrid a h (fun x2 => ∫ T1, f (clampedStep3 lam a b x0 (φ T1) x2) ∂mu) l :=
                  mul_le_mul_of_nonneg_left hm2 (by positivity)
              _ ≤ _ := hm1
          have hint_rhs0 : Integrable (fun T0 => ∫ T1, ∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu ∂mu) mu := by
            have hjoint2 : StronglyMeasurable (Function.uncurry (fun (p : InfTree23 × InfTree23) (T2 : InfTree23) =>
                f (clampedStep3 lam a b (φ p.1) (φ p.2) (φ T2)))) :=
              ((hf_cont.comp hc3_cont).measurable.comp ((hφ_meas.comp (measurable_fst.comp measurable_fst)).prodMk
                ((hφ_meas.comp (measurable_snd.comp measurable_fst)).prodMk (hφ_meas.comp measurable_snd)))).stronglyMeasurable
            have hinner_sm : StronglyMeasurable (Function.uncurry (fun T0 T1 =>
                ∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu)) :=
              hjoint2.integral_prod_right
            refine Integrable.of_bound hinner_sm.integral_prod_right.aestronglyMeasurable (max |f a| |f b|) ?_
            filter_upwards with T0
            have hpt1 : ∀ᵐ T1 ∂mu, ‖∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu‖ ≤ max |f a| |f b| := by
              filter_upwards with T1
              have hpt2 : ∀ᵐ T2 ∂mu, ‖f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2))‖ ≤ max |f a| |f b| := by
                filter_upwards with T2
                rw [Real.norm_eq_abs, abs_le]
                have hm := hc3_mem (φ T0) (φ T1) (φ T2)
                exact ⟨by have := neg_abs_le (f a); linarith [hf_mono hm.1, le_max_left |f a| |f b|],
                       by have := le_abs_self (f b); linarith [hf_mono hm.2, le_max_right |f a| |f b|]⟩
              simpa using norm_integral_le_of_norm_le_const hpt2
            simpa using norm_integral_le_of_norm_le_const hpt1
          have hint_each0 : ∀ x2 : ℝ, Integrable (fun T0 => evalGrid a h (fun x1 => f (clampedStep3 lam a b (φ T0) x1 x2)) l) mu := by
            intro x2
            refine (evalGrid_integrable l a h (fun x1 T0 => f (clampedStep3 lam a b (φ T0) x1 x2)) (fun x1 => ?_)).1
            exact integrable_clamped_mono hab hf_cont hf_mono
              (hc3_cont.measurable.comp (hφ_meas.prodMk (measurable_const.prodMk measurable_const)))
              (fun T0 => hc3_mem (φ T0) x1 x2)
          obtain ⟨hint_g0, heq_g0⟩ := evalGrid_integrable l a h
            (fun x2 T0 => evalGrid a h (fun x1 => f (clampedStep3 lam a b (φ T0) x1 x2)) l) hint_each0
          have hm0 : (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => ∫ T0, f (clampedStep3 lam a b (φ T0) x1 x2) ∂mu) l) l ≤
              (∫ T0, ∫ T1, ∫ T2, f (clampedStep3 lam a b (φ T0) (φ T1) (φ T2)) ∂mu ∂mu ∂mu) := by
            calc (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => ∫ T0, f (clampedStep3 lam a b (φ T0) x1 x2) ∂mu) l) l
                = ∫ T0, (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => f (clampedStep3 lam a b (φ T0) x1 x2)) l) l ∂mu := by
                  rw [integral_const_mul, heq_g0]
                  congr 1
                  refine evalGrid_congr l 0 (fun j2 _ _ => ?_)
                  simp only [Nat.sub_zero]
                  exact ((evalGrid_integrable l a h (fun x1 T0 => f (clampedStep3 lam a b (φ T0) x1 (a + (j2 : ℝ) * h))) (fun x1 =>
                    integrable_clamped_mono hab hf_cont hf_mono
                      (hc3_cont.measurable.comp (hφ_meas.prodMk (measurable_const.prodMk measurable_const)))
                      (fun T0 => hc3_mem (φ T0) x1 _))).2).symm
              _ ≤ _ := integral_mono (hint_g0.const_mul _) hint_rhs0 (fun T0 => hstep_T12 (φ T0))
          have hm0_ih : evalGrid a h (fun x2 => evalGrid a h (fun x1 => (1 / (M : ℝ)) * evalGrid a h (fun x0 => f (clampedStep3 lam a b x0 x1 x2)) l) l) l ≤
              evalGrid a h (fun x2 => evalGrid a h (fun x1 => ∫ T0, f (clampedStep3 lam a b (φ T0) x1 x2) ∂mu) l) l := by
            refine evalGrid_mono_pts l a (fun j2 _ => ?_)
            refine evalGrid_mono_pts l a (fun j1 _ => ?_)
            exact ih (fun x0 => f (clampedStep3 lam a b x0 (a + (j1 : ℝ) * h) (a + (j2 : ℝ) * h)))
              (hf_cont.comp (hc3_cont.comp (continuous_id.prodMk (continuous_const.prodMk continuous_const))))
              (fun y1 y2 hy => hf_mono (hc3_m0 _ _ hy))
          have hpull : evalGrid a h (fun x2 => evalGrid a h (fun x1 => (1 / (M : ℝ)) * evalGrid a h (fun x0 => f (clampedStep3 lam a b x0 x1 x2)) l) l) l =
              (1 / (M : ℝ)) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => evalGrid a h (fun x0 => f (clampedStep3 lam a b x0 x1 x2)) l) l) l := by
            simp_rw [evalGrid_const_mul]
          have hunclamp3 : evalGrid a h (fun x2 => evalGrid a h (fun x1 => evalGrid a h (fun x0 => f (clampedStep3 lam a b x0 x1 x2)) l) l) l =
              evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul l l) l) := by
            have h3a : 3 * a = (a + a) + a := by ring
            rw [h3a, evalGrid_polyMul h (fun s => f (condStep lam s)) (polyMul l l) (a + a) a l]
            have hcomm : ∀ (F : ℝ → ℝ → ℝ) (xs ys : List ℕ) (x0 y0 : ℝ),
                evalGrid x0 h (fun x => evalGrid y0 h (fun y => F x y) ys) xs =
                  evalGrid y0 h (fun y => evalGrid x0 h (fun x => F x y) xs) ys := by
              intro F xs
              induction xs with
              | nil => intro ys x0 y0; simp [evalGrid, evalGrid_const]
              | cons w ws ihx =>
                  intro ys x0 y0
                  simp only [evalGrid]
                  rw [ihx ys (x0 + h) y0, ← evalGrid_const_mul, ← evalGrid_add_func]
            rw [hcomm (fun s12 x2 => f (condStep lam (s12 + x2))) (polyMul l l) l (a + a) a]
            refine evalGrid_congr l 0 (fun j2 _ hj2 => ?_)
            simp only [Nat.sub_zero]
            rw [evalGrid_polyMul h (fun s12 => f (condStep lam (s12 + (a + (j2 : ℝ) * h)))) l a a l]
            refine evalGrid_congr l 0 (fun j1 _ hj1 => ?_)
            simp only [Nat.sub_zero]
            refine evalGrid_congr l 0 (fun j0 _ hj0 => ?_)
            simp only [Nat.sub_zero]
            have hx2 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j2) (by omega) hl_last
            have hx1 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j1) (by omega) hl_last
            have hx0 := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j0) (by omega) hl_last
            unfold clampedStep3
            rw [clampIcc_eq_self hx0, clampIcc_eq_self hx1, clampIcc_eq_self hx2]
            congr 2; ring
          rw [hpull, hunclamp3] at hm0_ih
          calc (1 / (M : ℝ) ^ 3) * evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul l l) l)
              = (1 / (M : ℝ) ^ 2) * ((1 / (M : ℝ)) * evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul l l) l)) := by ring
            _ ≤ (1 / (M : ℝ) ^ 2) * evalGrid a h (fun x2 => evalGrid a h (fun x1 => ∫ T0, f (clampedStep3 lam a b (φ T0) x1 x2) ∂mu) l) l :=
                mul_le_mul_of_nonneg_left hm0_ih (by positivity)
            _ ≤ _ := hm0
        obtain ⟨hsr2, hev2⟩ := checkIndexLower_sound hln hln2 hK (by norm_num : 0 < 2) hf_mono j2l (polyMul l l) 0 0 hlen_j2 (Nat.zero_le K) hidx2
        obtain ⟨hsr3, hev3⟩ := checkIndexLower_sound hln hln2 hK (by norm_num : 0 < 3) hf_mono j3l (polyMul (polyMul l l) l) 0 0 hlen_j3 (Nat.zero_le K) hidx3
        simp only [Nat.cast_ofNat, Nat.cast_zero, zero_mul, add_zero] at hev2 hev3
        have hb2 := evalGrid_bucketSorted a h f 0 (K + 1) 0 (List.zip j2l (polyMul l l)) (Nat.succ_pos K) (by simpa using hsr2)
        have hb3 := evalGrid_bucketSorted a h f 0 (K + 1) 0 (List.zip j3l (polyMul (polyMul l l) l)) (Nat.succ_pos K) (by simpa using hsr3)
        simp only [Nat.cast_zero, zero_mul, add_zero] at hb2 hb3
        set push := addLists (scaleList M (bucketSorted 0 (K + 1) 0 (List.zip j2l (polyMul l l))))
          (bucketSorted 0 (K + 1) 0 (List.zip j3l (polyMul (polyMul l l) l)))
        have hpush_eval : evalGrid a h f push =
            (M : ℝ) * evalPairs a h f (List.zip j2l (polyMul l l)) +
              evalPairs a h f (List.zip j3l (polyMul (polyMul l l) l)) := by
          unfold push
          rw [evalGrid_addLists, evalGrid_scaleList, hb2, hb3]; ring
        have habel := evalGrid_le_of_checkCdfLe (x0 := a) (le_of_lt hh_pos) hf_mono hcdf
        rw [evalGrid_scaleList, hpush_eval] at habel
        push_cast at habel
        have hM3_pos : (0 : ℝ) < 2 * (M : ℝ) ^ 3 := by positivity
        have hcomb : (1 / (M : ℝ)) * evalGrid a h f l ≤
            (1 / 2 : ℝ) * ((1 / (M : ℝ) ^ 2) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul l l)) +
            (1 / 2 : ℝ) * ((1 / (M : ℝ) ^ 3) * evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul l l) l)) := by
          have hstep_sum : (2 * (M : ℝ) * (M : ℝ)) * evalGrid a h f l ≤
              (M : ℝ) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul l l) +
              evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul l l) l) := by
            have := mul_le_mul_of_nonneg_left hev2 (le_of_lt hM_pos)
            linarith
          have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_pos
          rw [show (1 / 2 : ℝ) * ((1 / (M : ℝ) ^ 2) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul l l)) +
              (1 / 2 : ℝ) * ((1 / (M : ℝ) ^ 3) * evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul l l) l)) =
              ((M : ℝ) * evalGrid (2 * a) h (fun s => f (condStep lam s)) (polyMul l l) +
                evalGrid (3 * a) h (fun s => f (condStep lam s)) (polyMul (polyMul l l) l)) / (2 * (M : ℝ) ^ 3) by
                field_simp [hM_ne]]
          rw [le_div_iff₀ hM3_pos]
          have hlhs : (1 / (M : ℝ)) * evalGrid a h f l * (2 * (M : ℝ) ^ 3) =
              (2 * (M : ℝ) * (M : ℝ)) * evalGrid a h f l := by
            field_simp [hM_ne]
          linarith
        linarith
  have hlim_pt : ∀ T : InfTree23,
      Filter.Tendsto (fun n => gc (betaAtInit T lam (fun _ => b) n [])) Filter.atTop (nhds (gc (beta T lam))) := by
    intro T
    refine (hgc_cont.tendsto _).comp ?_
    rw [Metric.tendsto_atTop]
    intro eps heps
    have hq0 : 0 ≤ lam / 2 := by linarith
    have hq1 : lam / 2 < 1 := by linarith
    have hpow : Filter.Tendsto (fun n : ℕ => (lam / 2) ^ n * ((b - a) / a) * b) Filter.atTop (nhds 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ((b - a) / a)).mul_const b
    rw [Metric.tendsto_atTop] at hpow
    obtain ⟨N, hN⟩ := hpow eps heps
    refine ⟨N, fun n hn => ?_⟩
    have happrox := betaAtInit_uniform_approx T hlam0 hlam2 ⟨hab, le_rfl⟩ n
    have hN' := hN n hn
    rw [Real.dist_eq, sub_zero] at hN'
    rw [Real.dist_eq]
    exact lt_of_le_of_lt happrox (lt_of_le_of_lt (le_abs_self _) hN')
  have hdom : Filter.Tendsto (fun n => ∫ T, gc (betaAtInit T lam (fun _ => b) n []) ∂mu)
      Filter.atTop (nhds (∫ T, gc (beta T lam) ∂mu)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => max |gc a| |gc b|)
      (fun n => (hgc_cont.measurable.comp (measurable_betaAtInit lam b n [])).stronglyMeasurable.aestronglyMeasurable)
      (integrable_const _) (fun n => ?_) (Filter.Eventually.of_forall hlim_pt)
    filter_upwards with T
    rw [Real.norm_eq_abs, abs_le]
    have hm := betaAtInit_in_interval T hlam0 hlam2 (fun _ => ⟨hab, le_rfl⟩) n []
    exact ⟨by have := neg_abs_le (gc a); linarith [hgc_mono hm.1, le_max_left |gc a| |gc b|],
           by have := le_abs_self (gc b); linarith [hgc_mono hm.2, le_max_right |gc a| |gc b|]⟩
  have hgc_lim : (1 / (M : ℝ)) * evalGrid a h gc l ≤ (∫ T, gc (beta T lam) ∂mu) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hdom (Filter.Eventually.of_forall (fun n => hdepth n gc hgc_cont hgc_mono))
  have hrhs_eq : (∫ T, g (beta T lam) ∂mu) = (∫ T, gc (beta T lam) ∂mu) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun T => ?_))
    exact (congrArg g (clampIcc_eq_self (lemma_4_1_support T hlam0 hlam2))).symm
  have hlhs_eq : evalGrid a h gc l = evalGrid a h g l := by
    refine evalGrid_congr l 0 (fun j _ hj => ?_)
    simp only [Nat.sub_zero]
    have hxj := grid_pt_mem_Icc (le_of_lt hh_pos) (K := K) (j := j) (by omega) hl_last
    exact congrArg g (clampIcc_eq_self hxj)
  rw [hrhs_eq, ← hlhs_eq]
  exact hgc_lim

/-- Antitone corollaries via `-g`. -/
theorem upperEnv_sound_anti {mu : Measure InfTree23} [IsGWTree23 mu]
    {ln ld K M : ℕ} {u j2u j3u : List ℕ}
    (hchk : checkUpperEnv ln ld K M u j2u j3u = true) :
    let lam : ℝ := (ln : ℝ) / (ld : ℝ)
    let a : ℝ := 1 - lam / 2
    let b : ℝ := 1 - lam / 3
    let h : ℝ := (b - a) / (K : ℝ)
    ∀ {g : ℝ → ℝ}, ContinuousOn g (Set.Icc a b) → AntitoneOn g (Set.Icc a b) →
      (1 / (M : ℝ)) * evalGrid a h g u ≤ (∫ T, g (beta T lam) ∂mu) := by
  intro lam a b h g hg_cont hg_anti
  have hneg := upperEnv_sound (mu := mu) hchk (g := fun x => -g x) hg_cont.neg hg_anti.neg
  have h1 : (∫ T, -g (beta T lam) ∂mu) = -(∫ T, g (beta T lam) ∂mu) := integral_neg _
  have h2 : evalGrid a h (fun x => -g x) u = -evalGrid a h g u := by
    simpa using evalGrid_const_mul a h (-1) g u
  change (∫ T, -g (beta T lam) ∂mu) ≤ (1 / (M : ℝ)) * evalGrid a h (fun x => -g x) u at hneg
  rw [h1, h2] at hneg
  linarith

theorem lowerEnv_sound_anti {mu : Measure InfTree23} [IsGWTree23 mu]
    {ln ld K M : ℕ} {l j2l j3l : List ℕ}
    (hchk : checkLowerEnv ln ld K M l j2l j3l = true) :
    let lam : ℝ := (ln : ℝ) / (ld : ℝ)
    let a : ℝ := 1 - lam / 2
    let b : ℝ := 1 - lam / 3
    let h : ℝ := (b - a) / (K : ℝ)
    ∀ {g : ℝ → ℝ}, ContinuousOn g (Set.Icc a b) → AntitoneOn g (Set.Icc a b) →
      (∫ T, g (beta T lam) ∂mu) ≤ (1 / (M : ℝ)) * evalGrid a h g l := by
  intro lam a b h g hg_cont hg_anti
  have hneg := lowerEnv_sound (mu := mu) hchk (g := fun x => -g x) hg_cont.neg hg_anti.neg
  have h1 : (∫ T, -g (beta T lam) ∂mu) = -(∫ T, g (beta T lam) ∂mu) := integral_neg _
  have h2 : evalGrid a h (fun x => -g x) l = -evalGrid a h g l := by
    simpa using evalGrid_const_mul a h (-1) g l
  change (1 / (M : ℝ)) * evalGrid a h (fun x => -g x) l ≤ (∫ T, -g (beta T lam) ∂mu) at hneg
  rw [h1, h2] at hneg
  linarith

end GWSpeedCertificate
