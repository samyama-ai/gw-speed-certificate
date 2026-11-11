import GWSpeedCertificate.Criterion
import GWSpeedCertificate.StochasticOrder

/-!
# Section 6: Exact Integer Cell Verifier & Soundness (`CellVerifier.lean`)

Connects the analytic difference-quotient & corner-monotonicity lemmas (`Criterion.lean`)
with the discrete 1-step post-fixpoint RDE envelopes (`StochasticOrder.lean`) to certify
`StrictAntiOn (fun λ => R(λ) / λ) [λa, λb]` via pure `Nat` arithmetic (`checkCell`).

Every arithmetic step in `checkCell` uses exact natural-number operations (`+`, `*`, `/`, `<`, `≤`, `==`)
with zero floating-point numbers, zero `sorry`, and zero `native_decide`.
-/

namespace GWSpeedCertificate

open MeasureTheory

/-! ## 1. List Length Bounds & Helpers for `evalGrid` / `polyMul` -/

lemma scaleList_length (c : ℕ) : ∀ ys : List ℕ, (scaleList c ys).length = ys.length
  | [] => rfl
  | _ :: ys => by simp [scaleList, scaleList_length c ys]

lemma addLists_length : ∀ xs ys : List ℕ, (addLists xs ys).length = max xs.length ys.length
  | [], ys => by simp [addLists]
  | _ :: _, [] => by simp [addLists]
  | _ :: xs, _ :: ys => by simp [addLists, addLists_length xs ys, Nat.succ_max_succ]

lemma polyMul_length_le :
    ∀ {xs ys : List ℕ} {m n : ℕ},
      xs.length ≤ m + 1 → ys.length ≤ n + 1 → (polyMul xs ys).length ≤ m + n + 1
  | [], _, _, _, _, _ => by simp [polyMul]
  | 0 :: xs, _, 0, _, hx, _ => by
      simp only [List.length_cons] at hx
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hxs
      simp [polyMul]
  | 0 :: xs, ys, m + 1, n, hx, hy => by
      simp only [List.length_cons] at hx
      have ih := polyMul_length_le (Nat.le_of_succ_le_succ hx) hy
      simp only [polyMul, List.length_cons]
      omega
  | (_ + 1) :: xs, ys, 0, n, hx, hy => by
      simp only [List.length_cons] at hx
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hxs
      simp only [polyMul, List.length_singleton, addLists_length, scaleList_length]
      omega
  | (_ + 1) :: xs, ys, m + 1, n, hx, hy => by
      simp only [List.length_cons] at hx
      have ih := polyMul_length_le (Nat.le_of_succ_le_succ hx) hy
      simp only [polyMul, addLists_length, scaleList_length, List.length_cons]
      omega

lemma evalGrid_comm (hx hy : ℝ) (F : ℝ → ℝ → ℝ) :
    ∀ (xs : List ℕ) (x0 y0 : ℝ) (ys : List ℕ),
      evalGrid x0 hx (fun x => evalGrid y0 hy (fun y => F x y) ys) xs =
        evalGrid y0 hy (fun y => evalGrid x0 hx (fun x => F x y) xs) ys
  | [], _, _, ys => by simp [evalGrid, evalGrid_const]
  | w :: xs, x0, y0, ys => by
      simp only [evalGrid]
      rw [evalGrid_comm hx hy F xs (x0 + hx) y0 ys, ← evalGrid_const_mul, ← evalGrid_add_func]

lemma evalGrid_neg (x0 h : ℝ) (g : ℝ → ℝ) (ws : List ℕ) :
    evalGrid x0 h (fun x => -g x) ws = -evalGrid x0 h g ws := by
  simpa using evalGrid_const_mul x0 h (-1) g ws

lemma continuous_evalGrid {h : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) :
    ∀ (ws : List ℕ) (x0 : ℝ), Continuous (fun y => evalGrid x0 h (fun t => F y t) ws)
  | [], _ => by simp only [evalGrid]; exact continuous_const
  | _ :: ws, x0 => by
      simp only [evalGrid]
      exact (continuous_const.mul (hF.comp (continuous_id.prodMk continuous_const))).add
        (continuous_evalGrid hF ws (x0 + h))

lemma monotone_evalGrid_param {x0 h : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ t, Monotone (fun y => F y t)) :
    ∀ ws : List ℕ, Monotone (fun y => evalGrid x0 h (fun t => F y t) ws) := by
  intro ws y1 y2 hy
  exact evalGrid_mono_pts ws x0 (fun j _ => hF _ hy)

lemma evalGrid_integrable_local {α : Type*} [MeasurableSpace α] {mu : Measure α} :
    ∀ (ws : List ℕ) (x0 h : ℝ) (F : ℝ → α → ℝ),
      (∀ x, Integrable (F x) mu) →
      Integrable (fun ω => evalGrid x0 h (fun x => F x ω) ws) mu ∧
        (∫ ω, evalGrid x0 h (fun x => F x ω) ws ∂mu) = evalGrid x0 h (fun x => ∫ ω, F x ω ∂mu) ws
  | [], _, _, _, _ => ⟨integrable_zero _ _ _, by simp [evalGrid]⟩
  | w :: ws, x0, h, F, hint => by
      obtain ⟨hi_rest, heq_rest⟩ := evalGrid_integrable_local ws (x0 + h) h F hint
      have hi_head : Integrable (fun ω => (w : ℝ) * F x0 ω) mu := (hint x0).const_mul (w : ℝ)
      refine ⟨hi_head.add hi_rest, ?_⟩
      simp only [evalGrid]
      rw [integral_add hi_head hi_rest, integral_const_mul, heq_rest]

/-! ## 2. Clamped Bivariate Kernels & Multi-Tree Integrability -/

/-- Clamp a bivariate kernel `F` to `[ay, by_] × [at_, bt]`. -/
noncomputable def clampBox (ay by_ at_ bt : ℝ) (F : ℝ → ℝ → ℝ) (y t : ℝ) : ℝ :=
  F (clampIcc ay by_ y) (clampIcc at_ bt t)

lemma clampBox_props_mono_anti {ay by_ at_ bt : ℝ} (hay : ay ≤ by_) (hat : at_ ≤ bt)
    {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F) (Set.Icc ay by_ ×ˢ Set.Icc at_ bt))
    (hmono_y : ∀ t ∈ Set.Icc at_ bt, MonotoneOn (fun y => F y t) (Set.Icc ay by_))
    (hanti_t : ∀ y ∈ Set.Icc ay by_, AntitoneOn (fun t => F y t) (Set.Icc at_ bt)) :
    let Fc := clampBox ay by_ at_ bt F
    Continuous (Function.uncurry Fc) ∧
    (∀ t, Monotone (fun y => Fc y t)) ∧
    (∀ y, Antitone (fun t => Fc y t)) ∧
    (∃ C, ∀ y t, |Fc y t| ≤ C) := by
  intro Fc
  have hmap_cont : Continuous (fun p : ℝ × ℝ => (clampIcc ay by_ p.1, clampIcc at_ bt p.2)) :=
    ((continuous_clampIcc ay by_).comp continuous_fst).prodMk
      ((continuous_clampIcc at_ bt).comp continuous_snd)
  have hmap_mem : ∀ p : ℝ × ℝ, (clampIcc ay by_ p.1, clampIcc at_ bt p.2) ∈
      Set.Icc ay by_ ×ˢ Set.Icc at_ bt :=
    fun p => ⟨clampIcc_mem_Icc hay p.1, clampIcc_mem_Icc hat p.2⟩
  have hFc_cont : Continuous (Function.uncurry Fc) := hcont.comp_continuous hmap_cont hmap_mem
  have hFc_my : ∀ t, Monotone (fun y => Fc y t) := fun t y1 y2 hy =>
    hmono_y _ (clampIcc_mem_Icc hat t) (clampIcc_mem_Icc hay y1) (clampIcc_mem_Icc hay y2)
      (monotone_clampIcc ay by_ hy)
  have hFc_at : ∀ y, Antitone (fun t => Fc y t) := fun y t1 t2 ht =>
    hanti_t _ (clampIcc_mem_Icc hay y) (clampIcc_mem_Icc hat t1) (clampIcc_mem_Icc hat t2)
      (monotone_clampIcc at_ bt ht)
  refine ⟨hFc_cont, hFc_my, hFc_at, ⟨max |F ay bt| |F by_ at_|, fun y t => ?_⟩⟩
  have my := clampIcc_mem_Icc hay y
  have mt := clampIcc_mem_Icc hat t
  have hlo : F ay bt ≤ Fc y t := by
    unfold Fc clampBox
    exact (hanti_t ay ⟨le_rfl, hay⟩ mt ⟨hat, le_rfl⟩ mt.2).trans
      (hmono_y _ mt ⟨le_rfl, hay⟩ my my.1)
  have hhi : Fc y t ≤ F by_ at_ := by
    unfold Fc clampBox
    exact (hmono_y _ mt my ⟨hay, le_rfl⟩ my.2).trans
      (hanti_t by_ ⟨hay, le_rfl⟩ ⟨le_rfl, hat⟩ mt mt.1)
  rw [abs_le]
  exact ⟨by have := neg_abs_le (F ay bt); linarith [le_max_left |F ay bt| |F by_ at_|],
         by have := le_abs_self (F by_ at_); linarith [le_max_right |F ay bt| |F by_ at_|]⟩

lemma clampBox_props_mono_mono {ay by_ at_ bt : ℝ} (hay : ay ≤ by_) (hat : at_ ≤ bt)
    {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F) (Set.Icc ay by_ ×ˢ Set.Icc at_ bt))
    (hmono_y : ∀ t ∈ Set.Icc at_ bt, MonotoneOn (fun y => F y t) (Set.Icc ay by_))
    (hmono_t : ∀ y ∈ Set.Icc ay by_, MonotoneOn (fun t => F y t) (Set.Icc at_ bt)) :
    let Fc := clampBox ay by_ at_ bt F
    Continuous (Function.uncurry Fc) ∧
    (∀ t, Monotone (fun y => Fc y t)) ∧
    (∀ y, Monotone (fun t => Fc y t)) ∧
    (∃ C, ∀ y t, |Fc y t| ≤ C) := by
  intro Fc
  have hmap_cont : Continuous (fun p : ℝ × ℝ => (clampIcc ay by_ p.1, clampIcc at_ bt p.2)) :=
    ((continuous_clampIcc ay by_).comp continuous_fst).prodMk
      ((continuous_clampIcc at_ bt).comp continuous_snd)
  have hmap_mem : ∀ p : ℝ × ℝ, (clampIcc ay by_ p.1, clampIcc at_ bt p.2) ∈
      Set.Icc ay by_ ×ˢ Set.Icc at_ bt :=
    fun p => ⟨clampIcc_mem_Icc hay p.1, clampIcc_mem_Icc hat p.2⟩
  have hFc_cont : Continuous (Function.uncurry Fc) := hcont.comp_continuous hmap_cont hmap_mem
  have hFc_my : ∀ t, Monotone (fun y => Fc y t) := fun t y1 y2 hy =>
    hmono_y _ (clampIcc_mem_Icc hat t) (clampIcc_mem_Icc hay y1) (clampIcc_mem_Icc hay y2)
      (monotone_clampIcc ay by_ hy)
  have hFc_mt : ∀ y, Monotone (fun t => Fc y t) := fun y t1 t2 ht =>
    hmono_t _ (clampIcc_mem_Icc hay y) (clampIcc_mem_Icc hat t1) (clampIcc_mem_Icc hat t2)
      (monotone_clampIcc at_ bt ht)
  refine ⟨hFc_cont, hFc_my, hFc_mt, ⟨max |F ay at_| |F by_ bt|, fun y t => ?_⟩⟩
  have my := clampIcc_mem_Icc hay y
  have mt := clampIcc_mem_Icc hat t
  have hlo : F ay at_ ≤ Fc y t := by
    unfold Fc clampBox
    exact (hmono_t ay ⟨le_rfl, hay⟩ ⟨le_rfl, hat⟩ mt mt.1).trans
      (hmono_y _ mt ⟨le_rfl, hay⟩ my my.1)
  have hhi : Fc y t ≤ F by_ bt := by
    unfold Fc clampBox
    exact (hmono_y _ mt my ⟨hay, le_rfl⟩ my.2).trans
      (hmono_t by_ ⟨hay, le_rfl⟩ mt ⟨hat, le_rfl⟩ mt.2)
  rw [abs_le]
  exact ⟨by have := neg_abs_le (F ay at_); linarith [le_max_left |F ay at_| |F by_ bt|],
         by have := le_abs_self (F by_ bt); linarith [le_max_right |F ay at_| |F by_ bt|]⟩

/-- Universal integrability helper for 2-tree sums `∫ T1, ∫ T2, f (φ1 T1 + φ2 T2) ∂mu ∂mu`. -/
lemma integrable_sum2 {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ s, |f s| ≤ C)
    {φ1 φ2 : InfTree23 → ℝ} (hm1 : Measurable φ1) (hm2 : Measurable φ2) :
    (∀ T1, Integrable (fun T2 => f (φ1 T1 + φ2 T2)) mu) ∧
    Integrable (fun T1 => ∫ T2, f (φ1 T1 + φ2 T2) ∂mu) mu ∧
    (∀ T1, |∫ T2, f (φ1 T1 + φ2 T2) ∂mu| ≤ C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T1
    exact integrable_of_measurable_bounded (hf.measurable.comp (measurable_const.add hm2)) (fun _ => hC _)
  · have hsm : StronglyMeasurable (Function.uncurry (fun T1 T2 => f (φ1 T1 + φ2 T2))) :=
      (hf.measurable.comp ((hm1.comp measurable_fst).add (hm2.comp measurable_snd))).stronglyMeasurable
    refine Integrable.of_bound hsm.integral_prod_right.aestronglyMeasurable C ?_
    filter_upwards with T1
    have hpt : ∀ᵐ T2 ∂mu, ‖f (φ1 T1 + φ2 T2)‖ ≤ C := by
      filter_upwards with T2; simpa [Real.norm_eq_abs] using hC _
    simpa using norm_integral_le_of_norm_le_const hpt
  · intro T1
    have hpt : ∀ᵐ T2 ∂mu, ‖f (φ1 T1 + φ2 T2)‖ ≤ C := by
      filter_upwards with T2; simpa [Real.norm_eq_abs] using hC _
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hpt

/-- Universal integrability helper for 3-tree sums `∫ T1, ∫ T2, ∫ T3, f (φ1 T1 + φ2 T2 + φ3 T3) ∂mu`. -/
lemma integrable_sum3 {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ s, |f s| ≤ C)
    {φ1 φ2 φ3 : InfTree23 → ℝ} (hm1 : Measurable φ1) (hm2 : Measurable φ2) (hm3 : Measurable φ3) :
    (∀ T1 T2, Integrable (fun T3 => f (φ1 T1 + φ2 T2 + φ3 T3)) mu) ∧
    (∀ T1, Integrable (fun T2 => ∫ T3, f (φ1 T1 + φ2 T2 + φ3 T3) ∂mu) mu) ∧
    Integrable (fun T1 => ∫ T2, ∫ T3, f (φ1 T1 + φ2 T2 + φ3 T3) ∂mu ∂mu) mu ∧
    (∀ T1, |∫ T2, ∫ T3, f (φ1 T1 + φ2 T2 + φ3 T3) ∂mu ∂mu| ≤ C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T1 T2
    exact integrable_of_measurable_bounded (hf.measurable.comp (measurable_const.add hm3)) (fun _ => hC _)
  · intro T1
    have hshift : Continuous (fun s => f (φ1 T1 + s)) := hf.comp (continuous_const.add continuous_id)
    have hint := (integrable_sum2 (mu := mu) (f := fun s => f (φ1 T1 + s)) hshift (fun s => hC (φ1 T1 + s)) hm2 hm3).2.1
    simpa only [add_assoc] using hint
  · have hjoint2 : StronglyMeasurable (Function.uncurry (fun (p : InfTree23 × InfTree23) (T3 : InfTree23) =>
        f (φ1 p.1 + φ2 p.2 + φ3 T3))) :=
      (hf.measurable.comp (((hm1.comp (measurable_fst.comp measurable_fst)).add
        (hm2.comp (measurable_snd.comp measurable_fst))).add (hm3.comp measurable_snd))).stronglyMeasurable
    have hinner : StronglyMeasurable (Function.uncurry (fun T1 T2 => ∫ T3, f (φ1 T1 + φ2 T2 + φ3 T3) ∂mu)) :=
      hjoint2.integral_prod_right
    refine Integrable.of_bound hinner.integral_prod_right.aestronglyMeasurable C ?_
    filter_upwards with T1
    have hshift : Continuous (fun s => f (φ1 T1 + s)) := hf.comp (continuous_const.add continuous_id)
    have hpt1 : ∀ᵐ T2 ∂mu, ‖∫ T3, f (φ1 T1 + φ2 T2 + φ3 T3) ∂mu‖ ≤ C := by
      filter_upwards with T2
      have hb := (integrable_sum2 (mu := mu) (f := fun s => f (φ1 T1 + s)) hshift (fun s => hC (φ1 T1 + s)) hm2 hm3).2.2 T2
      simpa [Real.norm_eq_abs, add_assoc] using hb
    simpa using norm_integral_le_of_norm_le_const hpt1
  · intro T1
    have hshift : Continuous (fun s => f (φ1 T1 + s)) := hf.comp (continuous_const.add continuous_id)
    have hpt1 : ∀ᵐ T2 ∂mu, ‖∫ T3, f (φ1 T1 + φ2 T2 + φ3 T3) ∂mu‖ ≤ C := by
      filter_upwards with T2
      have hb := (integrable_sum2 (mu := mu) (f := fun s => f (φ1 T1 + s)) hshift (fun s => hC (φ1 T1 + s)) hm2 hm3).2.2 T2
      simpa [Real.norm_eq_abs, add_assoc] using hb
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hpt1

lemma integrable_biv3_outer {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {Fc : ℝ → ℝ → ℝ} (hcont : Continuous (Function.uncurry Fc)) {C : ℝ} (hC : ∀ y t, |Fc y t| ≤ C)
    {φ0 φ1 φ2 : InfTree23 → ℝ} (hm0 : Measurable φ0) (hm1 : Measurable φ1) (hm2 : Measurable φ2) :
    Integrable (fun T0 => ∫ T1, ∫ T2, Fc (φ0 T0) (φ1 T1 + φ2 T2) ∂mu ∂mu) mu := by
  have hjoint2 : StronglyMeasurable (Function.uncurry (fun (p : InfTree23 × InfTree23) (T2 : InfTree23) =>
      Fc (φ0 p.1) (φ1 p.2 + φ2 T2))) :=
    (hcont.measurable.comp ((hm0.comp (measurable_fst.comp measurable_fst)).prodMk
      ((hm1.comp (measurable_snd.comp measurable_fst)).add (hm2.comp measurable_snd)))).stronglyMeasurable
  have hinner : StronglyMeasurable (Function.uncurry (fun T0 T1 => ∫ T2, Fc (φ0 T0) (φ1 T1 + φ2 T2) ∂mu)) :=
    hjoint2.integral_prod_right
  refine Integrable.of_bound hinner.integral_prod_right.aestronglyMeasurable C ?_
  filter_upwards with T0
  have hb := (integrable_sum2 (mu := mu) (hcont.comp (continuous_const.prodMk continuous_id)) (hC (φ0 T0)) hm1 hm2).2.2
  have hpt : ∀ᵐ T1 ∂mu, ‖∫ T2, Fc (φ0 T0) (φ1 T1 + φ2 T2) ∂mu‖ ≤ C := by
    filter_upwards with T1; simpa [Real.norm_eq_abs] using hb T1
  simpa using norm_integral_le_of_norm_le_const hpt

lemma integrable_biv4_outer {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {Fc : ℝ → ℝ → ℝ} (hcont : Continuous (Function.uncurry Fc)) {C : ℝ} (hC : ∀ y t, |Fc y t| ≤ C)
    {φ0 φ1 φ2 φ3 : InfTree23 → ℝ}
    (hm0 : Measurable φ0) (hm1 : Measurable φ1) (hm2 : Measurable φ2) (hm3 : Measurable φ3) :
    Integrable (fun T0 => ∫ T1, ∫ T2, ∫ T3, Fc (φ0 T0) (φ1 T1 + φ2 T2 + φ3 T3) ∂mu ∂mu ∂mu) mu := by
  have hjoint3 : StronglyMeasurable (Function.uncurry (fun (p : (InfTree23 × InfTree23) × InfTree23) (T3 : InfTree23) =>
      Fc (φ0 p.1.1) (φ1 p.1.2 + φ2 p.2 + φ3 T3))) :=
    (hcont.measurable.comp ((hm0.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((hm1.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).add
        (hm2.comp (measurable_snd.comp measurable_fst))).add (hm3.comp measurable_snd)))).stronglyMeasurable
  have hi2 : StronglyMeasurable (Function.uncurry (fun (p : InfTree23 × InfTree23) (T2 : InfTree23) =>
      ∫ T3, Fc (φ0 p.1) (φ1 p.2 + φ2 T2 + φ3 T3) ∂mu)) := hjoint3.integral_prod_right
  have hi1 : StronglyMeasurable (Function.uncurry (fun T0 T1 =>
      ∫ T2, ∫ T3, Fc (φ0 T0) (φ1 T1 + φ2 T2 + φ3 T3) ∂mu ∂mu)) := hi2.integral_prod_right
  refine Integrable.of_bound hi1.integral_prod_right.aestronglyMeasurable C ?_
  filter_upwards with T0
  have hb := (integrable_sum3 (mu := mu) (hcont.comp (continuous_const.prodMk continuous_id)) (hC (φ0 T0)) hm1 hm2 hm3).2.2.2
  have hpt : ∀ᵐ T1 ∂mu, ‖∫ T2, ∫ T3, Fc (φ0 T0) (φ1 T1 + φ2 T2 + φ3 T3) ∂mu ∂mu‖ ≤ C := by
    filter_upwards with T1; simpa [Real.norm_eq_abs] using hb T1
  simpa using norm_integral_le_of_norm_le_const hpt

/-! ## 3. Multi-Tree Convolution Peeling Lemmas -/

lemma sum2_upper_anti {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {φ : InfTree23 → ℝ} (hm : Measurable φ) {a h M : ℝ} (hM : 0 < M) {w : List ℕ}
    (hE : ∀ g : ℝ → ℝ, Continuous g → Antitone g → (∫ T, g (φ T) ∂mu) ≤ (1 / M) * evalGrid a h g w)
    {f : ℝ → ℝ} (hf : Continuous f) (hanti : Antitone f) {C : ℝ} (hC : ∀ s, |f s| ≤ C) :
    (∫ T1, ∫ T2, f (φ T1 + φ T2) ∂mu ∂mu) ≤ (1 / M ^ 2) * evalGrid (2 * a) h f (polyMul w w) := by
  have hint_lhs := (integrable_sum2 (mu := mu) hf hC hm hm).2.1
  have hint_each : ∀ x2 : ℝ, Integrable (fun T1 => f (φ T1 + x2)) mu := fun x2 =>
    integrable_of_measurable_bounded (hf.measurable.comp (hm.add measurable_const)) (fun _ => hC _)
  obtain ⟨hint_g, heq_g⟩ := evalGrid_integrable_local w a h (fun x2 T1 => f (φ T1 + x2)) hint_each
  have h1 : (∫ T1, ∫ T2, f (φ T1 + φ T2) ∂mu ∂mu) ≤
      (1 / M) * evalGrid a h (fun x2 => ∫ T1, f (φ T1 + x2) ∂mu) w := by
    calc (∫ T1, ∫ T2, f (φ T1 + φ T2) ∂mu ∂mu)
        ≤ ∫ T1, (1 / M) * evalGrid a h (fun x2 => f (φ T1 + x2)) w ∂mu :=
          integral_mono hint_lhs (hint_g.const_mul _) (fun T1 =>
            hE (fun x2 => f (φ T1 + x2)) (hf.comp (continuous_const.add continuous_id))
              (fun _ _ huv => hanti (by linarith)))
      _ = (1 / M) * evalGrid a h (fun x2 => ∫ T1, f (φ T1 + x2) ∂mu) w := by
          rw [integral_const_mul, heq_g]
  have h2 : evalGrid a h (fun x2 => ∫ T1, f (φ T1 + x2) ∂mu) w ≤
      evalGrid a h (fun x2 => (1 / M) * evalGrid a h (fun x1 => f (x1 + x2)) w) w := by
    refine evalGrid_mono_pts w a (fun i _ => ?_)
    exact hE (fun x1 => f (x1 + (a + (i : ℝ) * h)))
      (hf.comp (continuous_id.add continuous_const)) (fun _ _ huv => hanti (by linarith))
  rw [evalGrid_const_mul, evalGrid_comm h h (fun x2 x1 => f (x1 + x2)) w a a w,
      ← evalGrid_polyMul h f w a a w, show a + a = 2 * a by ring] at h2
  calc (∫ T1, ∫ T2, f (φ T1 + φ T2) ∂mu ∂mu)
      ≤ (1 / M) * ((1 / M) * evalGrid (2 * a) h f (polyMul w w)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = (1 / M ^ 2) * evalGrid (2 * a) h f (polyMul w w) := by ring

lemma sum2_lower_anti {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {φ : InfTree23 → ℝ} (hm : Measurable φ) {a h M : ℝ} (hM : 0 < M) {w : List ℕ}
    (hE : ∀ g : ℝ → ℝ, Continuous g → Antitone g → (1 / M) * evalGrid a h g w ≤ (∫ T, g (φ T) ∂mu))
    {f : ℝ → ℝ} (hf : Continuous f) (hanti : Antitone f) {C : ℝ} (hC : ∀ s, |f s| ≤ C) :
    (1 / M ^ 2) * evalGrid (2 * a) h f (polyMul w w) ≤ (∫ T1, ∫ T2, f (φ T1 + φ T2) ∂mu ∂mu) := by
  have hint_rhs := (integrable_sum2 (mu := mu) hf hC hm hm).2.1
  have hint_each : ∀ x2 : ℝ, Integrable (fun T1 => f (φ T1 + x2)) mu := fun x2 =>
    integrable_of_measurable_bounded (hf.measurable.comp (hm.add measurable_const)) (fun _ => hC _)
  obtain ⟨hint_g, heq_g⟩ := evalGrid_integrable_local w a h (fun x2 T1 => f (φ T1 + x2)) hint_each
  have h1 : (1 / M) * evalGrid a h (fun x2 => ∫ T1, f (φ T1 + x2) ∂mu) w ≤
      (∫ T1, ∫ T2, f (φ T1 + φ T2) ∂mu ∂mu) := by
    calc (1 / M) * evalGrid a h (fun x2 => ∫ T1, f (φ T1 + x2) ∂mu) w
        = ∫ T1, (1 / M) * evalGrid a h (fun x2 => f (φ T1 + x2)) w ∂mu := by
          rw [integral_const_mul, heq_g]
      _ ≤ (∫ T1, ∫ T2, f (φ T1 + φ T2) ∂mu ∂mu) :=
          integral_mono (hint_g.const_mul _) hint_rhs (fun T1 =>
            hE _ (hf.comp (continuous_const.add continuous_id)) (fun _ _ huv => hanti (by linarith)))
  have h2 : evalGrid a h (fun x2 => (1 / M) * evalGrid a h (fun x1 => f (x1 + x2)) w) w ≤
      evalGrid a h (fun x2 => ∫ T1, f (φ T1 + x2) ∂mu) w := by
    refine evalGrid_mono_pts w a (fun _ _ => ?_)
    exact hE _ (hf.comp (continuous_id.add continuous_const)) (fun _ _ huv => hanti (by linarith))
  rw [evalGrid_const_mul, evalGrid_comm h h (fun x2 x1 => f (x1 + x2)) w a a w,
      ← evalGrid_polyMul h f w a a w, show a + a = 2 * a by ring] at h2
  calc (1 / M ^ 2) * evalGrid (2 * a) h f (polyMul w w)
      = (1 / M) * ((1 / M) * evalGrid (2 * a) h f (polyMul w w)) := by ring
    _ ≤ (1 / M) * evalGrid a h (fun x2 => ∫ T1, f (φ T1 + x2) ∂mu) w :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ _ := h1

lemma sum3_upper_anti {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {φ : InfTree23 → ℝ} (hm : Measurable φ) {a h M : ℝ} (hM : 0 < M) {w : List ℕ}
    (hE : ∀ g : ℝ → ℝ, Continuous g → Antitone g → (∫ T, g (φ T) ∂mu) ≤ (1 / M) * evalGrid a h g w)
    {f : ℝ → ℝ} (hf : Continuous f) (hanti : Antitone f) {C : ℝ} (hC : ∀ s, |f s| ≤ C) :
    (∫ T1, ∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu) ≤
      (1 / M ^ 3) * evalGrid (3 * a) h f (polyMul (polyMul w w) w) := by
  have hint_lhs := (integrable_sum3 (mu := mu) hf hC hm hm hm).2.2.1
  have hint_each1 : ∀ x3 : ℝ, Integrable (fun T1 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) mu := fun x3 =>
    (integrable_sum2 (mu := mu) (f := fun s => f (s + x3))
      (hf.comp (continuous_id.add continuous_const)) (fun s => hC (s + x3)) hm hm).2.1
  obtain ⟨hint_g1, heq_g1⟩ := evalGrid_integrable_local w a h
    (fun x3 T1 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) hint_each1
  have h1 : (∫ T1, ∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu) ≤
      (1 / M) * evalGrid a h (fun x3 => ∫ T1, ∫ T2, f (φ T1 + φ T2 + x3) ∂mu ∂mu) w := by
    have hstep1 : ∀ T1 : InfTree23,
        (∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu) ≤
          (1 / M) * evalGrid a h (fun x3 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) w := by
      intro T1
      have hi_l := (integrable_sum3 (mu := mu) hf hC hm hm hm).2.1 T1
      have hi_e : ∀ x3 : ℝ, Integrable (fun T2 => f (φ T1 + φ T2 + x3)) mu := fun x3 =>
        integrable_of_measurable_bounded (hf.measurable.comp ((measurable_const.add hm).add measurable_const)) (fun _ => hC _)
      obtain ⟨hi_r, heq_r⟩ := evalGrid_integrable_local w a h (fun x3 T2 => f (φ T1 + φ T2 + x3)) hi_e
      calc (∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu)
          ≤ ∫ T2, (1 / M) * evalGrid a h (fun x3 => f (φ T1 + φ T2 + x3)) w ∂mu :=
            integral_mono hi_l (hi_r.const_mul _) (fun T2 =>
              hE (fun x3 => f (φ T1 + φ T2 + x3)) (hf.comp (continuous_const.add continuous_id))
                (fun _ _ huv => hanti (by linarith)))
        _ = (1 / M) * evalGrid a h (fun x3 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) w := by
            rw [integral_const_mul, heq_r]
    calc (∫ T1, ∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu)
        ≤ ∫ T1, (1 / M) * evalGrid a h (fun x3 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) w ∂mu :=
          integral_mono hint_lhs (hint_g1.const_mul _) hstep1
      _ = (1 / M) * evalGrid a h (fun x3 => ∫ T1, ∫ T2, f (φ T1 + φ T2 + x3) ∂mu ∂mu) w := by
          rw [integral_const_mul, heq_g1]
  have h2 : evalGrid a h (fun x3 => ∫ T1, ∫ T2, f (φ T1 + φ T2 + x3) ∂mu ∂mu) w ≤
      evalGrid a h (fun x3 => (1 / M ^ 2) * evalGrid (2 * a) h (fun s12 => f (s12 + x3)) (polyMul w w)) w := by
    refine evalGrid_mono_pts w a (fun i _ => ?_)
    exact sum2_upper_anti (f := fun s12 => f (s12 + (a + (i : ℝ) * h))) hm hM hE
      (hf.comp (continuous_id.add continuous_const))
      (fun _ _ huv => hanti (by linarith)) (fun s => hC (s + (a + (i : ℝ) * h)))
  rw [evalGrid_const_mul, evalGrid_comm h h (fun x3 s12 => f (s12 + x3)) w a (2 * a) (polyMul w w),
      ← evalGrid_polyMul h f (polyMul w w) (2 * a) a w, show 2 * a + a = 3 * a by ring] at h2
  calc (∫ T1, ∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu)
      ≤ (1 / M) * ((1 / M ^ 2) * evalGrid (3 * a) h f (polyMul (polyMul w w) w)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = (1 / M ^ 3) * evalGrid (3 * a) h f (polyMul (polyMul w w) w) := by ring

lemma sum3_lower_anti {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {φ : InfTree23 → ℝ} (hm : Measurable φ) {a h M : ℝ} (hM : 0 < M) {w : List ℕ}
    (hE : ∀ g : ℝ → ℝ, Continuous g → Antitone g → (1 / M) * evalGrid a h g w ≤ (∫ T, g (φ T) ∂mu))
    {f : ℝ → ℝ} (hf : Continuous f) (hanti : Antitone f) {C : ℝ} (hC : ∀ s, |f s| ≤ C) :
    (1 / M ^ 3) * evalGrid (3 * a) h f (polyMul (polyMul w w) w) ≤
      (∫ T1, ∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu) := by
  have hint_rhs := (integrable_sum3 (mu := mu) hf hC hm hm hm).2.2.1
  have hint_each1 : ∀ x3 : ℝ, Integrable (fun T1 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) mu := fun x3 =>
    (integrable_sum2 (mu := mu) (hf.comp (continuous_id.add continuous_const)) (fun _ => hC _) hm hm).2.1
  obtain ⟨hint_g1, heq_g1⟩ := evalGrid_integrable_local w a h
    (fun x3 T1 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) hint_each1
  have h1 : (1 / M) * evalGrid a h (fun x3 => ∫ T1, ∫ T2, f (φ T1 + φ T2 + x3) ∂mu ∂mu) w ≤
      (∫ T1, ∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu) := by
    have hstep1 : ∀ T1 : InfTree23,
        (1 / M) * evalGrid a h (fun x3 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) w ≤
          (∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu) := by
      intro T1
      have hi_r := (integrable_sum3 (mu := mu) hf hC hm hm hm).2.1 T1
      have hi_e : ∀ x3 : ℝ, Integrable (fun T2 => f (φ T1 + φ T2 + x3)) mu := fun x3 =>
        integrable_of_measurable_bounded (hf.measurable.comp ((measurable_const.add hm).add measurable_const)) (fun _ => hC _)
      obtain ⟨hi_l, heq_l⟩ := evalGrid_integrable_local w a h (fun x3 T2 => f (φ T1 + φ T2 + x3)) hi_e
      calc (1 / M) * evalGrid a h (fun x3 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) w
          = ∫ T2, (1 / M) * evalGrid a h (fun x3 => f (φ T1 + φ T2 + x3)) w ∂mu := by
            rw [integral_const_mul, heq_l]
        _ ≤ (∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu) :=
            integral_mono (hi_l.const_mul _) hi_r (fun T2 =>
              hE _ (hf.comp (continuous_const.add continuous_id)) (fun _ _ huv => hanti (by linarith)))
    calc (1 / M) * evalGrid a h (fun x3 => ∫ T1, ∫ T2, f (φ T1 + φ T2 + x3) ∂mu ∂mu) w
        = ∫ T1, (1 / M) * evalGrid a h (fun x3 => ∫ T2, f (φ T1 + φ T2 + x3) ∂mu) w ∂mu := by
          rw [integral_const_mul, heq_g1]
      _ ≤ (∫ T1, ∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu) :=
          integral_mono (hint_g1.const_mul _) hint_rhs hstep1
  have h2 : evalGrid a h (fun x3 => (1 / M ^ 2) * evalGrid (2 * a) h (fun s12 => f (s12 + x3)) (polyMul w w)) w ≤
      evalGrid a h (fun x3 => ∫ T1, ∫ T2, f (φ T1 + φ T2 + x3) ∂mu ∂mu) w := by
    refine evalGrid_mono_pts w a (fun _ _ => ?_)
    exact sum2_lower_anti hm hM hE (hf.comp (continuous_id.add continuous_const))
      (fun _ _ huv => hanti (by linarith)) (fun _ => hC _)
  rw [evalGrid_const_mul, evalGrid_comm h h (fun x3 s12 => f (s12 + x3)) w a (2 * a) (polyMul w w),
      ← evalGrid_polyMul h f (polyMul w w) (2 * a) a w, show 2 * a + a = 3 * a by ring] at h2
  calc (1 / M ^ 3) * evalGrid (3 * a) h f (polyMul (polyMul w w) w)
      = (1 / M) * ((1 / M ^ 2) * evalGrid (3 * a) h f (polyMul (polyMul w w) w)) := by ring
    _ ≤ (1 / M) * evalGrid a h (fun x3 => ∫ T1, ∫ T2, f (φ T1 + φ T2 + x3) ∂mu ∂mu) w :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ _ := h1

lemma sum3_upper_mono {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {φ : InfTree23 → ℝ} (hm : Measurable φ) {a h M : ℝ} (hM : 0 < M) {w : List ℕ}
    (hE : ∀ g : ℝ → ℝ, Continuous g → Monotone g → (∫ T, g (φ T) ∂mu) ≤ (1 / M) * evalGrid a h g w)
    {f : ℝ → ℝ} (hf : Continuous f) (hmono : Monotone f) {C : ℝ} (hC : ∀ s, |f s| ≤ C) :
    (∫ T1, ∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu) ≤
      (1 / M ^ 3) * evalGrid (3 * a) h f (polyMul (polyMul w w) w) := by
  have hneg := sum3_lower_anti (mu := mu) (f := fun x => -f x) hm hM
    (fun g hg hga => by
      have hb := hE (fun x => -g x) hg.neg (fun _ _ huv => neg_le_neg (hga huv))
      rw [integral_neg, evalGrid_neg] at hb
      linarith)
    hf.neg (fun _ _ huv => neg_le_neg (hmono huv)) (fun s => by simpa using hC s)
  have hi_neg : (∫ T1, ∫ T2, ∫ T3, -f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu) =
      -(∫ T1, ∫ T2, ∫ T3, f (φ T1 + φ T2 + φ T3) ∂mu ∂mu ∂mu) := by
    simp only [integral_neg]
  rw [evalGrid_neg, hi_neg] at hneg
  linarith

/-! ## 4. Full 3-Tree & 4-Tree Box Envelope Bounds -/

lemma checkUpperEnv_dims {ln ld K M : ℕ} {u j2u j3u : List ℕ}
    (h : checkUpperEnv ln ld K M u j2u j3u = true) :
    0 < ln ∧ ln < 2 * ld ∧ 0 < K ∧ 0 < M ∧ u.length = K + 1 := by
  simp only [checkUpperEnv, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

lemma checkLowerEnv_dims {ln ld K M : ℕ} {l j2l j3l : List ℕ}
    (h : checkLowerEnv ln ld K M l j2l j3l = true) :
    0 < ln ∧ ln < 2 * ld ∧ 0 < K ∧ 0 < M ∧ l.length = K + 1 := by
  simp only [checkLowerEnv, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

lemma peel3_upper_mono_anti {mu : Measure InfTree23} [IsGWTree23 mu]
    {lna lnb ld K M : ℕ} {ua j2u j3u lb_env j2l j3l : List ℕ}
    (hua : checkUpperEnv lna ld K M ua j2u j3u = true)
    (hlb : checkLowerEnv lnb ld K M lb_env j2l j3l = true)
    {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F)
      (Set.Icc (1 - ((lna : ℝ) / ld) / 2) (1 - ((lna : ℝ) / ld) / 3) ×ˢ
       Set.Icc (2 * (1 - ((lnb : ℝ) / ld) / 2)) (2 * (1 - ((lnb : ℝ) / ld) / 3))))
    (hmy : ∀ t ∈ Set.Icc (2 * (1 - ((lnb : ℝ) / ld) / 2)) (2 * (1 - ((lnb : ℝ) / ld) / 3)),
      MonotoneOn (fun y => F y t) (Set.Icc (1 - ((lna : ℝ) / ld) / 2) (1 - ((lna : ℝ) / ld) / 3)))
    (hat : ∀ y ∈ Set.Icc (1 - ((lna : ℝ) / ld) / 2) (1 - ((lna : ℝ) / ld) / 3),
      AntitoneOn (fun t => F y t) (Set.Icc (2 * (1 - ((lnb : ℝ) / ld) / 2)) (2 * (1 - ((lnb : ℝ) / ld) / 3)))) :
    let la : ℝ := (lna : ℝ) / ld
    let lb : ℝ := (lnb : ℝ) / ld
    let aa : ℝ := 1 - la / 2
    let ba : ℝ := 1 - la / 3
    let ha : ℝ := (ba - aa) / K
    let ab : ℝ := 1 - lb / 2
    let bb : ℝ := 1 - lb / 3
    let hb : ℝ := (bb - ab) / K
    (∫ T0, ∫ T1, ∫ T2, F (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu ∂mu) ≤
      (1 / (M : ℝ) ^ 3) * evalGrid aa ha (fun y => evalGrid (2 * ab) hb (fun t => F y t) (polyMul lb_env lb_env)) ua := by
  obtain ⟨hlna, hlna2, hK, hM, hlen_ua⟩ := checkUpperEnv_dims hua
  obtain ⟨hlnb, hlnb2, _, _, hlen_lb⟩ := checkLowerEnv_dims hlb
  have hld : 0 < ld := by omega
  intro la lb aa ba ha ab bb hb
  have haa_eq : aa = 1 - la / 2 := rfl
  have hba_eq : ba = 1 - la / 3 := rfl
  have hab_eq : ab = 1 - lb / 2 := rfl
  have hbb_eq : bb = 1 - lb / 3 := rfl
  have hla0 : 0 < la := div_pos (Nat.cast_pos.mpr hlna) (Nat.cast_pos.mpr hld)
  have hla2 : la < 2 := by unfold la; rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]; exact_mod_cast hlna2
  have hlb0 : 0 < lb := div_pos (Nat.cast_pos.mpr hlnb) (Nat.cast_pos.mpr hld)
  have hlb2 : lb < 2 := by unfold lb; rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]; exact_mod_cast hlnb2
  have haa : aa ≤ ba := by linarith
  have hab : ab ≤ bb := by linarith
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hK_ne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hK)
  obtain ⟨hFc_cont, hFc_my, hFc_at, ⟨C, hC⟩⟩ := clampBox_props_mono_anti haa (by linarith) hcont hmy hat
  set Fc := clampBox aa ba (2 * ab) (2 * bb) F
  have hlhs_eq : (∫ T0, ∫ T1, ∫ T2, F (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu ∂mu) =
      (∫ T0, ∫ T1, ∫ T2, Fc (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu ∂mu) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun T0 => integral_congr_ae (Filter.Eventually.of_forall (fun T1 =>
      integral_congr_ae (Filter.Eventually.of_forall (fun T2 => ?_))))))
    have m0 := lemma_4_1_support T0 hla0 hla2
    have m1 := lemma_4_1_support T1 hlb0 hlb2
    have m2 := lemma_4_1_support T2 hlb0 hlb2
    dsimp only []
    unfold Fc clampBox
    rw [clampIcc_eq_self m0, clampIcc_eq_self ⟨by linarith [m1.1, m2.1], by linarith [m1.2, m2.2]⟩]
  rw [hlhs_eq]
  have hinner : ∀ T0 : InfTree23,
      (∫ T1, ∫ T2, Fc (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu) ≤
        (1 / (M : ℝ) ^ 2) * evalGrid (2 * ab) hb (Fc (beta T0 la)) (polyMul lb_env lb_env) := by
    intro T0
    refine sum2_upper_anti (measurable_beta lb) hM_pos
      (fun g hg hga => lowerEnv_sound_anti hlb hg.continuousOn (fun _ _ _ _ huv => hga huv))
      (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hFc_at _) (hC _)
  have hi_l := integrable_biv3_outer (mu := mu) hFc_cont hC (measurable_beta la) (measurable_beta lb) (measurable_beta lb)
  have hg_cont : Continuous (fun y => evalGrid (2 * ab) hb (fun t => Fc y t) (polyMul lb_env lb_env)) :=
    continuous_evalGrid hFc_cont _ _
  have hg_mono : Monotone (fun y => evalGrid (2 * ab) hb (fun t => Fc y t) (polyMul lb_env lb_env)) :=
    monotone_evalGrid_param hFc_my _
  have hi_r : Integrable (fun T0 => (1 / (M : ℝ) ^ 2) *
      evalGrid (2 * ab) hb (Fc (beta T0 la)) (polyMul lb_env lb_env)) mu := by
    refine (integrable_clamped_mono haa hg_cont hg_mono (measurable_beta la)
      (fun T0 => lemma_4_1_support T0 hla0 hla2)).const_mul _
  have houter : (∫ T0, ∫ T1, ∫ T2, Fc (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu ∂mu) ≤
      (1 / (M : ℝ) ^ 3) * evalGrid aa ha (fun y => evalGrid (2 * ab) hb (fun t => Fc y t) (polyMul lb_env lb_env)) ua := by
    calc (∫ T0, ∫ T1, ∫ T2, Fc (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu ∂mu)
        ≤ ∫ T0, (1 / (M : ℝ) ^ 2) * evalGrid (2 * ab) hb (Fc (beta T0 la)) (polyMul lb_env lb_env) ∂mu :=
          integral_mono hi_l hi_r hinner
      _ = (1 / (M : ℝ) ^ 2) * ∫ T0, evalGrid (2 * ab) hb (Fc (beta T0 la)) (polyMul lb_env lb_env) ∂mu :=
          integral_const_mul _ _
      _ ≤ (1 / (M : ℝ) ^ 2) * ((1 / (M : ℝ)) * evalGrid aa ha
          (fun y => evalGrid (2 * ab) hb (fun t => Fc y t) (polyMul lb_env lb_env)) ua) :=
          mul_le_mul_of_nonneg_left
            (upperEnv_sound hua hg_cont.continuousOn (fun _ _ _ _ huv => hg_mono huv)) (by positivity)
      _ = _ := by ring
  have hrhs_eq : evalGrid aa ha (fun y => evalGrid (2 * ab) hb (fun t => Fc y t) (polyMul lb_env lb_env)) ua =
      evalGrid aa ha (fun y => evalGrid (2 * ab) hb (fun t => F y t) (polyMul lb_env lb_env)) ua := by
    have hplen := polyMul_length_le (le_of_eq hlen_lb) (le_of_eq hlen_lb)
    refine evalGrid_congr ua 0 (fun i _ hi => ?_)
    simp only [Nat.sub_zero]
    refine evalGrid_congr (polyMul lb_env lb_env) 0 (fun j _ hj => ?_)
    simp only [Nat.sub_zero]
    have hy : aa + (i : ℝ) * ha ∈ Set.Icc aa ba :=
      grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := K) (by omega)
        (by rw [mul_div_cancel₀ _ hK_ne]; linarith)
    have ht : 2 * ab + (j : ℝ) * hb ∈ Set.Icc (2 * ab) (2 * bb) := by
      refine grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := 2 * K) (by omega) ?_
      push_cast; field_simp [hK_ne]; linarith
    unfold Fc clampBox
    rw [clampIcc_eq_self hy, clampIcc_eq_self ht]
  rwa [hrhs_eq] at houter

lemma peel3_lower_mono_anti {mu : Measure InfTree23} [IsGWTree23 mu]
    {lna lnb ld K M : ℕ} {ua j2u j3u lb_env j2l j3l : List ℕ}
    (hua : checkUpperEnv lna ld K M ua j2u j3u = true)
    (hlb : checkLowerEnv lnb ld K M lb_env j2l j3l = true)
    {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F)
      (Set.Icc (1 - ((lnb : ℝ) / ld) / 2) (1 - ((lnb : ℝ) / ld) / 3) ×ˢ
       Set.Icc (2 * (1 - ((lna : ℝ) / ld) / 2)) (2 * (1 - ((lna : ℝ) / ld) / 3))))
    (hmy : ∀ t ∈ Set.Icc (2 * (1 - ((lna : ℝ) / ld) / 2)) (2 * (1 - ((lna : ℝ) / ld) / 3)),
      MonotoneOn (fun y => F y t) (Set.Icc (1 - ((lnb : ℝ) / ld) / 2) (1 - ((lnb : ℝ) / ld) / 3)))
    (hat : ∀ y ∈ Set.Icc (1 - ((lnb : ℝ) / ld) / 2) (1 - ((lnb : ℝ) / ld) / 3),
      AntitoneOn (fun t => F y t) (Set.Icc (2 * (1 - ((lna : ℝ) / ld) / 2)) (2 * (1 - ((lna : ℝ) / ld) / 3)))) :
    let la : ℝ := (lna : ℝ) / ld
    let lb : ℝ := (lnb : ℝ) / ld
    let aa : ℝ := 1 - la / 2
    let ba : ℝ := 1 - la / 3
    let ha : ℝ := (ba - aa) / K
    let ab : ℝ := 1 - lb / 2
    let bb : ℝ := 1 - lb / 3
    let hb : ℝ := (bb - ab) / K
    (1 / (M : ℝ) ^ 3) * evalGrid ab hb (fun y => evalGrid (2 * aa) ha (fun t => F y t) (polyMul ua ua)) lb_env ≤
      (∫ T0, ∫ T1, ∫ T2, F (beta T0 lb) (beta T1 la + beta T2 la) ∂mu ∂mu ∂mu) := by
  obtain ⟨hlna, hlna2, hK, hM, hlen_ua⟩ := checkUpperEnv_dims hua
  obtain ⟨hlnb, hlnb2, _, _, hlen_lb⟩ := checkLowerEnv_dims hlb
  have hld : 0 < ld := by omega
  intro la lb aa ba ha ab bb hb
  have haa_eq : aa = 1 - la / 2 := rfl
  have hba_eq : ba = 1 - la / 3 := rfl
  have hab_eq : ab = 1 - lb / 2 := rfl
  have hbb_eq : bb = 1 - lb / 3 := rfl
  have hla0 : 0 < la := div_pos (Nat.cast_pos.mpr hlna) (Nat.cast_pos.mpr hld)
  have hla2 : la < 2 := by unfold la; rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]; exact_mod_cast hlna2
  have hlb0 : 0 < lb := div_pos (Nat.cast_pos.mpr hlnb) (Nat.cast_pos.mpr hld)
  have hlb2 : lb < 2 := by unfold lb; rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]; exact_mod_cast hlnb2
  have haa : aa ≤ ba := by linarith
  have hab : ab ≤ bb := by linarith
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hK_ne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hK)
  obtain ⟨hFc_cont, hFc_my, hFc_at, ⟨C, hC⟩⟩ := clampBox_props_mono_anti hab (by linarith) hcont hmy hat
  set Fc := clampBox ab bb (2 * aa) (2 * ba) F
  have hrhs_eq : (∫ T0, ∫ T1, ∫ T2, F (beta T0 lb) (beta T1 la + beta T2 la) ∂mu ∂mu ∂mu) =
      (∫ T0, ∫ T1, ∫ T2, Fc (beta T0 lb) (beta T1 la + beta T2 la) ∂mu ∂mu ∂mu) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun T0 => integral_congr_ae (Filter.Eventually.of_forall (fun T1 =>
      integral_congr_ae (Filter.Eventually.of_forall (fun T2 => ?_))))))
    have m0 := lemma_4_1_support T0 hlb0 hlb2
    have m1 := lemma_4_1_support T1 hla0 hla2
    have m2 := lemma_4_1_support T2 hla0 hla2
    dsimp only []
    unfold Fc clampBox
    rw [clampIcc_eq_self m0, clampIcc_eq_self ⟨by linarith [m1.1, m2.1], by linarith [m1.2, m2.2]⟩]
  rw [hrhs_eq]
  have hinner : ∀ T0 : InfTree23,
      (1 / (M : ℝ) ^ 2) * evalGrid (2 * aa) ha (Fc (beta T0 lb)) (polyMul ua ua) ≤
        (∫ T1, ∫ T2, Fc (beta T0 lb) (beta T1 la + beta T2 la) ∂mu ∂mu) := by
    intro T0
    refine sum2_lower_anti (measurable_beta la) hM_pos
      (fun g hg hga => upperEnv_sound_anti hua hg.continuousOn (fun _ _ _ _ huv => hga huv))
      (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hFc_at _) (hC _)
  have hi_r := integrable_biv3_outer (mu := mu) hFc_cont hC (measurable_beta lb) (measurable_beta la) (measurable_beta la)
  have hg_cont : Continuous (fun y => evalGrid (2 * aa) ha (fun t => Fc y t) (polyMul ua ua)) :=
    continuous_evalGrid hFc_cont _ _
  have hg_mono : Monotone (fun y => evalGrid (2 * aa) ha (fun t => Fc y t) (polyMul ua ua)) :=
    monotone_evalGrid_param hFc_my _
  have hi_l : Integrable (fun T0 => (1 / (M : ℝ) ^ 2) *
      evalGrid (2 * aa) ha (Fc (beta T0 lb)) (polyMul ua ua)) mu :=
    (integrable_clamped_mono hab hg_cont hg_mono (measurable_beta lb)
      (fun T0 => lemma_4_1_support T0 hlb0 hlb2)).const_mul _
  have houter : (1 / (M : ℝ) ^ 3) * evalGrid ab hb (fun y => evalGrid (2 * aa) ha (fun t => Fc y t) (polyMul ua ua)) lb_env ≤
      (∫ T0, ∫ T1, ∫ T2, Fc (beta T0 lb) (beta T1 la + beta T2 la) ∂mu ∂mu ∂mu) := by
    calc (1 / (M : ℝ) ^ 3) * evalGrid ab hb (fun y => evalGrid (2 * aa) ha (fun t => Fc y t) (polyMul ua ua)) lb_env
        = (1 / (M : ℝ) ^ 2) * ((1 / (M : ℝ)) * evalGrid ab hb
            (fun y => evalGrid (2 * aa) ha (fun t => Fc y t) (polyMul ua ua)) lb_env) := by ring
      _ ≤ (1 / (M : ℝ) ^ 2) * ∫ T0, evalGrid (2 * aa) ha (Fc (beta T0 lb)) (polyMul ua ua) ∂mu :=
          mul_le_mul_of_nonneg_left
            (lowerEnv_sound hlb hg_cont.continuousOn (fun _ _ _ _ huv => hg_mono huv)) (by positivity)
      _ = ∫ T0, (1 / (M : ℝ) ^ 2) * evalGrid (2 * aa) ha (Fc (beta T0 lb)) (polyMul ua ua) ∂mu :=
          (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono hi_l hi_r hinner
  have hlhs_eq : evalGrid ab hb (fun y => evalGrid (2 * aa) ha (fun t => Fc y t) (polyMul ua ua)) lb_env =
      evalGrid ab hb (fun y => evalGrid (2 * aa) ha (fun t => F y t) (polyMul ua ua)) lb_env := by
    have hplen := polyMul_length_le (le_of_eq hlen_ua) (le_of_eq hlen_ua)
    refine evalGrid_congr lb_env 0 (fun i _ hi => ?_)
    simp only [Nat.sub_zero]
    refine evalGrid_congr (polyMul ua ua) 0 (fun j _ hj => ?_)
    simp only [Nat.sub_zero]
    have hy : ab + (i : ℝ) * hb ∈ Set.Icc ab bb :=
      grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := K) (by omega)
        (by rw [mul_div_cancel₀ _ hK_ne]; linarith)
    have ht : 2 * aa + (j : ℝ) * ha ∈ Set.Icc (2 * aa) (2 * ba) := by
      refine grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := 2 * K) (by omega) ?_
      push_cast; field_simp [hK_ne]; linarith
    unfold Fc clampBox
    rw [clampIcc_eq_self hy, clampIcc_eq_self ht]
  rwa [hlhs_eq] at houter

lemma peel4_upper_mono_anti {mu : Measure InfTree23} [IsGWTree23 mu]
    {lna lnb ld K M : ℕ} {ua j2u j3u lb_env j2l j3l : List ℕ}
    (hua : checkUpperEnv lna ld K M ua j2u j3u = true)
    (hlb : checkLowerEnv lnb ld K M lb_env j2l j3l = true)
    {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F)
      (Set.Icc (1 - ((lna : ℝ) / ld) / 2) (1 - ((lna : ℝ) / ld) / 3) ×ˢ
       Set.Icc (3 * (1 - ((lnb : ℝ) / ld) / 2)) (3 * (1 - ((lnb : ℝ) / ld) / 3))))
    (hmy : ∀ t ∈ Set.Icc (3 * (1 - ((lnb : ℝ) / ld) / 2)) (3 * (1 - ((lnb : ℝ) / ld) / 3)),
      MonotoneOn (fun y => F y t) (Set.Icc (1 - ((lna : ℝ) / ld) / 2) (1 - ((lna : ℝ) / ld) / 3)))
    (hat : ∀ y ∈ Set.Icc (1 - ((lna : ℝ) / ld) / 2) (1 - ((lna : ℝ) / ld) / 3),
      AntitoneOn (fun t => F y t) (Set.Icc (3 * (1 - ((lnb : ℝ) / ld) / 2)) (3 * (1 - ((lnb : ℝ) / ld) / 3)))) :
    let la : ℝ := (lna : ℝ) / ld
    let lb : ℝ := (lnb : ℝ) / ld
    let aa : ℝ := 1 - la / 2
    let ba : ℝ := 1 - la / 3
    let ha : ℝ := (ba - aa) / K
    let ab : ℝ := 1 - lb / 2
    let bb : ℝ := 1 - lb / 3
    let hb : ℝ := (bb - ab) / K
    (∫ T0, ∫ T1, ∫ T2, ∫ T3, F (beta T0 la) (beta T1 lb + beta T2 lb + beta T3 lb) ∂mu ∂mu ∂mu ∂mu) ≤
      (1 / (M : ℝ) ^ 4) * evalGrid aa ha
        (fun y => evalGrid (3 * ab) hb (fun t => F y t) (polyMul (polyMul lb_env lb_env) lb_env)) ua := by
  obtain ⟨hlna, hlna2, hK, hM, hlen_ua⟩ := checkUpperEnv_dims hua
  obtain ⟨hlnb, hlnb2, _, _, hlen_lb⟩ := checkLowerEnv_dims hlb
  have hld : 0 < ld := by omega
  intro la lb aa ba ha ab bb hb
  have haa_eq : aa = 1 - la / 2 := rfl
  have hba_eq : ba = 1 - la / 3 := rfl
  have hab_eq : ab = 1 - lb / 2 := rfl
  have hbb_eq : bb = 1 - lb / 3 := rfl
  have hla0 : 0 < la := div_pos (Nat.cast_pos.mpr hlna) (Nat.cast_pos.mpr hld)
  have hla2 : la < 2 := by unfold la; rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]; exact_mod_cast hlna2
  have hlb0 : 0 < lb := div_pos (Nat.cast_pos.mpr hlnb) (Nat.cast_pos.mpr hld)
  have hlb2 : lb < 2 := by unfold lb; rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]; exact_mod_cast hlnb2
  have haa : aa ≤ ba := by linarith
  have hab : ab ≤ bb := by linarith
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hK_ne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hK)
  obtain ⟨hFc_cont, hFc_my, hFc_at, ⟨C, hC⟩⟩ := clampBox_props_mono_anti haa (by linarith) hcont hmy hat
  set Fc := clampBox aa ba (3 * ab) (3 * bb) F
  have hlhs_eq : (∫ T0, ∫ T1, ∫ T2, ∫ T3, F (beta T0 la) (beta T1 lb + beta T2 lb + beta T3 lb) ∂mu ∂mu ∂mu ∂mu) =
      (∫ T0, ∫ T1, ∫ T2, ∫ T3, Fc (beta T0 la) (beta T1 lb + beta T2 lb + beta T3 lb) ∂mu ∂mu ∂mu ∂mu) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun T0 => integral_congr_ae (Filter.Eventually.of_forall (fun T1 =>
      integral_congr_ae (Filter.Eventually.of_forall (fun T2 => integral_congr_ae (Filter.Eventually.of_forall (fun T3 => ?_))))))))
    have m0 := lemma_4_1_support T0 hla0 hla2
    have m1 := lemma_4_1_support T1 hlb0 hlb2
    have m2 := lemma_4_1_support T2 hlb0 hlb2
    have m3 := lemma_4_1_support T3 hlb0 hlb2
    dsimp only []
    unfold Fc clampBox
    rw [clampIcc_eq_self m0, clampIcc_eq_self ⟨by linarith [m1.1, m2.1, m3.1], by linarith [m1.2, m2.2, m3.2]⟩]
  rw [hlhs_eq]
  have hinner : ∀ T0 : InfTree23,
      (∫ T1, ∫ T2, ∫ T3, Fc (beta T0 la) (beta T1 lb + beta T2 lb + beta T3 lb) ∂mu ∂mu ∂mu) ≤
        (1 / (M : ℝ) ^ 3) * evalGrid (3 * ab) hb (Fc (beta T0 la)) (polyMul (polyMul lb_env lb_env) lb_env) := by
    intro T0
    refine sum3_upper_anti (measurable_beta lb) hM_pos
      (fun g hg hga => lowerEnv_sound_anti hlb hg.continuousOn (fun _ _ _ _ huv => hga huv))
      (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hFc_at _) (hC _)
  have hi_l := integrable_biv4_outer (mu := mu) hFc_cont hC (measurable_beta la)
    (measurable_beta lb) (measurable_beta lb) (measurable_beta lb)
  have hg_cont : Continuous (fun y => evalGrid (3 * ab) hb (fun t => Fc y t) (polyMul (polyMul lb_env lb_env) lb_env)) :=
    continuous_evalGrid hFc_cont _ _
  have hg_mono : Monotone (fun y => evalGrid (3 * ab) hb (fun t => Fc y t) (polyMul (polyMul lb_env lb_env) lb_env)) :=
    monotone_evalGrid_param hFc_my _
  have hi_r : Integrable (fun T0 => (1 / (M : ℝ) ^ 3) *
      evalGrid (3 * ab) hb (Fc (beta T0 la)) (polyMul (polyMul lb_env lb_env) lb_env)) mu :=
    (integrable_clamped_mono haa hg_cont hg_mono (measurable_beta la)
      (fun T0 => lemma_4_1_support T0 hla0 hla2)).const_mul _
  have houter : (∫ T0, ∫ T1, ∫ T2, ∫ T3, Fc (beta T0 la) (beta T1 lb + beta T2 lb + beta T3 lb) ∂mu ∂mu ∂mu ∂mu) ≤
      (1 / (M : ℝ) ^ 4) * evalGrid aa ha
        (fun y => evalGrid (3 * ab) hb (fun t => Fc y t) (polyMul (polyMul lb_env lb_env) lb_env)) ua := by
    calc (∫ T0, ∫ T1, ∫ T2, ∫ T3, Fc (beta T0 la) (beta T1 lb + beta T2 lb + beta T3 lb) ∂mu ∂mu ∂mu ∂mu)
        ≤ ∫ T0, (1 / (M : ℝ) ^ 3) * evalGrid (3 * ab) hb (Fc (beta T0 la)) (polyMul (polyMul lb_env lb_env) lb_env) ∂mu :=
          integral_mono hi_l hi_r hinner
      _ = (1 / (M : ℝ) ^ 3) * ∫ T0, evalGrid (3 * ab) hb (Fc (beta T0 la)) (polyMul (polyMul lb_env lb_env) lb_env) ∂mu :=
          integral_const_mul _ _
      _ ≤ (1 / (M : ℝ) ^ 3) * ((1 / (M : ℝ)) * evalGrid aa ha
          (fun y => evalGrid (3 * ab) hb (fun t => Fc y t) (polyMul (polyMul lb_env lb_env) lb_env)) ua) :=
          mul_le_mul_of_nonneg_left
            (upperEnv_sound hua hg_cont.continuousOn (fun _ _ _ _ huv => hg_mono huv)) (by positivity)
      _ = _ := by ring
  have hrhs_eq : evalGrid aa ha (fun y => evalGrid (3 * ab) hb (fun t => Fc y t) (polyMul (polyMul lb_env lb_env) lb_env)) ua =
      evalGrid aa ha (fun y => evalGrid (3 * ab) hb (fun t => F y t) (polyMul (polyMul lb_env lb_env) lb_env)) ua := by
    have hp2 := polyMul_length_le (le_of_eq hlen_lb) (le_of_eq hlen_lb)
    have hp3 := polyMul_length_le hp2 (le_of_eq hlen_lb)
    refine evalGrid_congr ua 0 (fun i _ hi => ?_)
    simp only [Nat.sub_zero]
    refine evalGrid_congr (polyMul (polyMul lb_env lb_env) lb_env) 0 (fun j _ hj => ?_)
    simp only [Nat.sub_zero]
    have hy : aa + (i : ℝ) * ha ∈ Set.Icc aa ba :=
      grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := K) (by omega)
        (by rw [mul_div_cancel₀ _ hK_ne]; linarith)
    have ht : 3 * ab + (j : ℝ) * hb ∈ Set.Icc (3 * ab) (3 * bb) := by
      refine grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := 3 * K) (by omega) ?_
      push_cast; field_simp [hK_ne]; linarith
    unfold Fc clampBox
    rw [clampIcc_eq_self hy, clampIcc_eq_self ht]
  rwa [hrhs_eq] at houter

lemma peel4_lower_mono_anti {mu : Measure InfTree23} [IsGWTree23 mu]
    {lna lnb ld K M : ℕ} {ua j2u j3u lb_env j2l j3l : List ℕ}
    (hua : checkUpperEnv lna ld K M ua j2u j3u = true)
    (hlb : checkLowerEnv lnb ld K M lb_env j2l j3l = true)
    {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F)
      (Set.Icc (1 - ((lnb : ℝ) / ld) / 2) (1 - ((lnb : ℝ) / ld) / 3) ×ˢ
       Set.Icc (3 * (1 - ((lna : ℝ) / ld) / 2)) (3 * (1 - ((lna : ℝ) / ld) / 3))))
    (hmy : ∀ t ∈ Set.Icc (3 * (1 - ((lna : ℝ) / ld) / 2)) (3 * (1 - ((lna : ℝ) / ld) / 3)),
      MonotoneOn (fun y => F y t) (Set.Icc (1 - ((lnb : ℝ) / ld) / 2) (1 - ((lnb : ℝ) / ld) / 3)))
    (hat : ∀ y ∈ Set.Icc (1 - ((lnb : ℝ) / ld) / 2) (1 - ((lnb : ℝ) / ld) / 3),
      AntitoneOn (fun t => F y t) (Set.Icc (3 * (1 - ((lna : ℝ) / ld) / 2)) (3 * (1 - ((lna : ℝ) / ld) / 3)))) :
    let la : ℝ := (lna : ℝ) / ld
    let lb : ℝ := (lnb : ℝ) / ld
    let aa : ℝ := 1 - la / 2
    let ba : ℝ := 1 - la / 3
    let ha : ℝ := (ba - aa) / K
    let ab : ℝ := 1 - lb / 2
    let bb : ℝ := 1 - lb / 3
    let hb : ℝ := (bb - ab) / K
    (1 / (M : ℝ) ^ 4) * evalGrid ab hb
        (fun y => evalGrid (3 * aa) ha (fun t => F y t) (polyMul (polyMul ua ua) ua)) lb_env ≤
      (∫ T0, ∫ T1, ∫ T2, ∫ T3, F (beta T0 lb) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) := by
  obtain ⟨hlna, hlna2, hK, hM, hlen_ua⟩ := checkUpperEnv_dims hua
  obtain ⟨hlnb, hlnb2, _, _, hlen_lb⟩ := checkLowerEnv_dims hlb
  have hld : 0 < ld := by omega
  intro la lb aa ba ha ab bb hb
  have haa_eq : aa = 1 - la / 2 := rfl
  have hba_eq : ba = 1 - la / 3 := rfl
  have hab_eq : ab = 1 - lb / 2 := rfl
  have hbb_eq : bb = 1 - lb / 3 := rfl
  have hla0 : 0 < la := div_pos (Nat.cast_pos.mpr hlna) (Nat.cast_pos.mpr hld)
  have hla2 : la < 2 := by unfold la; rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]; exact_mod_cast hlna2
  have hlb0 : 0 < lb := div_pos (Nat.cast_pos.mpr hlnb) (Nat.cast_pos.mpr hld)
  have hlb2 : lb < 2 := by unfold lb; rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]; exact_mod_cast hlnb2
  have haa : aa ≤ ba := by linarith
  have hab : ab ≤ bb := by linarith
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hK_ne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hK)
  obtain ⟨hFc_cont, hFc_my, hFc_at, ⟨C, hC⟩⟩ := clampBox_props_mono_anti hab (by linarith) hcont hmy hat
  set Fc := clampBox ab bb (3 * aa) (3 * ba) F
  have hrhs_eq : (∫ T0, ∫ T1, ∫ T2, ∫ T3, F (beta T0 lb) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) =
      (∫ T0, ∫ T1, ∫ T2, ∫ T3, Fc (beta T0 lb) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun T0 => integral_congr_ae (Filter.Eventually.of_forall (fun T1 =>
      integral_congr_ae (Filter.Eventually.of_forall (fun T2 => integral_congr_ae (Filter.Eventually.of_forall (fun T3 => ?_))))))))
    have m0 := lemma_4_1_support T0 hlb0 hlb2
    have m1 := lemma_4_1_support T1 hla0 hla2
    have m2 := lemma_4_1_support T2 hla0 hla2
    have m3 := lemma_4_1_support T3 hla0 hla2
    dsimp only []
    unfold Fc clampBox
    rw [clampIcc_eq_self m0, clampIcc_eq_self ⟨by linarith [m1.1, m2.1, m3.1], by linarith [m1.2, m2.2, m3.2]⟩]
  rw [hrhs_eq]
  have hinner : ∀ T0 : InfTree23,
      (1 / (M : ℝ) ^ 3) * evalGrid (3 * aa) ha (Fc (beta T0 lb)) (polyMul (polyMul ua ua) ua) ≤
        (∫ T1, ∫ T2, ∫ T3, Fc (beta T0 lb) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu) := by
    intro T0
    refine sum3_lower_anti (measurable_beta la) hM_pos
      (fun g hg hga => upperEnv_sound_anti hua hg.continuousOn (fun _ _ _ _ huv => hga huv))
      (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hFc_at _) (hC _)
  have hi_r := integrable_biv4_outer (mu := mu) hFc_cont hC (measurable_beta lb)
    (measurable_beta la) (measurable_beta la) (measurable_beta la)
  have hg_cont : Continuous (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) :=
    continuous_evalGrid hFc_cont _ _
  have hg_mono : Monotone (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) :=
    monotone_evalGrid_param hFc_my _
  have hi_l : Integrable (fun T0 => (1 / (M : ℝ) ^ 3) *
      evalGrid (3 * aa) ha (Fc (beta T0 lb)) (polyMul (polyMul ua ua) ua)) mu :=
    (integrable_clamped_mono hab hg_cont hg_mono (measurable_beta lb)
      (fun T0 => lemma_4_1_support T0 hlb0 hlb2)).const_mul _
  have houter : (1 / (M : ℝ) ^ 4) * evalGrid ab hb
        (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) lb_env ≤
      (∫ T0, ∫ T1, ∫ T2, ∫ T3, Fc (beta T0 lb) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) := by
    calc (1 / (M : ℝ) ^ 4) * evalGrid ab hb
          (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) lb_env
        = (1 / (M : ℝ) ^ 3) * ((1 / (M : ℝ)) * evalGrid ab hb
            (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) lb_env) := by ring
      _ ≤ (1 / (M : ℝ) ^ 3) * ∫ T0, evalGrid (3 * aa) ha (Fc (beta T0 lb)) (polyMul (polyMul ua ua) ua) ∂mu :=
          mul_le_mul_of_nonneg_left
            (lowerEnv_sound hlb hg_cont.continuousOn (fun _ _ _ _ huv => hg_mono huv)) (by positivity)
      _ = ∫ T0, (1 / (M : ℝ) ^ 3) * evalGrid (3 * aa) ha (Fc (beta T0 lb)) (polyMul (polyMul ua ua) ua) ∂mu :=
          (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono hi_l hi_r hinner
  have hlhs_eq : evalGrid ab hb (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) lb_env =
      evalGrid ab hb (fun y => evalGrid (3 * aa) ha (fun t => F y t) (polyMul (polyMul ua ua) ua)) lb_env := by
    have hp2 := polyMul_length_le (le_of_eq hlen_ua) (le_of_eq hlen_ua)
    have hp3 := polyMul_length_le hp2 (le_of_eq hlen_ua)
    refine evalGrid_congr lb_env 0 (fun i _ hi => ?_)
    simp only [Nat.sub_zero]
    refine evalGrid_congr (polyMul (polyMul ua ua) ua) 0 (fun j _ hj => ?_)
    simp only [Nat.sub_zero]
    have hy : ab + (i : ℝ) * hb ∈ Set.Icc ab bb :=
      grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := K) (by omega)
        (by rw [mul_div_cancel₀ _ hK_ne]; linarith)
    have ht : 3 * aa + (j : ℝ) * ha ∈ Set.Icc (3 * aa) (3 * ba) := by
      refine grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := 3 * K) (by omega) ?_
      push_cast; field_simp [hK_ne]; linarith
    unfold Fc clampBox
    rw [clampIcc_eq_self hy, clampIcc_eq_self ht]
  rwa [hlhs_eq] at houter

lemma peel4_upper_mono_mono {mu : Measure InfTree23} [IsGWTree23 mu]
    {lna ld K M : ℕ} {ua j2u j3u : List ℕ}
    (hua : checkUpperEnv lna ld K M ua j2u j3u = true)
    {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F)
      (Set.Icc (1 - ((lna : ℝ) / ld) / 2) (1 - ((lna : ℝ) / ld) / 3) ×ˢ
       Set.Icc (3 * (1 - ((lna : ℝ) / ld) / 2)) (3 * (1 - ((lna : ℝ) / ld) / 3))))
    (hmy : ∀ t ∈ Set.Icc (3 * (1 - ((lna : ℝ) / ld) / 2)) (3 * (1 - ((lna : ℝ) / ld) / 3)),
      MonotoneOn (fun y => F y t) (Set.Icc (1 - ((lna : ℝ) / ld) / 2) (1 - ((lna : ℝ) / ld) / 3)))
    (hmt : ∀ y ∈ Set.Icc (1 - ((lna : ℝ) / ld) / 2) (1 - ((lna : ℝ) / ld) / 3),
      MonotoneOn (fun t => F y t) (Set.Icc (3 * (1 - ((lna : ℝ) / ld) / 2)) (3 * (1 - ((lna : ℝ) / ld) / 3)))) :
    let la : ℝ := (lna : ℝ) / ld
    let aa : ℝ := 1 - la / 2
    let ba : ℝ := 1 - la / 3
    let ha : ℝ := (ba - aa) / K
    (∫ T0, ∫ T1, ∫ T2, ∫ T3, F (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) ≤
      (1 / (M : ℝ) ^ 4) * evalGrid aa ha
        (fun y => evalGrid (3 * aa) ha (fun t => F y t) (polyMul (polyMul ua ua) ua)) ua := by
  obtain ⟨hlna, hlna2, hK, hM, hlen_ua⟩ := checkUpperEnv_dims hua
  have hld : 0 < ld := by omega
  intro la aa ba ha
  have haa_eq : aa = 1 - la / 2 := rfl
  have hba_eq : ba = 1 - la / 3 := rfl
  have hla0 : 0 < la := div_pos (Nat.cast_pos.mpr hlna) (Nat.cast_pos.mpr hld)
  have hla2 : la < 2 := by unfold la; rw [div_lt_iff₀ (Nat.cast_pos.mpr hld)]; exact_mod_cast hlna2
  have haa : aa ≤ ba := by linarith
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hK_ne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hK)
  obtain ⟨hFc_cont, hFc_my, hFc_mt, ⟨C, hC⟩⟩ := clampBox_props_mono_mono haa (by linarith) hcont hmy hmt
  set Fc := clampBox aa ba (3 * aa) (3 * ba) F
  have hlhs_eq : (∫ T0, ∫ T1, ∫ T2, ∫ T3, F (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) =
      (∫ T0, ∫ T1, ∫ T2, ∫ T3, Fc (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun T0 => integral_congr_ae (Filter.Eventually.of_forall (fun T1 =>
      integral_congr_ae (Filter.Eventually.of_forall (fun T2 => integral_congr_ae (Filter.Eventually.of_forall (fun T3 => ?_))))))))
    have m0 := lemma_4_1_support T0 hla0 hla2
    have m1 := lemma_4_1_support T1 hla0 hla2
    have m2 := lemma_4_1_support T2 hla0 hla2
    have m3 := lemma_4_1_support T3 hla0 hla2
    dsimp only []
    unfold Fc clampBox
    rw [clampIcc_eq_self m0, clampIcc_eq_self ⟨by linarith [m1.1, m2.1, m3.1], by linarith [m1.2, m2.2, m3.2]⟩]
  rw [hlhs_eq]
  have hinner : ∀ T0 : InfTree23,
      (∫ T1, ∫ T2, ∫ T3, Fc (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu) ≤
        (1 / (M : ℝ) ^ 3) * evalGrid (3 * aa) ha (Fc (beta T0 la)) (polyMul (polyMul ua ua) ua) := by
    intro T0
    refine sum3_upper_mono (measurable_beta la) hM_pos
      (fun g hg hgm => upperEnv_sound hua hg.continuousOn (fun _ _ _ _ huv => hgm huv))
      (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hFc_mt _) (hC _)
  have hi_l := integrable_biv4_outer (mu := mu) hFc_cont hC (measurable_beta la)
    (measurable_beta la) (measurable_beta la) (measurable_beta la)
  have hg_cont : Continuous (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) :=
    continuous_evalGrid hFc_cont _ _
  have hg_mono : Monotone (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) :=
    monotone_evalGrid_param hFc_my _
  have hi_r : Integrable (fun T0 => (1 / (M : ℝ) ^ 3) *
      evalGrid (3 * aa) ha (Fc (beta T0 la)) (polyMul (polyMul ua ua) ua)) mu :=
    (integrable_clamped_mono haa hg_cont hg_mono (measurable_beta la)
      (fun T0 => lemma_4_1_support T0 hla0 hla2)).const_mul _
  have houter : (∫ T0, ∫ T1, ∫ T2, ∫ T3, Fc (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) ≤
      (1 / (M : ℝ) ^ 4) * evalGrid aa ha
        (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) ua := by
    calc (∫ T0, ∫ T1, ∫ T2, ∫ T3, Fc (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu)
        ≤ ∫ T0, (1 / (M : ℝ) ^ 3) * evalGrid (3 * aa) ha (Fc (beta T0 la)) (polyMul (polyMul ua ua) ua) ∂mu :=
          integral_mono hi_l hi_r hinner
      _ = (1 / (M : ℝ) ^ 3) * ∫ T0, evalGrid (3 * aa) ha (Fc (beta T0 la)) (polyMul (polyMul ua ua) ua) ∂mu :=
          integral_const_mul _ _
      _ ≤ (1 / (M : ℝ) ^ 3) * ((1 / (M : ℝ)) * evalGrid aa ha
          (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) ua) :=
          mul_le_mul_of_nonneg_left
            (upperEnv_sound hua hg_cont.continuousOn (fun _ _ _ _ huv => hg_mono huv)) (by positivity)
      _ = _ := by ring
  have hrhs_eq : evalGrid aa ha (fun y => evalGrid (3 * aa) ha (fun t => Fc y t) (polyMul (polyMul ua ua) ua)) ua =
      evalGrid aa ha (fun y => evalGrid (3 * aa) ha (fun t => F y t) (polyMul (polyMul ua ua) ua)) ua := by
    have hp2 := polyMul_length_le (le_of_eq hlen_ua) (le_of_eq hlen_ua)
    have hp3 := polyMul_length_le hp2 (le_of_eq hlen_ua)
    refine evalGrid_congr ua 0 (fun i _ hi => ?_)
    simp only [Nat.sub_zero]
    refine evalGrid_congr (polyMul (polyMul ua ua) ua) 0 (fun j _ hj => ?_)
    simp only [Nat.sub_zero]
    have hy : aa + (i : ℝ) * ha ∈ Set.Icc aa ba :=
      grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := K) (by omega)
        (by rw [mul_div_cancel₀ _ hK_ne]; linarith)
    have ht : 3 * aa + (j : ℝ) * ha ∈ Set.Icc (3 * aa) (3 * ba) := by
      refine grid_pt_mem_Icc (div_nonneg (by linarith) (Nat.cast_nonneg K)) (K := 3 * K) (by omega) ?_
      push_cast; field_simp [hK_ne]; linarith
    unfold Fc clampBox
    rw [clampIcc_eq_self hy, clampIcc_eq_self ht]
  rwa [hrhs_eq] at houter

/-! ## 5. Multi-Tree Conductance Expectations (`E2Expect`, `E3Expect`, `RFunc`) -/

/-- Expected root-edge conductance contribution for degree `ν = 2`. -/
noncomputable def E2Expect (mu : Measure InfTree23) (lam : ℝ) : ℝ :=
  ∫ T0, ∫ T1, ∫ T2, f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam) ∂mu ∂mu ∂mu

/-- Expected root-edge conductance contribution for degree `ν = 3`. -/
noncomputable def E3Expect (mu : Measure InfTree23) (lam : ℝ) : ℝ :=
  ∫ T0, ∫ T1, ∫ T2, ∫ T3,
    f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) ∂mu ∂mu ∂mu ∂mu

/-- Ratio `R(λ) = (2 E₂(λ) + 3 E₃(λ)) / (E₂(λ) + E₃(λ))` (`Lemma 3.1` in Paper 24). -/
noncomputable def RFunc (mu : Measure InfTree23) (lam : ℝ) : ℝ :=
  (2 * E2Expect mu lam + 3 * E3Expect mu lam) / (E2Expect mu lam + E3Expect mu lam)

lemma f0Func_box_props {lam ay by_ at_ bt : ℝ}
    (hay0 : 0 ≤ ay) (_hay : ay ≤ by_) (_hat : at_ ≤ bt) (hden_pos : 0 < lam - 1 + at_) :
    ContinuousOn (Function.uncurry (f0Func lam)) (Set.Icc ay by_ ×ˢ Set.Icc at_ bt) ∧
    (∀ t ∈ Set.Icc at_ bt, MonotoneOn (fun y => f0Func lam y t) (Set.Icc ay by_)) ∧
    (∀ y ∈ Set.Icc ay by_, AntitoneOn (fun t => f0Func lam y t) (Set.Icc at_ bt)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Function.uncurry f0Func
    refine continuousOn_fst.div ((continuousOn_const.add continuousOn_fst).add continuousOn_snd) ?_
    intro p hp
    have hy := hp.1.1
    have ht := hp.2.1
    linarith
  · intro t ht y1 hy1 y2 hy2 hle
    exact f0Func_mono_y0 (hay0.trans hy1.1) hle (by linarith [ht.1])
  · intro y hy t1 ht1 t2 ht2 hle
    exact f0Func_anti_t (hay0.trans hy.1) hle (by linarith [hy.1, ht1.1])

lemma f0_integrable3 {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {lam lamY lamT : ℝ} (hY0 : 0 < lamY) (hY2 : lamY < 2) (hT0 : 0 < lamT) (hT2 : lamT < 2)
    (hden : 0 < lam - 1 + 2 * (1 - lamT / 2)) :
    (∀ T0 T1, Integrable (fun T2 => f0Func lam (beta T0 lamY) (beta T1 lamT + beta T2 lamT)) mu) ∧
    (∀ T0, Integrable (fun T1 => ∫ T2, f0Func lam (beta T0 lamY) (beta T1 lamT + beta T2 lamT) ∂mu) mu) ∧
    Integrable (fun T0 => ∫ T1, ∫ T2, f0Func lam (beta T0 lamY) (beta T1 lamT + beta T2 lamT) ∂mu ∂mu) mu := by
  set ay := 1 - lamY / 2; set by_ := 1 - lamY / 3
  set at_ := 2 * (1 - lamT / 2); set bt := 2 * (1 - lamT / 3)
  obtain ⟨hc, hmy, hat⟩ := f0Func_box_props (lam := lam) (ay := ay) (by_ := by_) (at_ := at_) (bt := bt)
    (by unfold ay; linarith) (by unfold ay by_; linarith) (by unfold at_ bt; linarith) hden
  obtain ⟨hFc_cont, _, _, ⟨C, hC⟩⟩ := clampBox_props_mono_anti (by unfold ay by_; linarith) (by unfold at_ bt; linarith) hc hmy hat
  set Fc := clampBox ay by_ at_ bt (f0Func lam)
  have hpt : ∀ T0 T1 T2, f0Func lam (beta T0 lamY) (beta T1 lamT + beta T2 lamT) =
      Fc (beta T0 lamY) (beta T1 lamT + beta T2 lamT) := by
    intro T0 T1 T2
    have m0 := lemma_4_1_support T0 hY0 hY2
    have m1 := lemma_4_1_support T1 hT0 hT2
    have m2 := lemma_4_1_support T2 hT0 hT2
    unfold Fc clampBox
    rw [clampIcc_eq_self m0, clampIcc_eq_self ⟨by unfold at_; linarith [m1.1, m2.1], by unfold bt; linarith [m1.2, m2.2]⟩]
  simp_rw [hpt]
  refine ⟨fun T0 T1 => ?_, fun T0 => ?_, integrable_biv3_outer (mu := mu) hFc_cont hC (measurable_beta _) (measurable_beta _) (measurable_beta _)⟩
  · exact (integrable_sum2 (mu := mu) (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hC _) (measurable_beta _) (measurable_beta _)).1 T1
  · exact (integrable_sum2 (mu := mu) (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hC _) (measurable_beta _) (measurable_beta _)).2.1

lemma f0_integrable4 {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {lam lamY lamT : ℝ} (hY0 : 0 < lamY) (hY2 : lamY < 2) (hT0 : 0 < lamT) (hT2 : lamT < 2)
    (hden : 0 < lam - 1 + 3 * (1 - lamT / 2)) :
    (∀ T0 T1 T2, Integrable (fun T3 => f0Func lam (beta T0 lamY) (beta T1 lamT + beta T2 lamT + beta T3 lamT)) mu) ∧
    (∀ T0 T1, Integrable (fun T2 => ∫ T3, f0Func lam (beta T0 lamY) (beta T1 lamT + beta T2 lamT + beta T3 lamT) ∂mu) mu) ∧
    (∀ T0, Integrable (fun T1 => ∫ T2, ∫ T3, f0Func lam (beta T0 lamY) (beta T1 lamT + beta T2 lamT + beta T3 lamT) ∂mu ∂mu) mu) ∧
    Integrable (fun T0 => ∫ T1, ∫ T2, ∫ T3, f0Func lam (beta T0 lamY) (beta T1 lamT + beta T2 lamT + beta T3 lamT) ∂mu ∂mu ∂mu) mu := by
  set ay := 1 - lamY / 2; set by_ := 1 - lamY / 3
  set at_ := 3 * (1 - lamT / 2); set bt := 3 * (1 - lamT / 3)
  obtain ⟨hc, hmy, hat⟩ := f0Func_box_props (lam := lam) (ay := ay) (by_ := by_) (at_ := at_) (bt := bt)
    (by unfold ay; linarith) (by unfold ay by_; linarith) (by unfold at_ bt; linarith) hden
  obtain ⟨hFc_cont, _, _, ⟨C, hC⟩⟩ := clampBox_props_mono_anti (by unfold ay by_; linarith) (by unfold at_ bt; linarith) hc hmy hat
  set Fc := clampBox ay by_ at_ bt (f0Func lam)
  have hpt : ∀ T0 T1 T2 T3, f0Func lam (beta T0 lamY) (beta T1 lamT + beta T2 lamT + beta T3 lamT) =
      Fc (beta T0 lamY) (beta T1 lamT + beta T2 lamT + beta T3 lamT) := by
    intro T0 T1 T2 T3
    have m0 := lemma_4_1_support T0 hY0 hY2
    have m1 := lemma_4_1_support T1 hT0 hT2
    have m2 := lemma_4_1_support T2 hT0 hT2
    have m3 := lemma_4_1_support T3 hT0 hT2
    unfold Fc clampBox
    rw [clampIcc_eq_self m0, clampIcc_eq_self ⟨by unfold at_; linarith [m1.1, m2.1, m3.1], by unfold bt; linarith [m1.2, m2.2, m3.2]⟩]
  simp_rw [hpt]
  refine ⟨fun T0 T1 T2 => ?_, fun T0 T1 => ?_, fun T0 => ?_,
    integrable_biv4_outer (mu := mu) hFc_cont hC (measurable_beta _) (measurable_beta _) (measurable_beta _) (measurable_beta _)⟩
  · exact (integrable_sum3 (mu := mu) (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hC _) (measurable_beta _) (measurable_beta _) (measurable_beta _)).1 T1 T2
  · exact (integrable_sum3 (mu := mu) (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hC _) (measurable_beta _) (measurable_beta _) (measurable_beta _)).2.1 T1
  · exact (integrable_sum3 (mu := mu) (hFc_cont.comp (continuous_const.prodMk continuous_id)) (hC _) (measurable_beta _) (measurable_beta _) (measurable_beta _)).2.2.1

theorem E2Expect_pos {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {lam : ℝ} (h0 : 0 < lam) (h2 : lam < 2) : 0 < E2Expect mu lam := by
  set c := (1 - lam / 2) / 2
  have hc : 0 < c := by unfold c; linarith
  obtain ⟨hi2, hi1, hi0⟩ := f0_integrable3 (mu := mu) (lam := lam) h0 h2 h0 h2 (by linarith)
  have hpt : ∀ T0 T1 T2, c ≤ f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam) := by
    intro T0 T1 T2
    have m0 := lemma_4_1_support T0 h0 h2
    have m1 := lemma_4_1_support T1 h0 h2
    have m2 := lemma_4_1_support T2 h0 h2
    unfold c f0Func
    have hd : 0 < lam - 1 + beta T0 lam + (beta T1 lam + beta T2 lam) := by linarith
    have hd_le : lam - 1 + beta T0 lam + (beta T1 lam + beta T2 lam) ≤ 2 := by linarith
    calc (1 - lam / 2) / 2 ≤ (beta T0 lam) / 2 := div_le_div_of_nonneg_right m0.1 (by norm_num)
      _ ≤ (beta T0 lam) / (lam - 1 + beta T0 lam + (beta T1 lam + beta T2 lam)) :=
          div_le_div_of_nonneg_left (by linarith) hd hd_le
  have hle : c ≤ E2Expect mu lam := by
    unfold E2Expect
    have step2 : ∀ T0 T1, c ≤ ∫ T2, f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam) ∂mu := by
      intro T0 T1
      simpa using integral_mono (integrable_const c) (hi2 T0 T1) (hpt T0 T1)
    have step1 : ∀ T0, c ≤ ∫ T1, ∫ T2, f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam) ∂mu ∂mu := by
      intro T0
      simpa using integral_mono (integrable_const c) (hi1 T0) (step2 T0)
    simpa using integral_mono (integrable_const c) hi0 step1
  exact lt_of_lt_of_le hc hle

theorem E3Expect_pos {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {lam : ℝ} (h0 : 0 < lam) (h2 : lam < 2) : 0 < E3Expect mu lam := by
  set c := (1 - lam / 2) / 3
  have hc : 0 < c := by unfold c; linarith
  obtain ⟨hi3, hi2, hi1, hi0⟩ := f0_integrable4 (mu := mu) (lam := lam) h0 h2 h0 h2 (by linarith)
  have hpt : ∀ T0 T1 T2 T3, c ≤ f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) := by
    intro T0 T1 T2 T3
    have m0 := lemma_4_1_support T0 h0 h2
    have m1 := lemma_4_1_support T1 h0 h2
    have m2 := lemma_4_1_support T2 h0 h2
    have m3 := lemma_4_1_support T3 h0 h2
    unfold c f0Func
    have hd : 0 < lam - 1 + beta T0 lam + (beta T1 lam + beta T2 lam + beta T3 lam) := by linarith
    have hd_le : lam - 1 + beta T0 lam + (beta T1 lam + beta T2 lam + beta T3 lam) ≤ 3 := by linarith
    calc (1 - lam / 2) / 3 ≤ (beta T0 lam) / 3 := div_le_div_of_nonneg_right m0.1 (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith) hd hd_le
  have hle : c ≤ E3Expect mu lam := by
    unfold E3Expect
    have s3 : ∀ T0 T1 T2, c ≤ ∫ T3, f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) ∂mu :=
      fun T0 T1 T2 => by simpa using integral_mono (integrable_const c) (hi3 T0 T1 T2) (hpt T0 T1 T2)
    have s2 : ∀ T0 T1, c ≤ ∫ T2, ∫ T3, f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) ∂mu ∂mu :=
      fun T0 T1 => by simpa using integral_mono (integrable_const c) (hi2 T0 T1) (s3 T0 T1)
    have s1 : ∀ T0, c ≤ ∫ T1, ∫ T2, ∫ T3, f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) ∂mu ∂mu ∂mu :=
      fun T0 => by simpa using integral_mono (integrable_const c) (hi1 T0) (s2 T0)
    simpa using integral_mono (integrable_const c) hi0 s1
  exact lt_of_lt_of_le hc hle

theorem E3Expect_le_E2Expect {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {lam : ℝ} (h0 : 0 < lam) (h2 : lam < 2) : E3Expect mu lam ≤ E2Expect mu lam := by
  obtain ⟨hi2_2, hi2_1, hi2_0⟩ := f0_integrable3 (mu := mu) (lam := lam) h0 h2 h0 h2 (by linarith)
  obtain ⟨hi3_3, hi3_2, hi3_1, hi3_0⟩ := f0_integrable4 (mu := mu) (lam := lam) h0 h2 h0 h2 (by linarith)
  unfold E3Expect E2Expect
  refine integral_mono hi3_0 hi2_0 (fun T0 => integral_mono (hi3_1 T0) (hi2_1 T0) (fun T1 =>
    integral_mono (hi3_2 T0 T1) (hi2_2 T0 T1) (fun T2 => ?_)))
  have hpt : ∀ T3 : InfTree23,
      f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) ≤
        f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam) := by
    intro T3
    have m0 := (lemma_4_1_support T0 h0 h2).1
    have m1 := (lemma_4_1_support T1 h0 h2).1
    have m2 := (lemma_4_1_support T2 h0 h2).1
    have m3 := (lemma_4_1_support T3 h0 h2).1
    exact f0Func_anti_t (by linarith) (by linarith) (by linarith)
  simpa using integral_mono (hi3_3 T0 T1 T2) (integrable_const _) hpt

theorem RFunc_bounds {mu : Measure InfTree23} [IsProbabilityMeasure mu]
    {lam : ℝ} (h0 : 0 < lam) (h2 : lam < 2) :
    2 < RFunc mu lam ∧ RFunc mu lam ≤ 5 / 2 := by
  have hE2 := E2Expect_pos (mu := mu) h0 h2
  have hE3 := E3Expect_pos (mu := mu) h0 h2
  have hle := E3Expect_le_E2Expect (mu := mu) h0 h2
  have hden : E2Expect mu lam + E3Expect mu lam ≠ 0 := ne_of_gt (by linarith)
  have hid : RFunc mu lam = 2 + E3Expect mu lam / (E2Expect mu lam + E3Expect mu lam) := by
    unfold RFunc; field_simp [hden]; ring
  rw [hid]
  exact R_bounds_of_E2_E3 hE2 hE3 hle

/-! ## 6. Sparse Exact-Integer Double-Sum Evaluator (`sumGrid1`, `sumGrid2`) -/

/-- Sparse 1D integer dot-product skipping zero weights in `O(1)`. -/
def sumGrid1 (f : ℕ → ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | j, 0 :: ws => sumGrid1 f (j + 1) ws
  | j, w :: ws => w * f j + sumGrid1 f (j + 1) ws

/-- Sparse 2D integer bilinear evaluator skipping zero weights in both outer and inner lists. -/
def sumGrid2 (F : ℕ → ℕ → ℕ) : ℕ → List ℕ → List ℕ → ℕ
  | _, [], _ => 0
  | i, 0 :: wy, wt => sumGrid2 F (i + 1) wy wt
  | i, w :: wy, wt => w * sumGrid1 (F i) 0 wt + sumGrid2 F (i + 1) wy wt

lemma evalGrid_le_sumGrid1 {x0 h : ℝ} {g : ℝ → ℝ} {f : ℕ → ℕ} {S : ℕ} (hS : 0 < S) :
    ∀ (ws : List ℕ) (k : ℕ),
      (∀ j < ws.length, g (x0 + ((k + j : ℕ) : ℝ) * h) ≤ (f (k + j) : ℝ) / (S : ℝ)) →
      evalGrid (x0 + (k : ℝ) * h) h g ws ≤ (sumGrid1 f k ws : ℝ) / (S : ℝ)
  | [], _, _ => by simp [evalGrid, sumGrid1]
  | 0 :: ws, k, hfg => by
      simp only [evalGrid, Nat.cast_zero, zero_mul, zero_add, sumGrid1]
      have hsh : (x0 + (k : ℝ) * h) + h = x0 + ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
      rw [hsh]
      refine evalGrid_le_sumGrid1 hS ws (k + 1) (fun j hj => ?_)
      have h1 := hfg (j + 1) (by simp [List.length_cons]; omega)
      have hk : k + (j + 1) = k + 1 + j := by omega
      rwa [hk] at h1
  | (w + 1) :: ws, k, hfg => by
      simp only [evalGrid, sumGrid1, Nat.cast_add, Nat.cast_mul]
      have h0 := hfg 0 (by simp)
      simp only [Nat.add_zero] at h0
      have hw0 : (((w + 1 : ℕ) : ℝ) * g (x0 + (k : ℝ) * h)) ≤ (((w + 1) * f k : ℕ) : ℝ) / (S : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left h0 (Nat.cast_nonneg (w + 1))
        rwa [mul_div_assoc', ← Nat.cast_mul] at hm
      have hsh : (x0 + (k : ℝ) * h) + h = x0 + ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
      rw [hsh]
      have hrest : evalGrid (x0 + ((k + 1 : ℕ) : ℝ) * h) h g ws ≤ (sumGrid1 f (k + 1) ws : ℝ) / (S : ℝ) := by
        refine evalGrid_le_sumGrid1 hS ws (k + 1) (fun j hj => ?_)
        have h1 := hfg (j + 1) (by simp [List.length_cons]; omega)
        have hk : k + (j + 1) = k + 1 + j := by omega
        rwa [hk] at h1
      rw [add_div]
      push_cast at hw0 hrest ⊢
      linarith

lemma sumGrid1_le_evalGrid {x0 h : ℝ} {g : ℝ → ℝ} {f : ℕ → ℕ} {S : ℕ} (hS : 0 < S) :
    ∀ (ws : List ℕ) (k : ℕ),
      (∀ j < ws.length, (f (k + j) : ℝ) / (S : ℝ) ≤ g (x0 + ((k + j : ℕ) : ℝ) * h)) →
      (sumGrid1 f k ws : ℝ) / (S : ℝ) ≤ evalGrid (x0 + (k : ℝ) * h) h g ws
  | [], _, _ => by simp [evalGrid, sumGrid1]
  | 0 :: ws, k, hfg => by
      simp only [evalGrid, Nat.cast_zero, zero_mul, zero_add, sumGrid1]
      have hsh : (x0 + (k : ℝ) * h) + h = x0 + ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
      rw [hsh]
      refine sumGrid1_le_evalGrid hS ws (k + 1) (fun j hj => ?_)
      have h1 := hfg (j + 1) (by simp [List.length_cons]; omega)
      have hk : k + (j + 1) = k + 1 + j := by omega
      rwa [hk] at h1
  | (w + 1) :: ws, k, hfg => by
      simp only [evalGrid, sumGrid1, Nat.cast_add, Nat.cast_mul]
      have h0 := hfg 0 (by simp)
      simp only [Nat.add_zero] at h0
      have hw0 : (((w + 1) * f k : ℕ) : ℝ) / (S : ℝ) ≤ (((w + 1 : ℕ) : ℝ) * g (x0 + (k : ℝ) * h)) := by
        have hm := mul_le_mul_of_nonneg_left h0 (Nat.cast_nonneg (w + 1))
        rwa [mul_div_assoc', ← Nat.cast_mul] at hm
      have hsh : (x0 + (k : ℝ) * h) + h = x0 + ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
      rw [hsh]
      have hrest : (sumGrid1 f (k + 1) ws : ℝ) / (S : ℝ) ≤ evalGrid (x0 + ((k + 1 : ℕ) : ℝ) * h) h g ws := by
        refine sumGrid1_le_evalGrid hS ws (k + 1) (fun j hj => ?_)
        have h1 := hfg (j + 1) (by simp [List.length_cons]; omega)
        have hk : k + (j + 1) = k + 1 + j := by omega
        rwa [hk] at h1
      rw [add_div]
      push_cast at hw0 hrest ⊢
      linarith

lemma evalGrid2_le_sumGrid2 {y0 hy t0 ht : ℝ} {G : ℝ → ℝ → ℝ} {F : ℕ → ℕ → ℕ} {S : ℕ} (hS : 0 < S)
    {wy wt : List ℕ}
    (hpt : ∀ i < wy.length, ∀ j < wt.length,
      G (y0 + (i : ℝ) * hy) (t0 + (j : ℝ) * ht) ≤ (F i j : ℝ) / (S : ℝ)) :
    evalGrid y0 hy (fun y => evalGrid t0 ht (G y) wt) wy ≤ (sumGrid2 F 0 wy wt : ℝ) / (S : ℝ) := by
  have haux : ∀ (ys : List ℕ) (k : ℕ),
      (∀ i < ys.length, ∀ j < wt.length,
        G (y0 + ((k + i : ℕ) : ℝ) * hy) (t0 + (j : ℝ) * ht) ≤ (F (k + i) j : ℝ) / (S : ℝ)) →
      evalGrid (y0 + (k : ℝ) * hy) hy (fun y => evalGrid t0 ht (G y) wt) ys ≤
        (sumGrid2 F k ys wt : ℝ) / (S : ℝ) := by
    intro ys
    induction ys with
    | nil => intro _ _; simp [evalGrid, sumGrid2]
    | cons w ys ih =>
        cases w with
        | zero =>
            intro k hk
            simp only [evalGrid, Nat.cast_zero, zero_mul, zero_add, sumGrid2]
            have hsh : (y0 + (k : ℝ) * hy) + hy = y0 + ((k + 1 : ℕ) : ℝ) * hy := by push_cast; ring
            rw [hsh]
            refine ih (k + 1) (fun i hi j hj => ?_)
            have h1 := hk (i + 1) (by simp [List.length_cons]; omega) j hj
            have hki : k + (i + 1) = k + 1 + i := by omega
            rwa [hki] at h1
        | succ w =>
            intro k hk
            simp only [evalGrid, sumGrid2, Nat.cast_add, Nat.cast_mul]
            have hin : evalGrid t0 ht (G (y0 + (k : ℝ) * hy)) wt ≤ (sumGrid1 (F k) 0 wt : ℝ) / (S : ℝ) := by
              have h0 := evalGrid_le_sumGrid1 (x0 := t0) (h := ht) (g := G (y0 + (k : ℝ) * hy)) (f := F k) hS wt 0
                (fun j hj => by simpa using hk 0 (by simp) j hj)
              simpa using h0
            have hw : ((w + 1 : ℕ) : ℝ) * evalGrid t0 ht (G (y0 + (k : ℝ) * hy)) wt ≤
                (((w + 1) * sumGrid1 (F k) 0 wt : ℕ) : ℝ) / (S : ℝ) := by
              have hm := mul_le_mul_of_nonneg_left hin (Nat.cast_nonneg (w + 1))
              rwa [mul_div_assoc', ← Nat.cast_mul] at hm
            have hsh : (y0 + (k : ℝ) * hy) + hy = y0 + ((k + 1 : ℕ) : ℝ) * hy := by push_cast; ring
            rw [hsh]
            have hrest := ih (k + 1) (fun i hi j hj => by
              have h1 := hk (i + 1) (by simp [List.length_cons]; omega) j hj
              have hki : k + (i + 1) = k + 1 + i := by omega
              rwa [hki] at h1)
            rw [add_div]
            push_cast at hw hrest ⊢
            linarith
  simpa using haux wy 0 (by simpa using hpt)

lemma sumGrid2_le_evalGrid2 {y0 hy t0 ht : ℝ} {G : ℝ → ℝ → ℝ} {F : ℕ → ℕ → ℕ} {S : ℕ} (hS : 0 < S)
    {wy wt : List ℕ}
    (hpt : ∀ i < wy.length, ∀ j < wt.length,
      (F i j : ℝ) / (S : ℝ) ≤ G (y0 + (i : ℝ) * hy) (t0 + (j : ℝ) * ht)) :
    (sumGrid2 F 0 wy wt : ℝ) / (S : ℝ) ≤ evalGrid y0 hy (fun y => evalGrid t0 ht (G y) wt) wy := by
  have haux : ∀ (ys : List ℕ) (k : ℕ),
      (∀ i < ys.length, ∀ j < wt.length,
        (F (k + i) j : ℝ) / (S : ℝ) ≤ G (y0 + ((k + i : ℕ) : ℝ) * hy) (t0 + (j : ℝ) * ht)) →
      (sumGrid2 F k ys wt : ℝ) / (S : ℝ) ≤
        evalGrid (y0 + (k : ℝ) * hy) hy (fun y => evalGrid t0 ht (G y) wt) ys := by
    intro ys
    induction ys with
    | nil => intro _ _; simp [evalGrid, sumGrid2]
    | cons w ys ih =>
        cases w with
        | zero =>
            intro k hk
            simp only [evalGrid, Nat.cast_zero, zero_mul, zero_add, sumGrid2]
            have hsh : (y0 + (k : ℝ) * hy) + hy = y0 + ((k + 1 : ℕ) : ℝ) * hy := by push_cast; ring
            rw [hsh]
            refine ih (k + 1) (fun i hi j hj => ?_)
            have h1 := hk (i + 1) (by simp [List.length_cons]; omega) j hj
            have hki : k + (i + 1) = k + 1 + i := by omega
            rwa [hki] at h1
        | succ w =>
            intro k hk
            simp only [evalGrid, sumGrid2, Nat.cast_add, Nat.cast_mul]
            have hin : (sumGrid1 (F k) 0 wt : ℝ) / (S : ℝ) ≤ evalGrid t0 ht (G (y0 + (k : ℝ) * hy)) wt := by
              have h0 := sumGrid1_le_evalGrid (x0 := t0) (h := ht) (g := G (y0 + (k : ℝ) * hy)) (f := F k) hS wt 0
                (fun j hj => by simpa using hk 0 (by simp) j hj)
              simpa using h0
            have hw : (((w + 1) * sumGrid1 (F k) 0 wt : ℕ) : ℝ) / (S : ℝ) ≤
                ((w + 1 : ℕ) : ℝ) * evalGrid t0 ht (G (y0 + (k : ℝ) * hy)) wt := by
              have hm := mul_le_mul_of_nonneg_left hin (Nat.cast_nonneg (w + 1))
              rwa [mul_div_assoc', ← Nat.cast_mul] at hm
            have hsh : (y0 + (k : ℝ) * hy) + hy = y0 + ((k + 1 : ℕ) : ℝ) * hy := by push_cast; ring
            rw [hsh]
            have hrest := ih (k + 1) (fun i hi j hj => by
              have h1 := hk (i + 1) (by simp [List.length_cons]; omega) j hj
              have hki : k + (i + 1) = k + 1 + i := by omega
              rwa [hki] at h1)
            rw [add_div]
            push_cast at hw hrest ⊢
            linarith
  simpa using haux wy 0 (by simpa using hpt)

/-! ## 7. Exact Integer Cell Certificate & Pure-`Bool` Verifier (`checkCell`) -/

/-- Integer scale `10^8` for rational integrand bounds inside `checkCell`. -/
def cellScale : ℕ := 100000000

/-- Self-contained exact integer certificate for `[λa, λb] = [lna / ld, lnb / ld]`. -/
structure CellCert where
  lna : ℕ
  lnb : ℕ
  ld : ℕ
  K : ℕ
  M : ℕ
  ua : List ℕ
  j2ua : List ℕ
  j3ua : List ℕ
  lb_env : List ℕ
  j2lb : List ℕ
  j3lb : List ℕ

/-- Integer upper-sum accumulator for `E₂(λ)` on cell `c`. -/
def rawE2h (c : CellCert) : ℕ :=
  let D := 6 * c.ld * c.K
  let Dla := 6 * c.K * c.lna
  let Daa := 3 * c.K * (2 * c.ld - c.lna)
  let Dab := 3 * c.K * (2 * c.ld - c.lnb)
  sumGrid2 (fun i j =>
    (cellScale * (Daa + i * c.lna)) / ((Dla - D) + (Daa + i * c.lna) + (2 * Dab + j * c.lnb)) + 1)
    0 c.ua (polyMul c.lb_env c.lb_env)

/-- Integer lower-sum accumulator for `E₂(λ)` on cell `c`. -/
def rawE2l (c : CellCert) : ℕ :=
  let D := 6 * c.ld * c.K
  let Dlb := 6 * c.K * c.lnb
  let Daa := 3 * c.K * (2 * c.ld - c.lna)
  let Dab := 3 * c.K * (2 * c.ld - c.lnb)
  sumGrid2 (fun i j =>
    (cellScale * (Dab + i * c.lnb)) / ((Dlb - D) + (Dab + i * c.lnb) + (2 * Daa + j * c.lna)))
    0 c.lb_env (polyMul c.ua c.ua)

/-- Integer upper-sum accumulator for `E₃(λ)` on cell `c`. -/
def rawE3h (c : CellCert) : ℕ :=
  let D := 6 * c.ld * c.K
  let Dla := 6 * c.K * c.lna
  let Daa := 3 * c.K * (2 * c.ld - c.lna)
  let Dab := 3 * c.K * (2 * c.ld - c.lnb)
  let c2b := polyMul c.lb_env c.lb_env
  sumGrid2 (fun i j =>
    (cellScale * (Daa + i * c.lna)) / ((Dla - D) + (Daa + i * c.lna) + (3 * Dab + j * c.lnb)) + 1)
    0 c.ua (polyMul c2b c.lb_env)

/-- Integer lower-sum accumulator for `E₃(λ)` on cell `c`. -/
def rawE3l (c : CellCert) : ℕ :=
  let D := 6 * c.ld * c.K
  let Dlb := 6 * c.K * c.lnb
  let Daa := 3 * c.K * (2 * c.ld - c.lna)
  let Dab := 3 * c.K * (2 * c.ld - c.lnb)
  let c2a := polyMul c.ua c.ua
  sumGrid2 (fun i j =>
    (cellScale * (Dab + i * c.lnb)) / ((Dlb - D) + (Dab + i * c.lnb) + (3 * Daa + j * c.lna)))
    0 c.lb_env (polyMul c2a c.ua)

/-- Integer upper-sum accumulator for `H₃` (`h3Func`) on cell `c`. -/
def rawH3 (c : CellCert) : ℕ :=
  let D := 6 * c.ld * c.K
  let Dla := 6 * c.K * c.lna
  let Dlb := 6 * c.K * c.lnb
  let Daa := 3 * c.K * (2 * c.ld - c.lna)
  let E := 2 * D - Dlb
  let Knum := 2 * D + Dla - 2 * Dlb
  let c2a := polyMul c.ua c.ua
  sumGrid2 (fun i j =>
    let Dy := Daa + i * c.lna
    let Dt := 3 * Daa + j * c.lna
    (cellScale * (D * E * Dy * (Dt - E))) / ((E * (Dla - D) + Knum * (Dy + Dt)) ^ 2) + 1)
    0 c.ua (polyMul c2a c.ua)

/-- Integer upper-sum accumulator for `H₂` (`h2Func`) on cell `c`. -/
def rawH2 (c : CellCert) : ℕ :=
  let D := 6 * c.ld * c.K
  let Dla := 6 * c.K * c.lna
  let Dlb := 6 * c.K * c.lnb
  let Daa := 3 * c.K * (2 * c.ld - c.lna)
  let Dab := 3 * c.K * (2 * c.ld - c.lnb)
  let E := 2 * D - Dlb
  let Knum := 2 * D + Dla - 2 * Dlb
  sumGrid2 (fun i j =>
    let Dy := Daa + i * c.lna
    let Dt := 2 * Dab + j * c.lnb
    (cellScale * (D * E * Dy * (D + Dt))) / ((E * (Dla - D) + Knum * (Dy + Dt)) ^ 2) + 1)
    0 c.ua (polyMul c.lb_env c.lb_env)

/-- Pure `Bool` corner-monotonicity check for `h3Func` and `h2Func` on `[ab, ba]`. -/
def checkCellCorners (c : CellCert) : Bool :=
  let P := 6 * c.ld
  let Pla := 6 * c.lna
  let Plb := 6 * c.lnb
  let PA := 3 * (2 * c.ld - c.lnb)
  let PB := 2 * (3 * c.ld - c.lna)
  let PE := 2 * P - Plb
  let PK := 2 * P + Pla - 2 * Plb
  (c.ld < c.lna) &&
  (c.lna ≤ c.lnb) &&
  (2 * Plb < 2 * P + Pla) &&
  (PE * P + PK * PB < PE * Pla + 2 * PK * PA) &&
  (PE * P + 3 * PK * PB < PE * Pla + PK * PA + 2 * PE * PK) &&
  (PE * Pla + PK * PB < PE * P + 2 * PK * PA + 2 * PK * P)

/-- Pure `Bool` verifier for a cell certificate `c : CellCert` (`Proposition 6.2`). -/
def checkCell (c : CellCert) : Bool :=
  let e2h := c.M * rawE2h c
  let e2l := c.M * rawE2l c
  let e3h := rawE3h c
  let e3l := rawE3l c
  let h3_up := rawH3 c
  let h2_up := c.M * rawH2 c
  let num_r2 := if e3h ≤ e2l then e3h else 1
  let den_r2 := if e3h ≤ e2l then e2l + e3h else 2
  checkUpperEnv c.lna c.ld c.K c.M c.ua c.j2ua c.j3ua &&
  checkLowerEnv c.lnb c.ld c.K c.M c.lb_env c.j2lb c.j3lb &&
  checkCellCorners c &&
  (0 < e2l) &&
  (0 < e3l) &&
  (c.lnb * (e2h * den_r2 * h3_up + (e2h + e3l) * num_r2 * h2_up) <
    c.ld * den_r2 * (2 * e2h + 3 * e3l) * (e2l + e3l))

/-! ## 8. Soundness of `checkCell` (`Proposition 6.2`) -/

lemma nat_div_up_bound {S num den : ℕ} (hS : 0 < S) (hden : 0 < den) :
    (num : ℝ) / (den : ℝ) ≤ (((S * num) / den + 1 : ℕ) : ℝ) / (S : ℝ) := by
  have hS_pos : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hden_pos : (0 : ℝ) < den := Nat.cast_pos.mpr hden
  rw [div_le_div_iff₀ hden_pos hS_pos]
  have hdiv := Nat.div_add_mod (S * num) den
  have hmod := Nat.mod_lt (S * num) hden
  have hlt : S * num < ((S * num) / den + 1) * den := by
    have : ((S * num) / den + 1) * den = den * ((S * num) / den) + den := by ring
    omega
  have hle_cast : ((S * num : ℕ) : ℝ) ≤ ((((S * num) / den + 1) * den : ℕ) : ℝ) :=
    Nat.cast_le.mpr (le_of_lt hlt)
  push_cast at hle_cast ⊢
  linarith

lemma nat_div_lo_bound {S num den : ℕ} (hS : 0 < S) (hden : 0 < den) :
    (((S * num) / den : ℕ) : ℝ) / (S : ℝ) ≤ (num : ℝ) / (den : ℝ) := by
  have hS_pos : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hden_pos : (0 : ℝ) < den := Nat.cast_pos.mpr hden
  rw [div_le_div_iff₀ hS_pos hden_pos]
  have hle : den * ((S * num) / den) ≤ S * num := Nat.mul_div_le (S * num) den
  have hle_cast : ((den * ((S * num) / den) : ℕ) : ℝ) ≤ ((S * num : ℕ) : ℝ) :=
    Nat.cast_le.mpr hle
  push_cast at hle_cast
  linarith

lemma corner_identities (cell : CellCert) (h3 : cell.lnb < 2 * cell.ld)
    (hcorn : checkCellCorners cell = true) :
    let la : ℝ := (cell.lna : ℝ) / cell.ld
    let lb : ℝ := (cell.lnb : ℝ) / cell.ld
    let A : ℝ := 1 - lb / 2
    let B : ℝ := 1 - la / 3
    let c : ℝ := 1 / (2 - lb)
    let kap : ℝ := 1 - c * (lb - la)
    1 < la ∧ la ≤ lb ∧ lb < 2 ∧ 0 < A ∧ 0 < kap ∧
    cell.ld < cell.lna ∧ cell.lna ≤ cell.lnb ∧
    2 * (6 * cell.lnb) < 2 * (6 * cell.ld) + 6 * cell.lna ∧
    0 < (la - 1) + kap * (2 * A - B) ∧
    0 < (la - 1) + kap * (3 * A - B) ∧
    0 < c * (la - 1) + c * kap * A - c * kap * (3 * B) + 2 * kap ∧
    c * (la - 1) + c * kap * B - c * kap * (2 * A) - 2 * kap - 2 * kap * c * (lb - 1) < 0 := by
  dsimp only [checkCellCorners] at hcorn
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hcorn
  rcases hcorn with ⟨h1, h2, hkap_nat, hc_y2, hc_t3, hc_t2⟩
  set lna := cell.lna
  set lnb := cell.lnb
  set ld := cell.ld
  have hld : 0 < ld := by omega
  have hld_pos : (0 : ℝ) < ld := Nat.cast_pos.mpr hld
  have hld_ne : (ld : ℝ) ≠ 0 := ne_of_gt hld_pos
  intro la lb A B c kap
  have hla1 : 1 < la := by unfold la; rw [one_lt_div hld_pos]; exact_mod_cast h1
  have hlalb : la ≤ lb := by unfold la lb; exact div_le_div_of_nonneg_right (Nat.cast_le.mpr h2) (le_of_lt hld_pos)
  have hlb2 : lb < 2 := by unfold lb; rw [div_lt_iff₀ hld_pos]; exact_mod_cast h3
  have hA : 0 < A := by unfold A; linarith
  have h2lb_pos : 0 < 2 - lb := by linarith
  have h2lb_ne : 2 - lb ≠ 0 := ne_of_gt h2lb_pos
  set P : ℝ := 6 * (ld : ℝ)
  set Pla : ℝ := 6 * (lna : ℝ)
  set Plb : ℝ := 6 * (lnb : ℝ)
  set PA : ℝ := 3 * (2 * (ld : ℝ) - (lnb : ℝ))
  set PB : ℝ := 2 * (3 * (ld : ℝ) - (lna : ℝ))
  set PE : ℝ := 2 * P - Plb
  set PK : ℝ := 2 * P + Pla - 2 * Plb
  have hP_pos : 0 < P := by unfold P; positivity
  have hP_ne : P ≠ 0 := ne_of_gt hP_pos
  have hPla : Pla = P * la := by unfold Pla P la; field_simp [hld_ne]
  have hPlb : Plb = P * lb := by unfold Plb P lb; field_simp [hld_ne]
  have hPA : PA = P * A := by unfold PA P A lb; field_simp [hld_ne]; ring
  have hPB : PB = P * B := by unfold PB P B la; field_simp [hld_ne]; ring
  have hPE : PE = P * (2 - lb) := by unfold PE; rw [hPlb]; ring
  have hPE_pos : 0 < PE := by rw [hPE]; positivity
  have hPE_ne : PE ≠ 0 := ne_of_gt hPE_pos
  have hPK : PK = PE * kap := by
    unfold PK kap c; rw [hPla, hPlb, hPE]; field_simp [h2lb_ne]; ring
  have sub1 : ((2 * ld - lnb : ℕ) : ℝ) = 2 * (ld : ℝ) - lnb := by
    rw [Nat.cast_sub (by omega : lnb ≤ 2 * ld)]; push_cast; ring
  have sub2 : ((3 * ld - lna : ℕ) : ℝ) = 3 * (ld : ℝ) - lna := by
    rw [Nat.cast_sub (by omega : lna ≤ 3 * ld)]; push_cast; ring
  have sub3 : ((2 * (6 * ld) - 6 * lnb : ℕ) : ℝ) = PE := by
    rw [Nat.cast_sub (by omega : 6 * lnb ≤ 2 * (6 * ld))]; unfold PE P Plb; push_cast; ring
  have sub4 : ((2 * (6 * ld) + 6 * lna - 2 * (6 * lnb) : ℕ) : ℝ) = PK := by
    rw [Nat.cast_sub (le_of_lt hkap_nat)]; unfold PK P Pla Plb; push_cast; ring
  have hPK_pos : 0 < PK := by
    rw [← sub4]; exact Nat.cast_pos.mpr (by omega)
  have hkap_pos : 0 < kap := by
    have : 0 < PE * kap := by rwa [← hPK]
    exact pos_of_mul_pos_right this (le_of_lt hPE_pos)
  have hc_eq : c = P / PE := by unfold c; rw [hPE]; field_simp [hP_ne, h2lb_ne]
  have hy2 : 0 < (la - 1) + kap * (2 * A - B) := by
    have hnat := Nat.cast_lt (α := ℝ).mpr hc_y2
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, sub1, sub2, sub3, sub4] at hnat
    have hnat' : PE * P + PK * PB < PE * Pla + 2 * PK * PA := by
      unfold P Pla PA PB; linarith
    have hid : ((la - 1) + kap * (2 * A - B)) * (P * PE) =
        (PE * Pla + 2 * PK * PA) - (PE * P + PK * PB) := by
      rw [hPK, hPla, hPA, hPB]; ring
    have hpos : 0 < ((la - 1) + kap * (2 * A - B)) * (P * PE) := by linarith
    exact pos_of_mul_pos_left hpos (by positivity)
  have hy3 : 0 < (la - 1) + kap * (3 * A - B) := by
    have : 0 < kap * A := mul_pos hkap_pos hA
    linarith
  have ht3 : 0 < c * (la - 1) + c * kap * A - c * kap * (3 * B) + 2 * kap := by
    have hnat := Nat.cast_lt (α := ℝ).mpr hc_t3
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, sub1, sub2, sub3, sub4] at hnat
    have hnat' : PE * P + 3 * PK * PB < PE * Pla + PK * PA + 2 * PE * PK := by
      unfold P Pla PA PB; linarith
    have hid : (c * (la - 1) + c * kap * A - c * kap * (3 * B) + 2 * kap) * (PE * PE) =
        (PE * Pla + PK * PA + 2 * PE * PK) - (PE * P + 3 * PK * PB) := by
      rw [hc_eq, hPK, hPla, hPA, hPB]
      field_simp [hPE_ne]; ring
    have hpos : 0 < (c * (la - 1) + c * kap * A - c * kap * (3 * B) + 2 * kap) * (PE * PE) := by linarith
    exact pos_of_mul_pos_left hpos (by positivity)
  have ht2 : c * (la - 1) + c * kap * B - c * kap * (2 * A) - 2 * kap - 2 * kap * c * (lb - 1) < 0 := by
    have hnat := Nat.cast_lt (α := ℝ).mpr hc_t2
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, sub1, sub2, sub3, sub4] at hnat
    have hnat' : PE * Pla + PK * PB < PE * P + 2 * PK * PA + 2 * PK * P := by
      unfold P Pla PA PB; linarith
    have hid : (c * (la - 1) + c * kap * B - c * kap * (2 * A) - 2 * kap - 2 * kap * c * (lb - 1)) * (PE * PE) =
        (PE * Pla + PK * PB) - (PE * P + 2 * PK * PA + 2 * PK * P) := by
      rw [hc_eq, hPK, hPla, hPA, hPB, hPE]
      field_simp [hP_ne, h2lb_ne]; ring
    have hneg : (c * (la - 1) + c * kap * B - c * kap * (2 * A) - 2 * kap - 2 * kap * c * (lb - 1)) * (PE * PE) < 0 := by
      linarith
    by_contra hge
    have : 0 ≤ (c * (la - 1) + c * kap * B - c * kap * (2 * A) - 2 * kap - 2 * kap * c * (lb - 1)) * (PE * PE) :=
      mul_nonneg (not_lt.mp hge) (by positivity)
    linarith
  exact ⟨hla1, hlalb, hlb2, hA, hkap_pos, h1, h2, hkap_nat, hy2, hy3, ht3, ht2⟩

lemma cell_h3_h2_box_props (c : CellCert) (hlnb2 : c.lnb < 2 * c.ld)
    (hcorn : checkCellCorners c = true) :
    let la : ℝ := (c.lna : ℝ) / c.ld
    let lb : ℝ := (c.lnb : ℝ) / c.ld
    let ab : ℝ := 1 - lb / 2
    let ba : ℝ := 1 - la / 3
    ContinuousOn (Function.uncurry (h3Func la lb)) (Set.Icc ab ba ×ˢ Set.Icc (3 * ab) (3 * ba)) ∧
    (∀ {y1 y2 t1 t2 : ℝ},
      ab ≤ y1 → y1 ≤ y2 → y2 ≤ ba → 3 * ab ≤ t1 → t1 ≤ t2 → t2 ≤ 3 * ba →
      h3Func la lb y1 t1 ≤ h3Func la lb y2 t2) ∧
    ContinuousOn (Function.uncurry (h2Func la lb)) (Set.Icc ab ba ×ˢ Set.Icc (2 * ab) (2 * ba)) ∧
    (∀ {y1 y2 t1 t2 : ℝ},
      ab ≤ y1 → y1 ≤ y2 → y2 ≤ ba → 2 * ab ≤ t2 → t2 ≤ t1 → t1 ≤ 2 * ba →
      h2Func la lb y1 t1 ≤ h2Func la lb y2 t2) := by
  obtain ⟨hla1, hlalb, hlb2, hA_pos, hkap_pos, _, _, _, hy2_pos, hy3_pos, ht3_pos, ht2_neg⟩ :=
    corner_identities c hlnb2 hcorn
  set la : ℝ := (c.lna : ℝ) / c.ld
  set lb : ℝ := (c.lnb : ℝ) / c.ld
  set ab : ℝ := 1 - lb / 2
  set ba : ℝ := 1 - la / 3
  have hab_eq : ab = 1 - lb / 2 := rfl
  have hba_eq : ba = 1 - la / 3 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Function.uncurry h3Func
    refine (continuousOn_fst.mul ((continuousOn_const.mul continuousOn_snd).sub continuousOn_const)).div
      ((continuousOn_const.add (continuousOn_const.mul (continuousOn_fst.add continuousOn_snd))).pow 2) ?_
    intro p hp
    have hy : 0 < p.1 := lt_of_lt_of_le hA_pos hp.1.1
    have ht : 0 < p.2 := by linarith [hp.2.1]
    have hpos : 0 < (la - 1) + (1 - (1 / (2 - lb)) * (lb - la)) * (p.1 + p.2) := by
      have : 0 < (1 - (1 / (2 - lb)) * (lb - la)) * (p.1 + p.2) := mul_pos hkap_pos (by linarith)
      linarith
    exact pow_ne_zero 2 (ne_of_gt hpos)
  · intro y1 y2 t1 t2 hy1 hy12 hy2 ht1 ht12 ht2
    have hpos_t1 : 0 ≤ (1 / (2 - lb)) * t1 - 1 := by
      have hc0 : 0 ≤ 1 / (2 - lb) := by positivity
      have h32 : (1 / (2 - lb)) * (3 * (1 - lb / 2)) = 3 / 2 := by
        field_simp [show 2 - lb ≠ 0 by linarith]
      have hm := mul_le_mul_of_nonneg_left ht1 hc0
      linarith
    exact h3Func_mono_box hla1 hlb2 hA_pos hy1 hy12 hy2 ht1 ht12 ht2 hkap_pos hpos_t1 hy3_pos ht3_pos
  · unfold Function.uncurry h2Func
    refine (continuousOn_fst.mul (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.add continuousOn_snd)))).div
      ((continuousOn_const.add (continuousOn_const.mul (continuousOn_fst.add continuousOn_snd))).pow 2) ?_
    intro p hp
    have hy : 0 < p.1 := lt_of_lt_of_le hA_pos hp.1.1
    have ht : 0 < p.2 := by linarith [hp.2.1]
    have hpos : 0 < (la - 1) + (1 - (1 / (2 - lb)) * (lb - la)) * (p.1 + p.2) := by
      have : 0 < (1 - (1 / (2 - lb)) * (lb - la)) * (p.1 + p.2) := mul_pos hkap_pos (by linarith)
      linarith
    exact pow_ne_zero 2 (ne_of_gt hpos)
  · intro y1 y2 t1 t2 hy1 hy12 hy2 ht2 ht21 ht1
    exact h2Func_mono_anti_box hla1 hlb2 hlalb hA_pos hy1 hy12 hy2 ht2 ht21 ht1 hkap_pos hy2_pos ht2_neg

set_option maxHeartbeats 800000 in
lemma cell_E2_E3_bounds {mu : Measure InfTree23} [IsGWTree23 mu] (c : CellCert)
    (hua : checkUpperEnv c.lna c.ld c.K c.M c.ua c.j2ua c.j3ua = true)
    (hlb : checkLowerEnv c.lnb c.ld c.K c.M c.lb_env c.j2lb c.j3lb = true)
    (hcorn : checkCellCorners c = true) :
    let la : ℝ := (c.lna : ℝ) / c.ld
    let lb : ℝ := (c.lnb : ℝ) / c.ld
    let Q : ℝ := (cellScale : ℝ) * (c.M : ℝ) ^ 4
    (∀ lam ∈ Set.Icc la lb,
      ((c.M * rawE2l c : ℕ) : ℝ) / Q ≤ E2Expect mu lam ∧
      E2Expect mu lam ≤ ((c.M * rawE2h c : ℕ) : ℝ) / Q) ∧
    (∀ lam ∈ Set.Icc la lb,
      (rawE3l c : ℝ) / Q ≤ E3Expect mu lam ∧
      E3Expect mu lam ≤ (rawE3h c : ℝ) / Q) := by
  set raw_e2h := rawE2h c
  set raw_e2l := rawE2l c
  set raw_e3h := rawE3h c
  set raw_e3l := rawE3l c
  set e2h : ℕ := c.M * raw_e2h
  set e2l : ℕ := c.M * raw_e2l
  set e3h : ℕ := raw_e3h
  set e3l : ℕ := raw_e3l
  obtain ⟨hlna0, hlna2, hK, hM, _⟩ := checkUpperEnv_dims hua
  obtain ⟨hlnb0, hlnb2, _, _, _⟩ := checkLowerEnv_dims hlb
  have hld : 0 < c.ld := by omega
  obtain ⟨hla1, hlalb, hlb2, hA_pos, _, hld_lt_lna, hlna_le_lnb, _, _, _, _, _⟩ :=
    corner_identities c hlnb2 hcorn
  obtain ⟨hD_pos, hDla, hDaa, hDha⟩ := grid_identities (ln := c.lna) hld hlna2 hK
  obtain ⟨_, hDlb, hDab, hDhb⟩ := grid_identities (ln := c.lnb) hld hlnb2 hK
  set la : ℝ := (c.lna : ℝ) / c.ld
  set lb : ℝ := (c.lnb : ℝ) / c.ld
  set aa : ℝ := 1 - la / 2
  set ba : ℝ := 1 - la / 3
  set ha : ℝ := (ba - aa) / c.K
  set ab : ℝ := 1 - lb / 2
  set bb : ℝ := 1 - lb / 3
  set hb : ℝ := (bb - ab) / c.K
  have haa_eq : aa = 1 - la / 2 := rfl
  have hba_eq : ba = 1 - la / 3 := rfl
  have hab_eq : ab = 1 - lb / 2 := rfl
  have hbb_eq : bb = 1 - lb / 3 := rfl
  have hla0 : 0 < la := by linarith
  have hla2 : la < 2 := by linarith
  have hlb0 : 0 < lb := by linarith
  have haa_ba : aa ≤ ba := by linarith
  have hab_bb : ab ≤ bb := by linarith
  have hM_pos : (0 : ℝ) < c.M := Nat.cast_pos.mpr hM
  have hS_pos : 0 < cellScale := by decide
  set D_nat : ℕ := 6 * c.ld * c.K
  set Dla_nat : ℕ := 6 * c.K * c.lna
  set Dlb_nat : ℕ := 6 * c.K * c.lnb
  set Daa_nat : ℕ := 3 * c.K * (2 * c.ld - c.lna)
  set Dab_nat : ℕ := 3 * c.K * (2 * c.ld - c.lnb)
  have hD_ne : ((D_nat : ℝ)) ≠ 0 := ne_of_gt hD_pos
  have hD_lt_Dla : D_nat < Dla_nat := by
    unfold D_nat Dla_nat
    rw [show 6 * c.ld * c.K = (6 * c.K) * c.ld by ring]
    exact Nat.mul_lt_mul_of_pos_left hld_lt_lna (by omega)
  have hD_lt_Dlb : D_nat < Dlb_nat := by
    have hld_lt_lnb : c.ld < c.lnb := lt_of_lt_of_le hld_lt_lna hlna_le_lnb
    unfold D_nat Dlb_nat
    rw [show 6 * c.ld * c.K = (6 * c.K) * c.ld by ring]
    exact Nat.mul_lt_mul_of_pos_left hld_lt_lnb (by omega)
  set c2a := polyMul c.ua c.ua
  set c3a := polyMul c2a c.ua
  set c2b := polyMul c.lb_env c.lb_env
  set c3b := polyMul c2b c.lb_env
  set Q : ℝ := (cellScale : ℝ) * (c.M : ℝ) ^ 4

  -- Bound 1 & 2: Uniform bounds on `E2Expect mu lam` and `E3Expect mu lam` for ALL `lam ∈ [la, lb]`
  have hE2_bounds : ∀ lam ∈ Set.Icc la lb,
      (e2l : ℝ) / Q ≤ E2Expect mu lam ∧ E2Expect mu lam ≤ (e2h : ℝ) / Q := by
    intro lam ⟨hlam_lo, hlam_hi⟩
    have hlam0 : 0 < lam := by linarith
    have hlam2 : lam < 2 := by linarith
    obtain ⟨hi_m2, hi_m1, hi_m0⟩ := f0_integrable3 (mu := mu) (lam := lam) hlam0 hlam2 hlam0 hlam2 (by linarith)
    obtain ⟨hi_u2, hi_u1, hi_u0⟩ := f0_integrable3 (mu := mu) (lam := la) hla0 hla2 hlb0 hlb2 (by linarith)
    obtain ⟨hi_l2, hi_l1, hi_l0⟩ := f0_integrable3 (mu := mu) (lam := lb) hlb0 hlb2 hla0 hla2 (by linarith)
    -- Upper bound: `E2(lam) ≤ E2_mixed(la, lb) ≤ e2h / Q`
    have hpt_up : ∀ T0 T1 T2,
        f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam) ≤
          f0Func la (beta T0 la) (beta T1 lb + beta T2 lb) := by
      intro T0 T1 T2
      have m0 := (lemma_4_1_support T0 hlam0 hlam2).1
      have m1 := (lemma_4_1_support T1 hlb0 hlb2).1
      have m2 := (lemma_4_1_support T2 hlb0 hlb2).1
      have d0 := lemma_4_2_mono T0 hla0 hlam_lo hlam2
      have d1 := lemma_4_2_mono T1 hlam0 hlam_hi hlb2
      have d2 := lemma_4_2_mono T2 hlam0 hlam_hi hlb2
      calc f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam)
          ≤ f0Func la (beta T0 lam) (beta T1 lam + beta T2 lam) :=
            f0Func_anti_lam (by linarith) hlam_lo (by linarith [d1, d2])
        _ ≤ f0Func la (beta T0 la) (beta T1 lam + beta T2 lam) :=
            f0Func_mono_y0 (by linarith) d0 (by linarith [d1, d2])
        _ ≤ f0Func la (beta T0 la) (beta T1 lb + beta T2 lb) :=
            f0Func_anti_t (by linarith) (by linarith) (by linarith)
    have hint_up : E2Expect mu lam ≤ ∫ T0, ∫ T1, ∫ T2, f0Func la (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu ∂mu :=
      integral_mono hi_m0 hi_u0 (fun T0 => integral_mono (hi_m1 T0) (hi_u1 T0) (fun T1 =>
        integral_mono (hi_m2 T0 T1) (hi_u2 T0 T1) (hpt_up T0 T1)))
    obtain ⟨hc_u, hmy_u, hat_u⟩ := f0Func_box_props (lam := la) (ay := aa) (by_ := ba) (at_ := 2 * ab) (bt := 2 * bb)
      (by linarith) haa_ba (by linarith) (by linarith)
    have hpeel_u := peel3_upper_mono_anti (mu := mu) hua hlb hc_u hmy_u hat_u
    have hgrid_u : evalGrid aa ha (fun y => evalGrid (2 * ab) hb (f0Func la y) c2b) c.ua ≤
        (raw_e2h : ℝ) / (cellScale : ℝ) := by
      unfold raw_e2h rawE2h c2b
      refine evalGrid2_le_sumGrid2 hS_pos (fun i _ j _ => ?_)
      set Dy : ℕ := Daa_nat + i * c.lna
      set Dt : ℕ := 2 * Dab_nat + j * c.lnb
      set den : ℕ := (Dla_nat - D_nat) + Dy + Dt
      have hden_pos : 0 < den := by unfold den; omega
      have hid : f0Func la (aa + (i : ℝ) * ha) (2 * ab + (j : ℝ) * hb) = (Dy : ℝ) / (den : ℝ) := by
        unfold f0Func den Dy Dt
        have hDy : ((Daa_nat + i * c.lna : ℕ) : ℝ) = (D_nat : ℝ) * (aa + (i : ℝ) * ha) := by
          push_cast; rw [← hDaa, ← hDha]; ring
        have hDt : ((2 * Dab_nat + j * c.lnb : ℕ) : ℝ) = (D_nat : ℝ) * (2 * ab + (j : ℝ) * hb) := by
          push_cast; rw [← hDab, ← hDhb]; ring
        have hDen : (((Dla_nat - D_nat) + (Daa_nat + i * c.lna) + (2 * Dab_nat + j * c.lnb) : ℕ) : ℝ) =
            (D_nat : ℝ) * (la - 1 + (aa + (i : ℝ) * ha) + (2 * ab + (j : ℝ) * hb)) := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (le_of_lt hD_lt_Dla), hDy, hDt, ← hDla]
          ring
        rw [hDy, hDen, mul_div_mul_left _ _ hD_ne]
      rw [hid]
      exact nat_div_up_bound hS_pos hden_pos
    -- Lower bound: `e2l / Q ≤ E2_mixed(lb, la) ≤ E2(lam)`
    have hpt_lo : ∀ T0 T1 T2,
        f0Func lb (beta T0 lb) (beta T1 la + beta T2 la) ≤
          f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam) := by
      intro T0 T1 T2
      have m0 := (lemma_4_1_support T0 hlb0 hlb2).1
      have m1 := (lemma_4_1_support T1 hlam0 hlam2).1
      have m2 := (lemma_4_1_support T2 hlam0 hlam2).1
      have d0 := lemma_4_2_mono T0 hlam0 hlam_hi hlb2
      have d1 := lemma_4_2_mono T1 hla0 hlam_lo hlam2
      have d2 := lemma_4_2_mono T2 hla0 hlam_lo hlam2
      calc f0Func lb (beta T0 lb) (beta T1 la + beta T2 la)
          ≤ f0Func lam (beta T0 lb) (beta T1 la + beta T2 la) :=
            f0Func_anti_lam (by linarith) hlam_hi (by linarith [d1, d2])
        _ ≤ f0Func lam (beta T0 lam) (beta T1 la + beta T2 la) :=
            f0Func_mono_y0 (by linarith) d0 (by linarith [d1, d2])
        _ ≤ f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam) :=
            f0Func_anti_t (by linarith) (by linarith) (by linarith)
    have hint_lo : (∫ T0, ∫ T1, ∫ T2, f0Func lb (beta T0 lb) (beta T1 la + beta T2 la) ∂mu ∂mu ∂mu) ≤ E2Expect mu lam :=
      integral_mono hi_l0 hi_m0 (fun T0 => integral_mono (hi_l1 T0) (hi_m1 T0) (fun T1 =>
        integral_mono (hi_l2 T0 T1) (hi_m2 T0 T1) (hpt_lo T0 T1)))
    obtain ⟨hc_l, hmy_l, hat_l⟩ := f0Func_box_props (lam := lb) (ay := ab) (by_ := bb) (at_ := 2 * aa) (bt := 2 * ba)
      (by linarith) hab_bb (by linarith) (by linarith)
    have hpeel_l := peel3_lower_mono_anti (mu := mu) hua hlb hc_l hmy_l hat_l
    have hgrid_l : (raw_e2l : ℝ) / (cellScale : ℝ) ≤
        evalGrid ab hb (fun y => evalGrid (2 * aa) ha (f0Func lb y) c2a) c.lb_env := by
      unfold raw_e2l rawE2l c2a
      refine sumGrid2_le_evalGrid2 hS_pos (fun i _ j _ => ?_)
      set Dy : ℕ := Dab_nat + i * c.lnb
      set Dt : ℕ := 2 * Daa_nat + j * c.lna
      set den : ℕ := (Dlb_nat - D_nat) + Dy + Dt
      have hden_pos : 0 < den := by unfold den; omega
      have hid : f0Func lb (ab + (i : ℝ) * hb) (2 * aa + (j : ℝ) * ha) = (Dy : ℝ) / (den : ℝ) := by
        unfold f0Func den Dy Dt
        have hDy : ((Dab_nat + i * c.lnb : ℕ) : ℝ) = (D_nat : ℝ) * (ab + (i : ℝ) * hb) := by
          push_cast; rw [← hDab, ← hDhb]; ring
        have hDt : ((2 * Daa_nat + j * c.lna : ℕ) : ℝ) = (D_nat : ℝ) * (2 * aa + (j : ℝ) * ha) := by
          push_cast; rw [← hDaa, ← hDha]; ring
        have hDen : (((Dlb_nat - D_nat) + (Dab_nat + i * c.lnb) + (2 * Daa_nat + j * c.lna) : ℕ) : ℝ) =
            (D_nat : ℝ) * (lb - 1 + (ab + (i : ℝ) * hb) + (2 * aa + (j : ℝ) * ha)) := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (le_of_lt hD_lt_Dlb), hDy, hDt, ← hDlb]
          ring
        rw [hDy, hDen, mul_div_mul_left _ _ hD_ne]
      rw [hid]
      exact nat_div_lo_bound hS_pos hden_pos
    have hM_ne : (c.M : ℝ) ≠ 0 := ne_of_gt hM_pos
    have hS_ne : (cellScale : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hS_pos)
    refine ⟨?_, ?_⟩
    · have h1 : (e2l : ℝ) / Q = (1 / (c.M : ℝ) ^ 3) * ((raw_e2l : ℝ) / (cellScale : ℝ)) := by
        unfold e2l Q; push_cast; field_simp [hM_ne, hS_ne]
      rw [h1]
      exact (mul_le_mul_of_nonneg_left hgrid_l (by positivity)).trans (hpeel_l.trans hint_lo)
    · have h1 : (e2h : ℝ) / Q = (1 / (c.M : ℝ) ^ 3) * ((raw_e2h : ℝ) / (cellScale : ℝ)) := by
        unfold e2h Q; push_cast; field_simp [hM_ne, hS_ne]
      rw [h1]
      exact hint_up.trans (hpeel_u.trans (mul_le_mul_of_nonneg_left hgrid_u (by positivity)))

  have hE3_bounds : ∀ lam ∈ Set.Icc la lb,
      (e3l : ℝ) / Q ≤ E3Expect mu lam ∧ E3Expect mu lam ≤ (e3h : ℝ) / Q := by
    intro lam ⟨hlam_lo, hlam_hi⟩
    have hlam0 : 0 < lam := by linarith
    have hlam2 : lam < 2 := by linarith
    obtain ⟨hi_m3, hi_m2, hi_m1, hi_m0⟩ := f0_integrable4 (mu := mu) (lam := lam) hlam0 hlam2 hlam0 hlam2 (by linarith)
    obtain ⟨hi_u3, hi_u2, hi_u1, hi_u0⟩ := f0_integrable4 (mu := mu) (lam := la) hla0 hla2 hlb0 hlb2 (by linarith)
    obtain ⟨hi_l3, hi_l2, hi_l1, hi_l0⟩ := f0_integrable4 (mu := mu) (lam := lb) hlb0 hlb2 hla0 hla2 (by linarith)
    have hpt_up : ∀ T0 T1 T2 T3,
        f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) ≤
          f0Func la (beta T0 la) (beta T1 lb + beta T2 lb + beta T3 lb) := by
      intro T0 T1 T2 T3
      have m0 := (lemma_4_1_support T0 hlam0 hlam2).1
      have m1 := (lemma_4_1_support T1 hlb0 hlb2).1
      have m2 := (lemma_4_1_support T2 hlb0 hlb2).1
      have m3 := (lemma_4_1_support T3 hlb0 hlb2).1
      have d0 := lemma_4_2_mono T0 hla0 hlam_lo hlam2
      have d1 := lemma_4_2_mono T1 hlam0 hlam_hi hlb2
      have d2 := lemma_4_2_mono T2 hlam0 hlam_hi hlb2
      have d3 := lemma_4_2_mono T3 hlam0 hlam_hi hlb2
      calc f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam)
          ≤ f0Func la (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) :=
            f0Func_anti_lam (by linarith) hlam_lo (by linarith)
        _ ≤ f0Func la (beta T0 la) (beta T1 lam + beta T2 lam + beta T3 lam) :=
            f0Func_mono_y0 (by linarith) d0 (by linarith)
        _ ≤ f0Func la (beta T0 la) (beta T1 lb + beta T2 lb + beta T3 lb) :=
            f0Func_anti_t (by linarith) (by linarith) (by linarith)
    have hint_up : E3Expect mu lam ≤ ∫ T0, ∫ T1, ∫ T2, ∫ T3, f0Func la (beta T0 la) (beta T1 lb + beta T2 lb + beta T3 lb) ∂mu ∂mu ∂mu ∂mu :=
      integral_mono hi_m0 hi_u0 (fun T0 => integral_mono (hi_m1 T0) (hi_u1 T0) (fun T1 =>
        integral_mono (hi_m2 T0 T1) (hi_u2 T0 T1) (fun T2 => integral_mono (hi_m3 T0 T1 T2) (hi_u3 T0 T1 T2) (hpt_up T0 T1 T2))))
    obtain ⟨hc_u, hmy_u, hat_u⟩ := f0Func_box_props (lam := la) (ay := aa) (by_ := ba) (at_ := 3 * ab) (bt := 3 * bb)
      (by linarith) haa_ba (by linarith) (by linarith)
    have hpeel_u := peel4_upper_mono_anti (mu := mu) hua hlb hc_u hmy_u hat_u
    have hgrid_u : evalGrid aa ha (fun y => evalGrid (3 * ab) hb (f0Func la y) c3b) c.ua ≤
        (raw_e3h : ℝ) / (cellScale : ℝ) := by
      unfold raw_e3h rawE3h c3b c2b
      refine evalGrid2_le_sumGrid2 hS_pos (fun i _ j _ => ?_)
      set Dy : ℕ := Daa_nat + i * c.lna
      set Dt : ℕ := 3 * Dab_nat + j * c.lnb
      set den : ℕ := (Dla_nat - D_nat) + Dy + Dt
      have hden_pos : 0 < den := by unfold den; omega
      have hid : f0Func la (aa + (i : ℝ) * ha) (3 * ab + (j : ℝ) * hb) = (Dy : ℝ) / (den : ℝ) := by
        unfold f0Func den Dy Dt
        have hDy : ((Daa_nat + i * c.lna : ℕ) : ℝ) = (D_nat : ℝ) * (aa + (i : ℝ) * ha) := by
          push_cast; rw [← hDaa, ← hDha]; ring
        have hDt : ((3 * Dab_nat + j * c.lnb : ℕ) : ℝ) = (D_nat : ℝ) * (3 * ab + (j : ℝ) * hb) := by
          push_cast; rw [← hDab, ← hDhb]; ring
        have hDen : (((Dla_nat - D_nat) + (Daa_nat + i * c.lna) + (3 * Dab_nat + j * c.lnb) : ℕ) : ℝ) =
            (D_nat : ℝ) * (la - 1 + (aa + (i : ℝ) * ha) + (3 * ab + (j : ℝ) * hb)) := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (le_of_lt hD_lt_Dla), hDy, hDt, ← hDla]
          ring
        rw [hDy, hDen, mul_div_mul_left _ _ hD_ne]
      rw [hid]
      exact nat_div_up_bound hS_pos hden_pos
    have hpt_lo : ∀ T0 T1 T2 T3,
        f0Func lb (beta T0 lb) (beta T1 la + beta T2 la + beta T3 la) ≤
          f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) := by
      intro T0 T1 T2 T3
      have m0 := (lemma_4_1_support T0 hlb0 hlb2).1
      have m1 := (lemma_4_1_support T1 hlam0 hlam2).1
      have m2 := (lemma_4_1_support T2 hlam0 hlam2).1
      have m3 := (lemma_4_1_support T3 hlam0 hlam2).1
      have d0 := lemma_4_2_mono T0 hlam0 hlam_hi hlb2
      have d1 := lemma_4_2_mono T1 hla0 hlam_lo hlam2
      have d2 := lemma_4_2_mono T2 hla0 hlam_lo hlam2
      have d3 := lemma_4_2_mono T3 hla0 hlam_lo hlam2
      calc f0Func lb (beta T0 lb) (beta T1 la + beta T2 la + beta T3 la)
          ≤ f0Func lam (beta T0 lb) (beta T1 la + beta T2 la + beta T3 la) :=
            f0Func_anti_lam (by linarith) hlam_hi (by linarith)
        _ ≤ f0Func lam (beta T0 lam) (beta T1 la + beta T2 la + beta T3 la) :=
            f0Func_mono_y0 (by linarith) d0 (by linarith)
        _ ≤ f0Func lam (beta T0 lam) (beta T1 lam + beta T2 lam + beta T3 lam) :=
            f0Func_anti_t (by linarith) (by linarith) (by linarith)
    have hint_lo : (∫ T0, ∫ T1, ∫ T2, ∫ T3, f0Func lb (beta T0 lb) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) ≤ E3Expect mu lam :=
      integral_mono hi_l0 hi_m0 (fun T0 => integral_mono (hi_l1 T0) (hi_m1 T0) (fun T1 =>
        integral_mono (hi_l2 T0 T1) (hi_m2 T0 T1) (fun T2 => integral_mono (hi_l3 T0 T1 T2) (hi_m3 T0 T1 T2) (hpt_lo T0 T1 T2))))
    obtain ⟨hc_l, hmy_l, hat_l⟩ := f0Func_box_props (lam := lb) (ay := ab) (by_ := bb) (at_ := 3 * aa) (bt := 3 * ba)
      (by linarith) hab_bb (by linarith) (by linarith)
    have hpeel_l := peel4_lower_mono_anti (mu := mu) hua hlb hc_l hmy_l hat_l
    have hgrid_l : (raw_e3l : ℝ) / (cellScale : ℝ) ≤
        evalGrid ab hb (fun y => evalGrid (3 * aa) ha (f0Func lb y) c3a) c.lb_env := by
      unfold raw_e3l rawE3l c3a c2a
      refine sumGrid2_le_evalGrid2 hS_pos (fun i _ j _ => ?_)
      set Dy : ℕ := Dab_nat + i * c.lnb
      set Dt : ℕ := 3 * Daa_nat + j * c.lna
      set den : ℕ := (Dlb_nat - D_nat) + Dy + Dt
      have hden_pos : 0 < den := by unfold den; omega
      have hid : f0Func lb (ab + (i : ℝ) * hb) (3 * aa + (j : ℝ) * ha) = (Dy : ℝ) / (den : ℝ) := by
        unfold f0Func den Dy Dt
        have hDy : ((Dab_nat + i * c.lnb : ℕ) : ℝ) = (D_nat : ℝ) * (ab + (i : ℝ) * hb) := by
          push_cast; rw [← hDab, ← hDhb]; ring
        have hDt : ((3 * Daa_nat + j * c.lna : ℕ) : ℝ) = (D_nat : ℝ) * (3 * aa + (j : ℝ) * ha) := by
          push_cast; rw [← hDaa, ← hDha]; ring
        have hDen : (((Dlb_nat - D_nat) + (Dab_nat + i * c.lnb) + (3 * Daa_nat + j * c.lna) : ℕ) : ℝ) =
            (D_nat : ℝ) * (lb - 1 + (ab + (i : ℝ) * hb) + (3 * aa + (j : ℝ) * ha)) := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (le_of_lt hD_lt_Dlb), hDy, hDt, ← hDlb]
          ring
        rw [hDy, hDen, mul_div_mul_left _ _ hD_ne]
      rw [hid]
      exact nat_div_lo_bound hS_pos hden_pos
    have hM_ne : (c.M : ℝ) ≠ 0 := ne_of_gt hM_pos
    have hS_ne : (cellScale : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hS_pos)
    refine ⟨?_, ?_⟩
    · have h1 : (e3l : ℝ) / Q = (1 / (c.M : ℝ) ^ 4) * ((raw_e3l : ℝ) / (cellScale : ℝ)) := by
        unfold e3l Q; field_simp [hM_ne, hS_ne]
      rw [h1]
      exact (mul_le_mul_of_nonneg_left hgrid_l (by positivity)).trans (hpeel_l.trans hint_lo)
    · have h1 : (e3h : ℝ) / Q = (1 / (c.M : ℝ) ^ 4) * ((raw_e3h : ℝ) / (cellScale : ℝ)) := by
        unfold e3h Q; field_simp [hM_ne, hS_ne]
      rw [h1]
      exact hint_up.trans (hpeel_u.trans (mul_le_mul_of_nonneg_left hgrid_u (by positivity)))
  exact ⟨hE2_bounds, hE3_bounds⟩

set_option maxHeartbeats 800000 in
lemma cell_H3_H2_bounds {mu : Measure InfTree23} [IsGWTree23 mu] (c : CellCert)
    (hua : checkUpperEnv c.lna c.ld c.K c.M c.ua c.j2ua c.j3ua = true)
    (hlb : checkLowerEnv c.lnb c.ld c.K c.M c.lb_env c.j2lb c.j3lb = true)
    (hcorn : checkCellCorners c = true) :
    let la : ℝ := (c.lna : ℝ) / c.ld
    let lb : ℝ := (c.lnb : ℝ) / c.ld
    let Q : ℝ := (cellScale : ℝ) * (c.M : ℝ) ^ 4
    (∫ T0, ∫ T1, ∫ T2, ∫ T3,
      h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) ≤
      (rawH3 c : ℝ) / Q ∧
    (∫ T0, ∫ T1, ∫ T2,
      h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu ∂mu) ≤
      ((c.M * rawH2 c : ℕ) : ℝ) / Q := by
  set raw_h3 := rawH3 c
  set raw_h2 := rawH2 c
  set h3_up : ℕ := raw_h3
  set h2_up : ℕ := c.M * raw_h2
  obtain ⟨hlna0, hlna2, hK, hM, _⟩ := checkUpperEnv_dims hua
  obtain ⟨hlnb0, hlnb2, _, _, _⟩ := checkLowerEnv_dims hlb
  have hld : 0 < c.ld := by omega
  obtain ⟨hla1, hlalb, hlb2, hA_pos, _, hld_lt_lna, _, hkap_nat, _, _, _, _⟩ :=
    corner_identities c hlnb2 hcorn
  obtain ⟨hh3_cont_big, hh3_mono_big, hh2_cont_big, hh2_mono_big⟩ :=
    cell_h3_h2_box_props c hlnb2 hcorn
  obtain ⟨hD_pos, hDla, hDaa, hDha⟩ := grid_identities (ln := c.lna) hld hlna2 hK
  obtain ⟨_, hDlb, hDab, hDhb⟩ := grid_identities (ln := c.lnb) hld hlnb2 hK
  set la : ℝ := (c.lna : ℝ) / c.ld
  set lb : ℝ := (c.lnb : ℝ) / c.ld
  set aa : ℝ := 1 - la / 2
  set ba : ℝ := 1 - la / 3
  set ha : ℝ := (ba - aa) / c.K
  set ab : ℝ := 1 - lb / 2
  set bb : ℝ := 1 - lb / 3
  set hb : ℝ := (bb - ab) / c.K
  have haa_eq : aa = 1 - la / 2 := rfl
  have hba_eq : ba = 1 - la / 3 := rfl
  have hab_eq : ab = 1 - lb / 2 := rfl
  have hbb_eq : bb = 1 - lb / 3 := rfl
  have haa_ab : ab ≤ aa := by linarith
  have hbb_ba : bb ≤ ba := by linarith
  have hM_pos : (0 : ℝ) < c.M := Nat.cast_pos.mpr hM
  have hS_pos : 0 < cellScale := by decide
  set D_nat : ℕ := 6 * c.ld * c.K
  set Dla_nat : ℕ := 6 * c.K * c.lna
  set Dlb_nat : ℕ := 6 * c.K * c.lnb
  set Daa_nat : ℕ := 3 * c.K * (2 * c.ld - c.lna)
  set Dab_nat : ℕ := 3 * c.K * (2 * c.ld - c.lnb)
  set E_nat : ℕ := 2 * D_nat - Dlb_nat
  set Knum_nat : ℕ := 2 * D_nat + Dla_nat - 2 * Dlb_nat
  have hD_ne : ((D_nat : ℝ)) ≠ 0 := ne_of_gt hD_pos
  have hD_lt_Dla : D_nat < Dla_nat := by
    unfold D_nat Dla_nat
    rw [show 6 * c.ld * c.K = (6 * c.K) * c.ld by ring]
    exact Nat.mul_lt_mul_of_pos_left hld_lt_lna (by omega)
  have hDlb_lt_2D : Dlb_nat < 2 * D_nat := by
    unfold Dlb_nat D_nat
    rw [show 2 * (6 * c.ld * c.K) = (6 * c.K) * (2 * c.ld) by ring]
    exact Nat.mul_lt_mul_of_pos_left hlnb2 (by omega)
  have h2Dlb_lt : 2 * Dlb_nat < 2 * D_nat + Dla_nat := by
    unfold Dlb_nat D_nat Dla_nat
    have hmul := Nat.mul_lt_mul_of_pos_left hkap_nat hK
    linarith
  have hE_pos_nat : 0 < E_nat := by omega
  have hE_cast : (E_nat : ℝ) = (D_nat : ℝ) * (2 - lb) := by
    unfold E_nat
    rw [Nat.cast_sub (le_of_lt hDlb_lt_2D), Nat.cast_mul, ← hDlb]
    push_cast; ring
  have hKnum_cast : (Knum_nat : ℝ) = (E_nat : ℝ) * (1 - (1 / (2 - lb)) * (lb - la)) := by
    have hsub : (Knum_nat : ℝ) = 2 * (D_nat : ℝ) + (Dla_nat : ℝ) - 2 * (Dlb_nat : ℝ) := by
      unfold Knum_nat
      rw [Nat.cast_sub (le_of_lt h2Dlb_lt)]
      push_cast; ring
    rw [hsub, ← hDla, ← hDlb, hE_cast]
    have h2lb_ne : 2 - lb ≠ 0 := by linarith
    field_simp [h2lb_ne]; ring
  have hE_ne : (E_nat : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hE_pos_nat)
  set c2a := polyMul c.ua c.ua
  set c3a := polyMul c2a c.ua
  set c2b := polyMul c.lb_env c.lb_env
  set Q : ℝ := (cellScale : ℝ) * (c.M : ℝ) ^ 4

  -- Bound 3: Upper bound `h3_up / Q` on `∫∫∫∫ h3Func la lb (beta T0 la) (∑ beta Ti la)`
  have hH3_bound : (∫ T0, ∫ T1, ∫ T2, ∫ T3,
      h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu) ≤ (h3_up : ℝ) / Q := by
    have hsub : Set.Icc aa ba ×ˢ Set.Icc (3 * aa) (3 * ba) ⊆ Set.Icc ab ba ×ˢ Set.Icc (3 * ab) (3 * ba) :=
      Set.prod_mono (Set.Icc_subset_Icc_left haa_ab) (Set.Icc_subset_Icc_left (by linarith))
    have hpeel := peel4_upper_mono_mono (mu := mu) hua (hh3_cont_big.mono hsub)
      (fun t ht y1 hy1 y2 hy2 hle => hh3_mono_big (haa_ab.trans hy1.1) hle hy2.2 (by linarith [ht.1]) le_rfl ht.2)
      (fun y hy t1 ht1 t2 ht2 hle => hh3_mono_big (haa_ab.trans hy.1) le_rfl hy.2 (by linarith [ht1.1]) hle ht2.2)
    have hgrid : evalGrid aa ha (fun y => evalGrid (3 * aa) ha (h3Func la lb y) c3a) c.ua ≤
        (raw_h3 : ℝ) / (cellScale : ℝ) := by
      unfold raw_h3 rawH3 c3a c2a
      refine evalGrid2_le_sumGrid2 hS_pos (fun i _ j _ => ?_)
      set Dy : ℕ := Daa_nat + i * c.lna
      set Dt : ℕ := 3 * Daa_nat + j * c.lna
      set num : ℕ := D_nat * E_nat * Dy * (Dt - E_nat)
      set den : ℕ := (E_nat * (Dla_nat - D_nat) + Knum_nat * (Dy + Dt)) ^ 2
      have hE_le_Dt : E_nat ≤ Dt := by
        have h1 : E_nat = 6 * c.K * (2 * c.ld - c.lnb) := by
          unfold E_nat D_nat Dlb_nat
          rw [show 2 * (6 * c.ld * c.K) = 6 * c.K * (2 * c.ld) by ring, ← Nat.mul_sub_left_distrib]
        have h2 : 6 * c.K * (2 * c.ld - c.lnb) ≤ 9 * c.K * (2 * c.ld - c.lna) := by
          have hsub_le : 2 * c.ld - c.lnb ≤ 2 * c.ld - c.lna := by omega
          nlinarith
        unfold Dt Daa_nat
        linarith [Nat.zero_le (j * c.lna)]
      have hden_pos : 0 < den := by
        unfold den; exact pow_pos (by have : 0 < E_nat * (Dla_nat - D_nat) := Nat.mul_pos hE_pos_nat (by omega); omega) 2
      have hid : h3Func la lb (aa + (i : ℝ) * ha) (3 * aa + (j : ℝ) * ha) = (num : ℝ) / (den : ℝ) := by
        unfold h3Func num den
        have hDy : (Dy : ℝ) = (D_nat : ℝ) * (aa + (i : ℝ) * ha) := by
          unfold Dy; push_cast; rw [← hDaa, ← hDha]; ring
        have hDt : (Dt : ℝ) = (D_nat : ℝ) * (3 * aa + (j : ℝ) * ha) := by
          unfold Dt; push_cast; rw [← hDaa, ← hDha]; ring
        have hNum : ((D_nat * E_nat * Dy * (Dt - E_nat) : ℕ) : ℝ) =
            ((D_nat : ℝ) * (E_nat : ℝ)) ^ 2 *
              ((aa + (i : ℝ) * ha) * ((1 / (2 - lb)) * (3 * aa + (j : ℝ) * ha) - 1)) := by
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hE_le_Dt, hDy, hDt, hE_cast]
          have h2lb_ne : 2 - lb ≠ 0 := by linarith
          field_simp [h2lb_ne]
        have hDen : (((E_nat * (Dla_nat - D_nat) + Knum_nat * (Dy + Dt)) ^ 2 : ℕ) : ℝ) =
            ((D_nat : ℝ) * (E_nat : ℝ)) ^ 2 *
              ((la - 1) + (1 - (1 / (2 - lb)) * (lb - la)) * ((aa + (i : ℝ) * ha) + (3 * aa + (j : ℝ) * ha))) ^ 2 := by
          rw [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add,
              Nat.cast_sub (le_of_lt hD_lt_Dla), hDy, hDt, ← hDla, hKnum_cast]
          ring
        have hfac_ne : ((D_nat : ℝ) * (E_nat : ℝ)) ^ 2 ≠ 0 :=
          pow_ne_zero 2 (mul_ne_zero hD_ne hE_ne)
        rw [hNum, hDen, mul_div_mul_left _ _ hfac_ne]
      rw [hid]
      exact nat_div_up_bound hS_pos hden_pos
    have hM_ne : (c.M : ℝ) ≠ 0 := ne_of_gt hM_pos
    have hS_ne : (cellScale : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hS_pos)
    have h1 : (h3_up : ℝ) / Q = (1 / (c.M : ℝ) ^ 4) * ((raw_h3 : ℝ) / (cellScale : ℝ)) := by
      unfold h3_up Q; field_simp [hM_ne, hS_ne]
    rw [h1]
    exact hpeel.trans (mul_le_mul_of_nonneg_left hgrid (by positivity))

  -- Bound 4: Upper bound `h2_up / Q` on `∫∫∫ h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb)`
  have hH2_bound : (∫ T0, ∫ T1, ∫ T2,
      h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu ∂mu) ≤ (h2_up : ℝ) / Q := by
    have hsub : Set.Icc aa ba ×ˢ Set.Icc (2 * ab) (2 * bb) ⊆ Set.Icc ab ba ×ˢ Set.Icc (2 * ab) (2 * ba) :=
      Set.prod_mono (Set.Icc_subset_Icc_left haa_ab) (Set.Icc_subset_Icc_right (by linarith))
    have hpeel := peel3_upper_mono_anti (mu := mu) hua hlb (hh2_cont_big.mono hsub)
      (fun t ht y1 hy1 y2 hy2 hle => hh2_mono_big (haa_ab.trans hy1.1) hle hy2.2 ht.1 le_rfl (by linarith [ht.2]))
      (fun y hy t1 ht1 t2 ht2 hle => hh2_mono_big (haa_ab.trans hy.1) le_rfl hy.2 ht1.1 hle (by linarith [ht2.2]))
    have hgrid : evalGrid aa ha (fun y => evalGrid (2 * ab) hb (h2Func la lb y) c2b) c.ua ≤
        (raw_h2 : ℝ) / (cellScale : ℝ) := by
      unfold raw_h2 rawH2 c2b
      refine evalGrid2_le_sumGrid2 hS_pos (fun i _ j _ => ?_)
      set Dy : ℕ := Daa_nat + i * c.lna
      set Dt : ℕ := 2 * Dab_nat + j * c.lnb
      set num : ℕ := D_nat * E_nat * Dy * (D_nat + Dt)
      set den : ℕ := (E_nat * (Dla_nat - D_nat) + Knum_nat * (Dy + Dt)) ^ 2
      have hden_pos : 0 < den := by
        unfold den; exact pow_pos (by have : 0 < E_nat * (Dla_nat - D_nat) := Nat.mul_pos hE_pos_nat (by omega); omega) 2
      have hid : h2Func la lb (aa + (i : ℝ) * ha) (2 * ab + (j : ℝ) * hb) = (num : ℝ) / (den : ℝ) := by
        unfold h2Func num den
        have hDy : (Dy : ℝ) = (D_nat : ℝ) * (aa + (i : ℝ) * ha) := by
          unfold Dy; push_cast; rw [← hDaa, ← hDha]; ring
        have hDt : (Dt : ℝ) = (D_nat : ℝ) * (2 * ab + (j : ℝ) * hb) := by
          unfold Dt; push_cast; rw [← hDab, ← hDhb]; ring
        have hNum : ((D_nat * E_nat * Dy * (D_nat + Dt) : ℕ) : ℝ) =
            ((D_nat : ℝ) * (E_nat : ℝ)) ^ 2 *
              ((aa + (i : ℝ) * ha) * (1 + (1 / (2 - lb)) * (lb - 1 + (2 * ab + (j : ℝ) * hb)))) := by
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_add D_nat Dt, hDy, hDt, hE_cast]
          have h2lb_ne : 2 - lb ≠ 0 := by linarith
          field_simp [h2lb_ne]; ring
        have hDen : (((E_nat * (Dla_nat - D_nat) + Knum_nat * (Dy + Dt)) ^ 2 : ℕ) : ℝ) =
            ((D_nat : ℝ) * (E_nat : ℝ)) ^ 2 *
              ((la - 1) + (1 - (1 / (2 - lb)) * (lb - la)) * ((aa + (i : ℝ) * ha) + (2 * ab + (j : ℝ) * hb))) ^ 2 := by
          rw [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add,
              Nat.cast_sub (le_of_lt hD_lt_Dla), hDy, hDt, ← hDla, hKnum_cast]
          ring
        have hfac_ne : ((D_nat : ℝ) * (E_nat : ℝ)) ^ 2 ≠ 0 :=
          pow_ne_zero 2 (mul_ne_zero hD_ne hE_ne)
        rw [hNum, hDen, mul_div_mul_left _ _ hfac_ne]
      rw [hid]
      exact nat_div_up_bound hS_pos hden_pos
    have hM_ne : (c.M : ℝ) ≠ 0 := ne_of_gt hM_pos
    have hS_ne : (cellScale : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hS_pos)
    have h1 : (h2_up : ℝ) / Q = (1 / (c.M : ℝ) ^ 3) * ((raw_h2 : ℝ) / (cellScale : ℝ)) := by
      unfold h2_up Q; push_cast; field_simp [hM_ne, hS_ne]
    rw [h1]
    exact hpeel.trans (mul_le_mul_of_nonneg_left hgrid (by positivity))
  exact ⟨hH3_bound, hH2_bound⟩

set_option maxHeartbeats 800000 in
lemma cell_diff_bounds {mu : Measure InfTree23} [IsGWTree23 mu] (c : CellCert)
    (hlnb2 : c.lnb < 2 * c.ld) (hcorn : checkCellCorners c = true)
    {H3 H2 : ℝ}
    (hH3_bound : (∫ T0, ∫ T1, ∫ T2, ∫ T3,
      h3Func ((c.lna : ℝ) / c.ld) ((c.lnb : ℝ) / c.ld) (beta T0 ((c.lna : ℝ) / c.ld))
        (beta T1 ((c.lna : ℝ) / c.ld) + beta T2 ((c.lna : ℝ) / c.ld) + beta T3 ((c.lna : ℝ) / c.ld))
        ∂mu ∂mu ∂mu ∂mu) ≤ H3)
    (hH2_bound : (∫ T0, ∫ T1, ∫ T2,
      h2Func ((c.lna : ℝ) / c.ld) ((c.lnb : ℝ) / c.ld) (beta T0 ((c.lna : ℝ) / c.ld))
        (beta T1 ((c.lnb : ℝ) / c.ld) + beta T2 ((c.lnb : ℝ) / c.ld)) ∂mu ∂mu ∂mu) ≤ H2)
    {lam1 lam2 : ℝ}
    (hlam1 : lam1 ∈ Set.Icc ((c.lna : ℝ) / c.ld) ((c.lnb : ℝ) / c.ld))
    (hlam2 : lam2 ∈ Set.Icc ((c.lna : ℝ) / c.ld) ((c.lnb : ℝ) / c.ld))
    (hlt : lam1 < lam2) :
    let R1 := RFunc mu lam1
    (2 - R1) * ((E2Expect mu lam2 - E2Expect mu lam1) / (lam2 - lam1)) ≤ (R1 - 2) * H2 ∧
    (3 - R1) * ((E3Expect mu lam2 - E3Expect mu lam1) / (lam2 - lam1)) ≤ (3 - R1) * H3 := by
  obtain ⟨hla1, hlalb, hlb2, hA_pos, hkap_pos, _, _, _, _, _, _, _⟩ :=
    corner_identities c hlnb2 hcorn
  obtain ⟨hh3_cont_big, hh3_mono_big, hh2_cont_big, hh2_mono_big⟩ :=
    cell_h3_h2_box_props c hlnb2 hcorn
  set la : ℝ := (c.lna : ℝ) / c.ld
  set lb : ℝ := (c.lnb : ℝ) / c.ld
  set aa : ℝ := 1 - la / 2
  set ba : ℝ := 1 - la / 3
  set ab : ℝ := 1 - lb / 2
  set bb : ℝ := 1 - lb / 3
  have haa_eq : aa = 1 - la / 2 := rfl
  have hba_eq : ba = 1 - la / 3 := rfl
  have hab_eq : ab = 1 - lb / 2 := rfl
  have hbb_eq : bb = 1 - lb / 3 := rfl
  have hla0 : 0 < la := by linarith
  have hla2 : la < 2 := by linarith
  have hlb0 : 0 < lb := by linarith
  have haa_ab : ab ≤ aa := by linarith
  have hbb_ba : bb ≤ ba := by linarith
  have haa_ba : aa ≤ ba := by linarith
  have hlam1_0 : 0 < lam1 := by linarith [hlam1.1]
  have hlam1_2 : lam1 < 2 := by linarith [hlam1.2]
  have hlam2_0 : 0 < lam2 := by linarith [hlam2.1]
  have hlam2_2 : lam2 < 2 := by linarith [hlam2.2]
  set E2_1 := E2Expect mu lam1
  set E3_1 := E3Expect mu lam1
  set E2_2 := E2Expect mu lam2
  set E3_2 := E3Expect mu lam2
  set R1 := RFunc mu lam1
  obtain ⟨hR1_gt2, hR1_le25⟩ := RFunc_bounds (mu := mu) hlam1_0 hlam1_2
  have hdiff2 : (2 - R1) * ((E2_2 - E2_1) / (lam2 - lam1)) ≤ (R1 - 2) * H2 := by
    obtain ⟨hi1_2, hi1_1, hi1_0⟩ := f0_integrable3 (mu := mu) (lam := lam1) hlam1_0 hlam1_2 hlam1_0 hlam1_2 (by linarith)
    obtain ⟨hi2_2, hi2_1, hi2_0⟩ := f0_integrable3 (mu := mu) (lam := lam2) hlam2_0 hlam2_2 hlam2_0 hlam2_2 (by linarith)
    -- Integrability of `h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb)`
    have hsub2 : Set.Icc aa ba ×ˢ Set.Icc (2 * ab) (2 * bb) ⊆ Set.Icc ab ba ×ˢ Set.Icc (2 * ab) (2 * ba) :=
      Set.prod_mono (Set.Icc_subset_Icc_left haa_ab) (Set.Icc_subset_Icc_right (by linarith))
    obtain ⟨hFc2_cont, _, _, ⟨C2, hC2⟩⟩ := clampBox_props_mono_anti haa_ba (by linarith) (hh2_cont_big.mono hsub2)
      (fun t ht y1 hy1 y2 hy2 hle => hh2_mono_big (haa_ab.trans hy1.1) hle hy2.2 ht.1 le_rfl (by linarith [ht.2]))
      (fun y hy t1 ht1 t2 ht2 hle => hh2_mono_big (haa_ab.trans hy.1) le_rfl hy.2 ht1.1 hle (by linarith [ht2.2]))
    set Fc2 := clampBox aa ba (2 * ab) (2 * bb) (h2Func la lb)
    have hFc2_eq : ∀ T0 T1 T2, h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb) = Fc2 (beta T0 la) (beta T1 lb + beta T2 lb) := by
      intro T0 T1 T2
      have m0 := lemma_4_1_support T0 hla0 hla2
      have m1 := lemma_4_1_support T1 hlb0 hlb2
      have m2 := lemma_4_1_support T2 hlb0 hlb2
      unfold Fc2 clampBox
      rw [clampIcc_eq_self m0, clampIcc_eq_self ⟨by linarith [m1.1, m2.1], by linarith [m1.2, m2.2]⟩]
    have hih2_2 : ∀ T0 T1, Integrable (fun T2 => h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb)) mu := by
      intro T0 T1; simp_rw [hFc2_eq]
      exact (integrable_sum2 (mu := mu) (hFc2_cont.comp (continuous_const.prodMk continuous_id)) (hC2 _) (measurable_beta _) (measurable_beta _)).1 T1
    have hih2_1 : ∀ T0, Integrable (fun T1 => ∫ T2, h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu) mu := by
      intro T0; simp_rw [hFc2_eq]
      exact (integrable_sum2 (mu := mu) (hFc2_cont.comp (continuous_const.prodMk continuous_id)) (hC2 _) (measurable_beta _) (measurable_beta _)).2.1
    have hih2_0 : Integrable (fun T0 => ∫ T1, ∫ T2, h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu) mu := by
      simp_rw [hFc2_eq]
      exact integrable_biv3_outer (mu := mu) hFc2_cont hC2 (measurable_beta _) (measurable_beta _) (measurable_beta _)
    have hpt2 : ∀ T0 T1 T2,
        (2 - R1) * ((f0Func lam2 (beta T0 lam2) (beta T1 lam2 + beta T2 lam2) -
          f0Func lam1 (beta T0 lam1) (beta T1 lam1 + beta T2 lam1)) / (lam2 - lam1)) ≤
        (R1 - 2) * h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb) := by
      intro T0 T1 T2
      have s0_1 := lemma_4_1_support T0 hlam1_0 hlam1_2
      have s1_1 := lemma_4_1_support T1 hlam1_0 hlam1_2
      have s2_1 := lemma_4_1_support T2 hlam1_0 hlam1_2
      have lip0 := (lemma_4_3_lipschitz T0 hlam1_0 hlt hlam2_2).2
      have lip1 := (lemma_4_3_lipschitz T1 hlam1_0 hlt hlam2_2).2
      have lip2 := (lemma_4_3_lipschitz T2 hlam1_0 hlt hlam2_2).2
      have hc_le : 1 / (2 - lam2) ≤ 1 / (2 - lb) :=
        one_div_le_one_div_of_le (by linarith) (by linarith [hlam2.2])
      have hlip0_up : beta T0 lam1 - beta T0 lam2 ≤ (lam2 - lam1) * (1 / (2 - lb)) * beta T0 lam1 := by
        have h1 : (lam2 - lam1) * beta T0 lam1 / (2 - lam2) = ((lam2 - lam1) * beta T0 lam1) * (1 / (2 - lam2)) := by ring
        have h2 : ((lam2 - lam1) * beta T0 lam1) * (1 / (2 - lam2)) ≤ ((lam2 - lam1) * beta T0 lam1) * (1 / (2 - lb)) :=
          mul_le_mul_of_nonneg_left hc_le (mul_nonneg (by linarith) (by linarith [s0_1.1]))
        linarith
      have hlip0_lo : (1 - (1 / (2 - lb)) * (lb - la)) * beta T0 lam1 ≤ beta T0 lam2 := by
        have hm : (lam2 - lam1) * (1 / (2 - lb)) * beta T0 lam1 ≤ (lb - la) * (1 / (2 - lb)) * beta T0 lam1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [hlam1.1, hlam2.2]) (by positivity)) (by linarith [s0_1.1])
        linarith
      have hlip_s_lo : (1 - (1 / (2 - lb)) * (lb - la)) * (beta T1 lam1 + beta T2 lam1) ≤ beta T1 lam2 + beta T2 lam2 := by
        have h1 : beta T1 lam1 - beta T1 lam2 ≤ (lb - la) * (1 / (2 - lb)) * beta T1 lam1 := by
          have ha : (lam2 - lam1) * beta T1 lam1 / (2 - lam2) ≤ ((lam2 - lam1) * beta T1 lam1) * (1 / (2 - lb)) := by
            rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hc_le (mul_nonneg (by linarith) (by linarith [s1_1.1]))
          have hb : ((lam2 - lam1) * beta T1 lam1) * (1 / (2 - lb)) ≤ ((lb - la) * beta T1 lam1) * (1 / (2 - lb)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [hlam1.1, hlam2.2]) (by linarith [s1_1.1])) (by positivity)
          linarith
        have h2 : beta T2 lam1 - beta T2 lam2 ≤ (lb - la) * (1 / (2 - lb)) * beta T2 lam1 := by
          have ha : (lam2 - lam1) * beta T2 lam1 / (2 - lam2) ≤ ((lam2 - lam1) * beta T2 lam1) * (1 / (2 - lb)) := by
            rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hc_le (mul_nonneg (by linarith) (by linarith [s2_1.1]))
          have hb : ((lam2 - lam1) * beta T2 lam1) * (1 / (2 - lb)) ≤ ((lb - la) * beta T2 lam1) * (1 / (2 - lb)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [hlam1.1, hlam2.2]) (by linarith [s2_1.1])) (by positivity)
          linarith
        linarith
      have h61 := lemma_6_1_nu2 hla1 hlb2 hlam1.1 hlt hlam2.2 hR1_gt2
        (by linarith [s0_1.1]) (by linarith [s1_1.1, s2_1.1]) hlip0_up hlip0_lo
        (add_le_add (lemma_4_2_mono T1 hlam1_0 (le_of_lt hlt) hlam2_2) (lemma_4_2_mono T2 hlam1_0 (le_of_lt hlt) hlam2_2))
        hlip_s_lo hkap_pos
      have hm_box := hh2_mono_big
        (by unfold ab; linarith [s0_1.1, hlam1.2])
        (lemma_4_2_mono T0 hla0 hlam1.1 hlam1_2)
        (lemma_4_1_support T0 hla0 hla2).2
        (by linarith [(lemma_4_1_support T1 hlb0 hlb2).1, (lemma_4_1_support T2 hlb0 hlb2).1])
        (add_le_add (lemma_4_2_mono T1 hlam1_0 hlam1.2 hlb2) (lemma_4_2_mono T2 hlam1_0 hlam1.2 hlb2))
        (by unfold ba; linarith [s1_1.2, s2_1.2, hlam1.1])
      exact h61.trans (mul_le_mul_of_nonneg_left hm_box (by linarith))
    have hstep2 : ∀ T0 T1,
        (2 - R1) * (((∫ T2, f0Func lam2 (beta T0 lam2) (beta T1 lam2 + beta T2 lam2) ∂mu) -
          (∫ T2, f0Func lam1 (beta T0 lam1) (beta T1 lam1 + beta T2 lam1) ∂mu)) / (lam2 - lam1)) ≤
        (R1 - 2) * ∫ T2, h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu := by
      intro T0 T1
      rw [← integral_sub (hi2_2 T0 T1) (hi1_2 T0 T1), ← integral_div, ← integral_const_mul, ← integral_const_mul]
      exact integral_mono ((((hi2_2 T0 T1).sub (hi1_2 T0 T1)).div_const _).const_mul _)
        ((hih2_2 T0 T1).const_mul _) (hpt2 T0 T1)
    have hstep1 : ∀ T0,
        (2 - R1) * (((∫ T1, ∫ T2, f0Func lam2 (beta T0 lam2) (beta T1 lam2 + beta T2 lam2) ∂mu ∂mu) -
          (∫ T1, ∫ T2, f0Func lam1 (beta T0 lam1) (beta T1 lam1 + beta T2 lam1) ∂mu ∂mu)) / (lam2 - lam1)) ≤
        (R1 - 2) * ∫ T1, ∫ T2, h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu := by
      intro T0
      rw [← integral_sub (hi2_1 T0) (hi1_1 T0), ← integral_div, ← integral_const_mul, ← integral_const_mul]
      exact integral_mono ((((hi2_1 T0).sub (hi1_1 T0)).div_const _).const_mul _)
        ((hih2_1 T0).const_mul _) (hstep2 T0)
    have hstep0 :
        (2 - R1) * ((E2_2 - E2_1) / (lam2 - lam1)) ≤
        (R1 - 2) * ∫ T0, ∫ T1, ∫ T2, h2Func la lb (beta T0 la) (beta T1 lb + beta T2 lb) ∂mu ∂mu ∂mu := by
      unfold E2_2 E2_1 E2Expect
      rw [← integral_sub hi2_0 hi1_0, ← integral_div, ← integral_const_mul, ← integral_const_mul]
      exact integral_mono (((hi2_0.sub hi1_0).div_const _).const_mul _)
        (hih2_0.const_mul _) hstep1
    exact hstep0.trans (mul_le_mul_of_nonneg_left hH2_bound (by linarith))

  have hdiff3 : (3 - R1) * ((E3_2 - E3_1) / (lam2 - lam1)) ≤ (3 - R1) * H3 := by
    obtain ⟨hi1_3, hi1_2, hi1_1, hi1_0⟩ := f0_integrable4 (mu := mu) (lam := lam1) hlam1_0 hlam1_2 hlam1_0 hlam1_2 (by linarith)
    obtain ⟨hi2_3, hi2_2, hi2_1, hi2_0⟩ := f0_integrable4 (mu := mu) (lam := lam2) hlam2_0 hlam2_2 hlam2_0 hlam2_2 (by linarith)
    have hsub3 : Set.Icc aa ba ×ˢ Set.Icc (3 * aa) (3 * ba) ⊆ Set.Icc ab ba ×ˢ Set.Icc (3 * ab) (3 * ba) :=
      Set.prod_mono (Set.Icc_subset_Icc_left haa_ab) (Set.Icc_subset_Icc_left (by linarith))
    obtain ⟨hFc3_cont, _, _, ⟨C3, hC3⟩⟩ := clampBox_props_mono_mono haa_ba (by linarith) (hh3_cont_big.mono hsub3)
      (fun t ht y1 hy1 y2 hy2 hle => hh3_mono_big (haa_ab.trans hy1.1) hle hy2.2 (by linarith [ht.1]) le_rfl ht.2)
      (fun y hy t1 ht1 t2 ht2 hle => hh3_mono_big (haa_ab.trans hy.1) le_rfl hy.2 (by linarith [ht1.1]) hle ht2.2)
    set Fc3 := clampBox aa ba (3 * aa) (3 * ba) (h3Func la lb)
    have hFc3_eq : ∀ T0 T1 T2 T3, h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) =
        Fc3 (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) := by
      intro T0 T1 T2 T3
      have m0 := lemma_4_1_support T0 hla0 hla2
      have m1 := lemma_4_1_support T1 hla0 hla2
      have m2 := lemma_4_1_support T2 hla0 hla2
      have m3 := lemma_4_1_support T3 hla0 hla2
      unfold Fc3 clampBox
      rw [clampIcc_eq_self m0, clampIcc_eq_self ⟨by linarith [m1.1, m2.1, m3.1], by linarith [m1.2, m2.2, m3.2]⟩]
    have hih3_3 : ∀ T0 T1 T2, Integrable (fun T3 => h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la)) mu := by
      intro T0 T1 T2; simp_rw [hFc3_eq]
      exact (integrable_sum3 (mu := mu) (hFc3_cont.comp (continuous_const.prodMk continuous_id)) (hC3 _) (measurable_beta _) (measurable_beta _) (measurable_beta _)).1 T1 T2
    have hih3_2 : ∀ T0 T1, Integrable (fun T2 => ∫ T3, h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu) mu := by
      intro T0 T1; simp_rw [hFc3_eq]
      exact (integrable_sum3 (mu := mu) (hFc3_cont.comp (continuous_const.prodMk continuous_id)) (hC3 _) (measurable_beta _) (measurable_beta _) (measurable_beta _)).2.1 T1
    have hih3_1 : ∀ T0, Integrable (fun T1 => ∫ T2, ∫ T3, h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu) mu := by
      intro T0; simp_rw [hFc3_eq]
      exact (integrable_sum3 (mu := mu) (hFc3_cont.comp (continuous_const.prodMk continuous_id)) (hC3 _) (measurable_beta _) (measurable_beta _) (measurable_beta _)).2.2.1
    have hih3_0 : Integrable (fun T0 => ∫ T1, ∫ T2, ∫ T3, h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu) mu := by
      simp_rw [hFc3_eq]
      exact integrable_biv4_outer (mu := mu) hFc3_cont hC3 (measurable_beta _) (measurable_beta _) (measurable_beta _) (measurable_beta _)
    have hpt3 : ∀ T0 T1 T2 T3,
        (3 - R1) * ((f0Func lam2 (beta T0 lam2) (beta T1 lam2 + beta T2 lam2 + beta T3 lam2) -
          f0Func lam1 (beta T0 lam1) (beta T1 lam1 + beta T2 lam1 + beta T3 lam1)) / (lam2 - lam1)) ≤
        (3 - R1) * h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) := by
      intro T0 T1 T2 T3
      have s0_1 := lemma_4_1_support T0 hlam1_0 hlam1_2
      have s1_1 := lemma_4_1_support T1 hlam1_0 hlam1_2
      have s2_1 := lemma_4_1_support T2 hlam1_0 hlam1_2
      have s3_1 := lemma_4_1_support T3 hlam1_0 hlam1_2
      have hc_le : 1 / (2 - lam2) ≤ 1 / (2 - lb) :=
        one_div_le_one_div_of_le (by linarith) (by linarith [hlam2.2])
      have hlip_single : ∀ T : InfTree23,
          beta T lam1 - beta T lam2 ≤ (lam2 - lam1) * (1 / (2 - lb)) * beta T lam1 := by
        intro T
        have sT := (lemma_4_1_support T hlam1_0 hlam1_2).1
        have lT := (lemma_4_3_lipschitz T hlam1_0 hlt hlam2_2).2
        have ha : (lam2 - lam1) * beta T lam1 / (2 - lam2) ≤ ((lam2 - lam1) * beta T lam1) * (1 / (2 - lb)) := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hc_le (mul_nonneg (by linarith) (by linarith))
        linarith
      have hlip_lo_single : ∀ T : InfTree23,
          (1 - (1 / (2 - lb)) * (lb - la)) * beta T lam1 ≤ beta T lam2 := by
        intro T
        have sT := (lemma_4_1_support T hlam1_0 hlam1_2).1
        have hm : (lam2 - lam1) * (1 / (2 - lb)) * beta T lam1 ≤ (lb - la) * (1 / (2 - lb)) * beta T lam1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [hlam1.1, hlam2.2]) (by positivity)) (by linarith)
        linarith [hlip_single T]
      have hR1_lt3 : R1 < 3 := by unfold R1; linarith
      have h61 := lemma_6_1_nu3
        (s := beta T1 lam1 + beta T2 lam1 + beta T3 lam1)
        (s' := beta T1 lam2 + beta T2 lam2 + beta T3 lam2)
        hla1 hlb2 hlam1.1 hlt hlam2.2 hR1_lt3
        (by linarith [s0_1.1])
        (by linarith [s1_1.1, s2_1.1, s3_1.1, hlam1.2])
        (lemma_4_2_mono T0 hlam1_0 (le_of_lt hlt) hlam2_2)
        (hlip_lo_single T0)
        (by linarith [hlip_single T1, hlip_single T2, hlip_single T3])
        (by linarith [hlip_lo_single T1, hlip_lo_single T2, hlip_lo_single T3])
        hkap_pos
      have hm_box := hh3_mono_big
        (t1 := beta T1 lam1 + beta T2 lam1 + beta T3 lam1)
        (t2 := beta T1 la + beta T2 la + beta T3 la)
        (by unfold ab; linarith [s0_1.1, hlam1.2])
        (lemma_4_2_mono T0 hla0 hlam1.1 hlam1_2)
        (lemma_4_1_support T0 hla0 hla2).2
        (by unfold ab; linarith [s1_1.1, s2_1.1, s3_1.1, hlam1.2])
        (by linarith [lemma_4_2_mono T1 hla0 hlam1.1 hlam1_2, lemma_4_2_mono T2 hla0 hlam1.1 hlam1_2, lemma_4_2_mono T3 hla0 hlam1.1 hlam1_2])
        (by unfold ba; linarith [(lemma_4_1_support T1 hla0 hla2).2, (lemma_4_1_support T2 hla0 hla2).2, (lemma_4_1_support T3 hla0 hla2).2])
      exact h61.trans (mul_le_mul_of_nonneg_left hm_box (by linarith))
    have hstep3 : ∀ T0 T1 T2,
        (3 - R1) * (((∫ T3, f0Func lam2 (beta T0 lam2) (beta T1 lam2 + beta T2 lam2 + beta T3 lam2) ∂mu) -
          (∫ T3, f0Func lam1 (beta T0 lam1) (beta T1 lam1 + beta T2 lam1 + beta T3 lam1) ∂mu)) / (lam2 - lam1)) ≤
        (3 - R1) * ∫ T3, h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu := by
      intro T0 T1 T2
      rw [← integral_sub (hi2_3 T0 T1 T2) (hi1_3 T0 T1 T2), ← integral_div, ← integral_const_mul, ← integral_const_mul]
      exact integral_mono ((((hi2_3 T0 T1 T2).sub (hi1_3 T0 T1 T2)).div_const _).const_mul _)
        ((hih3_3 T0 T1 T2).const_mul _) (hpt3 T0 T1 T2)
    have hstep2 : ∀ T0 T1,
        (3 - R1) * (((∫ T2, ∫ T3, f0Func lam2 (beta T0 lam2) (beta T1 lam2 + beta T2 lam2 + beta T3 lam2) ∂mu ∂mu) -
          (∫ T2, ∫ T3, f0Func lam1 (beta T0 lam1) (beta T1 lam1 + beta T2 lam1 + beta T3 lam1) ∂mu ∂mu)) / (lam2 - lam1)) ≤
        (3 - R1) * ∫ T2, ∫ T3, h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu := by
      intro T0 T1
      rw [← integral_sub (hi2_2 T0 T1) (hi1_2 T0 T1), ← integral_div, ← integral_const_mul, ← integral_const_mul]
      exact integral_mono ((((hi2_2 T0 T1).sub (hi1_2 T0 T1)).div_const _).const_mul _)
        ((hih3_2 T0 T1).const_mul _) (hstep3 T0 T1)
    have hstep1 : ∀ T0,
        (3 - R1) * (((∫ T1, ∫ T2, ∫ T3, f0Func lam2 (beta T0 lam2) (beta T1 lam2 + beta T2 lam2 + beta T3 lam2) ∂mu ∂mu ∂mu) -
          (∫ T1, ∫ T2, ∫ T3, f0Func lam1 (beta T0 lam1) (beta T1 lam1 + beta T2 lam1 + beta T3 lam1) ∂mu ∂mu ∂mu)) / (lam2 - lam1)) ≤
        (3 - R1) * ∫ T1, ∫ T2, ∫ T3, h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu := by
      intro T0
      rw [← integral_sub (hi2_1 T0) (hi1_1 T0), ← integral_div, ← integral_const_mul, ← integral_const_mul]
      exact integral_mono ((((hi2_1 T0).sub (hi1_1 T0)).div_const _).const_mul _)
        ((hih3_1 T0).const_mul _) (hstep2 T0)
    have hstep0 :
        (3 - R1) * ((E3_2 - E3_1) / (lam2 - lam1)) ≤
        (3 - R1) * ∫ T0, ∫ T1, ∫ T2, ∫ T3, h3Func la lb (beta T0 la) (beta T1 la + beta T2 la + beta T3 la) ∂mu ∂mu ∂mu ∂mu := by
      unfold E3_2 E3_1 E3Expect
      rw [← integral_sub hi2_0 hi1_0, ← integral_div, ← integral_const_mul, ← integral_const_mul]
      exact integral_mono (((hi2_0.sub hi1_0).div_const _).const_mul _)
        (hih3_0.const_mul _) hstep1
    exact hstep0.trans (mul_le_mul_of_nonneg_left hH3_bound (by linarith))
  exact ⟨hdiff2, hdiff3⟩

set_option maxHeartbeats 800000 in
/-- **Main Cell Verifier Soundness Theorem (`Proposition 6.2`)**:
    If `checkCell c = true`, then `λ ↦ R(λ) / λ` is strictly decreasing on `[lna / ld, lnb / ld]`. -/
theorem checkCell_sound {mu : Measure InfTree23} [IsGWTree23 mu] (c : CellCert)
    (hok : checkCell c = true) :
    StrictAntiOn (fun lam => RFunc mu lam / lam)
      (Set.Icc ((c.lna : ℝ) / (c.ld : ℝ)) ((c.lnb : ℝ) / (c.ld : ℝ))) := by
  set raw_e2h := rawE2h c
  set raw_e2l := rawE2l c
  set raw_e3h := rawE3h c
  set raw_e3l := rawE3l c
  set raw_h3 := rawH3 c
  set raw_h2 := rawH2 c
  set e2h : ℕ := c.M * raw_e2h
  set e2l : ℕ := c.M * raw_e2l
  set e3h : ℕ := raw_e3h
  set e3l : ℕ := raw_e3l
  set h3_up : ℕ := raw_h3
  set h2_up : ℕ := c.M * raw_h2
  set num_r2 : ℕ := if e3h ≤ e2l then e3h else 1
  set den_r2 : ℕ := if e3h ≤ e2l then e2l + e3h else 2
  have hok' : checkUpperEnv c.lna c.ld c.K c.M c.ua c.j2ua c.j3ua = true ∧
      checkLowerEnv c.lnb c.ld c.K c.M c.lb_env c.j2lb c.j3lb = true ∧
      checkCellCorners c = true ∧
      0 < e2l ∧ 0 < e3l ∧
      c.lnb * (e2h * den_r2 * h3_up + (e2h + e3l) * num_r2 * h2_up) <
        c.ld * den_r2 * (2 * e2h + 3 * e3l) * (e2l + e3l) := by
    simpa only [checkCell, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hok
  clear hok
  rcases hok' with ⟨hua, hlb, hcorn, he2l_pos, he3l_pos, hfinal_lt⟩
  obtain ⟨hlna0, hlna2, hK, hM, _⟩ := checkUpperEnv_dims hua
  obtain ⟨hlnb0, hlnb2, _, _, _⟩ := checkLowerEnv_dims hlb
  obtain ⟨hla1, hlalb, hlb2, _, _, _, _, _, _, _, _, _⟩ := corner_identities c hlnb2 hcorn
  obtain ⟨hE2_bounds, hE3_bounds⟩ := cell_E2_E3_bounds (mu := mu) c hua hlb hcorn
  obtain ⟨hH3_bound, hH2_bound⟩ := cell_H3_H2_bounds (mu := mu) c hua hlb hcorn
  set la : ℝ := (c.lna : ℝ) / c.ld
  set lb : ℝ := (c.lnb : ℝ) / c.ld
  have hM_pos : (0 : ℝ) < c.M := Nat.cast_pos.mpr hM
  have hS_pos : 0 < cellScale := by decide
  set Q : ℝ := (cellScale : ℝ) * (c.M : ℝ) ^ 4
  have hQ_pos : 0 < Q := by unfold Q; positivity
  have hQ_ne : Q ≠ 0 := ne_of_gt hQ_pos
  intro lam1 hlam1 lam2 hlam2 hlt
  have hlam1_0 : 0 < lam1 := by linarith [hlam1.1]
  have hlam1_2 : lam1 < 2 := by linarith [hlam1.2]
  have hlam2_0 : 0 < lam2 := by linarith [hlam2.1]
  have hlam2_2 : lam2 < 2 := by linarith [hlam2.2]
  set E2_1 := E2Expect mu lam1
  set E3_1 := E3Expect mu lam1
  set E2_2 := E2Expect mu lam2
  set E3_2 := E3Expect mu lam2
  set N1 := 2 * E2_1 + 3 * E3_1
  set M1 := E2_1 + E3_1
  set N2 := 2 * E2_2 + 3 * E3_2
  set M2 := E2_2 + E3_2
  set R1 := RFunc mu lam1
  have hM1_pos : 0 < M1 := add_pos (E2Expect_pos hlam1_0 hlam1_2) (E3Expect_pos hlam1_0 hlam1_2)
  have hM2_pos : 0 < M2 := add_pos (E2Expect_pos hlam2_0 hlam2_2) (E3Expect_pos hlam2_0 hlam2_2)
  obtain ⟨hR1_gt2, hR1_le25⟩ := RFunc_bounds (mu := mu) hlam1_0 hlam1_2
  dsimp only []
  rw [show RFunc mu lam2 = N2 / M2 from rfl, show RFunc mu lam1 = N1 / M1 from rfl]
  have hdq : (N2 / M2) / lam2 < (N1 / M1) / lam1 ↔
      ((N2 - N1) - R1 * (M2 - M1)) / (lam2 - lam1) < (R1 / lam1) * M2 :=
    lemma_3_2_diff_quotient hlam1_0 hlt hM1_pos hM2_pos
  rw [hdq]
  have hdecomp : ((N2 - N1) - R1 * (M2 - M1)) / (lam2 - lam1) =
      (2 - R1) * ((E2_2 - E2_1) / (lam2 - lam1)) + (3 - R1) * ((E3_2 - E3_1) / (lam2 - lam1)) := by
    unfold N1 N2 M1 M2; ring
  rw [hdecomp]
  obtain ⟨hdiff2, hdiff3⟩ := cell_diff_bounds (mu := mu) c hlnb2 hcorn hH3_bound hH2_bound hlam1 hlam2 hlt

  -- Combine integer expectation bounds (`hfinal_lt`) to close the strict inequality!
  obtain ⟨he2_1_lo, he2_1_hi⟩ := hE2_bounds lam1 hlam1
  obtain ⟨he3_1_lo, he3_1_hi⟩ := hE3_bounds lam1 hlam1
  obtain ⟨he2_2_lo, _⟩ := hE2_bounds lam2 hlam2
  obtain ⟨he3_2_lo, _⟩ := hE3_bounds lam2 hlam2
  have hden_r2_pos : 0 < den_r2 := by unfold den_r2; split_ifs <;> omega
  have hden_r2_cast : (0 : ℝ) < den_r2 := Nat.cast_pos.mpr hden_r2_pos
  have he2h_e3l_pos : (0 : ℝ) < (e2h : ℝ) + (e3l : ℝ) := by
    have : 0 < e3l := he3l_pos
    positivity
  have hR1_ident : R1 = 2 + E3_1 / (E2_1 + E3_1) := by
    have hd : E2Expect mu lam1 + E3Expect mu lam1 ≠ 0 := ne_of_gt hM1_pos
    unfold R1 RFunc E2_1 E3_1
    field_simp [hd]; ring
  have hR1_lo : ((2 * e2h + 3 * e3l : ℕ) : ℝ) / ((e2h : ℝ) + (e3l : ℝ)) ≤ R1 := by
    rw [hR1_ident]
    have h1 : ((2 * e2h + 3 * e3l : ℕ) : ℝ) / ((e2h : ℝ) + (e3l : ℝ)) =
        2 + (e3l : ℝ) / ((e2h : ℝ) + (e3l : ℝ)) := by
      push_cast; field_simp [ne_of_gt he2h_e3l_pos]; ring
    rw [h1]
    have hdiv : (e3l : ℝ) / ((e2h : ℝ) + (e3l : ℝ)) ≤ E3_1 / (E2_1 + E3_1) := by
      rw [div_le_div_iff₀ he2h_e3l_pos hM1_pos]
      have a1 : (e3l : ℝ) ≤ Q * E3_1 := by
        have hm := mul_le_mul_of_nonneg_left he3_1_lo (le_of_lt hQ_pos)
        rwa [mul_div_cancel₀ _ hQ_ne] at hm
      have a2 : Q * E2_1 ≤ (e2h : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left he2_1_hi (le_of_lt hQ_pos)
        rwa [mul_div_cancel₀ _ hQ_ne] at hm
      have hmul : (e3l : ℝ) * (Q * (E2_1 + E3_1)) ≤ (Q * E3_1) * ((e2h : ℝ) + (e3l : ℝ)) := by
        nlinarith [E2Expect_pos (mu := mu) hlam1_0 hlam1_2, E3Expect_pos (mu := mu) hlam1_0 hlam1_2]
      have hmul' : Q * ((e3l : ℝ) * (E2_1 + E3_1)) ≤ Q * (E3_1 * ((e2h : ℝ) + (e3l : ℝ))) := by
        linarith
      exact le_of_mul_le_mul_left hmul' hQ_pos
    linarith
  have h3_minus_R1 : 3 - R1 ≤ (e2h : ℝ) / ((e2h : ℝ) + (e3l : ℝ)) := by
    have hsum1 : ((2 * e2h + 3 * e3l : ℕ) : ℝ) / ((e2h : ℝ) + (e3l : ℝ)) +
        (e2h : ℝ) / ((e2h : ℝ) + (e3l : ℝ)) = 3 := by
      push_cast; field_simp [ne_of_gt he2h_e3l_pos]; ring
    linarith
  have hR1_minus_2 : R1 - 2 ≤ (num_r2 : ℝ) / (den_r2 : ℝ) := by
    unfold num_r2 den_r2
    split_ifs with hcap
    · rw [hR1_ident]
      have hpos_le : (0 : ℝ) < (e2l : ℝ) + (e3h : ℝ) := by
        have : 0 < e2l := he2l_pos; positivity
      push_cast
      rw [add_sub_cancel_left, div_le_div_iff₀ hM1_pos hpos_le]
      have a1 : Q * E3_1 ≤ (e3h : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left he3_1_hi (le_of_lt hQ_pos)
        rwa [mul_div_cancel₀ _ hQ_ne] at hm
      have a2 : (e2l : ℝ) ≤ Q * E2_1 := by
        have hm := mul_le_mul_of_nonneg_left he2_1_lo (le_of_lt hQ_pos)
        rwa [mul_div_cancel₀ _ hQ_ne] at hm
      have hmul : Q * (E3_1 * ((e2l : ℝ) + (e3h : ℝ))) ≤ Q * ((e3h : ℝ) * (E2_1 + E3_1)) := by
        nlinarith [E2Expect_pos (mu := mu) hlam1_0 hlam1_2, E3Expect_pos (mu := mu) hlam1_0 hlam1_2]
      exact le_of_mul_le_mul_left hmul hQ_pos
    · push_cast; linarith
  have hM2_lo : ((e2l : ℝ) + (e3l : ℝ)) / Q ≤ M2 := by
    unfold M2; rw [add_div]; linarith
  have hlam1_le_lb : lam1 ≤ lb := hlt.le.trans hlam2.2
  have hinv_lam : (c.ld : ℝ) / (c.lnb : ℝ) ≤ 1 / lam1 := by
    have h1 : 1 / lb ≤ 1 / lam1 := one_div_le_one_div_of_le hlam1_0 hlam1_le_lb
    have hlnb_ne : (c.lnb : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hlnb0)
    have h2 : (c.ld : ℝ) / (c.lnb : ℝ) = 1 / lb := by unfold lb; field_simp [hlnb_ne]
    rwa [h2]

  have hlhs_chain : (2 - R1) * ((E2_2 - E2_1) / (lam2 - lam1)) + (3 - R1) * ((E3_2 - E3_1) / (lam2 - lam1)) ≤
      ((e2h : ℝ) / ((e2h : ℝ) + (e3l : ℝ))) * ((h3_up : ℝ) / Q) +
        ((num_r2 : ℝ) / (den_r2 : ℝ)) * ((h2_up : ℝ) / Q) := by
    have t3 : (3 - R1) * ((h3_up : ℝ) / Q) ≤ ((e2h : ℝ) / ((e2h : ℝ) + (e3l : ℝ))) * ((h3_up : ℝ) / Q) :=
      mul_le_mul_of_nonneg_right h3_minus_R1 (by positivity)
    have t2 : (R1 - 2) * ((h2_up : ℝ) / Q) ≤ ((num_r2 : ℝ) / (den_r2 : ℝ)) * ((h2_up : ℝ) / Q) :=
      mul_le_mul_of_nonneg_right hR1_minus_2 (by positivity)
    linarith
  have hrhs_chain : (((2 * e2h + 3 * e3l : ℕ) : ℝ) / ((e2h : ℝ) + (e3l : ℝ))) *
      ((c.ld : ℝ) / (c.lnb : ℝ)) * (((e2l : ℝ) + (e3l : ℝ)) / Q) ≤ (R1 / lam1) * M2 := by
    have hR_div : (((2 * e2h + 3 * e3l : ℕ) : ℝ) / ((e2h : ℝ) + (e3l : ℝ))) * ((c.ld : ℝ) / (c.lnb : ℝ)) ≤
        R1 * (1 / lam1) :=
      mul_le_mul hR1_lo hinv_lam (by positivity) (by linarith)
    rw [div_eq_mul_one_div R1 lam1]
    exact mul_le_mul hR_div hM2_lo (by positivity) (by positivity)
  have hmid_lt : ((e2h : ℝ) / ((e2h : ℝ) + (e3l : ℝ))) * ((h3_up : ℝ) / Q) +
      ((num_r2 : ℝ) / (den_r2 : ℝ)) * ((h2_up : ℝ) / Q) <
      (((2 * e2h + 3 * e3l : ℕ) : ℝ) / ((e2h : ℝ) + (e3l : ℝ))) *
        ((c.ld : ℝ) / (c.lnb : ℝ)) * (((e2l : ℝ) + (e3l : ℝ)) / Q) := by
    have hlnb_pos : (0 : ℝ) < c.lnb := Nat.cast_pos.mpr hlnb0
    have hbig_pos : 0 < Q * ((e2h : ℝ) + (e3l : ℝ)) * (den_r2 : ℝ) * (c.lnb : ℝ) := by positivity
    have hnat_cast : (((c.lnb * (e2h * den_r2 * h3_up + (e2h + e3l) * num_r2 * h2_up) : ℕ) : ℝ)) <
        (((c.ld * den_r2 * (2 * e2h + 3 * e3l) * (e2l + e3l) : ℕ) : ℝ)) :=
      Nat.cast_lt.mpr hfinal_lt
    have hlhs_id : (((e2h : ℝ) / ((e2h : ℝ) + (e3l : ℝ))) * ((h3_up : ℝ) / Q) +
        ((num_r2 : ℝ) / (den_r2 : ℝ)) * ((h2_up : ℝ) / Q)) *
          (Q * ((e2h : ℝ) + (e3l : ℝ)) * (den_r2 : ℝ) * (c.lnb : ℝ)) =
        (((c.lnb * (e2h * den_r2 * h3_up + (e2h + e3l) * num_r2 * h2_up) : ℕ) : ℝ)) := by
      push_cast
      field_simp [hQ_ne, ne_of_gt he2h_e3l_pos, ne_of_gt hden_r2_cast, ne_of_gt hlnb_pos]
    have hrhs_id : ((((2 * e2h + 3 * e3l : ℕ) : ℝ) / ((e2h : ℝ) + (e3l : ℝ))) *
        ((c.ld : ℝ) / (c.lnb : ℝ)) * (((e2l : ℝ) + (e3l : ℝ)) / Q)) *
          (Q * ((e2h : ℝ) + (e3l : ℝ)) * (den_r2 : ℝ) * (c.lnb : ℝ)) =
        (((c.ld * den_r2 * (2 * e2h + 3 * e3l) * (e2l + e3l) : ℕ) : ℝ)) := by
      push_cast
      field_simp [hQ_ne, ne_of_gt he2h_e3l_pos, ne_of_gt hlnb_pos]
    by_contra hge
    have hm := mul_le_mul_of_nonneg_right (not_lt.mp hge) (le_of_lt hbig_pos)
    linarith
  exact lt_of_le_of_lt hlhs_chain (lt_of_lt_of_le hmid_lt hrhs_chain)

end GWSpeedCertificate
