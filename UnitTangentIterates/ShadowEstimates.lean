module

public import UnitTangentIterates.ShadowPath

/-!
# Estimates along paths of rears (Lemma 6.2, and the curvature and perimeter control)

For a valid path `P` with curvature at most `κ ∈ (0, 1)` we prove, at every time:

* `Ovals.PathData.Valid.rear_bounds`: if `∫ g |η| ≤ w`, `|η| ≤ s₀` and `|∂ₛη| ≤ s₁` along `P`,
  then along the rear path `∫ g_R |η_R| ≤ w`, `|η_R| ≤ C₀ w` and
  `|∂ₓη_R| ≤ s₀ / cos A + C₀ w` (estimates (6.5)–(6.7) of the paper, with `A = arcsin κ`);
* `Ovals.PathData.Valid.rear_δ_growth`: the steering angle `δ`, hence the rear curvature
  `tan δ`, grows at most at rate `sup (|η_R| + |η| + |∂ₛη|)`.  At a maximum of `δ(t, ·)` one has
  `∂ₜδ = η_R - η cos δ + ∂ₛη`, so no second derivatives are needed;
* `Ovals.PathData.Valid.perimeter_change`: the half-perimeter `∫ g` changes at rate at most
  `κ ∫ g |η|` (first variation of length).
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

namespace PathData

variable {P : PathData} {κ m : ℝ}

/-- Uniform bounds on the normal velocity of a path. -/
def Bounded (P : PathData) (w s₀ s₁ : ℝ) : Prop :=
  (∀ t, ∫ u in (0 : ℝ)..P.p, P.g t u * |P.η t u| ≤ w) ∧ (∀ t u, |P.η t u| ≤ s₀) ∧
    ∀ t u, |deriv (P.η t) u / P.g t u| ≤ s₁

/-- The constant `C₀ = (1 - e^{-π / tan A})⁻¹` of the `L¹ → L^∞` bound, `A = arcsin κ`. -/
noncomputable def C₀ (κ : ℝ) : ℝ := (1 - Real.exp (-(π / Real.tan (Real.arcsin κ))))⁻¹

lemma tan_arcsin_pos {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) : 0 < Real.tan (Real.arcsin κ) :=
  Real.tan_pos_of_pos_of_lt_pi_div_two (Real.arcsin_pos.2 hκ0) (arcsin_lt_pi_div_two hκ1)

lemma one_sub_exp_pos {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    0 < 1 - Real.exp (-(π / Real.tan (Real.arcsin κ))) := by
  have := tan_arcsin_pos hκ0 hκ1
  have : Real.exp (-(π / Real.tan (Real.arcsin κ))) < 1 :=
    (Real.exp_lt_exp.2 (neg_lt_zero.2 (by positivity))).trans_eq Real.exp_zero
  linarith

lemma C₀_pos {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) : 0 < C₀ κ :=
  inv_pos.2 (one_sub_exp_pos hκ0 hκ1)

lemma Valid.rear_turn (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t : ℝ) :
    ∫ u in (0 : ℝ)..P.p, P.g t u * Real.sin (P.δ t u) = π := by
  have hδs := hP.δ_spec hκ0 hκ1 t
  have hδc := hP.δ_cont hκ0 hκ1 t
  have e : (fun u => P.g t u * Real.sin (P.δ t u)) =
      fun u => P.a t u - (P.a t u - P.g t u * Real.sin (P.δ t u)) := by
    funext u; ring
  have hi : IntervalIntegrable (fun u => P.a t u - P.g t u * Real.sin (P.δ t u))
      MeasureTheory.volume 0 P.p := ((hP.a_cont t).sub ((hP.g_cont t).mul
      (Real.continuous_sin.comp hδc))).intervalIntegrable _ _
  rw [e, intervalIntegral.integral_sub ((hP.a_cont t).intervalIntegrable _ _) hi, hP.turn t,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hδs.2.1 u) hi,
    show P.δ t P.p = P.δ t 0 from by simpa using hδs.1 0, sub_self, sub_zero]

/-- The rear half-perimeter is at least `π / tan A`. -/
lemma Valid.rear_perimeter_ge (hP : P.Valid κ m) (hκ0 : 0 < κ) (hκ1 : κ < 1) (t : ℝ) :
    π / Real.tan (Real.arcsin κ) ≤ ∫ u in (0 : ℝ)..P.p, P.g t u * Real.cos (P.δ t u) := by
  have htan := tan_arcsin_pos hκ0 hκ1
  have hδs := hP.δ_spec hκ0.le hκ1 t
  have hδc := hP.δ_cont hκ0.le hκ1 t
  rw [div_le_iff₀ htan, ← hP.rear_turn hκ0.le hκ1 t, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_mono_on hP.p_pos.le
    (((hP.g_cont t).mul (Real.continuous_sin.comp hδc)).intervalIntegrable _ _)
    ((((hP.g_cont t).mul (Real.continuous_cos.comp hδc)).mul continuous_const).intervalIntegrable
      _ _) fun u _ => ?_
  have hb := hδs.2.2 u
  have hc := hP.cos_δ_pos hκ0.le hκ1 t u
  have htle : Real.tan (P.δ t u) ≤ Real.tan (Real.arcsin κ) :=
    Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [hb.1, Real.pi_pos], hb.2.trans_lt (arcsin_lt_pi_div_two hκ1)⟩
      ⟨by linarith [Real.arcsin_nonneg.2 hκ0.le, Real.pi_pos], arcsin_lt_pi_div_two hκ1⟩ hb.2
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hc] at htle
  have := mul_le_mul_of_nonneg_left htle (hP.g_pos t u).le
  linarith

/-- **Estimates (6.5)–(6.7) at every time.** -/
theorem Valid.rear_bounds (hP : P.Valid κ m) (hκ0 : 0 < κ) (hκ1 : κ < 1) {w s₀ s₁ : ℝ}
    (hB : P.Bounded w s₀ s₁) :
    P.rear.Bounded w (C₀ κ * w) (s₀ / Real.cos (Real.arcsin κ) + C₀ κ * w) := by
  obtain ⟨hw, hs₀, hs₁⟩ := hB
  have hA := arcsin_lt_pi_div_two hκ1
  have hδs := hP.δ_spec hκ0.le hκ1
  have hδc := hP.δ_cont hκ0.le hκ1
  have hJ := hP.rear_η_hasDerivAt hκ0.le hκ1
  have hηRp : ∀ t, Function.Periodic (P.rear.η t) P.p := fun t u => by
    simp only [PathData.rear, hP.ξ_per t u, hP.η_per t u, hP.ω_per t u, (hδs t).1 u,
      ((hP.D_spec hκ0.le hκ1 t).1) u]
  have hsup : ∀ t u, |P.rear.η t u| ≤ C₀ κ * w := fun t u => by
    have h1 := jacobi_sup_le hP.p_pos (hP.η_diff t).continuous (hP.g_cont t) (hδc t)
      (hP.η_per t) (hP.g_per t) (hδs t).1 (hP.g_pos t) (hδs t).2.2 hA (hJ t) (hηRp t) u
    have h2 := hP.rear_perimeter_ge hκ0 hκ1 t
    have h3 : Real.exp (-∫ v in (0 : ℝ)..P.p, P.g t v * Real.cos (P.δ t v)) ≤
        Real.exp (-(π / Real.tan (Real.arcsin κ))) := Real.exp_le_exp.2 (by linarith)
    have hpos := one_sub_exp_pos hκ0 hκ1
    rw [C₀, ← div_eq_inv_mul, le_div_iff₀ hpos]
    nlinarith [abs_nonneg (P.rear.η t u), hw t]
  refine ⟨fun t => ?_, hsup, fun t u => ?_⟩
  · exact (jacobi_L1_le hP.p_pos (hP.η_diff t).continuous (hP.g_cont t) (hδc t) (hP.g_pos t)
      (hδs t).2.2 hA (hJ t) (hηRp t)).trans (hw t)
  · rw [(hJ t u).deriv]
    have h1 := jacobi_deriv_bound (η := P.η t) (ηR := P.rear.η t) (hP.g_pos t) (hδs t).2.2 hA u
    have hcA : 0 < Real.cos (Real.arcsin κ) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.arcsin_nonneg.2 hκ0.le, Real.pi_pos], hA⟩
    calc _ ≤ |P.η t u| / Real.cos (Real.arcsin κ) + |P.rear.η t u| := h1
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_right (hs₀ t u) hcA.le) (hsup t u)

/-- At a critical point of the steering angle, `∂ₜδ = η_R - η cos δ + ∂ₛη`. -/
lemma Valid.D_eq_of_crit (hP : P.Valid κ m) {t u : ℝ}
    (hcrit : P.a t u = P.g t u * Real.sin (P.δ t u)) :
    P.D t u = P.rear.η t u - P.η t u * Real.cos (P.δ t u) + deriv (P.η t) u / P.g t u := by
  have hg := hP.g_pos t u
  have hr := hP.rot t u
  simp only [PathData.rear]
  field_simp
  rw [hcrit] at hr
  linear_combination hr

/-- **Growth of the steering angle along a path.** -/
theorem Valid.rear_δ_growth (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {c : ℝ}
    (hc : ∀ t u, |P.rear.η t u| + |P.η t u| + |deriv (P.η t) u / P.g t u| ≤ c)
    {t₀ t₁ B : ℝ} (h01 : t₀ ≤ t₁) (hB : ∀ v, P.δ t₀ v ≤ B) (u : ℝ) :
    P.δ t₁ u ≤ B + c * (t₁ - t₀) := by
  refine max_growth hP.p_pos (hP.δ_cont hκ0 hκ1) (fun t => (hP.δ_spec hκ0 hκ1 t).1)
    (hP.D_cont hκ0 hκ1) (fun t => (hP.D_spec hκ0 hκ1 t).1) (hP.δ_udiff hκ0 hκ1)
    (fun t v hv => ?_) h01 hB u
  have hd := (hP.δ_spec hκ0 hκ1 t).2.1 v
  have h0 : P.a t v - P.g t v * Real.sin (P.δ t v) = 0 :=
    IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hv) hd
  rw [hP.D_eq_of_crit (by linarith)]
  have h1 := hc t v
  have h2 : -(P.η t v * Real.cos (P.δ t v)) ≤ |P.η t v| := by
    have h3 : |P.η t v * Real.cos (P.δ t v)| ≤ |P.η t v| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    linarith [neg_le_abs (P.η t v * Real.cos (P.δ t v))]
  linarith [le_abs_self (P.rear.η t v), le_abs_self (deriv (P.η t) v / P.g t v)]

/-- **First variation of the half-perimeter.** -/
theorem Valid.perimeter_change (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) {w : ℝ}
    (hw : ∀ t, ∫ u in (0 : ℝ)..P.p, P.g t u * |P.η t u| ≤ w) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) :
    |(∫ u in (0 : ℝ)..P.p, P.g t₁ u) - ∫ u in (0 : ℝ)..P.p, P.g t₀ u| ≤ κ * w * (t₁ - t₀) := by
  have hderiv : ∀ t, HasDerivAt (fun t => ∫ u in (0 : ℝ)..P.p, P.g t u)
      (∫ u in (0 : ℝ)..P.p, P.gd t u) t := fun t =>
    (hP.g_udiff t).hasDerivAt_integral hP.g_cont (hP.gd_cont t) hP.p_pos.le
  have hbound : ∀ t, ‖∫ u in (0 : ℝ)..P.p, P.gd t u‖ ≤ κ * w := fun t => by
    have hξd : ∀ u, HasDerivAt (P.ξ t) (P.gd t u + P.η t u * P.a t u) u := fun u => by
      have := (hP.ξ_diff t u).hasDerivAt
      rwa [show deriv (P.ξ t) u = P.gd t u + P.η t u * P.a t u by rw [hP.stretch]; ring] at this
    have hηa : Continuous fun u => P.η t u * P.a t u := (hP.η_diff t).continuous.mul (hP.a_cont t)
    have e : ∫ u in (0 : ℝ)..P.p, P.gd t u = -∫ u in (0 : ℝ)..P.p, P.η t u * P.a t u := by
      have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hξd u)
        (((hP.gd_cont t).add hηa).intervalIntegrable 0 P.p)
      rw [intervalIntegral.integral_add ((hP.gd_cont t).intervalIntegrable _ _)
        (hηa.intervalIntegrable _ _), show P.ξ t P.p = P.ξ t 0 by simpa using hP.ξ_per t 0,
        sub_self] at h1
      linarith
    rw [e, norm_neg, Real.norm_eq_abs]
    refine (intervalIntegral.abs_integral_le_integral_abs hP.p_pos.le).trans ?_
    calc ∫ u in (0 : ℝ)..P.p, |P.η t u * P.a t u|
        ≤ ∫ u in (0 : ℝ)..P.p, κ * (P.g t u * |P.η t u|) := by
          refine intervalIntegral.integral_mono_on hP.p_pos.le (hηa.abs.intervalIntegrable _ _)
            ((continuous_const.mul ((hP.g_cont t).mul
              (hP.η_diff t).continuous.abs)).intervalIntegrable _ _) fun u _ => ?_
          rw [abs_mul, abs_of_nonneg (hP.a_nonneg t u)]
          have := hP.a_le t u
          have := abs_nonneg (P.η t u)
          nlinarith
      _ = κ * ∫ u in (0 : ℝ)..P.p, P.g t u * |P.η t u| := intervalIntegral.integral_const_mul _ _
      _ ≤ κ * w := mul_le_mul_of_nonneg_left (hw t) hκ0
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => ∫ u in (0 : ℝ)..P.p, P.g t u)
    (fun t _ => (hderiv t).hasDerivWithinAt) (fun t _ => hbound t) t₁ ⟨h01, le_rfl⟩
  simpa [Real.norm_eq_abs] using this

end PathData

end Ovals

end
