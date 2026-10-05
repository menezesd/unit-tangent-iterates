module

public import UnitTangentIterates.PulseAux

/-!
# Lemma 3.5, step 1: the rear hairpin in arclength

For a profile `f` with `m ≤ f ≤ M` on `(0, π)`, the hairpin with radius of curvature
`f(θ)/sin θ` has an arclength parametrization: its tangent angle `ψ(x) ∈ (0, π)` solves
`ψ' = sin ψ / f(ψ)` (so its curvature is `K = sin ψ / f(ψ)`), with inverse `U(θ)` satisfying
`U' = f / sin`.  In the variable `v = log tan (ψ/2)` one has `dv/dx = 1/f ∈ [1/M, 1/m]`, which
gives the exponential decay `sin ψ(x) ≤ 2 e^{-|x|/M}` and the shift comparison
`sin ψ(x + h) ≤ e^{|h|/m} sin ψ(x)` (equation (3.9) of the paper).
-/

@[expose] public section

namespace Ovals

open Real Set Filter Topology

theorem continuous_angleMap : Continuous angleMap :=
  continuous_iff_continuousAt.2 fun v => (hasDerivAt_angleMap v).continuousAt

/-- Two-sided Lipschitz bounds for a function with derivative in `[m, M]`. -/
theorem sub_bounds_of_deriv_mem {F F' : ℝ → ℝ} {m M : ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (hm : ∀ x, m ≤ F' x) (hM : ∀ x, F' x ≤ M) {a b : ℝ} (hab : a ≤ b) :
    m * (b - a) ≤ F b - F a ∧ F b - F a ≤ M * (b - a) := by
  have h1 : Monotone (fun t => F t - m * t) :=
    monotone_of_hasDerivAt_nonneg (f' := fun t => F' t - m)
      (fun t => (hF t).sub ((hasDerivAt_id t).const_mul m |>.congr_deriv (by simp)))
      (fun t => by show 0 ≤ F' t - m; linarith [hm t])
  have h2 : Monotone (fun t => M * t - F t) :=
    monotone_of_hasDerivAt_nonneg (f' := fun t => M - F' t)
      (fun t => (((hasDerivAt_id t).const_mul M).congr_deriv (by simp)).sub (hF t))
      (fun t => by show 0 ≤ M - F' t; linarith [hM t])
  have e1 := h1 hab
  have e2 := h2 hab
  simp only at e1 e2
  constructor <;> nlinarith

/-- **The rear hairpin in arclength.** -/
theorem exists_rear_angle {f : ℝ → ℝ} {m M : ℝ} (hm : 0 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfM : ∀ θ ∈ Ioo 0 π, f θ ≤ M) (hfc : ContinuousOn f (Ioo 0 π)) :
    ∃ ψ U : ℝ → ℝ, (∀ x, ψ x ∈ Ioo 0 π) ∧
      (∀ x, HasDerivAt ψ (Real.sin (ψ x) / f (ψ x)) x) ∧
      (∀ θ ∈ Ioo 0 π, ψ (U θ) = θ) ∧
      (∀ θ ∈ Ioo 0 π, HasDerivAt U (f θ / Real.sin θ) θ) ∧
      (∀ x h, Real.sin (ψ (x + h)) ≤ Real.exp (|h| / m) * Real.sin (ψ x)) ∧
      (∀ x, Real.sin (ψ x) ≤ 2 * Real.exp (-(|x| / M))) ∧
      Tendsto ψ atBot (𝓝 0) ∧ Tendsto ψ atTop (𝓝 π) := by
  set F : ℝ → ℝ := fun v => f (angleMap v) with hFdef
  have hFc : Continuous F := hfc.comp_continuous continuous_angleMap angleMap_mem
  have hFm : ∀ v, m ≤ F v := fun v => hf _ (angleMap_mem v)
  have hFM : ∀ v, F v ≤ M := fun v => hfM _ (angleMap_mem v)
  set arcU : ℝ → ℝ := fun v => ∫ t in (0 : ℝ)..v, F t with harcU
  have hU : ∀ v, HasDerivAt arcU (F v) v := fun v =>
    (hFc.integral_hasStrictDerivAt 0 v).hasDerivAt
  have hU0 : arcU 0 = 0 := by simp [harcU]
  obtain ⟨V, hUV, hVU, hVd⟩ := exists_inverse_of_deriv_ge hm hU hFm
  have hbd := fun {a b : ℝ} (hab : a ≤ b) => sub_bounds_of_deriv_mem hU hFm hFM hab
  have hMpos : 0 < M := hm.trans_le ((hFm 0).trans (hFM 0))
  -- `V` is `1/m`-Lipschitz and `|V x| ≥ |x| / M`
  have hVlip : ∀ x x', |V x' - V x| ≤ |x' - x| / m := by
    intro x x'
    rw [le_div_iff₀ hm]
    rcases le_total (V x) (V x') with h | h
    · have := (hbd h).1
      rw [hUV, hUV] at this
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]; linarith
    · have := (hbd h).1
      rw [hUV, hUV] at this
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by nlinarith)]; linarith
  have hVlow : ∀ x, |x| ≤ M * |V x| := by
    intro x
    rcases le_total 0 (V x) with h | h
    · obtain ⟨h1, h2⟩ := hbd h
      rw [hUV, hU0] at h1 h2
      rw [abs_of_nonneg h, abs_of_nonneg (by nlinarith)]; linarith
    · obtain ⟨h1, h2⟩ := hbd h
      rw [hUV, hU0] at h1 h2
      rw [abs_of_nonpos h, abs_of_nonpos (by nlinarith)]; linarith
  have hVmono : StrictMono V := strictMono_of_hasDerivAt_pos hVd fun x =>
    inv_pos.2 (hm.trans_le (hFm _))
  have hV0 : V 0 = 0 := by have := hVU 0; rwa [hU0] at this
  refine ⟨fun x => angleMap (V x), fun θ => arcU (angleMapInv θ), fun x => angleMap_mem _,
    fun x => ?_, fun θ hθ => ?_, fun θ hθ => ?_, fun x h => ?_, fun x => ?_, ?_, ?_⟩
  · have h := (hasDerivAt_angleMap (V x)).comp x (hVd x)
    convert h using 1
  · simp only [hVU, angleMap_angleMapInv hθ]
  · have h := (hU (angleMapInv θ)).comp θ (hasDerivAt_angleMapInv hθ)
    convert h using 1
    simp only [hFdef, angleMap_angleMapInv hθ]; ring
  · simp only [sin_angleMap]
    have hc := cosh_le_exp_mul_cosh (V x) (V (x + h) - V x)
    rw [add_sub_cancel] at hc
    have hw : Real.exp |V (x + h) - V x| ≤ Real.exp (|h| / m) := by
      apply Real.exp_le_exp.2
      have := hVlip x (x + h)
      rwa [add_sub_cancel_left] at this
    have h1 := Real.cosh_pos (V x)
    have h2 := Real.cosh_pos (V (x + h))
    rw [div_le_iff₀ h2, mul_one_div, div_mul_eq_mul_div, le_div_iff₀ h1]
    nlinarith [Real.exp_pos |V (x + h) - V x|]
  · simp only [sin_angleMap]
    refine (inv_cosh_le _).trans ?_
    gcongr
    rw [div_le_iff₀ hMpos]; linarith [hVlow x]
  · have hVbot : Tendsto V atBot atBot := by
      refine tendsto_atBot_mono' atBot ?_ (tendsto_id.atBot_div_const hMpos)
      filter_upwards [eventually_le_atBot 0] with x hx
      have h0 : V x ≤ 0 := hV0 ▸ hVmono.monotone hx
      have := hVlow x
      rw [abs_of_nonpos hx, abs_of_nonpos h0] at this
      simp only [id]; rw [le_div_iff₀ hMpos]; linarith
    have hT : Tendsto angleMap atBot (𝓝 0) := by
      have h := ((Real.continuous_arctan.tendsto 0).comp Real.tendsto_exp_atBot).const_mul 2
      simpa [angleMap, Function.comp_def] using h
    exact hT.comp hVbot
  · have hVtop : Tendsto V atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const hMpos)
      filter_upwards [eventually_ge_atTop 0] with x hx
      have h0 : 0 ≤ V x := hV0 ▸ hVmono.monotone hx
      have := hVlow x
      rw [abs_of_nonneg hx, abs_of_nonneg h0] at this
      simp only [id]; rw [div_le_iff₀ hMpos]; linarith
    have hT : Tendsto angleMap atTop (𝓝 π) := by
      have h := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
        Real.tendsto_exp_atTop).const_mul 2
      convert h using 2
      ring
    exact hT.comp hVtop

end Ovals

end
