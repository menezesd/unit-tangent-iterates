module

public import UnitTangentIterates.SelectedRear
public import UnitTangentIterates.Reparam
public import UnitTangentIterates.ShadowRep

/-!
# The selected rear as a curve in its own arclength

Let `F` be the centered curve with arclength curvature `K` (half-period `L'`), `δ` a periodic
steering angle for `K`, and `k` a curvature function with `k(∫₀ˢ cos δ) = tan δ(s)`.  Then the
rear `F - τ(Θ - δ)` is exactly the centered curve with curvature `k`, read at rear arclength
`x(s) = ∫₀ˢ cos δ` (`Ovals.rearCurve_eq_curveOfCurvature`).  Consequently
`𝒯 (X_R ∘ x) = F`, and the rear is no wider than the front in any direction
(`Ovals.width_rear_le`).  Rotations do not affect widths (`Ovals.width_rotate`).
-/

@[expose] public section

namespace Ovals

open Real Complex

/-- Rotating the initial angle rotates the curve. -/
lemma curveOfCurvature_rotate (θ : ℝ) (κ : ℝ → ℝ) (L s : ℝ) :
    curveOfCurvature θ κ L s = tau θ * curveOfCurvature 0 κ L s := by
  have e : ∀ r, tau (angleOfCurvature θ κ r) = tau θ * tau (angleOfCurvature 0 κ r) :=
    fun r => by rw [← tau_add]; congr 1; unfold angleOfCurvature; ring
  simp only [curveOfCurvature, e, intervalIntegral.integral_const_mul]
  ring

lemma coord_tau_mul (θ : ℝ) (v z : ℂ) : coord v (tau θ * z) = coord (tau (-θ) * v) z := by
  have h : (starRingEnd ℂ) (tau (-θ)) = tau θ := by
    unfold tau; rw [← Complex.exp_conj]; congr 1; simp
  simp only [coord, map_mul, h]
  ring_nf

lemma norm_tau_mul {θ : ℝ} {v : ℂ} (hv : ‖v‖ = 1) : ‖tau θ * v‖ = 1 := by
  rw [norm_mul, norm_tau, hv, one_mul]

/-- **Widths are rotation invariant.** -/
lemma width_rotate {θ θ' W : ℝ} {κ : ℝ → ℝ} {L : ℝ}
    (h : ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature θ κ L s -
      curveOfCurvature θ κ L s') ≤ W) :
    ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature θ' κ L s -
      curveOfCurvature θ' κ L s') ≤ W := by
  obtain ⟨v, hv, hW⟩ := h
  refine ⟨tau (θ' - θ) * v, norm_tau_mul hv, fun s s' => ?_⟩
  have := hW s s'
  rw [curveOfCurvature_rotate θ, curveOfCurvature_rotate θ, ← mul_sub, coord_tau_mul] at this
  rw [curveOfCurvature_rotate θ', curveOfCurvature_rotate θ', ← mul_sub, coord_tau_mul,
    ← mul_assoc, ← tau_add]
  convert this using 3; ring_nf

section rear

variable {θ L' L'' : ℝ} {K δ k : ℝ → ℝ}

/-- **The rear in its own arclength.** -/
theorem rearCurve_eq_curveOfCurvature (hK : Continuous K) (hKp : Function.Periodic K L')
    (hKi : ∫ r in (0 : ℝ)..L', K r = π)
    (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s) (hδp : Function.Periodic δ L')
    (hcos : ∀ s, 0 < Real.cos (δ s)) (hk : Continuous k) (hkp : Function.Periodic k L'')
    (hki : ∫ r in (0 : ℝ)..L'', k r = π) (hL : ∫ r in (0 : ℝ)..L', Real.cos (δ r) = L'')
    (hkx : ∀ s, k (∫ r in (0 : ℝ)..s, Real.cos (δ r)) = Real.tan (δ s)) (s : ℝ) :
    rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ s =
      curveOfCurvature (θ - δ 0) k L'' (∫ r in (0 : ℝ)..s, Real.cos (δ r)) := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun s => (hδ s).continuousAt
  have hcc : Continuous fun r => Real.cos (δ r) := Real.continuous_cos.comp hδc
  set x : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, Real.cos (δ r) with hxdef
  have hx : ∀ s, HasDerivAt x (Real.cos (δ s)) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hcc.intervalIntegrable _ _)
      (hcc.stronglyMeasurableAtFilter _ _) hcc.continuousAt
  have hxp : ∀ s, x (s + L') = x s + L'' := fun s => by
    simp only [hxdef]; rw [integral_add_period hcc (fun r => by simp only [hδp r]), hL]
  have hF : ∀ s, HasDerivAt (curveOfCurvature θ K L') (tau (angleOfCurvature θ K s)) s :=
    hasDerivAt_curveOfCurvature hK
  have hΘ : ∀ s, HasDerivAt (angleOfCurvature θ K) (K s) s := hasDerivAt_angleOfCurvature hK
  -- the angles agree
  have hang : ∀ s, angleOfCurvature (θ - δ 0) k (x s) = angleOfCurvature θ K s - δ s := by
    have hd : ∀ s, HasDerivAt (fun s => angleOfCurvature (θ - δ 0) k (x s) -
        (angleOfCurvature θ K s - δ s)) 0 s := fun s => by
      have h1 := (hasDerivAt_angleOfCurvature (θ₀ := θ - δ 0) hk (x s)).comp s (hx s)
      have h2 := h1.sub ((hΘ s).sub (hδ s))
      convert h2 using 1
      rw [hkx s, Real.tan_eq_sin_div_cos]
      field_simp [(hcos s).ne']
      ring
    intro s
    have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) s 0
    simp only [hxdef, intervalIntegral.integral_same, angleOfCurvature] at this
    simp only [angleOfCurvature]
    linarith
  -- the curves have the same derivative
  have hR := hasDerivAt_rearCurve hF hΘ hδ
  have hC : ∀ s, HasDerivAt (fun s => curveOfCurvature (θ - δ 0) k L'' (x s))
      ((Real.cos (δ s) : ℂ) * tau (angleOfCurvature θ K s - δ s)) s := fun s => by
    have := (hasDerivAt_curveOfCurvature (θ₀ := θ - δ 0) (L := L'') hk (x s)).scomp s (hx s)
    rw [hang s] at this
    simpa [Complex.real_smul] using this
  have hd : ∀ s, HasDerivAt (fun s => rearCurve (curveOfCurvature θ K L')
      (angleOfCurvature θ K) δ s - curveOfCurvature (θ - δ 0) k L'' (x s)) 0 s := fun s => by
    have := (hR s).sub (hC s)
    simpa using this
  have hconst : ∀ s, rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ s -
      curveOfCurvature (θ - δ 0) k L'' (x s) =
      rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ 0 -
      curveOfCurvature (θ - δ 0) k L'' (x 0) := fun s =>
    is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) s 0
  -- antiperiodicity forces the constant to vanish
  have hanti : rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ L' -
      curveOfCurvature (θ - δ 0) k L'' (x L') =
      -(rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ 0 -
      curveOfCurvature (θ - δ 0) k L'' (x 0)) := by
    have h1 : rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ (0 + L') =
        -rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ 0 := by
      simp only [rearCurve]
      rw [curveOfCurvature_add_period hK hKp hKi, angleOfCurvature_add_period hK hKp hKi,
        hδp 0, show angleOfCurvature θ K 0 + π - δ 0 = (angleOfCurvature θ K 0 - δ 0) + π by ring,
        tau_add_pi]
      ring
    have h2 : curveOfCurvature (θ - δ 0) k L'' (x (0 + L')) =
        -curveOfCurvature (θ - δ 0) k L'' (x 0) := by
      rw [hxp, curveOfCurvature_add_period hk hkp hki]
    rw [zero_add] at h1 h2
    rw [h1, h2]; ring
  have h0 : rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ 0 -
      curveOfCurvature (θ - δ 0) k L'' (x 0) = 0 := by
    have := hconst L'
    rw [hanti] at this
    have h2 : (2 : ℂ) * (rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ 0 -
      curveOfCurvature (θ - δ 0) k L'' (x 0)) = 0 := by linear_combination -this
    simpa using h2
  have := hconst s
  rw [h0, sub_eq_zero] at this
  exact this

/-- **Rears are no wider than fronts**: under the hypotheses of
`rearCurve_eq_curveOfCurvature`, if the front lies in a strip of width `W`, so does the rear. -/
theorem width_rear_le (hK : Continuous K) (hKp : Function.Periodic K L')
    (hKi : ∫ r in (0 : ℝ)..L', K r = π) (hL' : 0 < L')
    (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s) (hδp : Function.Periodic δ L')
    (hcos : ∀ s, 0 < Real.cos (δ s)) (hk : Continuous k) (hkp : Function.Periodic k L'')
    (hki : ∫ r in (0 : ℝ)..L'', k r = π) (hL : ∫ r in (0 : ℝ)..L', Real.cos (δ r) = L'')
    (hkx : ∀ s, k (∫ r in (0 : ℝ)..s, Real.cos (δ r)) = Real.tan (δ s)) {W : ℝ}
    (hW : ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature θ K L' s -
      curveOfCurvature θ K L' s') ≤ W) (θ' : ℝ) :
    ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature θ' k L'' s -
      curveOfCurvature θ' k L'' s') ≤ W := by
  refine width_rotate (θ := θ - δ 0) ?_
  obtain ⟨v, hv, hvW⟩ := hW
  refine ⟨v, hv, ?_⟩
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun s => (hδ s).continuousAt
  have hcc : Continuous fun r => Real.cos (δ r) := Real.continuous_cos.comp hδc
  set x : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, Real.cos (δ r) with hxdef
  have hx : ∀ s, HasDerivAt x (Real.cos (δ s)) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hcc.intervalIntegrable _ _)
      (hcc.stronglyMeasurableAtFilter _ _) hcc.continuousAt
  obtain ⟨m, hm, hmc⟩ := exists_pos_lower_bound_of_periodic hL' hcc (fun r => by simp [hδp r])
    hcos
  obtain ⟨G, hG1, -, -⟩ := exists_inverse_of_deriv_ge hm hx hmc
  set γ := curveOfCurvature (θ - δ 0) k L''
  have hγd : Differentiable ℝ γ := fun s => (hasDerivAt_curveOfCurvature hk s).differentiableAt
  have hL''pos : 0 < L'' := by
    rw [← hL]; exact integral_pos_of_periodic hL' hcc hcos
  -- `𝒯 γ ∘ x = F`
  have hT : ∀ s, unitTangentTransform γ (x s) = curveOfCurvature θ K L' s := fun s => by
    have h1 : unitTangentTransform (γ ∘ x) = unitTangentTransform γ ∘ x :=
      unitTangentTransform_comp hγd (fun s => (hx s).differentiableAt)
        (fun s => by rw [(hx s).deriv]; exact hcos s)
    have h2 : γ ∘ x = rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ := by
      funext s
      exact (rearCurve_eq_curveOfCurvature hK hKp hKi hδ hδp hcos hk hkp hki hL hkx s).symm
    have h3 := unitTangentTransform_rearCurve (F := curveOfCurvature θ K L')
      (Θ := angleOfCurvature θ K) (hasDerivAt_curveOfCurvature (θ₀ := θ) (L := L') hK)
      (hasDerivAt_angleOfCurvature (θ₀ := θ) hK) hδ hcos
    rw [h2, h3] at h1
    exact (congrFun h1 s).symm
  refine width_le_of_unitTangent (p := 2 * L'') (by positivity) hγd
    (curveOfCurvature_periodic hk hkp hki) fun t t' => ?_
  rw [← hG1 t, ← hG1 t', hT, hT]
  exact hvW _ _

end rear

end Ovals

end
