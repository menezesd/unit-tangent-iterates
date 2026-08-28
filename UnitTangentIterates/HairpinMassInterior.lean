import Mathlib
import UnitTangentIterates.HairpinTotalMass
import UnitTangentIterates.HairpinTailsInterior
import UnitTangentIterates.HairpinPulseMass

/-!
# Total curvature and steering mass, without endpoint regularity

`HairpinTotalMass.integral_curv_eq_pi` — the rear tangent turns through `π` —
and the steering-mass identity `∫ y = π` are the last members of the hairpin
chain still stated with the global profile hypothesis `ContDiff ℝ ∞ f` and
positivity of `f` on the whole line.

As everywhere else on this path, those hypotheses are used for exactly one
thing: continuity of `curvField f ∘ θ` (and, pointwise, nonnegativity of the
curvature along `θ`).  This file restates them accordingly, completing the
interior route for the `mass` field of
`PaperHairpinQuantitativeData.Data`.

Main results: `integrableOn_curv_Ioi_of_comp`, `integrableOn_curv_Iic_of_comp`,
`integral_curv_eq_pi_of_comp`.
-/

noncomputable section

open Set Filter MeasureTheory Topology Real HairpinRelative

namespace HairpinMassInterior

variable {f theta : ℝ → ℝ} {A M : ℝ}

/-- Integrability of the curvature on the right half-line, from interior data. -/
theorem integrableOn_curv_Ioi_of_comp
    (hcont : Continuous fun u => curvField f (theta u))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M) :
    IntegrableOn (fun u => curvField f (theta u)) (Ioi 0) volume := by
  have hA : 0 ≤ A := by
    have h := (hnn 0).trans (hdecay 0)
    by_contra hneg
    push_neg at hneg
    nlinarith [Real.exp_pos (-|(0:ℝ)| / M)]
  have hg : IntegrableOn (fun x : ℝ => A * Real.exp (-(1 / M) * x)) (Ioi 0) volume :=
    (exp_neg_integrableOn_Ioi 0 (by positivity : (0:ℝ) < 1 / M)).const_mul A
  refine Integrable.mono' hg hcont.aestronglyMeasurable.restrict ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  have hx0 : (0:ℝ) ≤ x := le_of_lt hx
  have h1 : curvField f (theta x) ≤ A * Real.exp (-(1 / M) * x) := by
    have h := hdecay x
    rwa [abs_of_nonneg hx0, show -x / M = -(1 / M) * x by ring] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
  exact h1

/-- Integrability of the curvature on the left half-line, from interior data. -/
theorem integrableOn_curv_Iic_of_comp
    (hcont : Continuous fun u => curvField f (theta u))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M) :
    IntegrableOn (fun u => curvField f (theta u)) (Iic 0) volume := by
  have hA : 0 ≤ A := by
    have h := (hnn 0).trans (hdecay 0)
    by_contra hneg
    push_neg at hneg
    nlinarith [Real.exp_pos (-|(0:ℝ)| / M)]
  have hg : IntegrableOn (fun x : ℝ => A * Real.exp (1 / M * x)) (Iic 0) volume :=
    (integrableOn_exp_mul_Iic (by positivity : (0:ℝ) < 1 / M) 0).const_mul A
  refine Integrable.mono' hg hcont.aestronglyMeasurable.restrict ?_
  refine ae_restrict_of_forall_mem measurableSet_Iic fun x hx => ?_
  have hx0 : x ≤ 0 := hx
  have h1 : curvField f (theta x) ≤ A * Real.exp (1 / M * x) := by
    have h := hdecay x
    rwa [abs_of_nonpos hx0, show - -x / M = 1 / M * x by ring] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
  exact h1

/-- **The rear tangent turns through `π`, from interior data.**  This is
`HairpinTotalMass.integral_curv_eq_pi` with the global profile hypothesis
replaced by continuity of `curvField f ∘ θ` and pointwise nonnegativity — the
only things its proof ever used.  The two limits `θ → π` and `θ → 0` come from
`tendsto_theta_atTop` / `tendsto_theta_atBot`, which are already profile-free. -/
theorem integral_curv_eq_pi_of_comp
    (hcont : Continuous fun u => curvField f (theta u))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hmem : ∀ u, theta u ∈ Ioo 0 π) (hsm : StrictMono theta)
    (hsurj : ∀ x ∈ Ioo (0:ℝ) π, ∃ u, theta u = x)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M) :
    ∫ u, curvField f (theta u) = π := by
  have hthetac : Continuous theta :=
    Differentiable.continuous fun u => (hderiv u).differentiableAt
  have hIoi := integrableOn_curv_Ioi_of_comp hcont hnn hdecay hM
  have hIic := integrableOn_curv_Iic_of_comp hcont hnn hdecay hM
  have h1 : (∫ u in Ioi (0:ℝ), curvField f (theta u)) = π - theta 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto hthetac.continuousWithinAt
      (fun x _ => hderiv x) hIoi (HairpinRelative.tendsto_theta_atTop hmem hsm hsurj)
  have h2 : (∫ u in Iic (0:ℝ), curvField f (theta u)) = theta 0 - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto hthetac.continuousWithinAt
      (fun x _ => hderiv x) hIic (HairpinRelative.tendsto_theta_atBot hmem hsm hsurj)
  have hsum := intervalIntegral.integral_Iic_add_Ioi hIic hIoi
  rw [h1, h2] at hsum
  linarith [hsum]

/-- Pointwise form of `pulseField_le_curvField`: no global positivity needed. -/
theorem pulseField_le_curvField_at {t : ℝ} (h0 : 0 ≤ curvField f t) :
    pulseField f t ≤ curvField f t := by
  have h1 : (1:ℝ) ≤ Real.sqrt (1 + curvField f t ^ 2) := by
    have h : (1:ℝ) ≤ 1 + curvField f t ^ 2 := by nlinarith [sq_nonneg (curvField f t)]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt h
  rw [pulseField]
  exact div_le_self h0 h1

/-- **The steering mass of the hairpin is `π`, from interior data.**  This is
`HairpinRelative.hairpin_pulse_mass_of_data` with the global profile hypothesis
removed: the coordinates are taken as given (they are produced by
`HairpinInteriorRegularity.exists_hairpin_coordinates_interior`), and the only
analytic inputs are continuity of `curvField f ∘ θ`, nonnegativity of the
curvature along `θ`, and the exponential tail — all available on the interior
route.  This supplies the `mass` field of
`PaperHairpinQuantitativeData.Data`. -/
theorem pulse_mass_of_comp
    (hcont : Continuous fun u => curvField f (theta u))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hmem : ∀ u, theta u ∈ Ioo 0 π) (hsm : StrictMono theta)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hA : 0 ≤ A) (hM : 0 < M)
    {x : ℝ → ℝ} (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hycont : Continuous fun s => pulseField f (theta (x s))) :
    (∫ s : ℝ, pulseField f (theta (x s))) = π := by
  set K : ℝ → ℝ := fun u => curvField f (theta u) with hK
  set y : ℝ → ℝ := fun s => pulseField f (theta (x s)) with hy
  have hsigderiv : ∀ u, HasDerivAt (frontArclength f theta)
      (Real.sqrt (1 + K u ^ 2)) u :=
    HairpinTailsInterior.hasDerivAt_frontArclength_of_comp hcont
  have hge : ∀ u, (1:ℝ) ≤ Real.sqrt (1 + K u ^ 2) := by
    intro u
    have h1 : (1:ℝ) ≤ 1 + K u ^ 2 := by nlinarith [sq_nonneg (K u)]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have hsigmono : StrictMono (frontArclength f theta) :=
    ArclengthInverse.strictMono_of_deriv_ge (c := 1) one_pos hsigderiv hge
  have hxleft : ∀ u, x (frontArclength f theta u) = u := fun u =>
    ArclengthInverse.leftInverse_of_rightInverse hsigmono.injective hxinv u
  have hmass : ∀ a b : ℝ,
      (∫ s in (frontArclength f theta a)..(frontArclength f theta b), y s)
        = ∫ u in a..b, K u := by
    intro a b
    refine HairpinMass.mass_identity (fun u _ => hsigderiv u) hcont hycont ?_
    intro u
    show pulseField f (theta (x (frontArclength f theta u)))
      = K u / Real.sqrt (1 + K u ^ 2)
    rw [hxleft u, pulseField]
  have hKint : Integrable K :=
    HairpinRelative.integrable_of_exp_bound hcont hnn hdecay hM
  have hle : ∀ u, pulseField f (theta u) ≤ curvField f (theta u) := fun u =>
    pulseField_le_curvField_at (hnn u)
  have hybound : ∀ s, y s ≤ A * Real.exp (A ^ 2 / 2) * Real.exp (-|s| / M) :=
    fun s => HairpinTailsInterior.pulse_decay_of_comp hcont hnn hle hdecay hA hM
      hxinv s
  have hynn : ∀ s, 0 ≤ y s := fun s => by
    have h := hnn (x s)
    have := pulseField_le_curvField_at (f := f) (t := theta (x s)) h
    rw [hy]
    exact div_nonneg h (Real.sqrt_nonneg _)
  have hyint : Integrable y :=
    HairpinRelative.integrable_of_exp_bound hycont hynn hybound hM
  have hsigTop : Tendsto (fun t : ℝ => frontArclength f theta t) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℝ))
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    have h := ArclengthInverse.le_of_deriv_ge (c := 1) hsigderiv hge hu
    rw [frontArclength_zero] at h
    simpa using h
  have hsigBot : Tendsto (fun t : ℝ => frontArclength f theta (-t)) atTop atBot := by
    have h : Tendsto (fun t : ℝ => frontArclength f theta t) atBot atBot := by
      refine tendsto_atBot_mono' atBot ?_ (tendsto_id (α := ℝ))
      filter_upwards [eventually_le_atBot (0:ℝ)] with u hu
      have h' := ArclengthInverse.ge_of_deriv_ge (c := 1) hsigderiv hge hu
      rw [frontArclength_zero] at h'
      simpa using h'
    exact h.comp tendsto_neg_atTop_atBot
  have h1 : Tendsto (fun t : ℝ =>
      ∫ s in (frontArclength f theta (-t))..(frontArclength f theta t), y s)
      atTop (𝓝 (∫ s, y s)) :=
    intervalIntegral_tendsto_integral hyint hsigBot hsigTop
  have h2 : Tendsto (fun t : ℝ => ∫ u in (-t)..t, K u) atTop (𝓝 (∫ u, K u)) :=
    intervalIntegral_tendsto_integral hKint tendsto_neg_atTop_atBot
      (tendsto_id (α := ℝ))
  have heq : (fun t : ℝ =>
      ∫ s in (frontArclength f theta (-t))..(frontArclength f theta t), y s)
      = fun t : ℝ => ∫ u in (-t)..t, K u := funext fun t => hmass (-t) t
  rw [heq] at h1
  have hpi : (∫ u, K u) = π :=
    integral_curv_eq_pi_of_comp hcont hnn hmem hsm hsurj hderiv hdecay hM
  have hyk : (∫ s, y s) = ∫ u, K u := tendsto_nhds_unique h1 h2
  rw [hy] at hyk ⊢
  rw [hyk, hpi]

end HairpinMassInterior
