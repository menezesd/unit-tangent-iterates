import Mathlib
import UnitTangentIterates.HairpinFrontCurvature
import UnitTangentIterates.PaperHairpinQuantitativeData

/-! # Interior phase chain for the canonical translator -/

noncomputable section

open Real Set

namespace CanonicalTranslatorLocalPhase

open HairpinRelative FrontPeriodization

/-- Exactly the local analytic information used by the phase argument.  No
extension of the profile through `0` or `π` is included. -/
structure InteriorPhaseData (f theta x g gp : ℝ → ℝ) : Prop where
  profile_continuous : ContinuousOn f (Ioo 0 Real.pi)
  profile_smooth : ∀ n : ℕ, ContDiffOn ℝ n f (Ioo 0 Real.pi)
  profile_pos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t
  angle_mem : ∀ u, theta u ∈ Ioo (0 : ℝ) Real.pi
  image_mem : ∀ t ∈ Ioo (0 : ℝ) Real.pi, g t ∈ Ioo (0 : ℝ) Real.pi
  angle_value : ∀ u, Hairpin.hairpinArclength f (Real.pi / 2) (theta u) = u
  arclength_strictMono : StrictMonoOn
    (Hairpin.hairpinArclength f (Real.pi / 2)) (Ioo 0 Real.pi)
  angle_deriv : ∀ u, HasDerivAt theta (curvField f (theta u)) u
  inverse_value : ∀ s, frontArclength f theta (x s) = s
  state_deriv : ∀ s, HasDerivAt (fun r => theta (x r))
    (pulseField f (theta (x s))) s
  shift : ∀ t ∈ Ioo (0 : ℝ) Real.pi,
    g t - t = Real.arctan (curvField f t)
  translator_deriv : ∀ t ∈ Ioo (0 : ℝ) Real.pi, HasDerivAt g (gp t) t
  translator_identity : ∀ t ∈ Ioo (0 : ℝ) Real.pi,
    f (g t) * gp t = f t + Real.cos t

/-! ### Interior-only versions of the front-curvature identities

`HairpinFrontCurvature` states these with a global positivity hypothesis
`∀ t, 0 < f t`.  Their proofs only ever evaluate `f` at points of `(0, π)`
(and at the image `g θ`, which stays in `(0, π)`), so the localized profile
data of `InteriorPhaseData` suffices.  They are restated here rather than
generalized upstream so that no already-verified module has to be rebuilt. -/

private theorem curvField_pos_on {f : ℝ → ℝ}
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) : 0 < curvField f θ :=
  div_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) (hfpos θ hθ)

private theorem delta_mem_on {f g : ℝ → ℝ}
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, g θ - θ = Real.arctan (curvField f θ))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    g θ - θ ∈ Ioo 0 (Real.pi / 2) := by
  rw [hdelta θ hθ]
  exact ⟨Real.arctan_pos.mpr (curvField_pos_on hfpos hθ),
    Real.arctan_lt_pi_div_two _⟩

private theorem cos_delta_pos_on {f g : ℝ → ℝ}
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, g θ - θ = Real.arctan (curvField f θ))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) : 0 < Real.cos (g θ - θ) := by
  have h := delta_mem_on hfpos hdelta hθ
  refine Real.cos_pos_of_mem_Ioo ⟨?_, h.2⟩
  linarith [h.1, Real.pi_pos]

private theorem sin_mul_cos_delta_on {f g : ℝ → ℝ}
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, g θ - θ = Real.arctan (curvField f θ))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    Real.sin θ * Real.cos (g θ - θ) = f θ * Real.sin (g θ - θ) := by
  have hcos := cos_delta_pos_on hfpos hdelta hθ
  have htan : Real.tan (g θ - θ) = curvField f θ := by
    rw [hdelta θ hθ, Real.tan_arctan]
  rw [Real.tan_eq_sin_div_cos, curvField,
    div_eq_div_iff hcos.ne' (hfpos θ hθ).ne'] at htan
  linarith

private theorem curvField_next_on {f g gp : ℝ → ℝ}
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, g θ - θ = Real.arctan (curvField f θ))
    (hnextd : ∀ θ ∈ Ioo (0 : ℝ) Real.pi,
      f (g θ) * gp θ = f θ + Real.cos θ)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (hgθ : g θ ∈ Ioo (0 : ℝ) Real.pi) :
    curvField f (g θ) = gp θ * pulseField f θ := by
  have hrel := sin_mul_cos_delta_on hfpos hdelta hθ
  set d : ℝ := g θ - θ with hd
  have hgd : g θ = θ + d := by rw [hd]; ring
  have hsin : Real.sin (g θ) = (f θ + Real.cos θ) * Real.sin d := by
    rw [hgd, Real.sin_add]
    nlinarith [hrel]
  have hfg : f (g θ) ≠ 0 := (hfpos _ hgθ).ne'
  rw [curvField, hsin, ← hnextd θ hθ,
    HairpinFrontCurvature.pulseField_eq_sin_delta hdelta hθ, ← hd]
  field_simp

private theorem sqrt_one_sub_pulse_sq_on {f g : ℝ → ℝ}
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, g θ - θ = Real.arctan (curvField f θ))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    Real.sqrt (1 - pulseField f θ ^ 2) = Real.cos (g θ - θ) := by
  have hcos := cos_delta_pos_on hfpos hdelta hθ
  rw [HairpinFrontCurvature.pulseField_eq_sin_delta hdelta hθ]
  have hsq : 1 - Real.sin (g θ - θ) ^ 2 = Real.cos (g θ - θ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (g θ - θ)
    linarith
  rw [hsq, Real.sqrt_sq hcos.le]

private theorem pulse_add_G_mul_deriv_on {f g gp theta x yp : ℝ → ℝ}
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, g θ - θ = Real.arctan (curvField f θ))
    (hnextd : ∀ θ ∈ Ioo (0 : ℝ) Real.pi,
      f (g θ) * gp θ = f θ + Real.cos θ)
    (hg : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, HasDerivAt g (gp θ) θ)
    (hmem : ∀ u, theta u ∈ Ioo (0 : ℝ) Real.pi)
    (himg : ∀ t ∈ Ioo (0 : ℝ) Real.pi, g t ∈ Ioo (0 : ℝ) Real.pi)
    (hxderiv : ∀ s,
      HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s)
    (hy : ∀ s,
      HasDerivAt (fun s => pulseField f (theta (x s))) (yp s) s) (s : ℝ) :
    pulseField f (theta (x s)) + G (pulseField f (theta (x s))) * yp s
      = curvField f (g (theta (x s))) := by
  have hcos := cos_delta_pos_on hfpos hdelta (hmem (x s))
  have hval : yp s = Real.cos (g (theta (x s)) - theta (x s))
      * ((gp (theta (x s)) - 1) * pulseField f (theta (x s))) :=
    (hy s).unique
      (HairpinFrontCurvature.hasDerivAt_pulse hdelta hg hmem hxderiv s)
  have hG : G (pulseField f (theta (x s)))
      = (Real.cos (g (theta (x s)) - theta (x s)))⁻¹ := by
    rw [G, sqrt_one_sub_pulse_sq_on hfpos hdelta (hmem (x s))]
  rw [hval, hG,
    curvField_next_on hfpos hdelta hnextd (hmem (x s)) (himg _ (hmem (x s)))]
  field_simp
  ring

/-- Positivity and continuity on the open angle interval suffice for strict
monotonicity of the hairpin arclength primitive; no endpoint lower bound is
needed. -/
theorem arclength_strictMonoOn_of_positive
    {f : ℝ → ℝ} (hfc : ContinuousOn f (Ioo (0 : ℝ) Real.pi))
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t) :
    StrictMonoOn (Hairpin.hairpinArclength f (Real.pi / 2))
      (Ioo (0 : ℝ) Real.pi) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) Real.pi)
  · exact HairpinArclength.continuousOn_arclength hfc
  · intro t ht
    rw [isOpen_Ioo.interior_eq] at ht
    have hd := HairpinArclength.hasDerivAt_arclength hfc ht
    rw [hd.deriv]
    exact div_pos (hfpos t ht) (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)

/-- The normalized front-arclength inverse fixes the origin. -/
theorem x_zero_of_inverse_value
    {f theta x : ℝ → ℝ}
    (hfc : ContinuousOn f (Ioo (0 : ℝ) Real.pi))
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo (0 : ℝ) Real.pi)
    (hthetad : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hinv : ∀ s, frontArclength f theta (x s) = s) : x 0 = 0 := by
  have hthetac : Continuous theta :=
    continuous_iff_continuousAt.2 fun u => (hthetad u).continuousAt
  have hfcomp : Continuous fun t => f (theta t) :=
    hfc.comp_continuous hthetac hmem
  have hne : ∀ t, f (theta t) ≠ 0 := fun t => (hfpos _ (hmem t)).ne'
  have hcurv : Continuous fun t => curvField f (theta t) := by
    have h := (Real.continuous_sin.comp hthetac).div hfcomp hne
    simpa [curvField] using h
  have hcont : Continuous fun t =>
      Real.sqrt (1 + curvField f (theta t) ^ 2) :=
    (continuous_const.add (hcurv.pow 2)).sqrt
  have hd : ∀ u, HasDerivAt (frontArclength f theta)
      (Real.sqrt (1 + curvField f (theta u) ^ 2)) u := fun u =>
    (hcont.integral_hasStrictDerivAt (0 : ℝ) u).hasDerivAt
  have hmono : StrictMono (frontArclength f theta) := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(hd u).deriv]
    positivity
  refine hmono.injective ?_
  rw [hinv 0]
  exact (HairpinRelative.frontArclength_zero f theta).symm

/-- Replace the two normalization fields of a localized phase package by
their canonical consequences. -/
theorem InteriorPhaseData.x_zero {f theta x g gp : ℝ → ℝ}
    (d : InteriorPhaseData f theta x g gp) : x 0 = 0 :=
  x_zero_of_inverse_value d.profile_continuous d.profile_pos d.angle_mem
    d.angle_deriv d.inverse_value

/-- Localized derivative of the image-angle phase. -/
theorem hasDerivAt_phase {f theta x g gp : ℝ → ℝ}
    (d : InteriorPhaseData f theta x g gp) (s : ℝ) :
    HasDerivAt (fun r => Hairpin.hairpinArclength f (Real.pi / 2)
      (g (theta (x r)))) 1 s := by
  have hm := d.image_mem _ (d.angle_mem (x s))
  have hA := HairpinArclength.hasDerivAt_arclength d.profile_continuous hm
  have hg := (d.translator_deriv _ (d.angle_mem (x s))).comp s (d.state_deriv s)
  have hc := hA.comp s hg
  have hnext := curvField_next_on d.profile_pos d.shift d.translator_identity
    (d.angle_mem (x s)) hm
  convert hc using 1
  rw [← hnext, curvField]
  field_simp [ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hm.1 hm.2),
    ne_of_gt (d.profile_pos _ hm)]

/-- The centered inverse angle takes the value `π/2` at arclength zero. -/
theorem theta_zero {f theta x g gp : ℝ → ℝ}
    (d : InteriorPhaseData f theta x g gp) : theta 0 = Real.pi / 2 := by
  apply d.arclength_strictMono.injOn (d.angle_mem 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rw [d.angle_value 0, Hairpin.hairpinArclength]
  simp

/-- The image-angle arclength differs from front arclength by one constant. -/
theorem phase_eq {f theta x g gp : ℝ → ℝ}
    (d : InteriorPhaseData f theta x g gp) (hx0 : x 0 = 0) (s : ℝ) :
    Hairpin.hairpinArclength f (Real.pi / 2) (g (theta (x s))) =
      s + Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2)) := by
  let psi := fun r => Hairpin.hairpinArclength f (Real.pi / 2) (g (theta (x r)))
  have hd : ∀ r, HasDerivAt (fun t => psi t - t) 0 r := fun r => by
    simpa [psi] using (hasDerivAt_phase d r).sub (hasDerivAt_id r)
  have hc := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) s 0
  simp only [psi, hx0, theta_zero d, sub_zero] at hc
  linarith

/-- Applying the inverse arclength angle to the common phase recovers the
translator image angle. -/
theorem theta_phase_eq {f theta x g gp : ℝ → ℝ}
    (d : InteriorPhaseData f theta x g gp) (hx0 : x 0 = 0) (s : ℝ) :
    theta (s + Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))) =
      g (theta (x s)) := by
  apply d.arclength_strictMono.injOn (d.angle_mem _)
    (d.image_mem _ (d.angle_mem (x s)))
  rw [d.angle_value, phase_eq d hx0 s]

/-- The translator front-curvature identity in the marking whose origin is
shifted by the common phase. -/
theorem front_curvature_identity_shifted
    {f theta x g gp yp : ℝ → ℝ}
    (d : InteriorPhaseData f theta x g gp) (hx0 : x 0 = 0)
    (hyp : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s)
    (s : ℝ) :
    curvField f (theta s) =
      pulseField f (theta (x (s - Hairpin.hairpinArclength f (Real.pi / 2)
        (g (Real.pi / 2))))) +
      FrontPeriodization.G
          (pulseField f (theta (x (s - Hairpin.hairpinArclength f
            (Real.pi / 2) (g (Real.pi / 2)))))) *
        yp (s - Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))) := by
  let r := s - Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))
  have hp := pulse_add_G_mul_deriv_on d.profile_pos d.shift
    d.translator_identity d.translator_deriv d.angle_mem d.image_mem
    d.state_deriv hyp r
  have hphase := theta_phase_eq d hx0 r
  have hrs : r + Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2)) = s := by
    dsimp [r]
    ring
  rw [hrs] at hphase
  rw [hphase]
  exact hp.symm

/-- Canonical localized phase witness exposed for a consecutive-data package.
The package supplies the translator/image identities; only its interior phase
data are required here. -/
theorem consecutive_local_phase
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : PaperHairpinQuantitativeData.ConsecutiveData
      f theta x g gp yp M Delta beta C Ht P Pp)
    (d : InteriorPhaseData f theta x g gp) (hx0 : x 0 = 0) :
    ∀ s, theta (s + Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))) =
      g (theta (x s)) :=
  theta_phase_eq d hx0

/-- Canonical consecutive phase, with the inverse origin discharged from the
localized quantitative data. -/
theorem canonical_consecutive_local_phase
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : PaperHairpinQuantitativeData.ConsecutiveData
      f theta x g gp yp M Delta beta C Ht P Pp)
    (d : InteriorPhaseData f theta x g gp) :
    ∀ s, theta (s + Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))) =
      g (theta (x s)) :=
  consecutive_local_phase c d d.x_zero

/-- The localized front identity supplies the exact local-phase conclusion
stored by `ConsecutiveData`, without a global smooth extension. -/
theorem canonical_local_phase
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : PaperHairpinQuantitativeData.ConsecutiveData
      f theta x g gp yp M Delta beta C Ht P Pp)
    (d : InteriorPhaseData f theta x g gp) :
    ∀ s, PaperHairpinQuantitativeData.ConsecutiveData.currentPulse f theta x s =
      Real.sqrt (1 - PaperHairpinQuantitativeData.ConsecutiveData.currentPulse f theta x s ^ 2) *
        ModelOrbitDefect.hairpinCurvature
          (PaperHairpinQuantitativeData.ConsecutiveData.previousPulse f theta x g)
          (PaperHairpinQuantitativeData.ConsecutiveData.previousPulseDeriv f theta g yp) (x s) := by
  intro s
  have hcurv := front_curvature_identity_shifted d d.x_zero c.pulse_deriv (x s)
  have hsteer := HairpinPulseIdentity.pulseField_eq_speed_mul_curvField
    f (theta (x s))
  rw [hcurv] at hsteer
  simpa [PaperHairpinQuantitativeData.ConsecutiveData.currentPulse,
    PaperHairpinQuantitativeData.ConsecutiveData.previousPulse,
    PaperHairpinQuantitativeData.ConsecutiveData.previousPulseDeriv,
    PaperHairpinQuantitativeData.ConsecutiveData.phase, ModelOrbitDefect.hairpinCurvature] using hsteer

end CanonicalTranslatorLocalPhase
