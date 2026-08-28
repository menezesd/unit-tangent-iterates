import UnitTangentIterates.CanonicalConsecutivePulseJet
import UnitTangentIterates.HairpinLowerComparison

/-! # Basic canonical consecutive-profile adapters -/


open MeasureTheory
open scoped ContDiff
open ShiftedCurvatureJetMajorant
open PaperHairpinQuantitativeData

namespace PaperHairpinConfig.PulseMassData

theorem shift {y : ℝ → ℝ} (d : PulseMassData y) (q : ℝ) :
    PulseMassData (ShiftedCurvatureJetMajorant.shift q y) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight (-q)).toMeasurableEquiv
  have hmp : MeasurePreserving e MeasureTheory.volume MeasureTheory.volume := by
    simpa [e] using measurePreserving_add_right MeasureTheory.volume (-q)
  constructor
  · have hi := hmp.integrable_comp_of_integrable d.integrable
    simpa [e, ShiftedCurvatureJetMajorant.shift, Function.comp_def, sub_eq_add_neg] using hi
  · have hi := hmp.integral_comp' (g := y)
    simpa [e, ShiftedCurvatureJetMajorant.shift, sub_eq_add_neg, d.mass_eq_pi] using hi

end PaperHairpinConfig.PulseMassData

namespace PaperHairpinConfig.PulsePairAnalyticData

/-- The isolated curvature of the preceding canonical pulse has a summable
translate family.  The proof uses only the exponential pulse tail, the
relative first-derivative bound, and the periodized strip which keeps the
argument of `G` in `[0,au]`. -/
theorem previousHairpinCurvature_summable
    {alpha au C CU DU DU2 D P : ℝ} {y yd yu yu' yu'' : ℝ → ℝ}
    (d : PaperHairpinConfig.PulsePairAnalyticData
      (alpha := alpha) (au := au) (C := C) (CU := CU)
      (DU := DU) (DU2 := DU2) (D := D) (P := P) y yd yu yu' yu'')
    (halpha : 0 < alpha) (hP : 0 < P) (hDU0 : 0 ≤ DU) (hau1 : au < 1) :
    ∀ r, Summable fun m : ℤ =>
      ModelOrbitDefect.hairpinCurvature yu yu' (r - m * P) := by
  intro r
  have habs : ∀ s, |yu s| ≤ CU * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (d.previous_nonneg s)]
    exact d.previous_decay s
  have hsum : Summable fun m : ℤ => yu (r - m * P) :=
    FrontPeriodizationIntegral.summable_translates halpha hP habs r
  have hy_le : ∀ s, yu s ≤ au := by
    intro s
    have hs := FrontPeriodizationIntegral.summable_translates halpha hP habs s
    have hcentral := hs.le_tsum (0 : ℤ) (fun m _ => d.previous_nonneg _)
    have hres := hcentral.trans (d.previous_periodized_strip s)
    simpa using hres
  have hGa0 : 0 ≤ FrontPeriodization.G au := by simp [FrontPeriodization.G]
  have hterm : ∀ s,
      |ModelOrbitDefect.hairpinCurvature yu yu' s| ≤
        (1 + FrontPeriodization.G au * DU) * yu s := by
    intro s
    have hGle := PeriodizedTurning.G_le_G_of_le
      (d.previous_nonneg s) (hy_le s) hau1
    have hG0 : 0 ≤ FrontPeriodization.G (yu s) := by
      simp [FrontPeriodization.G]
    calc
      |ModelOrbitDefect.hairpinCurvature yu yu' s|
          ≤ |yu s| + |FrontPeriodization.G (yu s) * yu' s| := by
            simpa [ModelOrbitDefect.hairpinCurvature] using abs_add_le (yu s)
              (FrontPeriodization.G (yu s) * yu' s)
      _ ≤ yu s + FrontPeriodization.G au * (DU * yu s) := by
        rw [abs_of_nonneg (d.previous_nonneg s), abs_mul,
          abs_of_nonneg hG0]
        have hmul := mul_le_mul hGle (d.previous_relative s) (abs_nonneg _) hGa0
        linarith
      _ = (1 + FrontPeriodization.G au * DU) * yu s := by ring
  have hcoef : 0 ≤ 1 + FrontPeriodization.G au * DU := by
    exact add_nonneg zero_le_one (mul_nonneg hGa0 hDU0)
  refine Summable.of_norm_bounded (hsum.norm.mul_left
    (1 + FrontPeriodization.G au * DU)) ?_
  intro m
  simpa [Real.norm_eq_abs, abs_of_nonneg (d.previous_nonneg _),
    abs_of_nonneg hcoef] using hterm (r - m * P)

end PaperHairpinConfig.PulsePairAnalyticData

namespace PaperHairpinQuantitativeData.ConsecutiveData

theorem currentPulse_nonneg
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (hfpos : ∀ t, 0 < f t) : ∀ s, 0 ≤ currentPulse f theta x s := by
  intro s
  exact HairpinRelative.pulseField_nonneg hfpos
    ⟨(c.quantitative.angle_mem (x s)).1.le, (c.quantitative.angle_mem (x s)).2.le⟩

theorem currentPulse_massData
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp) :
    PaperHairpinConfig.PulseMassData (currentPulse f theta x) :=
  ⟨c.quantitative.pulse_integrable, c.quantitative.mass⟩

theorem current_x_deriv
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∀ s, HasDerivAt x (Real.sqrt (1 - currentPulse f theta x s ^ 2)) s := by
  intro s
  simpa [currentPulse] using HairpinPulseIdentity.hasDerivAt_pulseInverse
    hf hfpos c.quantitative.angle_deriv c.quantitative.inverse_value s

theorem previousPulse_massData
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp) :
    PaperHairpinConfig.PulseMassData (previousPulse f theta x g) := by
  rw [previousPulse_eq_shift]
  exact c.currentPulse_massData.shift (phase f theta g)

/-- The intrinsic angle and front-coordinate inverses in `Data` are unique. -/
theorem coordinates_unique
    {f theta x g gp yp theta' x' : ℝ → ℝ}
    {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hmem' : ∀ u, theta' u ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hval' : ∀ u, Hairpin.hairpinArclength f (Real.pi / 2) (theta' u) = u)
    (hinv' : ∀ s, HairpinRelative.frontArclength f theta' (x' s) = s) :
    theta' = theta ∧ x' = x := by
  have hmono := CanonicalTranslatorLocalPhase.arclength_strictMonoOn_of_positive
    hf.continuous.continuousOn (fun t _ => hfpos t)
  have htheta : theta' = theta := by
    funext u
    apply hmono.injOn (hmem' u) (c.quantitative.angle_mem u)
    rw [hval' u, c.quantitative.angle_value u]
  subst theta'
  have hd := HairpinPulseIdentity.hasDerivAt_frontArclength_sqrt hf hfpos
    c.quantitative.angle_deriv
  have hfront : StrictMono (HairpinRelative.frontArclength f theta) := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(hd u).deriv]
    exact lt_of_lt_of_le one_pos
      (HairpinPulseIdentity.one_le_sqrt_one_add_curv_sq f (theta u))
  refine ⟨rfl, funext fun s => hfront.injective ?_⟩
  rw [hinv' s, c.quantitative.inverse_value s]

/-- The lower comparison constructed abstractly for the profile is therefore
the lower comparison for the canonical `Data` coordinates themselves. -/
theorem exists_canonical_lower_comparison
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ b0 : ℝ, 0 < b0 ∧ ∀ s,
      b0 * currentPulse f theta x s ≤ HairpinRelative.curvField f (theta s) := by
  obtain ⟨b0, theta', x', hb0, hmem, hval, hinv, hlower⟩ :=
    HairpinRelative.hairpin_curv_ge_pulse hf hfpos
  obtain ⟨rfl, rfl⟩ := c.coordinates_unique hf hfpos hmem hval hinv
  exact ⟨b0, hb0, by simpa [currentPulse] using hlower⟩

/-- The rear-coordinate lower comparison transports to the translated prior
front coordinate.  The localized translator identity identifies the prior
isolated curvature with `curvField f (theta s)`, while the bounded-shift
Harnack estimate absorbs the phase translation into a smaller positive
constant. -/
theorem exists_previous_lower_comparison
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ b1 : ℝ, 0 < b1 ∧ ∀ s,
      b1 * previousPulse f theta x g s ≤
        ModelOrbitDefect.hairpinCurvature (previousPulse f theta x g)
          (previousPulseDeriv f theta g yp) s := by
  obtain ⟨b0, hb0, hlower⟩ := c.exists_canonical_lower_comparison hf hfpos
  have hne : (Set.Icc (0 : ℝ) Real.pi).Nonempty :=
    ⟨0, le_rfl, Real.pi_pos.le⟩
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Set.Icc (0:ℝ) Real.pi)
    hne hf.continuous.continuousOn
  obtain ⟨t1, ht1, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (0:ℝ) Real.pi)
    hne hf.continuous.continuousOn
  let m := f t0
  let A := f t1
  let q := phase f theta g
  let Ch := (A / m) * Real.exp (|q| / m)
  have hm : 0 < m := hfpos t0
  have hmA : m ≤ A := hmin ht1
  have hl : ∀ t, m ≤ f (theta t) := fun t =>
    hmin ⟨(c.quantitative.angle_mem t).1.le, (c.quantitative.angle_mem t).2.le⟩
  have hu : ∀ t, f (theta t) ≤ A := fun t =>
    hmax ⟨(c.quantitative.angle_mem t).1.le, (c.quantitative.angle_mem t).2.le⟩
  have hA : 0 < A := lt_of_lt_of_le hm hmA
  have hCh : 0 < Ch := mul_pos (div_pos hA hm) (Real.exp_pos _)
  have hKshift : ∀ s,
      HairpinRelative.curvField f (theta (s - q)) ≤
        Ch * HairpinRelative.curvField f (theta s) := by
    intro s
    exact HairpinTails.curvField_shift_harnack_along_theta hm hmA c.quantitative.angle_mem
      c.quantitative.angle_deriv hl hu (abs_nonneg q) (by simp [q])
  have hid : ∀ s, HairpinRelative.curvField f (theta s) =
      ModelOrbitDefect.hairpinCurvature (previousPulse f theta x g)
        (previousPulseDeriv f theta g yp) s := by
    intro s
    simpa [previousPulse, previousPulseDeriv, phase,
      ModelOrbitDefect.hairpinCurvature] using
        (CanonicalTranslatorLocalPhase.front_curvature_identity_shifted
          d d.x_zero c.pulse_deriv s)
  refine ⟨b0 / Ch, div_pos hb0 hCh, ?_⟩
  intro s
  have hlo := hlower (s - q)
  have hchain : b0 * previousPulse f theta x g s ≤
      Ch * HairpinRelative.curvField f (theta s) := by
    exact hlo.trans (hKshift s)
  rw [← hid s, div_mul_eq_mul_div, div_le_iff₀ hCh]
  linarith [hchain]

end PaperHairpinQuantitativeData.ConsecutiveData

