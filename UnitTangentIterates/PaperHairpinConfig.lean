import Mathlib
import UnitTangentIterates.ModelOrbitDefect
import UnitTangentIterates.ModelOrbitHairpinBridge
import UnitTangentIterates.ModelOrbitConfigSmooth
import UnitTangentIterates.PeriodizationSup
import UnitTangentIterates.FrontPeriodizationPositivity
import UnitTangentIterates.HairpinAsymptoticsComplete
import UnitTangentIterates.RearTailHairpin
import UnitTangentIterates.LargeSeparation

/-!
# Assembly of the paper hairpin into a model-orbit configuration

The large `ModelOrbitDefect.Config` record has one geometric field which should
not be supplied independently for the paper's hairpin: `Config.hid`.  It is a
consequence of the normalized rear-arclength coordinate and the isolated
hairpin identity.  This file separates that consequence from the genuinely
quantitative remainder of the configuration.

`ConfigRemainder` is deliberately opaque about the remaining quantitative
fields: it is a completion function waiting for the two pulse-mass
certificates and `hid`.  Its dependent result
ensures that the completed configuration uses the advertised pulses.  Thus it
does not assert any missing decay, period, positivity, mass, or matching
estimate.  `PaperHairpinData.toConfig` supplies the two integrability/mass
certificates and derives the omitted phase field using
`ModelOrbitHairpinBridge.phase_identity_modelRear`.
-/

noncomputable section

open Real HairpinRelative

open scoped ContDiff

namespace PaperHairpinConfig

open ModelOrbitDefect

variable {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P : ℝ}

/-! ## Derived analytic certificates -/

/-- The two measure-theoretic fields carried by each pulse in
`ModelOrbitDefect.Config`, bundled so integrability cannot be separated from
the exact steering-mass identity. -/
structure PulseMassData (y : ℝ → ℝ) : Prop where
  integrable : MeasureTheory.Integrable y
  mass_eq_pi : (∫ s : ℝ, y s) = Real.pi

namespace PulseMassData

/-- Exponential localization supplies the integrability half of a pulse-mass
certificate. -/
theorem of_exp_decay {y : ℝ → ℝ} {C alpha : ℝ}
    (halpha : 0 < alpha) (hycont : Continuous y)
    (hyb : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|))
    (hmass : (∫ s : ℝ, y s) = Real.pi) : PulseMassData y :=
  ⟨FrontPeriodizationIntegral.integrable_of_exp_bound' halpha hycont hyb, hmass⟩

/-- The canonical hairpin package produces its integrability and mass
certificate on one common arclength parametrization. -/
theorem exists_of_hairpin_profile {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ theta x : ℝ → ℝ,
      PulseMassData (fun s => pulseField f (theta (x s))) := by
  obtain ⟨theta, x, M, Delta, hM, hmem, hval, htheta, hx, hxd, hKdec, hydec,
    hyint, hmass, hDelta, hDpos⟩ :=
    HairpinAsymptoticsComplete.exists_hairpin_pulse_package hf hfpos
  exact ⟨theta, x, hyint, hmass⟩

end PulseMassData

/-- The decay and separation data which produce the absolute strip field of a
configuration. -/
structure PeriodizedStripData (y : ℝ → ℝ) (alpha C P a : ℝ) where
  alpha_pos : 0 < alpha
  period_pos : 0 < P
  half_overlap : Real.exp (-alpha * P) ≤ 1 / 2
  nonneg : ∀ s, 0 ≤ y s
  decay : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)
  pointwise : ∀ s, y s ≤ a
  overlap_budget : a + 4 * C * Real.exp (-(alpha / 2) * P) < 1

namespace PeriodizedStripData

/-- Periodization decay turns the paper's overlap budget into the strict
steering strip needed by the nonlinear curvature expression. -/
theorem periodized_abs_lt_one {y : ℝ → ℝ} {alpha C P a : ℝ}
    (d : PeriodizedStripData y alpha C P a) :
    ∀ s, |periodizedPulse y P s| < 1 := by
  intro s
  have hnonneg : 0 ≤ periodizedPulse y P s :=
    tsum_nonneg fun m => d.nonneg (s - m * P)
  rw [abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt
    (PeriodizationSup.periodization_le_of_sup d.alpha_pos d.period_pos
      d.half_overlap d.nonneg d.decay d.pointwise s)
    d.overlap_budget

/-- A non-strict target bound, in exactly the form stored by `Config`. -/
theorem periodized_abs_le {y : ℝ → ℝ} {alpha C P a A : ℝ}
    (d : PeriodizedStripData y alpha C P a)
    (hbudget : a + 4 * C * Real.exp (-(alpha / 2) * P) ≤ A) :
    ∀ s, |periodizedPulse y P s| ≤ A := by
  intro s
  have hnonneg : 0 ≤ periodizedPulse y P s :=
    tsum_nonneg fun m => d.nonneg (s - m * P)
  rw [abs_of_nonneg hnonneg]
  exact (PeriodizationSup.periodization_le_of_sup d.alpha_pos d.period_pos
    d.half_overlap d.nonneg d.decay d.pointwise s).trans hbudget

end PeriodizedStripData

/-- The geometric positivity branch of `Config.hcurvNonnegU`. -/
structure CurvaturePositivityData (y yd : ℝ → ℝ) (P : ℝ) : Prop where
  isolated_nonneg : ∀ s, 0 ≤ hairpinCurvature y yd s
  periodized_nonneg : ∀ s, 0 ≤ modelCurvature y yd P s

namespace CurvaturePositivityData

/-- The large-period error estimate constructs the geometric positivity
certificate used by the paper, without the stronger small-relative-derivative
alternative. -/
theorem of_large_period {y yd : ℝ → ℝ} {C alpha P D a b0 : ℝ}
    (halpha : 0 < alpha) (hP : 0 < P)
    (hq : Real.exp (-alpha * P) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hyd : ∀ s, |yd s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a)
    (hb0 : 0 ≤ b0)
    (hlower : ∀ s, b0 * y s ≤ hairpinCurvature y yd s)
    (hKSumm : ∀ r, Summable fun m : ℤ => hairpinCurvature y yd (r - m * P))
    (hsep : 8 * FrontPeriodization.lipConst a * D * C *
      Real.exp (-(alpha / 2) * P) ≤ b0) :
    CurvaturePositivityData y yd P := by
  rcases FrontPeriodizationPositivity.hairpin_and_modelCurvature_nonneg_of_large_period
    halpha hP hq hy0 hyb hD hyd ha0 ha1 hYa hb0 hlower hKSumm hsep with ⟨hK, hKP⟩
  exact ⟨hK, hKP⟩

/-- A positivity certificate supplies the second branch of
`Config.hcurvNonnegU`. -/
theorem config_branch {y yd : ℝ → ℝ} {P au DU : ℝ}
    (d : CurvaturePositivityData y yd P) :
    FrontPeriodization.G au * DU ≤ 1 ∨
      ((∀ s, 0 ≤ hairpinCurvature y yd s) ∧
        ∀ r, 0 ≤ modelCurvature y yd P r) :=
  Or.inr ⟨d.isolated_nonneg, d.periodized_nonneg⟩

end CurvaturePositivityData

/-- The rear-period and centered-cell fields of `Config`, packaged together. -/
structure RearCellData (y : ℝ → ℝ) (H P B : ℝ) : Prop where
  period_def : modelRearArclength (periodizedPulse y H) H = P
  left_endpoint : modelRearArclength (periodizedPulse y H) (-(H / 2)) ≤ -(H / 2) + B
  right_endpoint : H / 2 - B ≤
    modelRearArclength (periodizedPulse y H) (-(H / 2)) + P
  period_lower : H - 2 * B ≤ P

namespace RearCellData

open RearTailPulse PerimeterHairpinPulse

theorem modelRearArclength_eq_tail {y : ℝ → ℝ} {H t : ℝ} :
    modelRearArclength (periodizedPulse y H) t = RearTailPulse.rearArclength y H t := by
  simp [modelRearArclength, RearTrack.rearArclength,
    cos_modelSteering, RearTailPulse.rearArclength, RearTailPulse.speed,
    RearTailPulse.periodize, periodizedPulse]

/-- The tail estimates produce all three rear-cell inequalities when `B`
dominates their explicit arclength-defect constant. -/
theorem of_tail_bounds {y : ℝ → ℝ} {C alpha b H B : ℝ}
    (halpha : 0 < alpha) (hb1 : b < 1) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b)
    (hH : threshold alpha C b ≤ H)
    (hB : (1 + b) / 2 * (∫ s : ℝ, y s) ≤ B) :
    RearCellData y H (modelRearArclength (periodizedPulse y H) H) B := by
  let P := modelRearArclength (periodizedPulse y H) H
  have hleft0 := rearArclength_left_le halpha hb1 hy hy0 hyb hsup hH
  have hright0 := le_rearArclength_right halpha hb1 hy hy0 hyb hsup hH
  have hleft : modelRearArclength (periodizedPulse y H) (-(H / 2)) ≤
      -(H / 2) + B := by
    rw [modelRearArclength_eq_tail]
    exact hleft0.trans (by linarith)
  have hright : H / 2 - B ≤
      modelRearArclength (periodizedPulse y H) (H / 2) := by
    rw [modelRearArclength_eq_tail]
    exact le_trans (by linarith) hright0
  have hyabs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]
    exact hyb s
  have hYc : Continuous (periodizedPulse y H) := by
    simpa [periodizedPulse] using
      PeriodizedTurning.continuous_periodization halpha
        (lt_of_lt_of_le (threshold_pos halpha
          (Periodization.const_nonneg hy0 hyb) hb1) hH) hy hyabs
  have hdeltaC : Continuous (modelSteering (periodizedPulse y H)) :=
    continuous_modelSteering hYc
  have hdeltaPer : Function.Periodic (modelSteering (periodizedPulse y H)) H := by
    intro s
    unfold modelSteering
    have hp : (∑' m : ℤ, y (s + H - (m : ℝ) * H))
        = ∑' m : ℤ, y (s - (m : ℝ) * H) :=
      PeriodizedTurning.periodic_periodization y H s
    simp only [periodizedPulse]
    rw [hp]
  have hperiod : modelRearArclength (periodizedPulse y H) (-(H / 2)) + P =
      modelRearArclength (periodizedPulse y H) (H / 2) := by
    have hp := ArclengthInverse.rearArclength_add_period hdeltaC hdeltaPer (-(H / 2))
    unfold modelRearArclength
    change RearTrack.rearArclength (modelSteering (periodizedPulse y H)) (-(H / 2)) +
      P = RearTrack.rearArclength (modelSteering (periodizedPulse y H)) (H / 2)
    rw [show P = RearTrack.rearArclength (modelSteering (periodizedPulse y H)) H by rfl]
    convert hp.symm using 1 <;> ring
  refine ⟨rfl, hleft, ?_, ?_⟩
  · rwa [hperiod]
  · rw [← hperiod] at hright
    linarith

end RearCellData

/-- The scalar inequalities which remain after decay, strip, smoothness,
positivity, phase, and rear-cell geometry have been split into derived
certificates.  These are the genuine choices of constants in the matching
estimate. -/
structure QuantitativeConstants : Prop where
  overlap_current : Real.exp (-alpha * H) ≤ 1 / 2
  derivative_nonneg : 0 ≤ D
  beta_pos : 0 < beta
  beta_lt : beta < alpha / 2
  rear_tail_half : Real.exp (-(beta * P)) ≤ 1 / 2
  prior_derivative_nonneg : 0 ≤ DU
  prior_second_nonneg : 0 ≤ DU2
  prior_strip_nonneg : 0 ≤ au
  current_strip_nonneg : 0 ≤ a
  current_strip_lt : a < 1
  prior_strip_lt : au < 1
  isolated_sup : (1 + FrontPeriodization.G au * DU) * au ≤ Km
  isolated_decay : (1 + FrontPeriodization.G au * DU) * CU ≤ CK
  prior_model_sup : (1 + FrontPeriodization.G au * DU) * au ≤ kstar
  rear_derivative_pos : 0 < kd
  current_rear_sup : a / Real.sqrt (1 - a ^ 2) ≤ kstar
  current_rear_deriv : ((1 + FrontPeriodization.G a * D) * a + a) /
      Real.sqrt (1 - a ^ 2) ^ 3 ≤ kd
  prior_deriv_sup : DU * au + FrontPeriodization.lipConst au * (DU ^ 2 * au ^ 2) +
      FrontPeriodization.G au * (DU2 * au) ≤ kd
  isolated_deriv_sup : DU * au + FrontPeriodization.lipConst au * (DU ^ 2 * au ^ 2) +
      FrontPeriodization.G au * (DU2 * au) ≤ Kd
  final_matching : matchConst a C CK CU DU Km Kd au alpha beta B *
      Real.exp (-(beta * H)) ≤ eps0

/-- The profile-specific part of `QuantitativeConstants`; none of these
inequalities improves merely by increasing the separation. -/
structure ProfileConstants : Prop where
  derivative_nonneg : 0 ≤ D
  beta_pos : 0 < beta
  beta_lt : beta < alpha / 2
  prior_derivative_nonneg : 0 ≤ DU
  prior_second_nonneg : 0 ≤ DU2
  prior_strip_nonneg : 0 ≤ au
  current_strip_nonneg : 0 ≤ a
  current_strip_lt : a < 1
  prior_strip_lt : au < 1
  isolated_sup : (1 + FrontPeriodization.G au * DU) * au ≤ Km
  isolated_decay : (1 + FrontPeriodization.G au * DU) * CU ≤ CK
  prior_model_sup : (1 + FrontPeriodization.G au * DU) * au ≤ kstar
  rear_derivative_pos : 0 < kd
  current_rear_sup : a / Real.sqrt (1 - a ^ 2) ≤ kstar
  current_rear_deriv : ((1 + FrontPeriodization.G a * D) * a + a) /
      Real.sqrt (1 - a ^ 2) ^ 3 ≤ kd
  prior_deriv_sup : DU * au + FrontPeriodization.lipConst au * (DU ^ 2 * au ^ 2) +
      FrontPeriodization.G au * (DU2 * au) ≤ kd
  isolated_deriv_sup : DU * au + FrontPeriodization.lipConst au * (DU ^ 2 * au ^ 2) +
      FrontPeriodization.G au * (DU2 * au) ≤ Kd

/-- The three inequalities which follow solely by taking a sufficiently large
separation and its rear period. -/
structure SeparationConstants : Prop where
  overlap_current : Real.exp (-alpha * H) ≤ 1 / 2
  rear_tail_half : Real.exp (-(beta * P)) ≤ 1 / 2
  final_matching : matchConst a C CK CU DU Km Kd au alpha beta B *
      Real.exp (-(beta * H)) ≤ eps0

namespace SeparationConstants

/-- All separation-dependent constants hold beyond one common threshold.
The rear-period estimate `H - 2B ≤ P` converts exponential decay in `H` to
decay in `P`. -/
theorem exists_threshold (halpha : 0 < alpha) (hbeta : 0 < beta)
    (heps : 0 < eps0) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ ∀ H P : ℝ, Hs ≤ H → H - 2 * B ≤ P →
      SeparationConstants (alpha := alpha) (beta := beta) (a := a) (C := C)
        (CK := CK) (CU := CU) (DU := DU) (Km := Km) (Kd := Kd) (au := au)
        (B := B) (eps0 := eps0) (H := H) (P := P) := by
  obtain ⟨Hα, hHα0, hHα⟩ := LargeSeparation.exists_exp_threshold
    (C := (1 : ℝ)) halpha (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Hβ, hHβ0, hHβ⟩ := LargeSeparation.exists_exp_threshold
    (C := Real.exp (2 * beta * B)) hbeta (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Hm, hHm0, hHm⟩ := LargeSeparation.exists_exp_threshold
    (C := matchConst a C CK CU DU Km Kd au alpha beta B) hbeta heps
  refine ⟨max (max Hα Hβ) Hm, ?_, ?_⟩
  · exact hHα0.trans (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro H P hH hPH
    have hα : Hα ≤ H := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hH
    have hβ : Hβ ≤ H := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hH
    have hm : Hm ≤ H := le_trans (le_max_right _ _) hH
    refine ⟨?_, ?_, by simpa [neg_mul] using hHm H hm⟩
    · simpa using hHα H hα
    · have hmono : -beta * P ≤ -beta * (H - 2 * B) :=
        mul_le_mul_of_nonpos_left hPH (neg_nonpos.mpr hbeta.le)
      have hexp := Real.exp_le_exp.mpr hmono
      have htail := hHβ H hβ
      calc
        Real.exp (-(beta * P)) ≤ Real.exp (-beta * (H - 2 * B)) := by
          simpa [neg_mul] using hexp
        _ = Real.exp (2 * beta * B) * Real.exp (-beta * H) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ 1 / 2 := htail

end SeparationConstants

namespace QuantitativeConstants

/-- Recombine the fixed profile choices with the eventual separation
inequalities. -/
theorem of_profile_and_separation
    (p : ProfileConstants (alpha := alpha) (beta := beta) (a := a) (au := au)
      (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (s : SeparationConstants (alpha := alpha) (beta := beta) (a := a) (C := C)
      (CK := CK) (CU := CU) (DU := DU) (Km := Km) (Kd := Kd) (au := au)
      (B := B) (eps0 := eps0) (H := H) (P := P)) :
    QuantitativeConstants (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (kstar := kstar) (kd := kd)
      (eps0 := eps0) (H := H) (P := P) :=
  ⟨s.overlap_current, p.derivative_nonneg, p.beta_pos, p.beta_lt,
    s.rear_tail_half, p.prior_derivative_nonneg, p.prior_second_nonneg,
    p.prior_strip_nonneg, p.current_strip_nonneg, p.current_strip_lt,
    p.prior_strip_lt, p.isolated_sup, p.isolated_decay, p.prior_model_sup,
    p.rear_derivative_pos, p.current_rear_sup, p.current_rear_deriv,
    p.prior_deriv_sup, p.isolated_deriv_sup, s.final_matching⟩

end QuantitativeConstants

/-- All quantitative and analytic fields of `Config` except the common-phase
identity.  The equalities in the result prevent a completion from silently
changing any of the three advertised pulse functions. -/
structure ConfigRemainder (y yu yu' : ℝ → ℝ) where
  complete :
    PulseMassData y → PulseMassData yu →
    (∀ t, y t = Real.sqrt (1 - y t ^ 2) *
      hairpinCurvature yu yu' (modelRearArclength y t)) →
    {c : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0
        kstar kd eps0 H P // c.y = y ∧ c.yu = yu ∧ c.yu' = yu'}

/-- The function-level hypotheses which do not follow merely from choosing
the scalar majorants or increasing the separation.  For the paper hairpins
these are supplied by the common smooth pulse packages (at two consecutive
stages).  Keeping them in one record makes the exact remaining analytic
boundary of the model-orbit construction visible. -/
structure PulsePairAnalyticData (y yd yu yu' yu'' : ℝ → ℝ) : Prop where
  current_nonneg : ∀ s, 0 ≤ y s
  current_decay : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)
  current_deriv : ∀ s, HasDerivAt y (yd s) s
  current_deriv_continuous : Continuous yd
  current_deriv_decay : ∀ s, |yd s| ≤ C * Real.exp (-alpha * |s|)
  current_relative : ∀ s, |yd s| ≤ D * y s
  previous_deriv_continuous : Continuous yu'
  previous_nonneg : ∀ s, 0 ≤ yu s
  previous_decay : ∀ s, yu s ≤ CU * Real.exp (-alpha * |s|)
  previous_relative : ∀ s, |yu' s| ≤ DU * yu s
  previous_deriv : ∀ s, HasDerivAt yu (yu' s) s
  previous_second_deriv : ∀ s, HasDerivAt yu' (yu'' s) s
  previous_second_continuous : Continuous yu''
  previous_second_relative : ∀ s, |yu'' s| ≤ DU2 * yu s
  previous_periodized_strip : ∀ u, (∑' m : ℤ, yu (u - m * P)) ≤ au

namespace ConfigRemainder

/-- Assemble every non-phase, non-mass field of `ModelOrbitDefect.Config`
from the paper-shaped certificates.  In particular, the current periodized
strip, the three rear-cell inequalities, positivity, all fixed-profile scalar
bounds, and all large-separation scalar bounds are no longer fields of an
opaque completion function. -/
def of_certificates {y yd yu yu' yu'' : ℝ → ℝ} {b : ℝ}
    (analytic : PulsePairAnalyticData (alpha := alpha) (au := au)
      (C := C) (CU := CU) (DU := DU) (DU2 := DU2) (D := D) (P := P)
      y yd yu yu' yu'')
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (separation : SeparationConstants (alpha := alpha) (beta := beta) (a := a)
      (C := C) (CK := CK) (CU := CU) (DU := DU) (Km := Km) (Kd := Kd)
      (au := au) (B := B) (eps0 := eps0) (H := H) (P := P))
    (strip : PeriodizedStripData y alpha C H b)
    (strip_budget : b + 4 * C * Real.exp (-(alpha / 2) * H) ≤ a)
    (positive : CurvaturePositivityData yu yu' P)
    (rear : RearCellData y H P B) :
    ConfigRemainder (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0)
      (kstar := kstar) (kd := kd) (eps0 := eps0) (H := H) (P := P)
      y yu yu' where
  complete currentMass previousMass phase :=
    ⟨{
      y := y
      yd := yd
      yu := yu
      yu' := yu'
      yu'' := yu''
      ha := strip.alpha_pos
      hy0 := analytic.current_nonneg
      hyb := analytic.current_decay
      hH := strip.period_pos
      hq2 := separation.overlap_current
      hyderiv := analytic.current_deriv
      hydc := analytic.current_deriv_continuous
      hydb := analytic.current_deriv_decay
      hD0 := profile.derivative_nonneg
      hrelD := analytic.current_relative
      ha0 := profile.current_strip_nonneg
      ha1 := profile.current_strip_lt
      hYa' := PeriodizedStripData.periodized_abs_le strip strip_budget
      hid := phase
      hbeta0 := profile.beta_pos
      hbeta := profile.beta_lt
      hPdef' := rear.period_def
      hpB' := rear.left_endpoint
      hqB' := rear.right_endpoint
      hhalf := separation.rear_tail_half
      hyu'c := analytic.previous_deriv_continuous
      hyu0 := analytic.previous_nonneg
      hyub := analytic.previous_decay
      hDU := profile.prior_derivative_nonneg
      hyu'b := analytic.previous_relative
      hau0 := profile.prior_strip_nonneg
      hau1 := profile.prior_strip_lt
      hYau := analytic.previous_periodized_strip
      hyuderiv := analytic.previous_deriv
      hyu''deriv := analytic.previous_second_deriv
      hyu''c := analytic.previous_second_continuous
      hDU2 := profile.prior_second_nonneg
      hyu''b := analytic.previous_second_relative
      hyuint := previousMass.integrable
      hmassu := previousMass.mass_eq_pi
      hcurvNonnegU := CurvaturePositivityData.config_branch positive
      hkstarU := profile.prior_model_sup
      hKmU := profile.isolated_sup
      hCKU := profile.isolated_decay
      hPH := rear.period_lower
      hyint := currentMass.integrable
      hmass := currentMass.mass_eq_pi
      hkd := profile.rear_derivative_pos
      hkstar := profile.current_rear_sup
      hkdge := profile.current_rear_deriv
      hkdU := profile.prior_deriv_sup
      hKdU := profile.isolated_deriv_sup
      heps0 := separation.final_matching }, rfl, rfl, rfl⟩

/-- Once the fixed profile constants have been selected, one common threshold
of the front separation discharges every remaining scalar smallness condition.
The hypotheses after `H ≥ Hs` are precisely the function-level, strip,
positivity, and rear-cell certificates whose construction depends on the two
chosen consecutive hairpins. -/
theorem exists_separation_threshold
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ ∀ (H P b : ℝ) (y yd yu yu' yu'' : ℝ → ℝ),
      Hs ≤ H →
      PulsePairAnalyticData (alpha := alpha) (au := au)
        (C := C) (CU := CU) (DU := DU) (DU2 := DU2) (D := D) (P := P)
        y yd yu yu' yu'' →
      PeriodizedStripData y alpha C H b →
      b + 4 * C * Real.exp (-(alpha / 2) * H) ≤ a →
      CurvaturePositivityData yu yu' P → RearCellData y H P B →
      Nonempty (ConfigRemainder (alpha := alpha) (beta := beta) (a := a)
        (au := au) (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2)
        (D := D) (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0)
        (kstar := kstar) (kd := kd) (eps0 := eps0) (H := H) (P := P)
        y yu yu') := by
  have halpha : 0 < alpha := by
    linarith [profile.beta_pos, profile.beta_lt]
  obtain ⟨Hs, hHs0, hHs⟩ := SeparationConstants.exists_threshold
    (B := B) (a := a) (C := C) (CK := CK) (CU := CU) (DU := DU)
    (Km := Km) (Kd := Kd) (au := au) halpha profile.beta_pos heps
  refine ⟨Hs, hHs0, ?_⟩
  intro H P b y yd yu yu' yu'' hH analytic strip hbudget positive rear
  exact ⟨of_certificates analytic profile (hHs H P hH rear.period_lower)
    strip hbudget positive rear⟩

end ConfigRemainder

/-- The geometric data which turn a configuration remainder into the paper's
hairpin configuration.  Every field here is an actual hypothesis appearing in
the normalized hairpin construction. -/
structure PaperHairpinData (y yu yu' : ℝ → ℝ)
    extends ConfigRemainder (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0) (kstar := kstar)
      (kd := kd) (eps0 := eps0) (H := H) (P := P) y yu yu' where
  /-- normalized horizontal coordinate of the isolated hairpin -/
  x : ℝ → ℝ
  continuous_y : Continuous y
  x_zero : x 0 = 0
  x_deriv : ∀ s, HasDerivAt x (Real.sqrt (1 - y s ^ 2)) s
  /-- isolated curvature identity before rear-coordinate identification -/
  local_phase : ∀ s, y s = Real.sqrt (1 - y s ^ 2) * hairpinCurvature yu yu' (x s)
  /-- integrability and steering mass of the current pulse -/
  current_mass : PulseMassData y
  /-- integrability and steering mass of the previous-model pulse -/
  previous_mass : PulseMassData yu

namespace PaperHairpinData

/-- Witness-preserving form of the consecutive configuration constructor.
Unlike the Config projection below, this theorem retains the actual
`PaperHairpinData` object needed by `ConfiguredModelSequence.config_from_paper`. -/
theorem exists_threshold_toPaperHairpinData_of_consecutive
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧
      ∀ (Hnext Hcurr b : ℝ) (y yd yu yu' yu'' x : ℝ → ℝ),
      Hs ≤ Hnext →
      PulsePairAnalyticData (alpha := alpha) (au := au)
        (C := C) (CU := CU) (DU := DU) (DU2 := DU2) (D := D) (P := Hcurr)
        y yd yu yu' yu'' →
      PeriodizedStripData y alpha C Hnext b →
      b + 4 * C * Real.exp (-(alpha / 2) * Hnext) ≤ a →
      CurvaturePositivityData yu yu' Hcurr →
      modelRearArclength (periodizedPulse y Hnext) Hnext = Hcurr →
      modelRearArclength (periodizedPulse y Hnext) (-(Hnext / 2)) ≤
        -(Hnext / 2) + B →
      Hnext / 2 - B ≤
        modelRearArclength (periodizedPulse y Hnext) (-(Hnext / 2)) + Hcurr →
      Hnext - 2 * B ≤ Hcurr →
      Continuous y → x 0 = 0 →
      (∀ s, HasDerivAt x (Real.sqrt (1 - y s ^ 2)) s) →
      (∀ s, y s = Real.sqrt (1 - y s ^ 2) * hairpinCurvature yu yu' (x s)) →
      PulseMassData y → PulseMassData yu →
      Nonempty (PaperHairpinData (alpha := alpha) (beta := beta) (a := a)
        (au := au) (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2)
        (D := D) (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0)
        (kstar := kstar) (kd := kd) (eps0 := eps0) (H := Hnext)
        (P := Hcurr) y yu yu') := by
  obtain ⟨Hs, hHs0, hassemble⟩ := ConfigRemainder.exists_separation_threshold
    (C := C) (B := B) (theta0 := theta0) profile heps
  refine ⟨Hs, hHs0, ?_⟩
  intro Hnext Hcurr b y yd yu yu' yu'' x hH analytic strip hbudget positive
    hrec hleft hright hlower hyc hx0 hxd hphase hymass hyumass
  let rear : RearCellData y Hnext Hcurr B :=
    ⟨hrec, hleft, hright, hlower⟩
  obtain ⟨remainder⟩ := hassemble Hnext Hcurr b y yd yu yu' yu'' hH analytic
    strip hbudget positive rear
  exact
    ⟨{ remainder with
      x := x
      continuous_y := hyc
      x_zero := hx0
      x_deriv := hxd
      local_phase := hphase
      current_mass := hymass
      previous_mass := hyumass }⟩

/-- The recurrence-indexed form of the paper configuration construction.
Here `Hnext` is the separation of the `(n+1)`-st two-cap model and `Hcurr` is
the separation of the `n`-th model.  The recurrence

`rearPeriod(y,Hnext) = Hcurr`

is used directly as `Config.hPdef'`.  Beyond one threshold all scalar
smallness fields are automatic.  The remaining hypotheses are exactly the
two-pulse analytic/coherence facts: the periodized strips and positivity,
the centered rear-cell endpoints, and the normalized local phase identity.
The result is the actual output of `PaperHairpinData.toConfig`, not merely an
opaque `ConfigRemainder`. -/
theorem exists_threshold_toConfig_of_consecutive
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧
      ∀ (Hnext Hcurr b : ℝ) (y yd yu yu' yu'' x : ℝ → ℝ),
      Hs ≤ Hnext →
      PulsePairAnalyticData (alpha := alpha) (au := au)
        (C := C) (CU := CU) (DU := DU) (DU2 := DU2) (D := D) (P := Hcurr)
        y yd yu yu' yu'' →
      PeriodizedStripData y alpha C Hnext b →
      b + 4 * C * Real.exp (-(alpha / 2) * Hnext) ≤ a →
      CurvaturePositivityData yu yu' Hcurr →
      modelRearArclength (periodizedPulse y Hnext) Hnext = Hcurr →
      modelRearArclength (periodizedPulse y Hnext) (-(Hnext / 2)) ≤
        -(Hnext / 2) + B →
      Hnext / 2 - B ≤
        modelRearArclength (periodizedPulse y Hnext) (-(Hnext / 2)) + Hcurr →
      Hnext - 2 * B ≤ Hcurr →
      Continuous y → x 0 = 0 →
      (∀ s, HasDerivAt x (Real.sqrt (1 - y s ^ 2)) s) →
      (∀ s, y s = Real.sqrt (1 - y s ^ 2) * hairpinCurvature yu yu' (x s)) →
      PulseMassData y → PulseMassData yu →
      Nonempty {c : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D
          Km Kd B theta0 kstar kd eps0 Hnext Hcurr //
        c.y = y ∧ c.yu = yu ∧ c.yu' = yu'} := by
  obtain ⟨Hs, hHs0, hassemble⟩ := ConfigRemainder.exists_separation_threshold
    (C := C) (B := B) (theta0 := theta0) profile heps
  refine ⟨Hs, hHs0, ?_⟩
  intro Hnext Hcurr b y yd yu yu' yu'' x hH analytic strip hbudget positive
    hrec hleft hright hlower hyc hx0 hxd hphase hymass hyumass
  let rear : RearCellData y Hnext Hcurr B :=
    ⟨hrec, hleft, hright, hlower⟩
  obtain ⟨remainder⟩ := hassemble Hnext Hcurr b y yd yu yu' yu'' hH analytic
    strip hbudget positive rear
  exact ⟨remainder.complete hymass hyumass
    (ModelOrbitHairpinBridge.phase_identity_modelRear hyc hx0 hxd hphase)⟩

/-- Construct the full defect configuration.  The common-phase field is
derived, while every other field is supplied by `ConfigRemainder`. -/
def toConfig {y yu yu' : ℝ → ℝ}
    (d : PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0) (kstar := kstar)
      (kd := kd) (eps0 := eps0) (H := H) (P := P) y yu yu') :
    {c : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0
        kstar kd eps0 H P // c.y = y ∧ c.yu = yu ∧ c.yu' = yu'} :=
  d.complete d.current_mass d.previous_mass (ModelOrbitHairpinBridge.phase_identity_modelRear
    d.continuous_y d.x_zero d.x_deriv d.local_phase)

theorem toConfig_y {y yu yu' : ℝ → ℝ}
    (d : PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0) (kstar := kstar)
      (kd := kd) (eps0 := eps0) (H := H) (P := P) y yu yu') :
    d.toConfig.1.y = y :=
  d.toConfig.2.1

theorem toConfig_yu {y yu yu' : ℝ → ℝ}
    (d : PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0) (kstar := kstar)
      (kd := kd) (eps0 := eps0) (H := H) (P := P) y yu yu') :
    d.toConfig.1.yu = yu :=
  d.toConfig.2.2.1

theorem toConfig_yu' {y yu yu' : ℝ → ℝ}
    (d : PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0) (kstar := kstar)
      (kd := kd) (eps0 := eps0) (H := H) (P := P) y yu yu') :
    d.toConfig.1.yu' = yu' :=
  d.toConfig.2.2.2

/-- The completed configuration carries the current pulse's derived
integrability witness. -/
theorem toConfig_y_integrable {y yu yu' : ℝ → ℝ}
    (d : PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0) (kstar := kstar)
      (kd := kd) (eps0 := eps0) (H := H) (P := P) y yu yu') :
    MeasureTheory.Integrable y := by
  rw [← d.toConfig_y]
  exact d.toConfig.1.hyint

/-- The completed configuration carries the current pulse's exact mass. -/
theorem toConfig_y_mass {y yu yu' : ℝ → ℝ}
    (d : PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0) (kstar := kstar)
      (kd := kd) (eps0 := eps0) (H := H) (P := P) y yu yu') :
    (∫ s : ℝ, y s) = Real.pi := by
  rw [← d.toConfig_y]
  exact d.toConfig.1.hmass

/-- The completed configuration carries the previous pulse's derived
integrability witness and exact mass together. -/
theorem toConfig_yu_massData {y yu yu' : ℝ → ℝ}
    (d : PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0) (kstar := kstar)
      (kd := kd) (eps0 := eps0) (H := H) (P := P) y yu yu') :
    PulseMassData yu := by
  constructor
  · rw [← d.toConfig_yu]
    exact d.toConfig.1.hyuint
  · rw [← d.toConfig_yu]
    exact d.toConfig.1.hmassu

end PaperHairpinData

end PaperHairpinConfig
