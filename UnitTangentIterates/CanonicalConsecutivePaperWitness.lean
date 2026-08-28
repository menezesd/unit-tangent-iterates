import UnitTangentIterates.CanonicalConsecutiveConfig
import UnitTangentIterates.CanonicalConsecutiveInterior

/-! # Witness-preserving canonical consecutive configuration -/


open scoped ContDiff
open ShiftedCurvatureJetMajorant PaperHairpinQuantitativeData
open PaperHairpinQuantitativeData.ConsecutiveData

namespace PaperHairpinConfig.PaperHairpinData

/-- Canonical same-profile specialization of the witness-preserving paper
constructor.  All analytic/coherence fields are discharged; only the
period-dependent geometric certificates remain. -/
theorem exists_threshold_toPaperHairpinData_of_canonical_consecutive
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta0 Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta0 Cq Ht Pfun Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiffOn ℝ ∞ f (Set.Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Set.Ioo (0:ℝ) Real.pi, 0 < f t)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 ≤ alpha)
    (hdec0 : ∀ s, |currentPulse f theta x s| ≤ C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ ∀ Hnext Hcurr b : ℝ,
      Hs ≤ Hnext →
      (∀ u, (∑' m : ℤ, shift (phase f theta g) (currentPulse f theta x)
        (u - m * Hcurr)) ≤ au) →
      PeriodizedStripData (currentPulse f theta x) alpha C Hnext b →
      b + 4 * C * Real.exp (-(alpha / 2) * Hnext) ≤ a →
      CurvaturePositivityData (previousPulse f theta x g)
        (previousPulseDeriv f theta g yp) Hcurr →
      RearCellData (currentPulse f theta x) Hnext Hcurr B →
      Nonempty (PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
        (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
        (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0)
        (kstar := kstar) (kd := kd) (eps0 := eps0) (H := Hnext)
        (P := Hcurr) (currentPulse f theta x) (previousPulse f theta x g)
        (previousPulseDeriv f theta g yp)) := by
  obtain ⟨Hs, hHs0, hbuild⟩ :=
    exists_threshold_toPaperHairpinData_of_consecutive
      (C := C) (B := B) (theta0 := theta0) profile heps
  refine ⟨Hs, hHs0, ?_⟩
  intro Hnext Hcurr b hH hpriorStrip hstrip hbudget hpositive hrear
  obtain ⟨y2, hanalytic⟩ := c.pulsePairAnalyticData_of_quantitative
    (c.currentPulse_nonneg_interior hfpos) halpha hdec0 hdec1 hCU hD hDU hDU2 hpriorStrip
  exact hbuild Hnext Hcurr b (currentPulse f theta x) yp
    (previousPulse f theta x g) (previousPulseDeriv f theta g yp)
    (shift (phase f theta g) y2) x hH hanalytic hstrip hbudget hpositive
    hrear.period_def hrear.left_endpoint hrear.right_endpoint hrear.period_lower
    (c.quantitative.smooth_pulse 0).continuous d.x_zero (c.current_x_deriv_interior hf hfpos)
    (CanonicalTranslatorLocalPhase.canonical_local_phase c d)
    c.currentPulse_massData c.previousPulse_massData

end PaperHairpinConfig.PaperHairpinData


