import UnitTangentIterates.CanonicalConsecutiveConfig
import UnitTangentIterates.CanonicalConsecutiveInterior

/-! # Derived geometric certificates for canonical consecutive hairpins -/


open ShiftedCurvatureJetMajorant
open PaperHairpinQuantitativeData
open PaperHairpinQuantitativeData.ConsecutiveData

namespace PaperHairpinConfig

/-- A current-pulse strip at the preceding period automatically gives the
periodized strip of the phase-translated preceding pulse. -/
theorem previous_strip_of_current_strip
    {f theta x g : ℝ → ℝ} {alpha C P b au : ℝ}
    (hstrip : PeriodizedStripData (ConsecutiveData.currentPulse f theta x)
      alpha C P b)
    (hbudget : b + 4 * C * Real.exp (-(alpha / 2) * P) ≤ au) :
    ∀ u, (∑' m : ℤ, ConsecutiveData.previousPulse f theta x g (u - m * P)) ≤ au := by
  have hcurrent : ∀ u,
      ModelOrbitDefect.periodizedPulse (ConsecutiveData.currentPulse f theta x) P u ≤ au := by
    intro u
    exact le_trans (le_abs_self _)
      (PeriodizedStripData.periodized_abs_le hstrip hbudget u)
  simpa [ConsecutiveData.previousPulse_eq_shift] using
    (previous_periodized_strip_of_current
      (q := ConsecutiveData.phase f theta g) hcurrent)

/-- Tail localization and the exact quantitative mass construct the complete
rear-cell record when the preceding separation is defined to be the actual
rear period of the current two-cap model. -/
theorem rearCell_of_quantitative_tail
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {C alpha b H B : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta Cq Ht Pfun Pp)
    (halpha : 0 < alpha) (hb1 : b < 1)
    (hyb : ∀ s, ConsecutiveData.currentPulse f theta x s ≤
      C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, ConsecutiveData.currentPulse f theta x s ≤ b)
    (hH : PerimeterHairpinPulse.threshold alpha C b ≤ H)
    (hB : (1 + b) / 2 * Real.pi ≤ B)
    (hfpos : ∀ t ∈ Set.Ioo (0:ℝ) Real.pi, 0 < f t) :
    RearCellData (ConsecutiveData.currentPulse f theta x) H
      (ModelOrbitDefect.modelRearArclength
        (ModelOrbitDefect.periodizedPulse (ConsecutiveData.currentPulse f theta x) H) H) B := by
  apply RearCellData.of_tail_bounds halpha hb1
    (c.quantitative.smooth_pulse 0).continuous (c.currentPulse_nonneg_interior hfpos)
    hyb hsup hH
  simpa [c.quantitative.mass] using hB

end PaperHairpinConfig

