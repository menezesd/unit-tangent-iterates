import UnitTangentIterates.ShiftedCurvatureJetMajorant
import UnitTangentIterates.CanonicalTranslatorLocalPhase

/-!
# The canonical consecutive hairpin pulse pair

The preceding isolated pulse is not independent data: it is the current pulse
translated by the canonical translator phase.  This file specializes the
generic shifted-jet adapter to `ConsecutiveData`, keeping the TeX quantifier
order (one fixed profile, then consecutive separations).
-/


open ShiftedCurvatureJetMajorant

namespace PaperHairpinQuantitativeData.ConsecutiveData

/-- The preceding pulse is definitionally the phase translate of the current
pulse of the same canonical profile. -/
theorem previousPulse_eq_shift
    {f theta x g : ℝ → ℝ} :
    previousPulse f theta x g =
      shift (phase f theta g) (currentPulse f theta x) := by
  rfl

/-- The named preceding-pulse derivative is the same translate of the current
pulse derivative witness. -/
theorem previousPulseDeriv_eq_shift
    {f theta g yp : ℝ → ℝ} :
    previousPulseDeriv f theta g yp = shift (phase f theta g) yp := by
  rfl

/-- A finite jet for the current canonical pulse supplies the complete
two-pulse analytic package for the current/preceding same-profile pair. -/
theorem pulsePairAnalyticData_of_pulseJet
    {f theta x g gp yp y2 y3 y4 : ℝ → ℝ}
    {M Delta beta Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {D0 D1 D2 D3 D4 alpha C CU D DU DU2 au P : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta Cq Ht Pfun Pp)
    (hjet : PulseJet4 (currentPulse f theta x) yp y2 y3 y4)
    (hrel : PulseJetRelative (currentPulse f theta x) yp y2 y3 y4
      D0 D1 D2 D3 D4)
    (halpha : 0 ≤ alpha)
    (hdec0 : ∀ s, |currentPulse f theta x s| ≤ C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |phase f theta g|) ≤ CU)
    (hD : D1 ≤ D) (hDU : D1 ≤ DU) (hDU2 : D2 ≤ DU2)
    (hstrip : ∀ u, (∑' m : ℤ,
      shift (phase f theta g) (currentPulse f theta x) (u - m * P)) ≤ au) :
    PaperHairpinConfig.PulsePairAnalyticData
      (alpha := alpha) (au := au) (C := C) (CU := CU)
      (DU := DU) (DU2 := DU2) (D := D) (P := P)
      (currentPulse f theta x) yp (previousPulse f theta x g)
      (previousPulseDeriv f theta g yp) (shift (phase f theta g) y2) := by
  simpa [previousPulse_eq_shift, previousPulseDeriv_eq_shift] using
    (pulsePairAnalyticData_of_shift hjet hrel halpha hdec0 hdec1 hCU
      hD hDU hDU2 hstrip)

end PaperHairpinQuantitativeData.ConsecutiveData

