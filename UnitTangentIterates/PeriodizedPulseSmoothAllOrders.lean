import UnitTangentIterates.PeriodizedPulseSmooth
import UnitTangentIterates.PeriodizationFiniteDerivativeChain

/-!
# Smooth periodizations from an all-orders derivative chain

The finite-order bootstrap in `PeriodizedPulseSmooth` applies uniformly at
every order.  This module packages that observation for the all-orders pulse
certificate constructed from the paper's translator profile.
-/

noncomputable section

open Real
open scoped ContDiff

namespace PeriodizedPulseSmoothAllOrders

open ModelOrbitDefect PeriodizationFiniteDerivativeChain

/-- Every member of an exponentially localized derivative chain has a
periodization of every finite differentiability order. -/
theorem contDiff_nat_periodizedPulse
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    {C : ℕ → ℝ} {alpha P : ℝ} (halpha : 0 < alpha) (hP : 0 < P)
    (hb : ∀ n x, |zD n x| ≤ C n * Real.exp (-alpha * |x|)) :
    ∀ n r : ℕ, ContDiff ℝ (n : ℕ) (periodizedPulse (zD r) P)
  | 0, r => by
      apply PeriodizedPulseSmooth.contDiff_zero_periodizedPulse halpha hP
      · exact continuous_iff_continuousAt.2 fun x => (hz.deriv r x).continuousAt
      · exact hb r
  | n + 1, r => by
      have hb0 : ∀ x, |zD r x| ≤
          max (C r) (C (r + 1)) * Real.exp (-alpha * |x|) := by
        intro x
        exact (hb r x).trans (mul_le_mul_of_nonneg_right
          (le_max_left _ _) (Real.exp_pos _).le)
      have hb1 : ∀ x, |zD (r + 1) x| ≤
          max (C r) (C (r + 1)) * Real.exp (-alpha * |x|) := by
        intro x
        exact (hb (r + 1) x).trans (mul_le_mul_of_nonneg_right
          (le_max_right _ _) (Real.exp_pos _).le)
      exact PeriodizedPulseSmooth.contDiff_succ_periodizedPulse
        halpha hP (hz.deriv r) hb0 hb1
          (contDiff_nat_periodizedPulse hz halpha hP hb n (r + 1))

/-- Every periodized derivative in the chain is smooth. -/
theorem contDiff_top_periodizedPulse
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    {C : ℕ → ℝ} {alpha P : ℝ} (halpha : 0 < alpha) (hP : 0 < P)
    (hb : ∀ n x, |zD n x| ≤ C n * Real.exp (-alpha * |x|))
    (r : ℕ) :
    ContDiff ℝ ∞ (periodizedPulse (zD r) P) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_nat_periodizedPulse hz halpha hP hb n r

/-- The nonlinear model curvature is smooth once the periodized pulse remains
strictly inside the steering strip. -/
theorem contDiff_top_modelCurvature
    {zD : ℕ → ℝ → ℝ} (hz : DerivativeChain zD)
    {C : ℕ → ℝ} {alpha P : ℝ} (halpha : 0 < alpha) (hP : 0 < P)
    (hb : ∀ n x, |zD n x| ≤ C n * Real.exp (-alpha * |x|))
    (hstrip : ∀ s, |periodizedPulse (zD 0) P s| < 1) :
    ContDiff ℝ ∞ (modelCurvature (zD 0) (zD 1) P) :=
  ModelCurvatureSmooth.contDiff_top_modelCurvature
    (contDiff_top_periodizedPulse hz halpha hP hb 0)
    (contDiff_top_periodizedPulse hz halpha hP hb 1) hstrip

end PeriodizedPulseSmoothAllOrders
