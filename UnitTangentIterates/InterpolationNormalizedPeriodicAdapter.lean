import Mathlib
import UnitTangentIterates.InterpolationSelectedRearClosing
import UnitTangentIterates.SelInvPathTurningC2
import UnitTangentIterates.SelInvPathTurningFundamentalC2

/-!
# Normalized periodic data for the selected-inverse comparison

This is the normalized-parameter adapter used between interpolation closing
and `SelInvRearFamilySupFundamentalC2`.  For a smooth normal path with closed
slices and constant speed, the canonical spatial derivatives are periodic and
the turning integral is `2π` under the interpolation curvature bounds.  The
normal-rate basepoint condition remains explicit: it is a marking condition,
not a consequence of closing.
-/

noncomputable section

open Function Set Complex MeasureTheory MarkedSpace PathMetric

namespace InterpolationNormalizedPeriodicAdapter

open RearOwnHigherRegularity FrontFromPath SelInvPathTurningFundamentalC2
  SelInvPathRegularityC2 SelInvPathPerimC2

/-- **The normalized periodic hypothesis block.**  With
`V = pathVel X`, `A = pathAcc X`, and `P = pathPerim X`, this supplies the
spatial derivative, constant-speed, periodicity, and turning inputs of the
sup-fundamental selected-rear comparison. -/
theorem normalized_periodic_inputs
    {p q : Data} (Gamma : NormalPath p q) {kh kminP : ℝ}
    (hX3 : ContDiff ℝ (3 : ℕ) (uncurry Gamma.X))
    (hconst : ∀ t u, ‖pathVel Gamma.X t u‖ = ‖pathVel Gamma.X t 0‖)
    (hXper : ∀ t, Periodic (Gamma.X t) 1)
    (hPpos : ∀ t, 0 < pathPerim Gamma.X t)
    (hkminP : 0 < kminP)
    (hlow : ∀ t s, kminP ≤ curvOfPath (pathVel Gamma.X) (pathAcc Gamma.X)
      (pathPerim Gamma.X) t s)
    (hhigh : ∀ t s, curvOfPath (pathVel Gamma.X) (pathAcc Gamma.X)
      (pathPerim Gamma.X) t s ≤ kh)
    (hshort : ∀ t, kh * pathPerim Gamma.X t < 4 * Real.pi)
    (hmark : ∀ t, Gamma.eta t 0 = 0) :
    (∀ t u, HasDerivAt (Gamma.X t) (pathVel Gamma.X t u) u) ∧
      (∀ t u, HasDerivAt (pathVel Gamma.X t) (pathAcc Gamma.X t u) u) ∧
      (∀ t, Continuous (pathAcc Gamma.X t)) ∧
      (∀ t u, ‖pathVel Gamma.X t u‖ = pathPerim Gamma.X t) ∧
      (∀ t, Periodic (Gamma.X t) 1) ∧
      (∀ t, Periodic (pathVel Gamma.X t) 1) ∧
      (∀ t, Periodic (pathAcc Gamma.X t) 1) ∧
      (∀ t, (∫ u in (0 : ℝ)..1,
        ((starRingEnd ℂ) (pathVel Gamma.X t u) * pathAcc Gamma.X t u).im
          / pathPerim Gamma.X t ^ 2) = 2 * Real.pi) ∧
      (∀ t, Gamma.eta t 0 = 0) := by
  have hXdiff : Differentiable ℝ (uncurry Gamma.X) := hX3.differentiable (by norm_num)
  have hV2 : ContDiff ℝ (2 : ℕ) (uncurry (pathVel Gamma.X)) :=
    contDiff_partialArc_self hX3
  have hVdiff : Differentiable ℝ (uncurry (pathVel Gamma.X)) :=
    hV2.differentiable (by norm_num)
  have hA1 : ContDiff ℝ (1 : ℕ) (uncurry (pathAcc Gamma.X)) :=
    contDiff_partialArc_self hV2
  have hXd : ∀ t u, HasDerivAt (Gamma.X t) (pathVel Gamma.X t u) u :=
    hasDerivAt_partialArc hXdiff
  have hAd : ∀ t u, HasDerivAt (pathVel Gamma.X t) (pathAcc Gamma.X t u) u :=
    hasDerivAt_partialArc hVdiff
  have hAc : ∀ t, Continuous (pathAcc Gamma.X t) := fun t =>
    hA1.continuous.comp (continuous_const.prodMk continuous_id)
  have hVc : ∀ t, Continuous (pathVel Gamma.X t) := fun t =>
    hV2.continuous.comp (continuous_const.prodMk continuous_id)
  have hspeed : ∀ t u, ‖pathVel Gamma.X t u‖ = pathPerim Gamma.X t := by
    intro t u
    rw [hconst t u]
    rfl
  have hVper : ∀ t, Periodic (pathVel Gamma.X t) 1 :=
    periodic_partialArc hXdiff hXper
  have hAper : ∀ t, Periodic (pathAcc Gamma.X t) 1 :=
    periodic_partialArc hVdiff hVper
  have hturn : ∀ t, (∫ u in (0 : ℝ)..1,
      ((starRingEnd ℂ) (pathVel Gamma.X t u) * pathAcc Gamma.X t u).im
        / pathPerim Gamma.X t ^ 2) = 2 * Real.pi := fun t =>
    SelInvPathTurningC2.turning_of_slice
      (kh := kh) (P := pathPerim Gamma.X) (hAd t) (hVper t) (hAper t)
      (hVc t) (hAc t) (hspeed t) (hPpos t) hkminP (hlow t) (hhigh t) (hshort t)
  exact ⟨hXd, hAd, hAc, hspeed, hXper, hVper, hAper, hturn, hmark⟩

end InterpolationNormalizedPeriodicAdapter

