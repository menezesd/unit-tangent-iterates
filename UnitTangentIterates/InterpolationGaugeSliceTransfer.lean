import Mathlib
import UnitTangentIterates.InterpolationPathDist
import UnitTangentIterates.ExplicitNormalizedInterpolation

/-!
# Transfer from the raw interpolation to its normal gauge

The normal path constructed in `InterpolationPathDist.exists_normalPath_interp`
uses `pathCurve`: its slice is the raw curvature interpolation precomposed with
the (generally nonaffine) gauge flow.  This file records exactly which of the
raw normalized data survive that precomposition.

Periodicity and pointwise curvature bounds survive.  Spatial speed is multiplied
by the absolute gauge derivative.  Thus constant speed cannot be transferred
without an additional constant-speed (in particular, affine-slice) hypothesis
on the gauge flow.
-/

open Function

namespace InterpolationGaugeSliceTransfer

open CurvatureInterpolation InterpolationPathDist PathMetricCircle

/-- The exact slice used by the normal-gauge construction.  This is deliberately
not identified with the raw normalized slice `s ↦ X_t (2Lu)`. -/
theorem pathCurve_slice (k0 k1 : ℝ → ℝ) (theta0 L : ℝ)
    (Phi : ℝ → ℝ → ℝ) (t u : ℝ) :
    pathCurve k0 k1 theta0 L Phi t u =
      interpCurve (kappaInterp k0 k1 (B t)) theta0 L (Phi (B t) u) :=
  rfl

/-- Closing transfers through a gauge marking which transports one normalized
period to one full arclength period. -/
theorem periodic_pathCurve_of_translation (k0 k1 : ℝ → ℝ) (theta0 L : ℝ)
    (Phi : ℝ → ℝ → ℝ) (t : ℝ)
    (hraw : Periodic (interpCurve (kappaInterp k0 k1 (B t)) theta0 L) (2 * L))
    (hPhi : ∀ u, Phi (B t) (u + 1) = Phi (B t) u + 2 * L) :
    Periodic (pathCurve k0 k1 theta0 L Phi t) 1 := by
  intro u
  rw [pathCurve_slice, pathCurve_slice, hPhi]
  exact hraw (Phi (B t) u)

/-- The spatial derivative of the gauge slice.  Its scalar factor is the
spatial derivative of the gauge, not the fixed raw normalization factor `2L`. -/
theorem hasDerivAt_pathCurve_space (k0 k1 : ℝ → ℝ) (theta0 L : ℝ)
    (Phi : ℝ → ℝ → ℝ) (t u phiU : ℝ)
    (hk : Continuous (kappaInterp k0 k1 (B t)))
    (hPhi : HasDerivAt (Phi (B t)) phiU u) :
    HasDerivAt (pathCurve k0 k1 theta0 L Phi t)
      (phiU • tau (tangentAngle (kappaInterp k0 k1 (B t)) theta0
        (Phi (B t) u))) u := by
  exact (hasDerivAt_interpCurve (θ₀ := theta0) (L := L) hk (Phi (B t) u)).scomp u hPhi

/-- Consequently, the speed of a gauge slice is exactly the absolute gauge
speed.  This is the explicit extra datum needed by any constant-speed API. -/
theorem norm_deriv_pathCurve_eq_abs (k0 k1 : ℝ → ℝ) (theta0 L : ℝ)
    (Phi : ℝ → ℝ → ℝ) (t u phiU : ℝ)
    (hk : Continuous (kappaInterp k0 k1 (B t)))
    (hPhi : HasDerivAt (Phi (B t)) phiU u) :
    ‖deriv (pathCurve k0 k1 theta0 L Phi t) u‖ = |phiU| := by
  rw [(hasDerivAt_pathCurve_space k0 k1 theta0 L Phi t u phiU hk hPhi).deriv]
  simp [norm_tau, Real.norm_eq_abs]

/-- Pointwise curvature bounds are intrinsic and therefore remain available at
the point selected by the gauge marking. -/
theorem gauge_sampled_curvature_bounds (k0 k1 : ℝ → ℝ) (L : ℝ)
    (Phi : ℝ → ℝ → ℝ) (t u klo khi : ℝ)
    (hlow : ∀ s, klo ≤ kappaInterp k0 k1 (B t) s)
    (hhigh : ∀ s, kappaInterp k0 k1 (B t) s ≤ khi) :
    klo ≤ kappaInterp k0 k1 (B t) (Phi (B t) u) ∧
      kappaInterp k0 k1 (B t) (Phi (B t) u) ≤ khi :=
  ⟨hlow _, hhigh _⟩

/-- A constant-speed hypothesis for the normal gauge is precisely a hypothesis
on the spatial derivative of `Phi`; it is not a consequence of raw unit speed. -/
theorem gauge_constant_speed_of_flow_derivative (k0 k1 : ℝ → ℝ) (theta0 L : ℝ)
    (Phi : ℝ → ℝ → ℝ) (t P : ℝ)
    (hk : Continuous (kappaInterp k0 k1 (B t)))
    (phiU : ℝ → ℝ)
    (hPhi : ∀ u, HasDerivAt (Phi (B t)) (phiU u) u)
    (hspeed : ∀ u, |phiU u| = P) :
    ∀ u, ‖deriv (pathCurve k0 k1 theta0 L Phi t) u‖ = P := by
  intro u
  rw [norm_deriv_pathCurve_eq_abs k0 k1 theta0 L Phi t u (phiU u) hk (hPhi u)]
  exact hspeed u

end InterpolationGaugeSliceTransfer
