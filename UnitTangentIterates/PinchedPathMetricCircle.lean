import Mathlib
import UnitTangentIterates.PinchedPathMetric
import UnitTangentIterates.SelInvLipUniversalCircle

/-!
# The pinched pseudometric is not vacuous

This file checks the notions of `PinchedPathBasic.lean` on the marked circle of
radius `r > 1`: it is an admissible *curve* (`IsPinchedCurve`) for the pinching
`kminP = κ̂ = 1/r`, so the constant path at it is admissible, its pinched
self-distance is zero, and the triangle inequality and the Lipschitz bound of
`PinchedPathMetric.lean` apply to it.

Main results: `circle_isPinchedCurve`, `circle_pinchedDist_self`,
`circle_dist_selInv_le_pinchedDist`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist
  RearJacobiSourceCost SelInvLipUniversal GaugeMarkedDataOfRearFamily
  SelInvPathTurningCircle SelInvLipUniversalCircle

variable {r : ℝ}

/-- **The marked circle of radius `r > 1` is an admissible curve** for the
pinching `kminP = κ̂ = 1/r`. -/
theorem circle_isPinchedCurve (hr : 1 < r) :
    IsPinchedCurve (1 / r) (1 / r) (circleData r) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hΓ := restCirclePath_isPinched hr
  have hX6 : ContDiff ℝ (6 : ℕ) (uncurry (restCirclePath r).X) :=
    contDiff_uncurry_restCirclePath
  have hsm : ContDiff ℝ (6 : ℕ) (⇑(circleData r).1) := contDiff_start (restCirclePath r) hX6
  have hsm1 : ContDiff ℝ (1 : ℕ) (⇑(circleData r).1) := hsm.of_le (by norm_num)
  have hvel : ∀ t u, pathVel (constFam (circleData r)) t u = deriv (⇑(circleData r).1) u :=
    fun t u => pathVel_constFam hsm1 t u
  have hperim : ‖deriv (⇑(circleData r).1) 0‖ = 2 * Real.pi * r := by
    rw [← hvel 0 0]
    show ‖pathVel (restCirclePath r).X 0 0‖ = 2 * Real.pi * r
    exact pathPerim_restCirclePath hr0 0
  refine
    { smooth := hsm
      per := hΓ.per 0
      speed := fun u => ?_
      speed_pos := ?_
      kmin := hΓ.kmin
      kmax := hΓ.kmax
      short := ?_
      slit := ?_ }
  · rw [← hvel 0 u, ← hvel 0 0]
    exact hΓ.speed 0 u
  · rw [hperim]; positivity
  · rw [hperim]
    have h : 1 / r * (2 * Real.pi * r) = 2 * Real.pi := by field_simp
    rw [h]
    linarith [Real.pi_pos]
  · rw [← hvel 0 0]
    exact hΓ.slit 0

/-- The pinched costs of the circle to itself form a nonempty set. -/
theorem circle_pinchedSet_nonempty (hr : 1 < r) :
    (pinchedSet (1 / r) (1 / r) (circleData r) (circleData r)).Nonempty :=
  pinchedSet_self_nonempty (circle_isPinchedCurve hr)

/-- **The pinched self-distance of the circle is zero.** -/
theorem circle_pinchedDist_self (hr : 1 < r) :
    pinchedDist (1 / r) (1 / r) (circleData r) (circleData r) = 0 :=
  pinchedDist_self (circle_isPinchedCurve hr)

/-- **The Lipschitz bound applies to the circle**: its two thresholds are met,
the pinched self-distance being zero. -/
theorem circle_dist_selInv_le_pinchedDist (hr : 1 < r) :
    dist (SelectedInverseMap.selInv (1 / r) (circleData r))
        (SelectedInverseMap.selInv (1 / r) (circleData r))
      ≤ selInvLipUniversal (1 / r) (1 / r) (rearKappa1 (1 / r))
          (perim (SelectedInverseMap.selInv (1 / r) (circleData r)))
          (perim (SelectedInverseMap.selInv (1 / r) (circleData r)))
        * pinchedDist (1 / r) (1 / r) (circleData r) (circleData r) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hp := circleData_mem_tube hr0
  have hkmin : 0 < 1 / r := by positivity
  have hkh1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have hzero := circle_pinchedDist_self hr
  refine dist_selInv_le_pinchedDist hp.hasDerivAt_curve hp.hasDerivAt_vel
    hp.hasDerivAt_curve hp.hasDerivAt_vel hkh1 hkmin le_rfl
    (circle_pinchedSet_nonempty hr) ?_ ?_
  · rw [hzero]; norm_num
  · rw [hzero]; norm_num

/-- The triangle inequality of the pinched pseudometric, at the circle. -/
theorem circle_pinchedDist_triangle (hr : 1 < r) :
    pinchedDist (1 / r) (1 / r) (circleData r) (circleData r)
      ≤ pinchedDist (1 / r) (1 / r) (circleData r) (circleData r)
        + pinchedDist (1 / r) (1 / r) (circleData r) (circleData r) :=
  pinchedDist_triangle (circle_pinchedSet_nonempty hr) (circle_pinchedSet_nonempty hr)

end PinchedPath
