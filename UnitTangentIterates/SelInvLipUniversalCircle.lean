import Mathlib
import UnitTangentIterates.SelInvTubePathDist
import UnitTangentIterates.SelInvModulusLinearCircle

/-!
# The universal Lipschitz bound is not vacuous

`SelInvLipUniversal.dist_selInv_le_lipUniversal_pathDist` bounds the marked
distance of the two selected inverses by the universal constant times the path
pseudodistance, under the hypothesis that the two fronts are joined by normal
paths of cost arbitrarily close to `pathDist`, of cost at most one, with pinched
slices; `SelInvTubePathDist.dist_selInv_le_lipUniversal_pinchedPathDist` asks
instead for one admissible path.  This file checks both hypothesis blocks on the
resting circle of radius `r > 1`, whose constant path is admissible and of cost
zero.

Main results: `restCirclePath_isPinched`, `restCircle_lipUniversal_instance`,
`restCircle_pinchedCostSet_nonempty`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvLipUniversalCircle

open UniformFrameBounds RearOwnHigherRegularity FrontFromPath
  SelInvFrontCostC2 RearJacobiSourceCost SelInvFrontStripC2
  SelInvPathRegularityC2 SelInvPathCurvatureC2 SelInvPathCurvBoundC2
  SelInvPathPerimC2 SelInvPathGaugeC2 SelInvPathBoundsC2 SelInvPathTurningC2
  SelInvPathTubeC2 GaugeMarkedDataOfRearFamily SelInvFrontChangeVarC2
  SelInvFrontVelocityC2 SelInvPathTurningCircle SelInvModulusLinear
  SelInvModulusLinearCircle SelInvLipUniversal SelInvTubePathDist

variable {r : ℝ}

/-- **The resting circle is an admissible path** for the `C²` estimate, with the
curvature pinching `kminP = κ̂ = 1/r`. -/
theorem restCirclePath_isPinched (hr : 1 < r) :
    IsPinchedPath (1 / r) (1 / r) (restCirclePath r) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hpi := Real.pi_pos
  have hconst : ∀ t u, ‖pathVel (restCirclePath r).X t u‖
      = ‖pathVel (restCirclePath r).X t 0‖ := by
    intro t u
    rw [pathVel_restCirclePath hr0, pathVel_restCirclePath hr0,
      norm_vel_circleData hr0, norm_vel_circleData hr0]
  have hXper : ∀ t, Periodic ((restCirclePath r).X t) 1 := by
    intro t u
    show (r : ℂ) * normExp (u + 1) = (r : ℂ) * normExp u
    rw [periodic_normExp u]
  have hnu : ∀ t u, (restCirclePath r).nu t u
      = Complex.I * (pathVel (restCirclePath r).X t u
          / ((pathPerim (restCirclePath r).X t : ℝ) : ℂ)) := by
    intro t u
    have hc : 0 < 2 * Real.pi * r := by positivity
    rw [pathVel_restCirclePath hr0, pathPerim_restCirclePath hr0, circleData_vel]
    have hne : ((2 * Real.pi * r : ℝ) : ℂ) ≠ 0 := by
      simpa using (ne_of_gt hc)
    show -normExp u = _
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hKn := pathKn_restCirclePath (r := r) hr0
  have hshort : ∀ t, 1 / r * pathPerim (restCirclePath r).X t < 4 * Real.pi := by
    intro t
    rw [pathPerim_restCirclePath hr0]
    have h : 1 / r * (2 * Real.pi * r) = 2 * Real.pi := by field_simp
    rw [h]
    linarith
  have hslit : ∀ t, pathVel (restCirclePath r).X t 0 ∈ Complex.slitPlane := by
    intro t
    rw [pathVel_restCirclePath hr0, circleData_vel]
    right
    have h0 : normExp 0 = 1 := by simp [normExp]
    rw [h0, mul_one]
    simp
    positivity
  exact
    { smooth := contDiff_uncurry_restCirclePath
      speed := hconst
      per := hXper
      normal := hnu
      kmin := fun t σ => le_of_eq (hKn t σ).symm
      kmax := fun t σ => le_of_eq (hKn t σ)
      short := hshort
      slit := hslit
      rest := fun _ => rfl }

/-- **The hypothesis block of the universal Lipschitz bound is consistent.**
For the marked circle of radius `r > 1`, with the curvature pinching
`kminP = κ̂ = 1/r` and the gauge `κ̂' = rearKappa1 (1/r)`, the resting circle path
witnesses the hypothesis of
`SelInvLipUniversal.dist_selInv_le_lipUniversal_pathDist` at every `ε > 0`. -/
theorem restCircle_lipUniversal_instance (hr : 1 < r) :
    dist (SelectedInverseMap.selInv (1 / r) (circleData r))
        (SelectedInverseMap.selInv (1 / r) (circleData r))
      ≤ selInvLipUniversal (1 / r) (1 / r) (rearKappa1 (1 / r))
          (perim (SelectedInverseMap.selInv (1 / r) (circleData r)))
          (perim (SelectedInverseMap.selInv (1 / r) (circleData r)))
        * pathDist (circleData r) (circleData r) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hp := circleData_mem_tube hr0
  have hkmin : 0 < 1 / r := by positivity
  have hkh1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have hΓ := restCirclePath_isPinched hr
  refine dist_selInv_le_lipUniversal_pathDist hp.hasDerivAt_curve hp.hasDerivAt_vel
    hp.hasDerivAt_curve hp.hasDerivAt_vel hkh1 hkmin le_rfl (fun ε hε => ?_)
  refine ⟨restCirclePath r, ?_, ?_, hΓ.smooth, hΓ.speed, hΓ.per, hΓ.normal, hΓ.kmin,
    hΓ.kmax, hΓ.short, hΓ.slit, hΓ.rest, ?_⟩
  · rw [cost_restCirclePath]
    simpa using hε.le
  · rw [cost_restCirclePath]; norm_num
  · rw [cost_restCirclePath]; norm_num

/-- **The pinched pseudodistance is not vacuous**: the resting circle is an
admissible path of cost zero, so the constrained infimum of
`SelInvTubePathDist` is taken over a nonempty set. -/
theorem restCircle_pinchedCostSet_nonempty (hr : 1 < r) :
    (pinchedCostSet (1 / r) (1 / r) (rearKappa1 (1 / r)) (circleData r)
      (circleData r)).Nonempty := by
  refine ⟨0, restCirclePath r, cost_restCirclePath, restCirclePath_isPinched hr, ?_, ?_⟩
  · rw [cost_restCirclePath]; norm_num
  · rw [cost_restCirclePath]; norm_num

end SelInvLipUniversalCircle
