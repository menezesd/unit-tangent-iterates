import Mathlib
import UnitTangentIterates.SelInvPathTubeC2
import UnitTangentIterates.SelInvPathTurningCircle

/-!
# The `C²` estimate with the tube membership produced is not vacuous

`SelInvPathTubeC2.dist_selInv_le_modulus_of_path_tube_C2` states the `C²`
comparison of the two marked selected inverses with the tube membership of the
two ends produced from the pinching of the slices, the ends being asked only to
carry their velocity and their acceleration as the derivatives of their curve.
This file checks that hypothesis block on the resting circle of radius `r > 1`
of `SelInvPathTurningCircle.lean`.

Main result: `restCircle_tube_instance`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathTubeCircle

open UniformFrameBounds RearOwnHigherRegularity FrontFromPath
  SelInvFrontCostC2 RearJacobiSourceCost SelInvFrontStripC2
  SelInvPathRegularityC2 SelInvPathCurvatureC2 SelInvPathCurvBoundC2
  SelInvPathPerimC2 SelInvPathGaugeC2 SelInvPathBoundsC2 SelInvPathTurningC2
  SelInvPathTubeC2 GaugeMarkedDataOfRearFamily SelInvFrontChangeVarC2
  SelInvFrontVelocityC2 SelInvPathTurningCircle

variable {r : ℝ}

/-- **The hypothesis block of the `C²` estimate with the tube membership
produced is consistent.**  Every hypothesis of
`SelInvPathTubeC2.dist_selInv_le_modulus_of_path_tube_C2` holds for the resting
circle of radius `r > 1`; in particular the marked circle carries its velocity
and its acceleration as the derivatives of its curve. -/
theorem restCircle_tube_instance (hr : 1 < r) :
    ∃ P0 P1 : ℝ, 0 < P0 ∧ (∀ t, P0 ≤ pathPerim (restCirclePath r).X t) ∧
      (∀ t, pathPerim (restCirclePath r).X t ≤ P1) ∧
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin (1 / r))) ∧
      (∀ t σ, HasDerivAt (dn t) ((pathPerim (restCirclePath r).X) t * (pathKn (restCirclePath r).X (pathPerim (restCirclePath r).X) t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / (pathPerim (restCirclePath r).X) t)) ∧
      ∀ (Rb : ℝ → ℝ) (khat rr : ℝ),
        rearKappa1 (1 / r) ≤ khat →
        (∀ t x,
          |frameTangential (rearOwnVelocity (restCirclePath r).X (pathVel (restCirclePath r).X) (pathAcc (restCirclePath r).X) (pathPerim (restCirclePath r).X) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel (restCirclePath r).X) (pathAcc (restCirclePath r).X) (pathPerim (restCirclePath r).X)) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t x| ≤ Rb t) →
        (∀ t, Rb t ≤ rr * (restCirclePath r).m t) → 0 ≤ rr →
        RearCostDensity.rearCostConst (1 / r) khat (rearKappa2 (1 / r))
            (rearArclength (δ 0) ((pathPerim (restCirclePath r).X) 0)) (jacobiSourceConst (1 / r) P0) * cost (restCirclePath r) ≤ 1 →
      dist (SelectedInverseMap.selInv (1 / r) (circleData r)) (SelectedInverseMap.selInv (1 / r) (circleData r))
        ≤ selInvFrontModulus P1 (1 / r) (perim (SelectedInverseMap.selInv (1 / r) (circleData r)))
            (perim (SelectedInverseMap.selInv (1 / r) (circleData r))) ((1 / r) / Real.sqrt (1 - (1 / r) ^ 2))
            (2 * (1 / r) / Real.sqrt (1 - (1 / r) ^ 2) ^ 3) (pathPv0 (1 / r) P0 khat rr) khat (jacobiSourceConst (1 / r) P0)
            (cost (restCirclePath r)) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hpi := Real.pi_pos
  have hp := circleData_mem_tube hr0
  have hkmin : 0 < 1 / r := by positivity
  have hkh1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have hXC6 : ContDiff ℝ (6 : ℕ) (uncurry (restCirclePath r).X) :=
    contDiff_uncurry_restCirclePath
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
  have hKnmin : ∀ t σ, 1 / r
      ≤ pathKn (restCirclePath r).X (pathPerim (restCirclePath r).X) t σ :=
    fun t σ => le_of_eq (hKn t σ).symm
  have hKnk : ∀ t σ, pathKn (restCirclePath r).X (pathPerim (restCirclePath r).X) t σ
      ≤ 1 / r := fun t σ => le_of_eq (hKn t σ)
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
  have hmark : ∀ t, (restCirclePath r).eta t 0 = 0 := fun _ => rfl
  exact dist_selInv_le_modulus_of_path_tube_C2 (restCirclePath r)
    hp.hasDerivAt_curve hp.hasDerivAt_vel hp.hasDerivAt_curve hp.hasDerivAt_vel
    hkh1 hXC6 hconst hXper hnu hkmin hKnmin hKnk hshort hslit hmark

end SelInvPathTubeCircle
