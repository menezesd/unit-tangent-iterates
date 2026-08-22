import Mathlib
import UnitTangentIterates.SelInvModulusLinear
import UnitTangentIterates.SelInvPathTurningCircle

/-!
# The Lipschitz form of the `C²` estimate is not vacuous

`SelInvModulusLinear.dist_selInv_le_lip_cost` states the `C²` comparison of the
two marked selected inverses with the modulus replaced by an explicit constant
times the cost, for a normal path of cost at most one satisfying the geometric
hypotheses of `SelInvPathTubeBaseC2.dist_selInv_le_modulus_of_path_tube_base_C2`.
This file checks that hypothesis block — including the smallness of the cost —
on the resting circle of radius `r > 1` of `SelInvPathTurningCircle.lean`, whose
cost is zero.

Main result: `restCircle_lip_instance`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvModulusLinearCircle

open UniformFrameBounds RearOwnHigherRegularity FrontFromPath
  SelInvFrontCostC2 RearJacobiSourceCost SelInvFrontStripC2
  SelInvPathRegularityC2 SelInvPathCurvatureC2 SelInvPathCurvBoundC2
  SelInvPathPerimC2 SelInvPathGaugeC2 SelInvPathBoundsC2 SelInvPathTurningC2
  SelInvPathTubeC2 SelInvPathTubeBaseC2 GaugeMarkedDataOfRearFamily SelInvFrontChangeVarC2
  SelInvFrontVelocityC2 SelInvPathTurningCircle SelInvModulusLinear

variable {r : ℝ}

/-- The resting circle path has cost zero. -/
theorem cost_restCirclePath : cost (restCirclePath r) = 0 := by
  have h : (restCirclePath r).m = fun _ => (0 : ℝ) := rfl
  simp [cost, h]

/-- **The hypothesis block of the Lipschitz form of the `C²` estimate is
consistent.**  Every hypothesis of
`SelInvModulusLinear.dist_selInv_le_lip_cost` holds for the resting circle of
radius `r > 1`; its cost is zero, so the smallness condition on the cost holds
as well. -/
theorem restCircle_lip_instance (hr : 1 < r) :
    ∃ P0 P1 : ℝ, 0 < P0 ∧ (∀ t, P0 ≤ pathPerim (restCirclePath r).X t) ∧
      (∀ t, pathPerim (restCirclePath r).X t ≤ P1) ∧
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin (1 / r))) ∧
      (∀ t σ, HasDerivAt (dn t)
        ((pathPerim (restCirclePath r).X) t
          * (pathKn (restCirclePath r).X (pathPerim (restCirclePath r).X) t σ
              - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / (pathPerim (restCirclePath r).X) t)) ∧
      ∀ (khat : ℝ),
        rearKappa1 (1 / r) ≤ khat →
        RearCostDensity.rearCostConst (1 / r) khat (rearKappa2 (1 / r))
            (rearArclength (δ 0) ((pathPerim (restCirclePath r).X) 0))
            (jacobiSourceConst (1 / r) P0) * cost (restCirclePath r) ≤ 1 →
      dist (SelectedInverseMap.selInv (1 / r) (circleData r))
          (SelectedInverseMap.selInv (1 / r) (circleData r))
        ≤ selInvFrontLip P1 (1 / r) (perim (SelectedInverseMap.selInv (1 / r) (circleData r)))
            (perim (SelectedInverseMap.selInv (1 / r) (circleData r)))
            ((1 / r) / Real.sqrt (1 - (1 / r) ^ 2))
            (2 * (1 / r) / Real.sqrt (1 - (1 / r) ^ 2) ^ 3)
            (pathPv0 (1 / r) P0 khat (P1 * ((1 / r) / (1 - (1 / r) ^ 2)))) khat
            (jacobiSourceConst (1 / r) P0) * cost (restCirclePath r) := by
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
  have hcost : cost (restCirclePath r) ≤ 1 := by
    rw [cost_restCirclePath]; norm_num
  exact dist_selInv_le_lip_cost (restCirclePath r)
    hp.hasDerivAt_curve hp.hasDerivAt_vel hp.hasDerivAt_curve hp.hasDerivAt_vel
    hkh1 hXC6 hconst hXper hnu hkmin hKnmin hKnk hshort hslit hmark hcost

end SelInvModulusLinearCircle
