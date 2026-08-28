import UnitTangentIterates.FiniteColumnStablePhysicalComponentCompactness
import UnitTangentIterates.ReachableVariableSpeedFrontCurvature

/-!
# Stable-component and canonical-model bridges for reachable curvature

This file connects the finite stable physical-component package to the strict
all-slice curvature cap.  It also replaces the coarse common tube speed floor
by the sharper row-local floor obtained from marked distance to an ordinary
canonical model.
-/

noncomputable section

open Set Function Complex MeasureTheory
open MarkedSpace PathMetric PathMetric.NormalPath

namespace ReachableVariableSpeedFrontCurvatureStable

open VariableMarkedTube
open FiniteColumnStablePhysicalComponentCompactness
open ReachableVariableSpeedFrontCurvature
open ConfiguredCombinedPhysicalDiagonalLargeSeparation

/-- Stable physical components put a path inside the configured curvature cost
budget as soon as their scalar defect satisfies the corresponding strict
`4 C d` inequality. -/
theorem cost_lt_sourceCurvatureCostBudget_of_stablePhysicalComponents
    {p q : Data} {Gamma : NormalPath p q} {P C d : ℝ}
    (H : StablePhysicalComponents Gamma P C d)
    (hsmall : (4 * C) * d < sourceCurvatureCostBudget) :
    cost Gamma < sourceCurvatureCostBudget :=
  H.cost_le_four_mul.trans_lt hsmall

/-- Marked distance `r` from an ordinary model with speed floor `c0` improves
the reachable variable-tube member's speed floor to the row-local value
`c0-r`. -/
theorem variableTube_with_model_distance_speed_floor
    {model p : Data} {c0 k0 d0 c C kmin delta r : ℝ}
    (hmodel : IsTubeMember c0 k0 d0 model)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hdist : dist model p ≤ r) :
    IsVariableTubeMember (c0 - r) C kmin delta p := by
  refine { hp with speed_lb := ?_ }
  intro u
  have hvR := (MarkedSpace.dist_vel_apply_le model p u).trans hdist
  have htri : ‖model.2.1 u‖ ≤
      ‖model.2.1 u - p.2.1 u‖ + ‖p.2.1 u‖ := by
    calc
      ‖model.2.1 u‖ = ‖(model.2.1 u - p.2.1 u) + p.2.1 u‖ := by ring
      _ ≤ ‖model.2.1 u - p.2.1 u‖ + ‖p.2.1 u‖ := norm_add_le _ _
  linarith [hmodel.speed_lb u]

/-- The canonical-model version of the initial curvature estimate.  Its scalar
premise uses the sharp local speed floor `c0-r`, rather than the common speed
floor retained by the full recursive tube. -/
theorem initial_abs_curvature_le_of_canonical_model_distance
    {p q model : Data} {g gu theta kappa : ℝ → ℝ → ℝ}
    {c0 k0 d0 c C kmin delta A0 r : ℝ}
    (Gamma : NormalPath p q)
    (hmodel : IsTubeMember c0 k0 d0 model)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hloc : 0 < c0 - r)
    (hmodelAcc : ∀ u, ‖model.2.2 u‖ ≤ A0)
    (hdist : dist model p ≤ r)
    (hg_nonneg : ∀ u, 0 ≤ g 0 u)
    (hXu : ∀ u, HasDerivAt (Gamma.X 0)
      ((g 0 u : ℂ) * Complex.exp (Complex.I * (theta 0 u : ℂ))) u)
    (hgu : ∀ u, HasDerivAt (g 0) (gu 0 u) u)
    (hthetau : ∀ u, HasDerivAt (theta 0) (g 0 u * kappa 0 u) u) :
    ∀ u, |kappa 0 u| ≤ (A0 + r) / (c0 - r) ^ 2 := by
  exact initial_abs_curvature_le_of_model_distance Gamma
    (variableTube_with_model_distance_speed_floor hmodel hp hdist) hloc
    hmodelAcc hdist hg_nonneg hXu hgu hthetau

/-- The finite stable-component package, canonical grid distance, and two
explicit scalar inequalities imply the configured all-time curvature cap.

The scalar assumptions are exactly
`(A0+r)/(c0-r)^2 ≤ 2/3` and `4*Ccomp*d < 6/61`.
-/
theorem abs_curvature_lt_sourceKh_of_stableComponents_and_canonicalModel
    {p q model : Data} {g gu theta kappa : ℝ → ℝ → ℝ}
    {c0 k0 d0 c C kmin delta A0 r P Ccomp d : ℝ}
    (Gamma : NormalPath p q) (hT : Gamma.T = 1)
    (hmodel : IsTubeMember c0 k0 d0 model)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hloc : 0 < c0 - r)
    (hmodelAcc : ∀ u, ‖model.2.2 u‖ ≤ A0)
    (hdist : dist model p ≤ r)
    (hg_nonneg : ∀ u, 0 ≤ g 0 u)
    (hXu : ∀ u, HasDerivAt (Gamma.X 0)
      ((g 0 u : ℂ) * Complex.exp (Complex.I * (theta 0 u : ℂ))) u)
    (hgu : ∀ u, HasDerivAt (g 0) (gu 0 u) u)
    (hthetau : ∀ u, HasDerivAt (theta 0) (g 0 u * kappa 0 u) u)
    (hbdd : ∀ t, BddAbove (Set.range fun u => |iteratedDeriv 2 (Gamma.eta t) u|))
    (hderiv : ∀ t x, HasDerivAt (fun s => kappa s x)
      (iteratedDeriv 2 (Gamma.eta t) x + (kappa t x) ^ 2 * Gamma.eta t x) t)
    (hint : ∀ x, IntervalIntegrable
      (fun t => iteratedDeriv 2 (Gamma.eta t) x +
        (kappa t x) ^ 2 * Gamma.eta t x) volume 0 1)
    (hnonneg : ∀ t x, 0 ≤ kappa t x)
    (hinitial : (A0 + r) / (c0 - r) ^ 2 ≤ TubeConstants.kbar (1 / 2))
    (H : StablePhysicalComponents Gamma P Ccomp d)
    (hcomponentSmall : (4 * Ccomp) * d < sourceCurvatureCostBudget) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, |kappa t u| < sourceKh := by
  apply abs_curvature_lt_sourceKh_of_model_distance_and_cost Gamma hT
    (variableTube_with_model_distance_speed_floor hmodel hp hdist) hloc
    hmodelAcc hdist hg_nonneg hXu hgu hthetau hbdd hderiv hint hnonneg hinitial
  exact cost_lt_sourceCurvatureCostBudget_of_stablePhysicalComponents
    H hcomponentSmall

end ReachableVariableSpeedFrontCurvatureStable
