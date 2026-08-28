import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed
import UnitTangentIterates.TubeInvariance
import UnitTangentIterates.VariableMarkedTubeLocalStability

/-!
# A strict curvature cap for reachable variable-speed fronts

This file separates the two estimates needed when a marked selected inverse is
transported through one finite row.

* Marked `C2` distance from a model controls the curvature of the initial
  variable-speed slice.
* The stopped curvature estimate then propagates that cap through every slice
  of a unit-duration normal path.

For the configured half-curvature model, the intermediate ceiling is `2 / 3`
and the selected-inverse ceiling is `sourceKh = 5 / 6`.  The corresponding
uniform path-cost budget is the explicit constant `6 / 61`.
-/

noncomputable section

open Set Function Complex MeasureTheory
open MarkedSpace PathMetric PathMetric.NormalPath

namespace ReachableVariableSpeedFrontCurvature

open VariableMarkedTube
open ConfiguredCombinedPhysicalDiagonalLargeSeparation

/-- The uniform cost budget which carries the intermediate curvature ceiling
`2 / 3` strictly below the configured source ceiling `5 / 6`. -/
def sourceCurvatureCostBudget : ℝ := 6 / 61

theorem sourceCurvatureCostBudget_pos : 0 < sourceCurvatureCostBudget := by
  norm_num [sourceCurvatureCostBudget]

/-- Marked distance from a model converts its acceleration bound and the speed
floor of the reachable slice into an intrinsic curvature bound.

The conclusion uses only the initial slice of the variable-speed frame.  Thus
it applies equally to a grid point, a transported front, or the initial slice
of a chosen gauge path. -/
theorem initial_abs_curvature_le_of_model_distance
    {p q model : Data} {g gu theta kappa : ℝ → ℝ → ℝ}
    {c C kmin delta A0 r : ℝ}
    (Gamma : NormalPath p q)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hc : 0 < c)
    (hmodelAcc : ∀ u, ‖model.2.2 u‖ ≤ A0)
    (hdist : dist model p ≤ r)
    (hg_nonneg : ∀ u, 0 ≤ g 0 u)
    (hXu : ∀ u, HasDerivAt (Gamma.X 0)
      ((g 0 u : ℂ) * Complex.exp (Complex.I * (theta 0 u : ℂ))) u)
    (hgu : ∀ u, HasDerivAt (g 0) (gu 0 u) u)
    (hthetau : ∀ u, HasDerivAt (theta 0) (g 0 u * kappa 0 u) u) :
    ∀ u, |kappa 0 u| ≤ (A0 + r) / c ^ 2 := by
  intro u
  have hvel := NormalPathC2IncrementVariableSpeed.vel_eq_of_slice
    (g := g) (theta := theta) Gamma 0 hp.hasDerivAt_curve (funext Gamma.start) hXu u
  have hacc := NormalPathC2IncrementVariableSpeed.acc_eq_of_slice
    (g := g) (gu := gu) (theta := theta) (kappa := kappa) Gamma 0
    hp.hasDerivAt_curve hp.hasDerivAt_vel (funext Gamma.start) hXu hgu hthetau u
  have hg_speed : c ≤ g 0 u := by
    have hs := hp.speed_lb u
    rw [hvel, norm_mul, Complex.norm_exp] at hs
    simpa [abs_of_nonneg (hg_nonneg u)] using hs
  have hc_sq : 0 < c ^ 2 := sq_pos_of_pos hc
  have hg_sq : c ^ 2 ≤ (g 0 u) ^ 2 := by
    nlinarith [hg_nonneg u]
  have him : |(g 0 u) ^ 2 * kappa 0 u| ≤
      ‖(gu 0 u : ℂ) + Complex.I * (((g 0 u) ^ 2 * kappa 0 u : ℝ) : ℂ)‖ := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_add, zero_mul, one_mul] using Complex.abs_im_le_norm
      ((gu 0 u : ℂ) + Complex.I * (((g 0 u) ^ 2 * kappa 0 u : ℝ) : ℂ))
  have hcomponent : |(g 0 u) ^ 2 * kappa 0 u| ≤ ‖p.2.2 u‖ := by
    calc
      |(g 0 u) ^ 2 * kappa 0 u| ≤
          ‖(gu 0 u : ℂ) + Complex.I * (((g 0 u) ^ 2 * kappa 0 u : ℝ) : ℂ)‖ := him
      _ = ‖((gu 0 u : ℂ) +
            Complex.I * (((g 0 u) ^ 2 * kappa 0 u : ℝ) : ℂ)) *
            Complex.exp (Complex.I * (theta 0 u : ℂ))‖ := by
        rw [norm_mul, Complex.norm_exp]
        simp
      _ = ‖p.2.2 u‖ := by rw [hacc]
  have hdistAcc : ‖p.2.2 u - model.2.2 u‖ ≤ r :=
    (VariableMarkedTubeLocalStability.dist_acc_apply_le p model u).trans
      (by simpa [dist_comm] using hdist)
  have hpAcc : ‖p.2.2 u‖ ≤ A0 + r := by
    calc
      ‖p.2.2 u‖ = ‖(p.2.2 u - model.2.2 u) + model.2.2 u‖ := by ring
      _ ≤ ‖p.2.2 u - model.2.2 u‖ + ‖model.2.2 u‖ := norm_add_le _ _
      _ ≤ r + A0 := add_le_add hdistAcc (hmodelAcc u)
      _ = A0 + r := add_comm _ _
  apply (le_div_iff₀ hc_sq).2
  calc
    |kappa 0 u| * c ^ 2 = c ^ 2 * |kappa 0 u| := mul_comm _ _
    _ ≤ (g 0 u) ^ 2 * |kappa 0 u| :=
      mul_le_mul_of_nonneg_right hg_sq (abs_nonneg _)
    _ = |(g 0 u) ^ 2 * kappa 0 u| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (g 0 u))]
    _ ≤ ‖p.2.2 u‖ := hcomponent
    _ ≤ A0 + r := hpAcc

/-- A model-distance initial cap followed by the stopped curvature estimate.
This generic form exposes the exact two scalar inequalities needed by a
configured row. -/
theorem abs_curvature_lt_of_model_distance_and_cost
    {p q model : Data} {g gu theta kappa : ℝ → ℝ → ℝ}
    {c C kmin delta A0 r kb ke : ℝ}
    (Gamma : NormalPath p q) (hT : Gamma.T = 1)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hc : 0 < c)
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
    (hinitial : (A0 + r) / c ^ 2 ≤ kb)
    (hsmall : (1 + ke ^ 2) * cost Gamma < ke - kb) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, |kappa t u| < ke := by
  have hinit : ∀ u, kappa 0 u ≤ kb := by
    intro u
    calc
      kappa 0 u ≤ |kappa 0 u| := le_abs_self _
      _ ≤ (A0 + r) / c ^ 2 :=
        initial_abs_curvature_le_of_model_distance Gamma hp hc hmodelAcc hdist
          hg_nonneg hXu hgu hthetau u
      _ ≤ kb := hinitial
  have hall := TubeInvariance.curvature_lt_of_cost Gamma hT hbdd hderiv hint
    hnonneg hinit hsmall
  intro t ht u
  rw [abs_of_nonneg (hnonneg t u)]
  exact hall t ht u

/-- Configured all-slice curvature cap.  The half-curvature model first gives
the intermediate ceiling `2 / 3`; a path cost below `6 / 61` then keeps every
reachable slice strictly below `sourceKh = 5 / 6`. -/
theorem abs_curvature_lt_sourceKh_of_model_distance_and_cost
    {p q model : Data} {g gu theta kappa : ℝ → ℝ → ℝ}
    {c C kmin delta A0 r : ℝ}
    (Gamma : NormalPath p q) (hT : Gamma.T = 1)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hc : 0 < c)
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
    (hinitial : (A0 + r) / c ^ 2 ≤ TubeConstants.kbar (1 / 2))
    (hcost : cost Gamma < sourceCurvatureCostBudget) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, |kappa t u| < sourceKh := by
  apply abs_curvature_lt_of_model_distance_and_cost
    (kb := TubeConstants.kbar (1 / 2)) (ke := sourceKh)
    Gamma hT hp hc hmodelAcc hdist hg_nonneg hXu hgu hthetau hbdd hderiv hint
    hnonneg hinitial
  rw [sourceKh_eq]
  norm_num [TubeConstants.kbar, sourceCurvatureCostBudget] at hcost ⊢
  nlinarith

end ReachableVariableSpeedFrontCurvature
