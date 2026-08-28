import UnitTangentIterates.VariableTerminalRowTubeAdapter

/-!
# One-step outer tube induction for recosted rows

This module separates the metric induction used to keep a recursively
constructed row in one fixed tube from the construction of the row itself.
The induction remembers only a distance from the fixed row model.  A new
edge is added by the triangle inequality, and the configured row budget then
turns the resulting radius bound into fixed variable-tube membership.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedOuterTubeStep

open VariableMarkedTube VariableMarkedTubeLocalStability
open VariableTerminalRowTubeAdapter

/-- The metric part of one outer-induction step. -/
theorem dist_next_le_prefix_add
    {base current next : Data} {accumulated stepError : ℝ}
    (hprefix : dist base current ≤ accumulated)
    (hstep : dist current next ≤ stepError) :
    dist base next ≤ accumulated + stepError := by
  exact (dist_triangle base current next).trans
    (add_le_add hprefix hstep)

/-- A one-step form of rowwise tube stability.

`current` need not itself carry any tube certificate.  This is intentional:
the outer induction retains only its distance from the fixed model `M`.
The local differential hypotheses are required only for the newly displayed
datum `next` (for example, a coherence package's mapped initial).
-/
theorem variableTube_next_of_rowBudget
    {Q : ℕ → Data} {P0 P1 khat G1 Cg : ℕ → ℝ}
    {c0 d0 A0 r rho C : ℕ → ℝ} {c dlt : ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (n : ℕ) {current next : Data} {accumulated stepError : ℝ}
    (hmodel : IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hmodel_acc : ∀ u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hcurve : ∀ u, HasDerivAt (⇑next.1) (next.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑next.2.1) (next.2.2 u) u)
    (hperiodic : Function.Periodic (⇑next.1) 1)
    (hcurv : ∀ u, 0 ≤
      ((starRingEnd ℂ) (next.2.1 u) * next.2.2 u).im)
    (hprefix : dist (Q n) current ≤ accumulated)
    (hstep : dist current next ≤ stepError)
    (hradius : accumulated + stepError ≤ r n) :
    IsVariableTubeMember c (C n) 0 dlt next := by
  have hdist : dist (Q n) next ≤ r n :=
    (dist_next_le_prefix_add hprefix hstep).trans hradius
  have hlocal := variableTube_of_dist_le hmodel hcurve hvel hperiodic
    hdist hmodel_acc hcurv (B.radius_nonnegative n)
    (B.local_speed_positive n) (B.acceleration_nonnegative n)
    (B.rho_positive n) (B.rho_half n) (B.acceleration_radius n)
    B.chord_nonnegative (B.chord_speed n) (B.chord_margin n)
  exact
    { hasDerivAt_curve := hlocal.hasDerivAt_curve
      hasDerivAt_vel := hlocal.hasDerivAt_vel
      periodic := hlocal.periodic
      speed_lb := fun u ↦ (B.target_speed n).trans (hlocal.speed_lb u)
      speed_ub := fun u ↦ (hlocal.speed_ub u).trans (B.upper_speed n)
      curv_lb := hlocal.curv_lb
      chord := hlocal.chord }

/-- Variant taking the already-combined distance estimate.  This is useful
when the outer induction packages the triangle step separately. -/
theorem variableTube_of_prefix_step_le_rowRadius
    {Q : ℕ → Data} {P0 P1 khat G1 Cg : ℕ → ℝ}
    {c0 d0 A0 r rho C : ℕ → ℝ} {c dlt : ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (n : ℕ) {next : Data}
    (hmodel : IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hmodel_acc : ∀ u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hcurve : ∀ u, HasDerivAt (⇑next.1) (next.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑next.2.1) (next.2.2 u) u)
    (hperiodic : Function.Periodic (⇑next.1) 1)
    (hcurv : ∀ u, 0 ≤
      ((starRingEnd ℂ) (next.2.1 u) * next.2.2 u).im)
    (hdist : dist (Q n) next ≤ r n) :
    IsVariableTubeMember c (C n) 0 dlt next := by
  have hlocal := variableTube_of_dist_le hmodel hcurve hvel hperiodic
    hdist hmodel_acc hcurv (B.radius_nonnegative n)
    (B.local_speed_positive n) (B.acceleration_nonnegative n)
    (B.rho_positive n) (B.rho_half n) (B.acceleration_radius n)
    B.chord_nonnegative (B.chord_speed n) (B.chord_margin n)
  exact
    { hasDerivAt_curve := hlocal.hasDerivAt_curve
      hasDerivAt_vel := hlocal.hasDerivAt_vel
      periodic := hlocal.periodic
      speed_lb := fun u ↦ (B.target_speed n).trans (hlocal.speed_lb u)
      speed_ub := fun u ↦ (hlocal.speed_ub u).trans (B.upper_speed n)
      curv_lb := hlocal.curv_lb
      chord := hlocal.chord }

end ConfiguredRecursiveEdgeRecostedOuterTubeStep
