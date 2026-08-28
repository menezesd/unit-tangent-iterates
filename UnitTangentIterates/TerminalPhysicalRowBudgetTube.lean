import UnitTangentIterates.ConfiguredGaugeEndpointDefect
import UnitTangentIterates.VariableTerminalRowTubeAdapter

/-!
# Ordinary physical terminals in a row-budget tube

The combined diagonal radius need not be represented by the legacy weighted
pullback-radius formula.  This adapter applies the same local stability
argument directly from a `RowBudget` and restores the terminal's constant
speed field from its ordinary physical certificate.
-/

noncomputable section

open MarkedSpace PathMetric

namespace TerminalPhysicalRowBudgetTube

open VariableMarkedTubeLocalStability
open VariableTerminalRowTubeAdapter

theorem mem_of_rowBudget
    {Q : ℕ → Data} {P0 P1 khat G1 Cg : ℕ → ℝ}
    {c0 d0 A0 r rho C : ℕ → ℝ} {c dlt : ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (n : ℕ) {M Z : Data}
    (hmodel : IsTubeMember (c0 n) 0 (d0 n) M)
    (hmodel_acc : ∀ u, ‖M.2.2 u‖ ≤ A0 n)
    (P : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts Z)
    (hcurv : ∀ u, 0 ≤
      ((starRingEnd ℂ) (Z.2.1 u) * Z.2.2 u).im)
    (hdist : dist M Z ≤ r n) :
    IsTubeMember c 0 dlt Z := by
  have hlocal := variableTube_of_dist_le hmodel
    P.tube.hasDerivAt_curve P.tube.hasDerivAt_vel P.tube.periodic
    hdist hmodel_acc hcurv (B.radius_nonnegative n)
    (B.local_speed_positive n) (B.acceleration_nonnegative n)
    (B.rho_positive n) (B.rho_half n) (B.acceleration_radius n)
    B.chord_nonnegative (B.chord_speed n) (B.chord_margin n)
  exact
    { hasDerivAt_curve := hlocal.hasDerivAt_curve
      hasDerivAt_vel := hlocal.hasDerivAt_vel
      periodic := hlocal.periodic
      speed_const := P.tube.speed_const
      speed_lb := fun u ↦ (B.target_speed n).trans (hlocal.speed_lb u)
      curv_lb := hlocal.curv_lb
      chord := hlocal.chord }

end TerminalPhysicalRowBudgetTube
