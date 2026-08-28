import UnitTangentIterates.VariableMarkedTubeLocalStability
import UnitTangentIterates.TriangularMarkedPathSchemeVariableTerminal

/-!
# Rowwise tube adapter for variable terminal markings

This module supplies exactly the `tube` field of the variable-terminal
triangular scheme.  A base path from the fixed row model to every depth,
together with its prefix-cost/tail estimate, places the whole row in one
marked ball.  Local stability then gives constants independent of depth.
-/

noncomputable section

open Set Function MarkedSpace PathMetric PathMetric.NormalPath
  NormalPathC2IncrementVariableSpeed

namespace VariableTerminalRowTubeAdapter

open VariableMarkedTube VariableMarkedTubeLocalStability

/-- Scalar margins for one row.  The common target constants `c` and `dlt`
may be weaker than the natural local constants `c0 n - r n` and `d0 n`. -/
structure RowBudget
    (Q : ℕ → Data) (P0 P1 khat G1 Cg : ℕ → ℝ)
    (c0 d0 A0 r rho C : ℕ → ℝ) (c dlt : ℝ) : Prop where
  radius_nonnegative : ∀ n, 0 ≤ r n
  local_speed_positive : ∀ n, 0 < c0 n - r n
  target_speed : ∀ n, c ≤ c0 n - r n
  acceleration_nonnegative : ∀ n, 0 ≤ A0 n
  rho_positive : ∀ n, 0 < rho n
  rho_half : ∀ n, rho n ≤ 1 / 2
  acceleration_radius : ∀ n,
    (A0 n + r n) * rho n ≤ (c0 n - r n) / 2
  chord_nonnegative : 0 ≤ dlt
  chord_speed : ∀ n, dlt ≤ (c0 n - r n) / 2
  chord_margin : ∀ n, 2 * r n ≤ (d0 n - dlt) * rho n
  upper_speed : ∀ n, perim (Q n) + r n ≤ C n

/-- Base paths and summable-tail control place every depth of a row in its
fixed local-stability ball. -/
theorem markedDist_le_rowRadius_of_basePath_tail
    {Q : ℕ → Data} {P : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg r tail : ℕ → ℝ}
    (basePath : ∀ n k, NormalPath (Q n) (P n k))
    (hQcurve : ∀ n u, HasDerivAt (⇑(Q n).1) ((Q n).2.1 u) u)
    (hQvel : ∀ n u, HasDerivAt (⇑(Q n).2.1) ((Q n).2.2 u) u)
    (hPcurve : ∀ n k u, HasDerivAt (⇑(P n k).1) ((P n k).2.1 u) u)
    (hPvel : ∀ n k u, HasDerivAt (⇑(P n k).2.1) ((P n k).2.2 u) u)
    (hgeometry : ∀ n k, IsVariableSpeedNormalPath
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) (basePath n k))
    (hcost : ∀ n k, cost (basePath n k) ≤
      ∑ j ∈ Finset.range k, e n j)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n) :
    ∀ n k, dist (Q n) (P n k) ≤ r n := by
  intro n k
  have hdist := dist_le_cost_variableSpeed (basePath n k)
    (hQcurve n) (hPcurve n k) (hQvel n) (hPvel n k) (hgeometry n k)
  have hC : 0 ≤ c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) :=
    c2ConstVar_nonneg _ _ _ _ _
  exact hdist.trans ((mul_le_mul_of_nonneg_left (hcost n k) hC).trans
    ((mul_le_mul_of_nonneg_left (hpartial n k) hC).trans (hradius n)))

/-- Adapter producing exactly the fixed rowwise tube-membership field required
by `TriangularMarkedPathSchemeVariableTerminal.Scheme`.

All dependence on recursive depth is confined to the base paths and their
costs.  The output constants are `c`, `C n`, and `dlt`, independent of `k`.
The endpoint oriented-curvature inequality is explicit because it cannot be
deduced from closeness to a model whose curvature floor is zero. -/
theorem schemeTube_of_basePath_tail
    {Q : ℕ → Data} {P : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg : ℕ → ℝ}
    {c0 d0 A0 r rho C tail : ℕ → ℝ} {c dlt : ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbase : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbase_acc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (basePath : ∀ n k, NormalPath (Q n) (P n k))
    (hPcurve : ∀ n k u, HasDerivAt (⇑(P n k).1) ((P n k).2.1 u) u)
    (hPvel : ∀ n k u, HasDerivAt (⇑(P n k).2.1) ((P n k).2.2 u) u)
    (hPperiodic : ∀ n k, Periodic (⇑(P n k).1) 1)
    (horiented : ∀ n k u, 0 ≤
      ((starRingEnd ℂ) ((P n k).2.1 u) * (P n k).2.2 u).im)
    (hgeometry : ∀ n k, IsVariableSpeedNormalPath
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) (basePath n k))
    (hcost : ∀ n k, cost (basePath n k) ≤
      ∑ j ∈ Finset.range k, e n j)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n) :
    ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k) := by
  have hdist : ∀ n k, dist (Q n) (P n k) ≤ r n :=
    markedDist_le_rowRadius_of_basePath_tail basePath
      (fun n => (hbase n).hasDerivAt_curve)
      (fun n => (hbase n).hasDerivAt_vel) hPcurve hPvel hgeometry hcost
      hpartial hradius
  intro n k
  have hlocal := variableTube_of_dist_le (hbase n) (hPcurve n k)
    (hPvel n k) (hPperiodic n k) (hdist n k) (hbase_acc n)
    (horiented n k) (B.radius_nonnegative n) (B.local_speed_positive n)
    (B.acceleration_nonnegative n) (B.rho_positive n) (B.rho_half n)
    (B.acceleration_radius n) B.chord_nonnegative (B.chord_speed n)
    (B.chord_margin n)
  exact
    { hasDerivAt_curve := hlocal.hasDerivAt_curve
      hasDerivAt_vel := hlocal.hasDerivAt_vel
      periodic := hlocal.periodic
      speed_lb := fun u => (B.target_speed n).trans (hlocal.speed_lb u)
      speed_ub := fun u => (hlocal.speed_ub u).trans (B.upper_speed n)
      curv_lb := hlocal.curv_lb
      chord := hlocal.chord }

end VariableTerminalRowTubeAdapter
