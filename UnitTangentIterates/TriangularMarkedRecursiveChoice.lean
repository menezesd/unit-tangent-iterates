import UnitTangentIterates.TriangularMarkedPathScheme

/-!
# Recursive-choice interface for triangular marked shadowing

The interface is deliberately relational: a gauge rear-family construction
may select a different terminal marking at every `(n,k)`.  No selected rear is
required to be the value of one global function on marked data.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace TriangularMarkedRecursiveChoice

/-- Output required from one gauge rear-family choice. -/
structure StageOutput
    (p front rear : Data) (bound P0 P1 kh G1 Cg c dlt : ℝ) where
  rear_tube : IsTubeMember c 0 dlt rear
  increment : NormalPath p rear
  increment_geometry :
    IsVariableSpeedNormalPath P0 P1 kh G1 Cg increment
  increment_cost : cost increment ≤ bound
  range_edge : range (ev front) =
    range (UnitTangent.unitTangentMap (ev rear))
  rear_harnack : ∀ a b : ℝ, a ≤ b →
    Real.exp (a - b) *
        (UnconditionalAssembly.arcCurv rear a /
          Real.sqrt (1 + UnconditionalAssembly.arcCurv rear a ^ 2)) ≤
      UnconditionalAssembly.arcCurv rear b /
        Real.sqrt (1 + UnconditionalAssembly.arcCurv rear b ^ 2)

/-- A recursively chosen triangular family.  `stage n k` is precisely the
package expected from a gauge rear-family step applied to the two entries in
column `k`. -/
structure Family
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 kh G1 Cg c dlt : ℝ) where
  P : ℕ → ℕ → Data
  base : ∀ n, P n 0 = Q n
  error_nonnegative : ∀ n k, 0 ≤ e n k
  error_summable : ∀ n, Summable (e n)
  base_tube : ∀ n, IsTubeMember c 0 dlt (Q n)
  base_harnack : ∀ n, ∀ a b : ℝ, a ≤ b →
    Real.exp (a - b) *
        (UnconditionalAssembly.arcCurv (Q n) a /
          Real.sqrt (1 + UnconditionalAssembly.arcCurv (Q n) a ^ 2)) ≤
      UnconditionalAssembly.arcCurv (Q n) b /
        Real.sqrt (1 + UnconditionalAssembly.arcCurv (Q n) b ^ 2)
  stage : ∀ n k,
    StageOutput (P n k) (P (n + 1) k) (P n (k + 1))
      (e n k) P0 P1 kh G1 Cg c dlt
  basePath : ∀ n k, NormalPath (Q n) (P n (k + 1))
  basePathGeometry : ∀ n k,
    IsVariableSpeedNormalPath P0 P1 kh G1 Cg (basePath n k)
  basePathCost : ∀ n k,
    cost (basePath n k) ≤ ∑ j ∈ Finset.range (k + 1), e n j

/-- Forget the construction order and expose the abstract triangular scheme. -/
def Family.toScheme
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 kh G1 Cg c dlt : ℝ}
    (F : Family Q e P0 P1 kh G1 Cg c dlt) :
    TriangularMarkedPathScheme.Scheme Q F.P e P0 P1 kh G1 Cg c dlt where
  base := F.base
  error_nonnegative := F.error_nonnegative
  error_summable := F.error_summable
  tube := by
    intro n k
    cases k with
    | zero => simpa [F.base n] using F.base_tube n
    | succ k => exact (F.stage n k).rear_tube
  stepPath := fun n k => (F.stage n k).increment
  stepGeometry := fun n k => (F.stage n k).increment_geometry
  stepCost := fun n k => (F.stage n k).increment_cost
  basePath := F.basePath
  basePathGeometry := F.basePathGeometry
  basePathCost := F.basePathCost
  finiteEdge := fun n k => (F.stage n k).range_edge
  finiteHarnack := by
    intro n k
    cases k with
    | zero =>
        simpa [F.base n] using F.base_harnack n
    | succ k => exact (F.stage n k).rear_harnack

/-- The recursive-choice interface feeds the fixed-map-free limit theorem
without any extra adapter or continuity assumption. -/
theorem exists_limitOutput
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 kh G1 Cg c dlt : ℝ}
    (F : Family Q e P0 P1 kh G1 Cg c dlt)
    (hC : 0 ≤ c2ConstVar P0 P1 kh G1 Cg)
    (hc : 0 < c) (hdlt : 0 < dlt) :
    Nonempty (TriangularMarkedPathScheme.LimitOutput
      Q F.P e P0 P1 kh G1 Cg c dlt) :=
  TriangularMarkedPathScheme.exists_limitOutput F.toScheme hC hc hdlt

end TriangularMarkedRecursiveChoice
