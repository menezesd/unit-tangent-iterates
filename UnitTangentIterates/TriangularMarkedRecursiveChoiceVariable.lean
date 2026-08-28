import UnitTangentIterates.TriangularMarkedRecursiveChoice
import UnitTangentIterates.TriangularMarkedPathSchemeVariable

/-!
# Recursive triangular choices with row-dependent path ceilings

Each row may use the finite variable-speed constants appropriate to its model
scale.  No supremum over all rows is part of the interface.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace TriangularMarkedRecursiveChoiceVariable

/-- A recursively chosen triangular family with rowwise path classes. -/
structure Family
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg : ℕ → ℝ) (c dlt : ℝ) where
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
    TriangularMarkedRecursiveChoice.StageOutput
      (P n k) (P (n + 1) k) (P n (k + 1)) (e n k)
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c dlt
  basePath : ∀ n k, NormalPath (Q n) (P n (k + 1))
  basePathGeometry : ∀ n k,
    IsVariableSpeedNormalPath (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
      (basePath n k)
  basePathCost : ∀ n k,
    cost (basePath n k) ≤ ∑ j ∈ Finset.range (k + 1), e n j

/-- Forget construction order and expose the row-dependent triangular scheme. -/
def Family.toScheme
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg : ℕ → ℝ} {c dlt : ℝ}
    (F : Family Q e P0 P1 khat G1 Cg c dlt) :
    TriangularMarkedPathSchemeVariable.Scheme
      Q F.P e P0 P1 khat G1 Cg c dlt where
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
    | zero => simpa [F.base n] using F.base_harnack n
    | succ k => exact (F.stage n k).rear_harnack

/-- Recursive rowwise choices feed the variable-ceiling limit theorem. -/
theorem exists_limitOutput
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg : ℕ → ℝ} {c dlt : ℝ}
    (F : Family Q e P0 P1 khat G1 Cg c dlt)
    (hc : 0 < c) (hdlt : 0 < dlt) :
    Nonempty (TriangularMarkedPathSchemeVariable.LimitOutput
      Q F.P e P0 P1 khat G1 Cg c dlt) :=
  TriangularMarkedPathSchemeVariable.exists_limitOutput F.toScheme hc hdlt

end TriangularMarkedRecursiveChoiceVariable
