import UnitTangentIterates.GaugeRearFamilyVariableTerminal
import UnitTangentIterates.TriangularMarkedPathSchemeVariableTerminal

/-!
# Recursive choices with variable terminal markings and rowwise ceilings
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace TriangularMarkedRecursiveChoiceVariableTerminal

open VariableMarkedTube

structure Family
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  P : ℕ → ℕ → Data
  base : ∀ n, P n 0 = Q n
  error_nonnegative : ∀ n k, 0 ≤ e n k
  error_summable : ∀ n, Summable (e n)
  tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k)
  base_harnack : ∀ n, ArclengthHarnackCertificate (Q n)
  stage : ∀ n k,
    GaugeRearFamilyVariableTerminal.RawStageOutput
      (P n k) (P (n + 1) k) (P n (k + 1)) (e n k)
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
  harnackClosed : ∀ n x, Tendsto (P n) atTop (nhds x) →
    (∀ k, ArclengthHarnackCertificate (P n k)) → ArclengthHarnackCertificate x

def Family.toScheme
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : Family Q e P0 P1 khat G1 Cg C c dlt) :
    TriangularMarkedPathSchemeVariableTerminal.Scheme
      Q F.P e P0 P1 khat G1 Cg C c dlt where
  base := F.base
  error_nonnegative := F.error_nonnegative
  error_summable := F.error_summable
  tube := F.tube
  stepPath := fun n k => (F.stage n k).increment
  stepGeometry := fun n k => (F.stage n k).increment_geometry
  stepCost := fun n k => (F.stage n k).increment_cost
  finiteEdge := fun n k => (F.stage n k).range_edge
  finiteHarnack := by
    intro n k
    cases k with
    | zero => simpa [F.base n] using F.base_harnack n
    | succ k => exact (F.stage n k).rear_harnack
  harnackClosed := F.harnackClosed

theorem exists_limitOutput
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : Family Q e P0 P1 khat G1 Cg C c dlt)
    (hc : 0 < c) :
    Nonempty (TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q F.P e P0 P1 khat G1 Cg C c dlt) :=
  TriangularMarkedPathSchemeVariableTerminal.exists_limitOutput F.toScheme hc

end TriangularMarkedRecursiveChoiceVariableTerminal
