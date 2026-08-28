import Mathlib
import UnitTangentIterates.C2NormalPathJunctionAdapter
import UnitTangentIterates.MarkedTopology

/-! # Summable controlled-junction sequences -/

noncomputable section

open Set Filter Topology MarkedSpace

namespace PathMetric

open NormalPath

/-- Per-stage strengthened path and junction certificates. -/
structure ControlledJunctionSequence (Q : ℕ → Data) where
  basePath : ∀ n, NormalPath (Q n) (Q (n + 1))
  baseC2 : ∀ n, C2NormalPathData (basePath n)
  junction : ∀ n, ReparamJunctionCertificate (p' := Q n) (q' := Q (n + 1)) (basePath n)
  junctionC2 : ∀ n, ReparamC2Certificate (basePath n) (baseC2 n) (junction n)

/-- The controlled marked path at stage `n`. -/
def ControlledJunctionSequence.path {Q : ℕ → Data}
    (S : ControlledJunctionSequence Q) (n : ℕ) : NormalPath (Q n) (Q (n + 1)) :=
  reparamAtJunction (S.basePath n) (S.baseC2 n) (S.junction n)

def ControlledJunctionSequence.path_c2 {Q : ℕ → Data}
    (S : ControlledJunctionSequence Q) (n : ℕ) : C2NormalPathData (S.path n) :=
  c2NormalPathData_reparamAtJunction (S.baseC2 n) (S.junction n) (S.junctionC2 n)

theorem ControlledJunctionSequence.path_cost {Q : ℕ → Data}
    (S : ControlledJunctionSequence Q) (n : ℕ) :
    cost (S.path n) =
      reparamCostConst (S.junction n).m (S.junction n).M (S.junction n).N *
        cost (S.basePath n) :=
  cost_reparamAtJunction (S.baseC2 n) (S.junction n)

/-- **Summable controlled-junction limit.**

The geometric comparison theorem is deliberately a hypothesis `hdist`: it may
come from the variable-speed `C²` increment estimate or from a separate
transport/marking comparison.  Everything specific to the controlled spatial
junction is constructed here. -/
theorem exists_limit_of_summable_controlledJunctions
    {Q : ℕ → Data} (S : ControlledJunctionSequence Q)
    {e : ℕ → ℝ} {c kmin dlt Cmetric : ℝ}
    (he0 : ∀ n, 0 ≤ e n) (hesum : Summable e)
    (hcost : ∀ n, cost (S.path n) ≤ e n)
    (hCmetric : 0 ≤ Cmetric)
    (hdist : ∀ n, dist (Q n) (Q (n + 1)) ≤ Cmetric * cost (S.path n))
    (htube : ∀ n, IsTubeMember c kmin dlt (Q n))
    (htube_closed : ∀ X, Tendsto Q atTop (𝓝 X) → IsTubeMember c kmin dlt X) :
    ∃ X : Data,
      Tendsto Q atTop (𝓝 X) ∧ IsTubeMember c kmin dlt X ∧
      (∀ n, Nonempty (C2NormalPathData (S.path n))) ∧
      (∀ n, cost (S.path n) ≤ e n) ∧
      (∀ n, dist (Q n) (Q (n + 1)) ≤ Cmetric * e n) := by
  have hsum' : Summable (fun n => Cmetric * e n) := hesum.mul_left Cmetric
  have hstep : ∀ n, dist (Q n) (Q (n + 1)) ≤ Cmetric * e n := by
    intro n
    exact (hdist n).trans (mul_le_mul_of_nonneg_left (hcost n) hCmetric)
  have hdistsum : Summable fun n => dist (Q n) (Q (n + 1)) :=
    Summable.of_nonneg_of_le (fun _ => dist_nonneg) hstep hsum'
  have hCauchy : CauchySeq Q := cauchySeq_of_summable_dist hdistsum
  obtain ⟨X, hX⟩ := cauchySeq_tendsto_of_complete hCauchy
  exact ⟨X, hX, htube_closed X hX, fun n => ⟨S.path_c2 n⟩, hcost, hstep⟩

/-- Capstone-facing form retaining an exact stagewise transport identity and
passing it to the limit through a continuous operator. -/
theorem exists_limit_of_summable_controlledJunctions_transport
    {Q : ℕ → Data} (S : ControlledJunctionSequence Q)
    {e : ℕ → ℝ} {c kmin dlt Cmetric : ℝ} {B : Data → Data}
    (he0 : ∀ n, 0 ≤ e n) (hesum : Summable e)
    (hcost : ∀ n, cost (S.path n) ≤ e n)
    (hCmetric : 0 ≤ Cmetric)
    (hdist : ∀ n, dist (Q n) (Q (n + 1)) ≤ Cmetric * cost (S.path n))
    (htube : ∀ n, IsTubeMember c kmin dlt (Q n))
    (htube_closed : ∀ X, Tendsto Q atTop (𝓝 X) → IsTubeMember c kmin dlt X)
    (htransport : ∀ n, Q n = B (Q (n + 1))) (hB : Continuous B) :
    ∃ X : Data,
      Tendsto Q atTop (𝓝 X) ∧ IsTubeMember c kmin dlt X ∧ X = B X ∧
      (∀ n, Q n = B (Q (n + 1))) ∧
      (∀ n, Nonempty (C2NormalPathData (S.path n))) ∧
      (∀ n, cost (S.path n) ≤ e n) := by
  obtain ⟨X, hX, hXtube, hC2, hcost', hstep⟩ :=
    exists_limit_of_summable_controlledJunctions S he0 hesum hcost hCmetric
      hdist htube htube_closed
  have hshift : Tendsto (fun n => Q (n + 1)) atTop (𝓝 X) :=
    hX.comp (Filter.tendsto_add_atTop_nat 1)
  have hBX : Tendsto (fun n => B (Q (n + 1))) atTop (𝓝 (B X)) := hB.continuousAt.tendsto.comp hshift
  have hsame : Tendsto (fun n => B (Q (n + 1))) atTop (𝓝 X) := by
    simpa only [← htransport] using hX
  have hfix : X = B X := tendsto_nhds_unique hsame hBX
  exact ⟨X, hX, hXtube, hfix, htransport, hC2, hcost'⟩

end PathMetric
