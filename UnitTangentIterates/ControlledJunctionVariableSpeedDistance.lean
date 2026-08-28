import Mathlib
import UnitTangentIterates.ControlledJunctionSequenceLimit
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed

/-! # Marked-distance control for variable-speed junction paths -/

noncomputable section

open Set MarkedSpace

namespace PathMetric

open NormalPathC2IncrementVariableSpeed NormalPath

/-- A variable-speed controlled junction has marked endpoint distance bounded
by its cost.  Tube membership supplies the endpoint derivative witnesses
required by the marked `C²` increment theorem. -/
theorem dist_le_cost_controlledJunction_variableSpeed
    {p q : Data} {Gamma : NormalPath p q} (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p) (q' := q) Gamma)
    {cp kp dp cq kq dq P0 P1 khat G1 Cg : ℝ}
    (hp : IsTubeMember cp kp dp p) (hq : IsTubeMember cq kq dq q)
    (hvar : IsVariableSpeedNormalPath P0 P1 khat G1 Cg
      (reparamAtJunction Gamma hC2 J)) :
    dist p q ≤ c2ConstVar P0 P1 khat G1 Cg *
      cost (reparamAtJunction Gamma hC2 J) := by
  exact dist_le_cost_variableSpeed (reparamAtJunction Gamma hC2 J)
    (fun u => hp.hasDerivAt_curve u) (fun u => hq.hasDerivAt_curve u)
    (fun u => hp.hasDerivAt_vel u) (fun u => hq.hasDerivAt_vel u) hvar

/-- Sequence adapter discharging the geometric `hdist` hypothesis of
`exists_limit_of_summable_controlledJunctions`. -/
theorem controlledJunction_distances_variableSpeed
    {Q : ℕ → Data} (S : ControlledJunctionSequence Q)
    {c kmin dlt P0 P1 khat G1 Cg : ℝ}
    (htube : ∀ n, IsTubeMember c kmin dlt (Q n))
    (hvar : ∀ n, IsVariableSpeedNormalPath P0 P1 khat G1 Cg (S.path n)) :
    ∀ n, dist (Q n) (Q (n + 1)) ≤
      c2ConstVar P0 P1 khat G1 Cg * cost (S.path n) := by
  intro n
  exact dist_le_cost_controlledJunction_variableSpeed
    (S.baseC2 n) (S.junction n) (htube n) (htube (n + 1)) (hvar n)

/-- Complete sequence-level variable-speed junction limit. -/
theorem exists_limit_of_summable_variableSpeed_controlledJunctions
    {Q : ℕ → Data} (S : ControlledJunctionSequence Q)
    {e : ℕ → ℝ} {c kmin dlt P0 P1 khat G1 Cg : ℝ}
    (he0 : ∀ n, 0 ≤ e n) (hesum : Summable e)
    (hcost : ∀ n, cost (S.path n) ≤ e n)
    (hconst : 0 ≤ c2ConstVar P0 P1 khat G1 Cg)
    (htube : ∀ n, IsTubeMember c kmin dlt (Q n))
    (htube_closed : ∀ X, Filter.Tendsto Q Filter.atTop (nhds X) →
      IsTubeMember c kmin dlt X)
    (hvar : ∀ n, IsVariableSpeedNormalPath P0 P1 khat G1 Cg (S.path n)) :
    ∃ X : Data,
      Filter.Tendsto Q Filter.atTop (nhds X) ∧ IsTubeMember c kmin dlt X ∧
      (∀ n, Nonempty (C2NormalPathData (S.path n))) ∧
      (∀ n, cost (S.path n) ≤ e n) ∧
      (∀ n, dist (Q n) (Q (n + 1)) ≤
        c2ConstVar P0 P1 khat G1 Cg * e n) := by
  exact exists_limit_of_summable_controlledJunctions S he0 hesum hcost hconst
    (controlledJunction_distances_variableSpeed S htube hvar) htube htube_closed

/-- Transport-capstone specialization with the variable-speed distance
hypothesis fully discharged. -/
theorem exists_limit_of_summable_variableSpeed_controlledJunctions_transport
    {Q : ℕ → Data} (S : ControlledJunctionSequence Q)
    {e : ℕ → ℝ} {c kmin dlt P0 P1 khat G1 Cg : ℝ} {B : Data → Data}
    (he0 : ∀ n, 0 ≤ e n) (hesum : Summable e)
    (hcost : ∀ n, cost (S.path n) ≤ e n)
    (hconst : 0 ≤ c2ConstVar P0 P1 khat G1 Cg)
    (htube : ∀ n, IsTubeMember c kmin dlt (Q n))
    (htube_closed : ∀ X, Filter.Tendsto Q Filter.atTop (nhds X) →
      IsTubeMember c kmin dlt X)
    (hvar : ∀ n, IsVariableSpeedNormalPath P0 P1 khat G1 Cg (S.path n))
    (htransport : ∀ n, Q n = B (Q (n + 1))) (hB : Continuous B) :
    ∃ X : Data,
      Filter.Tendsto Q Filter.atTop (nhds X) ∧ IsTubeMember c kmin dlt X ∧
      X = B X ∧ (∀ n, Q n = B (Q (n + 1))) ∧
      (∀ n, Nonempty (C2NormalPathData (S.path n))) ∧
      (∀ n, cost (S.path n) ≤ e n) := by
  exact exists_limit_of_summable_controlledJunctions_transport S he0 hesum hcost hconst
    (controlledJunction_distances_variableSpeed S htube hvar) htube htube_closed
    htransport hB

end PathMetric
