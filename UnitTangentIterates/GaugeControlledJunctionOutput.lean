import Mathlib
import UnitTangentIterates.GaugeRearFamilyFromFront
import UnitTangentIterates.C2NormalPathJunctionAdapter
import UnitTangentIterates.ControlledJunctionSequenceLimit

/-! # Gauge half of a controlled junction stage -/

noncomputable section

open Set Function MarkedSpace

namespace PathMetric

open NormalPath NormalPathC2IncrementVariableSpeed

/-- Compact downstream interface of the gauge rear-family construction.
The interpolation/fixed-reparameterization half is deliberately absent. -/
structure GaugeControlledJunctionOutput
    (p q : Data) (P0 P1 khat G1 Cg E : ℝ) where
  path : NormalPath p q
  c2 : C2NormalPathData path
  start : path.X 0 = p.1
  finish : path.X path.T = q.1
  variableSpeed : IsVariableSpeedNormalPath P0 P1 khat G1 Cg path
  cost_le : cost path ≤ E

/-- Package a gauge path after destructuring
`exists_variableSpeed_normalPath_of_rearFamily_from_front_with_eta_c2flow_and_c2`.
Its endpoint equalities are kept literally, rather than only as range
equalities, so the result can be used as one recursive marked stage. -/
def GaugeControlledJunctionOutput.ofGaugePath
    {p q : Data} {Gamma : NormalPath p q} {P0 P1 khat G1 Cg E : ℝ}
    (hC2 : C2NormalPathData Gamma)
    (hstart : Gamma.X 0 = p.1) (hfinish : Gamma.X Gamma.T = q.1)
    (hvar : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma)
    (hcost : cost Gamma ≤ E) :
    GaugeControlledJunctionOutput p q P0 P1 khat G1 Cg E where
  path := Gamma
  c2 := hC2
  start := hstart
  finish := hfinish
  variableSpeed := hvar
  cost_le := hcost

/-- A gauge output plus an abstract fixed spatial junction gives the path used
by `ControlledJunctionSequence`.  The cost inflation is exactly the existing
`reparamCostConst`. -/
theorem GaugeControlledJunctionOutput.exists_controlledStage
    {p q p' q' : Data} {P0 P1 khat G1 Cg E : ℝ}
    (G : GaugeControlledJunctionOutput p q P0 P1 khat G1 Cg E)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') G.path)
    (C : ReparamC2Certificate G.path G.c2 J) :
    ∃ Gamma' : NormalPath p' q',
      Nonempty (C2NormalPathData Gamma') ∧
      Gamma'.X 0 = p'.1 ∧ Gamma'.X Gamma'.T = q'.1 ∧
      cost Gamma' ≤ reparamCostConst J.m J.M J.N * E := by
  obtain ⟨Gamma', hC2, hstart, hfinish, hcost⟩ :=
    exists_controlled_reparam_junction G.c2 J C
  refine ⟨Gamma', hC2, hstart, hfinish, ?_⟩
  exact hcost.trans (mul_le_mul_of_nonneg_left G.cost_le
    (reparamCostConst_nonneg J.m_pos))

/-- Choose the `ControlledJunctionSequence` carried by stagewise gauge outputs
and abstract interpolation/reparameterization certificates. -/
def controlledJunctionSequenceOfGauge
    {Q : ℕ → Data} {P0 P1 khat G1 Cg : ℝ} {E : ℕ → ℝ}
    (G : ∀ n, GaugeControlledJunctionOutput (Q n) (Q (n + 1))
      P0 P1 khat G1 Cg (E n))
    (J : ∀ n, ReparamJunctionCertificate (p' := Q n) (q' := Q (n + 1)) (G n).path)
    (C : ∀ n, ReparamC2Certificate (G n).path (G n).c2 (J n)) :
    ControlledJunctionSequence Q where
  basePath := fun n => (G n).path
  baseC2 := fun n => (G n).c2
  junction := J
  junctionC2 := C

/-- Sequence-level gauge cost package.  A uniform bound for the abstract
junction constants is the only additional input needed to preserve
summability. -/
theorem controlledJunctionSequenceOfGauge_costs
    {Q : ℕ → Data} {P0 P1 khat G1 Cg C0 : ℝ} {E : ℕ → ℝ}
    (G : ∀ n, GaugeControlledJunctionOutput (Q n) (Q (n + 1))
      P0 P1 khat G1 Cg (E n))
    (J : ∀ n, ReparamJunctionCertificate (p' := Q n) (q' := Q (n + 1)) (G n).path)
    (C : ∀ n, ReparamC2Certificate (G n).path (G n).c2 (J n))
    (hC0 : 0 ≤ C0)
    (hconst : ∀ n, reparamCostConst (J n).m (J n).M (J n).N ≤ C0)
    (hE0 : ∀ n, 0 ≤ E n) (hEsum : Summable E) :
    let S := controlledJunctionSequenceOfGauge G J C
    (∀ n, cost (S.path n) ≤ C0 * E n) ∧ Summable (fun n => C0 * E n) := by
  dsimp only
  constructor
  · intro n
    have hbase := (cost_reparamAtJunction (G n).c2 (J n)).le
    exact hbase.trans <| mul_le_mul (hconst n) (G n).cost_le
      (G n).path.cost_nonneg hC0
  · exact hEsum.mul_left C0

/-- The complete gauge-derived prefix of
`PaperControlledJunctionInputs.ofVariableSpeed`.  Tube, range-orbit, ovality,
and closing inputs remain intentionally external. -/
structure GaugeControlledFamily
    (Q : ℕ → ℕ → Data) (P0 P1 khat G1 Cg : ℝ) where
  sequence : ∀ n, ControlledJunctionSequence (Q n)
  error : ℕ → ℕ → ℝ
  error_nonneg : ∀ n k, 0 ≤ error n k
  error_summable : ∀ n, Summable (error n)
  path_cost : ∀ n k, cost ((sequence n).path k) ≤ error n k
  variableSpeed : ∀ n k,
    IsVariableSpeedNormalPath P0 P1 khat G1 Cg ((sequence n).path k)

/-- Assemble the gauge prefix from a two-index family of controlled sequences
and their already-inflated summable stage majorants. -/
def GaugeControlledFamily.ofSequences
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg : ℝ}
    (S : ∀ n, ControlledJunctionSequence (Q n))
    (e : ℕ → ℕ → ℝ)
    (he0 : ∀ n k, 0 ≤ e n k)
    (hesum : ∀ n, Summable (e n))
    (hcost : ∀ n k, cost ((S n).path k) ≤ e n k)
    (hvar : ∀ n k,
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg ((S n).path k)) :
    GaugeControlledFamily Q P0 P1 khat G1 Cg where
  sequence := S
  error := e
  error_nonneg := he0
  error_summable := hesum
  path_cost := hcost
  variableSpeed := hvar

end PathMetric
