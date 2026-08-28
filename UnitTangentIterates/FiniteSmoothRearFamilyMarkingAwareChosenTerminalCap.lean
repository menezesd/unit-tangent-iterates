import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminal
import UnitTangentIterates.InterpolationVariableSpeedSelInvAdapter

/-!
# Quantitative cap of a sound marking-aware chosen terminal

The endpoint distance and the terminal curvature below belong to the same
chosen long-theorem output.  This is the rowwise estimate needed by the capped
marking-aware recursion; no independent terminal is selected.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareChosenTerminal

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  InterpolationVariableSpeedSelInvAdapter

/-- Linearize the exact retained-frame endpoint modulus on a bounded cost
interval. -/
theorem Output.endpoint_dist_le_linear
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B)
    (hM : 0 ≤ M) (hL : 0 ≤ B.physical.L)
    (hkb : 0 ≤ B.physical.kb) (hkL : 0 ≤ B.physical.kL)
    (hcost : O.chosen.Delta.cost ≤ M) :
    dist O.jets.rear base ≤
      canonicalMarkingLinearConst B.Lmax (rearPeriod A 0)
        (rearKappa1 kh) (rearKappa2 kh) M
        B.physical.L B.physical.kb B.physical.kL *
          O.chosen.Delta.cost := by
  apply O.endpoint_dist.trans
  apply markingC2Bound_flow_le_linear
  · exact (A.rear_period_pos 0).le.trans (B.rearPeriod_le 0)
  · exact (A.rear_period_pos 0).le
  · exact rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one
  · exact rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one
  · exact hM
  · exact hL
  · exact hkb
  · exact hkL
  · exact O.chosen.Delta.cost_nonneg
  · exact hcost

/-- Weaken the exact linearized endpoint estimate to a row coefficient and a
diagonal defect.  This is the numerical form of one `ColumnCap` row. -/
theorem Output.endpoint_dist_le_coefficient_mul_diagonal
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound M coefficient diagonal : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B)
    (hM : 0 ≤ M) (hL : 0 ≤ B.physical.L)
    (hkb : 0 ≤ B.physical.kb) (hkL : 0 ≤ B.physical.kL)
    (hcostM : O.chosen.Delta.cost ≤ M)
    (hcoefficient :
      canonicalMarkingLinearConst B.Lmax (rearPeriod A 0)
        (rearKappa1 kh) (rearKappa2 kh) M
        B.physical.L B.physical.kb B.physical.kL ≤ coefficient)
    (hcostDiagonal : O.chosen.Delta.cost ≤ diagonal) :
    dist O.jets.rear base ≤ coefficient * diagonal := by
  have hlinear := O.endpoint_dist_le_linear hM hL hkb hkL hcostM
  have hcanonical : 0 ≤
      canonicalMarkingLinearConst B.Lmax (rearPeriod A 0)
        (rearKappa1 kh) (rearKappa2 kh) M
        B.physical.L B.physical.kb B.physical.kL :=
    canonicalMarkingLinearConst_nonneg
      ((A.rear_period_pos 0).le.trans (B.rearPeriod_le 0))
      (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one)
  exact hlinear.trans
    (mul_le_mul hcoefficient hcostDiagonal O.chosen.Delta.cost_nonneg
      (hcanonical.trans hcoefficient))

end FiniteSmoothRearFamilyMarkingAwareChosenTerminal
