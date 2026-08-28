import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminalCap
import UnitTangentIterates.SelectedInverseShiftEquivariance

/-!
# Canonical endpoint caps for a chosen marking-aware terminal

The endpoint of the theorem-produced chosen path is the nonaffinely marked
terminal datum.  Its quantitative marking defect is measured from the
ordinary canonical terminal representative.  This file rewrites that defect
against an explicitly phase-shifted canonical pullback datum, while keeping
the two kinds of geometric information on their sound representatives:

* ordinary tube, strictness, and physical facts on the canonical target;
* parameter-invariant Harnack and range-edge facts on the chosen endpoint.

No equality between the canonical marking and an unshifted selected inverse is
asserted.
-/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath

namespace FiniteSmoothRearFamilyMarkingAwareChosenCanonicalEndpointCap

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  GaugeMarkedDataOfRearFamily
  GaugeRearFamilyVariableTerminal
  InterpolationVariableSpeedSelInvAdapter
  VariableMarkedTube

/-- The exact retained-marking endpoint modulus of a presented chosen row. -/
def exactEndpointCap
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base)
      (bound := bound) E}
    (O : PresentedOutputCore E B) : ℝ :=
  MarkingDeviationC2.markingC2Bound
    (2 * B.Lmax * rearKappa1 kh * O.chosen.Delta.cost)
    (MarkingFlowDefectC2.flowDefectC1Int (rearPeriod A 0)
      (rearKappa1 kh * O.chosen.Delta.cost))
    (MarkingFlowDefectC2.flowDefectC2Int (rearPeriod A 0)
      (rearKappa1 kh * O.chosen.Delta.cost)
      (rearKappa2 kh * O.chosen.Delta.cost))
    B.physical.L B.physical.kb B.physical.kL

/-- A sound identification of the row's ordinary terminal representative with
the phase-coherent canonical pullback datum. -/
structure PhaseCanonicalTarget
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base)
      (bound := bound) E}
    (O : PresentedOutputCore E B) (canonical : Data) where
  phase : ℝ
  base_eq : base = MarkedShift.shiftData phase canonical

namespace PhaseCanonicalTarget

variable
    {a b p base canonical : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base)
      (bound := bound) E}
    {O : PresentedOutputCore E B}

/-- The endpoint encoded in the chosen normal path is exactly the marked
terminal datum used by the cap. -/
theorem chosen_finish (H : PhaseCanonicalTarget O canonical) (u : ℝ) :
    O.chosen.Delta.X O.chosen.Delta.T u = O.jets.rear.1 u :=
  O.chosen.Delta.finish u

/-- Exact endpoint cap against the phase-coherent canonical target. -/
theorem endpoint_dist_le (H : PhaseCanonicalTarget O canonical) :
    dist O.jets.rear (MarkedShift.shiftData H.phase canonical) ≤
      exactEndpointCap O := by
  rw [← H.base_eq]
  exact O.endpoint_dist

/-- The ordinary physical tube remains attached to the canonical target. -/
theorem target_tube (H : PhaseCanonicalTarget O canonical) :
    IsTubeMember B.physical.cq 0 B.physical.dlt
      (MarkedShift.shiftData H.phase canonical) := by
  rw [← H.base_eq]
  exact B.zero_floor_tube

/-- The retained strictness certificate remains attached to the canonical
target, not to the nonaffine chosen marking. -/
def target_strict (H : PhaseCanonicalTarget O canonical) :
    UnconditionalAssembly.LimitStrictnessDataH
      (MarkedShift.shiftData H.phase canonical) := by
  rw [← H.base_eq]
  exact B.strict

/-- The full physical terminal package transported to the coherent target. -/
def target_physical (H : PhaseCanonicalTarget O canonical) :
    ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts
      (MarkedShift.shiftData H.phase canonical) := by
  rw [← H.base_eq]
  exact B.physical

/-- The coherent target itself supplies a canonical Harnack representative. -/
def target_harnack (H : PhaseCanonicalTarget O canonical) :
    ArclengthHarnackCertificate
      (MarkedShift.shiftData H.phase canonical) where
  q := MarkedShift.shiftData H.phase canonical
  c := B.physical.cq
  dlt := B.physical.dlt
  c_pos := B.physical.cq_pos
  dlt_pos := B.dlt_pos
  tube := H.target_tube
  same_range := rfl
  strictness := H.target_strict

/-- Harnack data for the actual chosen endpoint.  This is deliberately not an
ordinary tube certificate for its nonaffine marking. -/
def endpoint_harnack (H : PhaseCanonicalTarget O canonical) :
    ArclengthHarnackCertificate O.jets.rear :=
  O.stage.rear_harnack

/-- Exact geometric range edge carried by the theorem-produced chosen row. -/
theorem endpoint_range_edge (H : PhaseCanonicalTarget O canonical) :
    GeometricUnitTangentRangeEdge b O.jets.rear :=
  O.stage.range_edge

/-- The chosen marking and the canonical terminal target have exactly the same
curve image. -/
theorem endpoint_range_eq_target (H : PhaseCanonicalTarget O canonical) :
    range (⇑O.jets.rear.1) =
      range (⇑(MarkedShift.shiftData H.phase canonical).1) := by
  have hcont : Continuous O.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (O.psi_deriv u).continuousAt
  have hmono : StrictMono O.marking.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(O.psi_deriv u).deriv]
    exact lt_of_lt_of_le B.lambda_pos (O.marking.lower u)
  have hsurj : Surjective O.marking.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcont hmono O.marking.translate O.psi_zero
  have hrange : range (⇑O.jets.rear.1) = range (⇑base.1) := by
    apply Set.Subset.antisymm
    · rintro z ⟨u, rfl⟩
      exact ⟨O.marking.psi u, (O.marking.position u).symm⟩
    · rintro z ⟨x, rfl⟩
      obtain ⟨u, hu⟩ := hsurj x
      exact ⟨u, by rw [O.marking.position u, hu]⟩
  simpa [H.base_eq] using hrange

/-- Direct raw-selected-inverse specialization.  The equality hypothesis is
kept explicit because it is generally false before fixing the terminal phase. -/
theorem endpoint_dist_le_selInv
    (H : PhaseCanonicalTarget O canonical) {kap : ℝ} {q : Data}
    (htarget : MarkedShift.shiftData H.phase canonical =
      SelectedInverseMap.selInv kap q) :
    dist O.jets.rear (SelectedInverseMap.selInv kap q) ≤
      exactEndpointCap O := by
  rw [← htarget]
  exact H.endpoint_dist_le

/-- Linearized cap on a bounded chosen cost interval. -/
theorem endpoint_dist_le_linear
    (H : PhaseCanonicalTarget O canonical) {M : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ B.physical.L)
    (hkb : 0 ≤ B.physical.kb) (hkL : 0 ≤ B.physical.kL)
    (hcost : O.chosen.Delta.cost ≤ M) :
    dist O.jets.rear (MarkedShift.shiftData H.phase canonical) ≤
      canonicalMarkingLinearConst B.Lmax (rearPeriod A 0)
        (rearKappa1 kh) (rearKappa2 kh) M
        B.physical.L B.physical.kb B.physical.kL *
          O.chosen.Delta.cost := by
  rw [← H.base_eq]
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

/-- Row-coefficient/diagonal form consumed by finite-column capstones. -/
theorem endpoint_dist_le_coefficient_mul_diagonal
    (H : PhaseCanonicalTarget O canonical)
    {M coefficient diagonal : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ B.physical.L)
    (hkb : 0 ≤ B.physical.kb) (hkL : 0 ≤ B.physical.kL)
    (hcostM : O.chosen.Delta.cost ≤ M)
    (hcoefficient :
      canonicalMarkingLinearConst B.Lmax (rearPeriod A 0)
        (rearKappa1 kh) (rearKappa2 kh) M
        B.physical.L B.physical.kb B.physical.kL ≤ coefficient)
    (hcostDiagonal : O.chosen.Delta.cost ≤ diagonal) :
    dist O.jets.rear (MarkedShift.shiftData H.phase canonical) ≤
      coefficient * diagonal := by
  have hlinear := H.endpoint_dist_le_linear hM hL hkb hkL hcostM
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

end PhaseCanonicalTarget

end FiniteSmoothRearFamilyMarkingAwareChosenCanonicalEndpointCap
