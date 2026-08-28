import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput0

/-! # Presented endpoint alignment for n-aligned correlated columns -/

noncomputable section

open Set Function MarkedSpace PathMetric RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareSourceColumnAlignment0

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput0
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyPhysicalFront

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {K0 K1 K2 : ℝ}

/-- Source/column alignment with independent selected-rear presentations at
the two endpoints of the stage-`n` source. -/
structure PresentedAlignment0
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ)
    (initialPresented terminalPresented : Data) where
  physical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts terminalPresented
  zero_floor_tube : IsTubeMember physical.cq 0 physical.dlt terminalPresented
  physical_dlt_pos : 0 < physical.dlt
  initial : ∀ u,
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf 0 (rearPeriod (S.source n) 0 * u) = initialPresented.1 u
  terminal_carrier : ∀ x, terminalPresented.1 (x / perim terminalPresented) =
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf (S.column.step.richStage n).stage.increment.T x
  canonical_range : range (⇑(S.column.step.next n).1) =
    range (UnitTangent.unitTangentMap (ev terminalPresented))
  strict : UnconditionalAssembly.LimitStrictnessDataH terminalPresented
  Lmax : ℝ
  rearPeriod_le : ∀ t, rearPeriod (S.source n) t ≤ Lmax
  rearPeriod_terminal : rearPeriod (S.source n)
      (S.column.step.richStage n).stage.increment.T = perim terminalPresented
  physicalFront : Certificate (kh n) terminalPresented (S.column.step.next n)
  physicalFront_eq : physicalFront.physicalFront = terminalPresented

structure PresentedAppliedBounds0
    {S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (E : Applied (S.column.step.richStage n).stage.increment (S.source n))
    (terminalPresented : Data) where
  normal_sup : ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
    (iteratedDeriv j (fun u ↦ rearNormal (S.source n) t (E.Phi t u))) ≤
      (S.source n).m t
  cost_le : (∫ t in (0 : ℝ)..
      (S.column.step.richStage n).stage.increment.T,
      (S.source n).m t) ≤ e n (k + 1)
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  flow_lower : ∀ u, lambda ≤
    FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod (S.source n) 0)
      (S.column.step.richStage n).stage.increment.T u / perim terminalPresented
  flow_upper : ∀ u,
    FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod (S.source n) 0)
      (S.column.step.richStage n).stage.increment.T u / perim terminalPresented ≤ Lambda

def toPresentedTerminalData0
    {S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied (S.column.step.richStage n).stage.increment (S.source n)}
    {initialPresented terminalPresented : Data}
    (H : PresentedAlignment0 S n initialPresented terminalPresented)
    (B : PresentedAppliedBounds0 E terminalPresented) :
    PresentedData0 S E initialPresented terminalPresented where
  physical := H.physical
  zero_floor_tube := H.zero_floor_tube
  physical_dlt_pos := H.physical_dlt_pos
  initial u := by rw [E.initial]; exact H.initial u
  terminal_carrier := H.terminal_carrier
  canonical_range := H.canonical_range
  strict := H.strict
  normal_sup := B.normal_sup
  cost_le := B.cost_le
  lambda := B.lambda
  Lambda := B.Lambda
  lambda_pos := B.lambda_pos
  flow_lower := B.flow_lower
  flow_upper := B.flow_upper
  Lmax := H.Lmax
  rearPeriod_le := H.rearPeriod_le
  rearPeriod_terminal := H.rearPeriod_terminal
  physicalFront := H.physicalFront
  physicalFront_eq := H.physicalFront_eq

end FiniteSmoothRearFamilyMarkingAwareSourceColumnAlignment0
