import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput

/-! # Source/column alignment retained before terminal selection -/

noncomputable section

open Set Function MarkedSpace PathMetric RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareSourceColumnAlignment

open FiniteSmoothRearFamilyEnrichedMapProvider
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyPhysicalFront
  GaugeMarkedDataOfRearFamily
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {K0 K1 K2 : ℝ}

/-- The source-independent geometric equalities erased when a certified
column is paired with a marking-aware source. -/
structure Alignment
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ) where
  zero_floor_tube : IsTubeMember (retainedPhysical S n).cq 0
    (retainedPhysical S n).dlt
    (S.column.step.richStage (n + 1)).terminalBase
  physical_dlt_pos : 0 < (retainedPhysical S n).dlt
  initial : ∀ u,
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf 0 (rearPeriod (S.source n) 0 * u) =
        (S.column.step.next n).1 u
  terminal_carrier : ∀ x,
    (S.column.step.richStage (n + 1)).terminalBase.1
        (x / perim (S.column.step.richStage (n + 1)).terminalBase) =
      rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
        (S.source n).sf
        (S.column.step.richStage (n + 1)).stage.increment.T x
  canonical_range : range (⇑(S.column.step.next (n + 1)).1) =
    range (UnitTangent.unitTangentMap
      (ev (S.column.step.richStage (n + 1)).terminalBase))
  strict : UnconditionalAssembly.LimitStrictnessDataH
    (S.column.step.richStage (n + 1)).terminalBase
  Lmax : ℝ
  rearPeriod_le : ∀ t, rearPeriod (S.source n) t ≤ Lmax
  rearPeriod_terminal : rearPeriod (S.source n)
      (S.column.step.richStage (n + 1)).stage.increment.T =
    perim (S.column.step.richStage (n + 1)).terminalBase
  physicalFront : Certificate (kh n)
    (S.column.step.richStage (n + 1)).terminalBase
      (S.column.step.next (n + 1))
  physicalFront_eq : physicalFront.physicalFront =
    (S.column.step.richStage (n + 1)).terminalBase

/-- The genuinely application-dependent estimates not contained in the
intrinsic long-theorem result. -/
structure AppliedBounds
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)) where
  normal_sup : ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
    (iteratedDeriv j (fun u ↦ rearNormal (S.source n) t (E.Phi t u))) ≤
      (S.source n).m t
  cost_le : (∫ t in (0 : ℝ)..
      (S.column.step.richStage (n + 1)).stage.increment.T,
      (S.source n).m t) ≤ e n (k + 1)
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  flow_lower : ∀ u, lambda ≤
    FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod (S.source n) 0)
      (S.column.step.richStage (n + 1)).stage.increment.T u /
        perim (S.column.step.richStage (n + 1)).terminalBase
  flow_upper : ∀ u,
    FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod (S.source n) 0)
      (S.column.step.richStage (n + 1)).stage.increment.T u /
        perim (S.column.step.richStage (n + 1)).terminalBase ≤ Lambda

/-- Assemble the existing terminal-input residual package.  The initial
alignment is now source-level: `Applied.initial` supplies the only rewrite. -/
def toTerminalData
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)} (H : Alignment S n) (B : AppliedBounds E) :
    FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput.Data S E where
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

/-- Source/column alignment with an explicitly propagated terminal
presentation.  No equality with the legacy normalized terminal is asserted. -/
structure PresentedAlignment
    {Q current : ℕ → MarkedSpace.Data}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ)
    (presented : MarkedSpace.Data) where
  physical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts presented
  zero_floor_tube : IsTubeMember physical.cq 0 physical.dlt presented
  physical_dlt_pos : 0 < physical.dlt
  initial : ∀ u,
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf 0 (rearPeriod (S.source n) 0 * u) =
        (S.column.step.next n).1 u
  terminal_carrier : ∀ x, presented.1 (x / perim presented) =
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf
      (S.column.step.richStage (n + 1)).stage.increment.T x
  canonical_range : range (⇑(S.column.step.next (n + 1)).1) =
    range (UnitTangent.unitTangentMap (ev presented))
  strict : UnconditionalAssembly.LimitStrictnessDataH presented
  Lmax : ℝ
  rearPeriod_le : ∀ t, rearPeriod (S.source n) t ≤ Lmax
  rearPeriod_terminal : rearPeriod (S.source n)
      (S.column.step.richStage (n + 1)).stage.increment.T = perim presented
  physicalFront : Certificate (kh n) presented (S.column.step.next (n + 1))

/-- Application estimates whose normalization uses the propagated terminal
presentation. -/
structure PresentedAppliedBounds
    {Q current : ℕ → MarkedSpace.Data}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)) (presented : MarkedSpace.Data) where
  normal_sup : ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
    (iteratedDeriv j (fun u ↦ rearNormal (S.source n) t (E.Phi t u))) ≤
      (S.source n).m t
  cost_le : (∫ t in (0 : ℝ)..
      (S.column.step.richStage (n + 1)).stage.increment.T,
      (S.source n).m t) ≤ e n (k + 1)
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  flow_lower : ∀ u, lambda ≤
    FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod (S.source n) 0)
      (S.column.step.richStage (n + 1)).stage.increment.T u / perim presented
  flow_upper : ∀ u,
    FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod (S.source n) 0)
      (S.column.step.richStage (n + 1)).stage.increment.T u / perim presented ≤ Lambda

def toPresentedTerminalData
    {Q current : ℕ → MarkedSpace.Data}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)} {presented : MarkedSpace.Data}
    (H : PresentedAlignment S n presented)
    (B : PresentedAppliedBounds E presented) :
    FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput.PresentedData
      S E presented where
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

end FiniteSmoothRearFamilyMarkingAwareSourceColumnAlignment
