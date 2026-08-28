import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminal
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
import UnitTangentIterates.ConfiguredEnrichedCommonTubeCertificate

/-!
# Configured terminal input from retained column gauge data

The certified column already stores ordinary terminal physical facts for the
exact base used by the next marking-aware source.  This module selects those
facts and isolates the remaining alignment, flow, and strictness data erased
by the correlated-column interface.
-/

noncomputable section

open Set Function MarkedSpace PathMetric RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput

open FiniteSmoothRearFamilyEnrichedMapProvider
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyPhysicalFront
  GaugeMarkedDataOfRearFamily
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {K0 K1 K2 : ℝ}

/-- The ordinary physical facts retained by the exact gauge certificate of
the source row. -/
def retainedPhysical
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ) :
    ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts
      (S.column.step.richStage (n + 1)).terminalBase :=
  Classical.choice ((S.column.gauge (n + 1)).terminalPhysical_nonempty)

/-- Exact residual data needed after `retainedPhysical` has discharged all
ordinary Frenet and tube geometry. -/
structure Data
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)) where
  zero_floor_tube : IsTubeMember (retainedPhysical S n).cq 0
    (retainedPhysical S n).dlt
    (S.column.step.richStage (n + 1)).terminalBase
  physical_dlt_pos : 0 < (retainedPhysical S n).dlt
  initial : ∀ u,
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf 0 (E.Phi 0 u) = (S.column.step.next n).1 u
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

/-- Assemble the exact marking-aware `TerminalInput`, with its physical facts
selected from the retained gauge certificate. -/
theorem Data.exists_terminalInput
    {Q current : ℕ → MarkedSpace.Data}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)} (R : Data S E) :
    Nonempty (TerminalInput
      (p := S.column.step.next n)
      (base := (S.column.step.richStage (n + 1)).terminalBase)
      (bound := e n (k + 1)) E) := by
  exact ⟨TerminalInput.mk R.initial (retainedPhysical S n) R.zero_floor_tube
    R.physical_dlt_pos R.terminal_carrier R.canonical_range R.strict
    R.normal_sup R.cost_le R.lambda R.Lambda R.lambda_pos
    R.flow_lower R.flow_upper R.Lmax R.rearPeriod_le R.rearPeriod_terminal
    R.physicalFront R.physicalFront_eq⟩

noncomputable def Data.terminalInput
    {Q current : ℕ → MarkedSpace.Data}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)} (R : Data S E) :
    TerminalInput
      (p := S.column.step.next n)
      (base := (S.column.step.richStage (n + 1)).terminalBase)
      (bound := e n (k + 1)) E :=
  Classical.choice R.exists_terminalInput

/-- Parallel terminal input whose terminal presentation is the actual marked
`Data` produced by the gauge, rather than the normalized terminal stored in
the legacy column. -/
structure PresentedData
    {Q current : ℕ → MarkedSpace.Data}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)) (presented : MarkedSpace.Data) where
  physical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts presented
  zero_floor_tube : IsTubeMember physical.cq 0 physical.dlt presented
  physical_dlt_pos : 0 < physical.dlt
  initial : ∀ u,
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf 0 (E.Phi 0 u) = (S.column.step.next n).1 u
  terminal_carrier : ∀ x, presented.1 (x / perim presented) =
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf
      (S.column.step.richStage (n + 1)).stage.increment.T x
  canonical_range : range (⇑(S.column.step.next (n + 1)).1) =
    range (UnitTangent.unitTangentMap (ev presented))
  strict : UnconditionalAssembly.LimitStrictnessDataH presented
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
  Lmax : ℝ
  rearPeriod_le : ∀ t, rearPeriod (S.source n) t ≤ Lmax
  rearPeriod_terminal : rearPeriod (S.source n)
      (S.column.step.richStage (n + 1)).stage.increment.T = perim presented
  frontData : MarkedSpace.Data
  frontKinematics : PhysicalRearLimitKinematics (kh n) presented frontData
  physicalFront : Certificate (kh n) presented frontData

theorem PresentedData.exists_terminalInput
    {Q current : ℕ → MarkedSpace.Data}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)} {presented : MarkedSpace.Data}
    (R : PresentedData S E presented) :
    Nonempty (PresentedTerminalInputCore (p := S.column.step.next n)
      (base := presented) (bound := e n (k + 1)) E) := by
  exact ⟨PresentedTerminalInputCore.mk R.initial R.physical R.zero_floor_tube
    R.physical_dlt_pos R.terminal_carrier R.canonical_range R.strict
    R.normal_sup R.cost_le R.lambda R.Lambda R.lambda_pos
    R.flow_lower R.flow_upper R.Lmax R.rearPeriod_le R.rearPeriod_terminal
    R.frontData R.frontKinematics R.physicalFront⟩

noncomputable def PresentedData.terminalInput
    {Q current : ℕ → MarkedSpace.Data}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied (S.column.step.richStage (n + 1)).stage.increment
      (S.source n)} {presented : MarkedSpace.Data}
    (R : PresentedData S E presented) :
    PresentedTerminalInputCore (p := S.column.step.next n)
      (base := presented) (bound := e n (k + 1)) E :=
  Classical.choice R.exists_terminalInput

end FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput
