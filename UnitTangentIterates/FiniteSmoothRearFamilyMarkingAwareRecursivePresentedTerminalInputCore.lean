import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminal

/-!
# Sound presented terminal inputs from recursive terminal geometry

The recursive terminal constructor supplies the selected rear presentation,
its physical geometry, strictness, normal bounds, period control, and the
canonical physical-front certificate.  This adapter combines those fields
with the scalar flow/cost estimates of one actual application.
-/

noncomputable section

open Function Set MarkedSpace MarkedTopology PathMetric RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalInputCore

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyPhysicalFront

variable {p q a b : Data} {Gamma : NormalPath p q}
  {Delta : NormalPath a b}
  {P0 kh khat Qmax periodLower kap khatNext QmaxNext bound : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}

/-- The application-specific facts not already retained by recursive terminal
geometry. -/
structure Inputs
    (X : RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext)
    (E : Applied Delta X.source)
    (G : PresentedTerminalGeometry X.source E) (initial : Data) where
  initial_alignment : ∀ u,
    rearOwn X.source.F X.source.Theta X.source.delta X.source.sf 0
      (E.Phi 0 u) = initial.1 u
  cost_le : (∫ t in (0 : ℝ)..Delta.T, X.source.m t) ≤ bound
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  flow_lower : ∀ u, lambda ≤
    FlowDerivative.flowDeriv (fun t x => -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod X.source 0) Delta.T u / perim G.presented
  flow_upper : ∀ u,
    FlowDerivative.flowDeriv (fun t x => -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod X.source 0) Delta.T u / perim G.presented ≤ Lambda

/-- All sound terminal-input fields follow from the recursive geometry and
the application-specific scalar/front facts above. -/
def Inputs.toPresentedTerminalInputCore
    {X : RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext}
    {E : Applied Delta X.source}
    {G : PresentedTerminalGeometry X.source E} {initial : Data}
    (I : Inputs (bound := bound) X E G initial) :
    PresentedTerminalInputCore (p := initial) (base := G.presented)
      (bound := bound) E where
  initial := I.initial_alignment
  physical := G.physical
  zero_floor_tube := G.zero_floor_tube
  dlt_pos := G.physical_dlt_pos
  terminal_carrier := G.carrier
  canonical_range :=
    (FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry.RecursiveAnalyticSuccessor.presented_tangentRange_endpoint
      X G).symm
  strict := G.strict
  normal_sup := G.normal_sup
  cost_le := I.cost_le
  lambda := I.lambda
  Lambda := I.Lambda
  lambda_pos := I.lambda_pos
  flow_lower := I.flow_lower
  flow_upper := I.flow_upper
  Lmax := G.Lmax
  rearPeriod_le := G.period_le
  rearPeriod_terminal := by
    simpa [terminalPeriod] using G.period_eq.symm
  frontData := G.frontData
  frontKinematics := G.frontKinematics
  physicalFront := G.physicalFront

/-- The canonical physical-front presentation has the same unparameterized
range as the marked endpoint of the recursive path. -/
theorem front_range_endpoint
    {X : RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext}
    {E : Applied Delta X.source}
    (G : PresentedTerminalGeometry X.source E) :
    range (ev G.frontData) = range b.1 :=
  G.front_range.trans X.terminalRange

end FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalInputCore
