import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput

/-! # Presented terminal input for n-aligned correlated columns -/

noncomputable section

open Set Function MarkedSpace PathMetric RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput0

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyPhysicalFront

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {K0 K1 K2 : ℝ}

/-- Terminal input for a source stored on rich stage `n`.  Both selected-rear
endpoint presentations are explicit; neither is coerced to a legacy column
slot. -/
structure PresentedData0
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (E : Applied (S.column.step.richStage n).stage.increment (S.source n))
    (initialPresented terminalPresented : Data) where
  physical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts terminalPresented
  zero_floor_tube : IsTubeMember physical.cq 0 physical.dlt terminalPresented
  physical_dlt_pos : 0 < physical.dlt
  initial : ∀ u,
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf 0 (E.Phi 0 u) = initialPresented.1 u
  terminal_carrier : ∀ x, terminalPresented.1 (x / perim terminalPresented) =
    rearOwn (S.source n).F (S.source n).Theta (S.source n).delta
      (S.source n).sf (S.column.step.richStage n).stage.increment.T x
  canonical_range : range (⇑(S.column.step.next n).1) =
    range (UnitTangent.unitTangentMap (ev terminalPresented))
  strict : UnconditionalAssembly.LimitStrictnessDataH terminalPresented
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
  Lmax : ℝ
  rearPeriod_le : ∀ t, rearPeriod (S.source n) t ≤ Lmax
  rearPeriod_terminal : rearPeriod (S.source n)
      (S.column.step.richStage n).stage.increment.T = perim terminalPresented
  physicalFront : Certificate (kh n) terminalPresented (S.column.step.next n)
  physicalFront_eq : physicalFront.physicalFront = terminalPresented

theorem PresentedData0.exists_terminalInput
    {S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied (S.column.step.richStage n).stage.increment (S.source n)}
    {initialPresented terminalPresented : Data}
    (R : PresentedData0 S E initialPresented terminalPresented) :
    Nonempty (TerminalInput (p := initialPresented) (base := terminalPresented)
      (bound := e n (k + 1)) E) := by
  exact ⟨TerminalInput.mk R.initial R.physical R.zero_floor_tube
    R.physical_dlt_pos R.terminal_carrier R.canonical_range R.strict
    R.normal_sup R.cost_le R.lambda R.Lambda R.lambda_pos
    R.flow_lower R.flow_upper R.Lmax R.rearPeriod_le R.rearPeriod_terminal
    R.physicalFront R.physicalFront_eq⟩

noncomputable def PresentedData0.terminalInput
    {S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied (S.column.step.richStage n).stage.increment (S.source n)}
    {initialPresented terminalPresented : Data}
    (R : PresentedData0 S E initialPresented terminalPresented) :
    TerminalInput (p := initialPresented) (base := terminalPresented)
      (bound := e n (k + 1)) E :=
  Classical.choice R.exists_terminalInput

end FiniteSmoothRearFamilyMarkingAwareConfiguredTerminalInput0
