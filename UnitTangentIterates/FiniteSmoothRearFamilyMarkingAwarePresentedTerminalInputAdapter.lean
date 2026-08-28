import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometryAssembly
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminal

/-!
# Terminal input from intrinsic presented terminal geometry

The intrinsic terminal-geometry theorem already proves all physical endpoint
facts needed by a presented chosen row.  This adapter keeps only the initial
alignment and scalar flow bounds as explicit row-construction obligations.
-/

noncomputable section

open Set MarkedSpace PathMetric RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwarePresentedTerminalInputAdapter

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareSource

/-- Assemble the sound terminal boundary directly from the intrinsic terminal
rear.  No correlated-column or recursive-core object is involved. -/
def ofPresentedTerminalGeometry
    {a b p : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) (G : PresentedTerminalGeometry A E)
    (hinitial : ∀ u,
      rearOwn A.F A.Theta A.delta A.sf 0 (E.Phi 0 u) = p.1 u)
    (hfront : range (⇑b.1) = range (A.F Gamma.T))
    (hcost : (∫ t in (0 : ℝ)..Gamma.T, A.m t) ≤ bound)
    {lambda Lambda : ℝ} (hlambda : 0 < lambda)
    (hlower : ∀ u, lambda ≤
      FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
        E.Phi (rearPeriod A 0) Gamma.T u / perim G.presented)
    (hupper : ∀ u,
      FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
        E.Phi (rearPeriod A 0) Gamma.T u / perim G.presented ≤ Lambda) :
    PresentedTerminalInputCore (p := p) (base := G.presented)
      (bound := bound) E where
  initial := hinitial
  physical := G.physical
  zero_floor_tube := G.zero_floor_tube
  dlt_pos := G.physical_dlt_pos
  terminal_carrier := G.carrier
  canonical_range := hfront.trans G.tangent_range.symm
  strict := G.strict
  normal_sup := G.normal_sup
  cost_le := hcost
  lambda := lambda
  Lambda := Lambda
  lambda_pos := hlambda
  flow_lower := hlower
  flow_upper := hupper
  Lmax := G.Lmax
  rearPeriod_le := G.period_le
  rearPeriod_terminal := by
    simpa [terminalPeriod,
      FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod] using
      G.period_eq.symm
  frontData := G.frontData
  frontKinematics := G.frontKinematics
  physicalFront := G.physicalFront

end FiniteSmoothRearFamilyMarkingAwarePresentedTerminalInputAdapter
