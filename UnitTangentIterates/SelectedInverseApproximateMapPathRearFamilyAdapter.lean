import UnitTangentIterates.SelectedInverseApproximateMapPath
import UnitTangentIterates.GaugeRearFamilyFromFront
import UnitTangentIterates.SelInvRearFamilySupFundamentalC2
import UnitTangentIterates.GaugeNormalPathSeparated
import UnitTangentIterates.ConfiguredGaugeEndpointDefect
import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-!
# Rear-family output adapter for the selected-inverse approximate map

`GaugeRearFamilyFromFront` already proves the large differential construction:
it selects the gauge flow and returns a continuation which produces a
variable-speed normal path once its two endpoint markings and the three `C^2`
normal-rate sup bounds are identified.  This file records exactly that output
boundary.  In particular, it does not repeat the many front/rear differential
hypotheses of the constructor theorem.

The separate fields `M_le` and `M_control` are intentional.  The old
`SelectedInverseApproximateMapPath.Residual.rawGauge` now distinguishes its
front input cap from the inflated rear cap `mapRearCostCap kh Mtotal`.  The
gauge construction supplies the latter after choosing and integrating the rear
density.
-/

noncomputable section

open Function Set Complex MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack RearOwnArclength RearFamilyFrame
  NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace SelectedInverseApproximateMapPath

open GaugeMarkedDataOfRearFamily

/-- The correlated output of the finite smooth rear-family construction.

Unlike the historical existential path output, this record retains the exact
gauge frame, separated Jacobi estimates, terminal flow jets, and ordinary
physical endpoint facts belonging to the *same* selected path.  In
particular, `terminal_eq` prevents a downstream chosen recursion from making
an unrelated choice of marked terminal after it has selected `Delta`. -/
structure FiniteSmoothRearFamilyEnrichedOutput
    {p q : Data} (Gamma : NormalPath p q)
    (F : ℝ → ℝ → ℂ) (Theta delta sf : ℝ → ℝ → ℝ)
    (Ydot : ℝ → ℝ → ℂ) (Phi : ℝ → ℝ → ℝ)
    (periodValue costValue P0 kh khat : ℝ) (a b : Data) where
  Delta : NormalPath a b
  time_eq : Delta.T = Gamma.T
  density_eq : Delta.m = fun t => mapK kh * Gamma.m t
  cost_eq : cost Delta = costValue
  geometry : IsVariableSpeedNormalPath P0
    (costP1 periodValue khat costValue) khat
    (costG1 periodValue khat (rearKappa2 kh) costValue)
    (khat * costG1 periodValue khat (rearKappa2 kh) costValue +
      rearKappa2 kh * costP1 periodValue khat costValue ^ 2) Delta
  c2 : C2NormalPathData Delta
  Q : ℝ → ℝ
  Q' : ℝ → ℝ
  m : ℝ → ℝ
  xi : ℝ → ℝ → ℝ
  xiX : ℝ → ℝ → ℝ
  xiXX : ℝ → ℝ → ℝ
  kappa : ℝ
  kappa2 : ℝ
  retainedFrame : GaugeRearFamilyFundamental.RetainedGaugeFrame
    Phi Q Q' m xi kappa kappa2
  frame_m_eq : Delta.m = m
  m_continuous : Continuous m
  Q_zero_pos : 0 < Q 0
  Lmax : ℝ
  Q_le : ∀ t, Q t ≤ Lmax
  terminalBase : Data
  terminalJets : GaugeFlowMarkedTerminalJets.TerminalJets
    xi xiX xiXX Phi periodValue (perim terminalBase) Gamma.T terminalBase
  terminal_eq : terminalJets.rear = b
  Q_terminal : Q Delta.T = perim terminalBase
  physicalKinematics : PhysicalRearLimitKinematics kh terminalBase q
  terminalPhysical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts
    terminalBase
  lambda : ℝ
  Lambda : ℝ
  marking : NormalizedTerminalMarkingComposition.NormalizedC2Marking
    terminalBase b lambda Lambda
  terminal : GaugeRearFamilyVariableTerminal.RawTerminalResidual q b
  CW : ℝ
  C0 : ℝ
  C10 : ℝ
  C11 : ℝ
  C20 : ℝ
  C21 : ℝ
  C22 : ℝ
  flowed : GaugeNormalPathSeparated.FlowedBounds Gamma.eta Delta.eta
    CW C0 C10 C11 C20 C21 C22

/-- The correlated retained frame and terminal jets give the exact endpoint
marking defect for this same selected output. -/
theorem FiniteSmoothRearFamilyEnrichedOutput.endpoint_dist_le
    {p q a b : Data} {Gamma : NormalPath p q}
    {F : ℝ → ℝ → ℂ} {Theta delta sf : ℝ → ℝ → ℝ}
    {Ydot : ℝ → ℝ → ℂ} {Phi : ℝ → ℝ → ℝ}
    {periodValue costValue P0 kh khat : ℝ}
    (E : FiniteSmoothRearFamilyEnrichedOutput Gamma F Theta delta sf Ydot Phi
      periodValue costValue P0 kh khat a b) :
    dist E.terminalBase b ≤
      MarkingDeviationC2.markingC2Bound
        (2 * E.Lmax * E.kappa * E.Delta.cost)
        (MarkingFlowDefectC2.flowDefectC1Int (E.Q 0)
          (E.kappa * E.Delta.cost))
        (MarkingFlowDefectC2.flowDefectC2Int (E.Q 0)
          (E.kappa * E.Delta.cost) (E.kappa2 * E.Delta.cost))
        E.terminalPhysical.L E.terminalPhysical.kb E.terminalPhysical.kL := by
  have H := ConfiguredGaugeEndpointDefect.dist_terminalJets_le_of_retainedGaugeFrame
    E.Delta E.retainedFrame E.terminalJets E.terminalPhysical
    E.m_continuous E.frame_m_eq E.time_eq E.Q_zero_pos E.Q_le E.Q_terminal
  simpa [E.terminal_eq, dist_comm] using H

/-- Forget the retained analytic data only after assembling the exact rich
variable-terminal stage carried by the enriched output. -/
def FiniteSmoothRearFamilyEnrichedOutput.toRichStageData
    {p q a b : Data} {Gamma : NormalPath p q}
    {F : ℝ → ℝ → ℂ} {Theta delta sf : ℝ → ℝ → ℝ}
    {Ydot : ℝ → ℝ → ℂ} {Phi : ℝ → ℝ → ℝ}
    {periodValue costValue P0 kh khat : ℝ}
    (E : FiniteSmoothRearFamilyEnrichedOutput Gamma F Theta delta sf Ydot Phi
      periodValue costValue P0 kh khat a b)
    {bound c C dlt : ℝ} (hcost : costValue ≤ bound) :
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData
      a q b bound P0 (costP1 periodValue khat costValue) khat
      (costG1 periodValue khat (rearKappa2 kh) costValue)
      (khat * costG1 periodValue khat (rearKappa2 kh) costValue +
        rearKappa2 kh * costP1 periodValue khat costValue ^ 2)
      c C dlt where
  stage :=
    { increment := E.Delta
      increment_geometry := E.geometry
      increment_cost := E.cost_eq.le.trans hcost
      rear_curve_deriv := E.terminal.rear_curve_deriv
      rear_vel_deriv := E.terminal.rear_vel_deriv
      rear_periodic := E.terminal.rear_periodic
      rear_curvature_nonnegative := E.terminal.rear_curvature_nonnegative
      range_edge := E.terminal.range_edge
      rear_harnack := E.terminal.rear_harnack }
  terminalBase := E.terminalBase
  lambda := E.lambda
  Lambda := E.Lambda
  marking := E.marking

/-- The finite output of one smooth selected-rear gauge family.

The `produceEnriched` field is precisely the strengthened continuation returned by
`GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`,
without forgetting its correlated analytic data.  The remaining fields are
the facts which that theorem deliberately leaves to its caller: marking
compatibility, the gauge-coordinate sup density, and uniform period/cost
caps. -/
structure FiniteSmoothRearFamilyCertificate
    {p q : Data} (Gamma : NormalPath p q)
    (P0 kh khat Qmax Mtotal : ℝ) : Type where
  F : ℝ → ℝ → ℂ
  Theta : ℝ → ℝ → ℝ
  delta : ℝ → ℝ → ℝ
  sf : ℝ → ℝ → ℝ
  Ydot : ℝ → ℝ → ℂ
  Phi : ℝ → ℝ → ℝ
  periodValue : ℝ
  costValue : ℝ
  period_nonneg : 0 ≤ periodValue
  period_le : periodValue ≤ Qmax
  cost_nonneg : 0 ≤ costValue
  cost_le : costValue ≤ mapRearCostCap kh Mtotal
  cost_control : costValue ≤ mapK kh * cost Gamma
  phi_initial : ∀ u, Phi 0 u = periodValue * u
  phi_base : ∀ t, Phi t 0 = 0
  phi_flow : ∀ u t, HasDerivAt (fun r => Phi r u)
    (-frameTangential Ydot (rearOwnAngle Theta delta sf) t (Phi t u)) t
  initial_marking : ∀ u,
    rearOwn F Theta delta sf 0 (Phi 0 u) =
      (SelectedInverseMap.selInv kh p).1 u
  terminal_marking : ∀ u,
    rearOwn F Theta delta sf Gamma.T (Phi Gamma.T u) =
      (SelectedInverseMap.selInv kh q).1 u
  normalRate_sup : ∀ t, ∀ j ≤ 2,
    supNorm (iteratedDeriv j
      (fun u => frameNormal Ydot (rearOwnAngle Theta delta sf) t (Phi t u))) ≤
      mapK kh * Gamma.m t
  produceEnriched : ∀ (a b : Data),
    (∀ u, rearOwn F Theta delta sf 0 (Phi 0 u) = a.1 u) →
    (∀ u, rearOwn F Theta delta sf Gamma.T (Phi Gamma.T u) = b.1 u) →
    (∀ t, ∀ j ≤ 2,
      supNorm (iteratedDeriv j
        (fun u => frameNormal Ydot (rearOwnAngle Theta delta sf) t (Phi t u))) ≤
        mapK kh * Gamma.m t) →
    Nonempty (FiniteSmoothRearFamilyEnrichedOutput Gamma F Theta delta sf
      Ydot Phi periodValue costValue P0 kh khat a b)

/-- Historical finite path output, now a projection of the correlated
enriched output rather than a second existential choice. -/
theorem FiniteSmoothRearFamilyCertificate.produce
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax Mtotal : ℝ}
    (C : FiniteSmoothRearFamilyCertificate Gamma P0 kh khat Qmax Mtotal)
    (a b : Data)
    (hinitial : ∀ u, rearOwn C.F C.Theta C.delta C.sf 0 (C.Phi 0 u) = a.1 u)
    (hterminal : ∀ u,
      rearOwn C.F C.Theta C.delta C.sf Gamma.T (C.Phi Gamma.T u) = b.1 u)
    (hsup : ∀ t, ∀ j ≤ 2,
      supNorm (iteratedDeriv j
        (fun u => frameNormal C.Ydot
          (rearOwnAngle C.Theta C.delta C.sf) t (C.Phi t u))) ≤
        mapK kh * Gamma.m t) :
    ∃ Delta : NormalPath a b,
      Delta.T = Gamma.T ∧
      Delta.m = (fun t => mapK kh * Gamma.m t) ∧
      cost Delta = C.costValue ∧
      IsVariableSpeedNormalPath P0 (costP1 C.periodValue khat C.costValue) khat
        (costG1 C.periodValue khat (rearKappa2 kh) C.costValue)
        (khat * costG1 C.periodValue khat (rearKappa2 kh) C.costValue +
          rearKappa2 kh * costP1 C.periodValue khat C.costValue ^ 2) Delta := by
  let E := Classical.choice (C.produceEnriched a b hinitial hterminal hsup)
  exact ⟨E.Delta, E.time_eq, E.density_eq, E.cost_eq, E.geometry⟩

/-- A deterministic view of an enriched finite certificate.  The chosen
output is made once and all retained fields are projections of that same
choice.  This is the provider boundary used before a column is erased to a
plain `ColumnStep`. -/
structure EnrichedStageProducer
    {p q : Data} (Gamma : NormalPath p q)
    (P0 kh khat Qmax Mtotal : ℝ) where
  certificate : FiniteSmoothRearFamilyCertificate
    Gamma P0 kh khat Qmax Mtotal
  output : ∀ (a b : Data)
    (hinitial : ∀ u, rearOwn certificate.F certificate.Theta
      certificate.delta certificate.sf 0 (certificate.Phi 0 u) = a.1 u)
    (hterminal : ∀ u, rearOwn certificate.F certificate.Theta
      certificate.delta certificate.sf Gamma.T
        (certificate.Phi Gamma.T u) = b.1 u)
    (hsup : ∀ t, ∀ j ≤ 2,
      supNorm (iteratedDeriv j
        (fun u => frameNormal certificate.Ydot
          (rearOwnAngle certificate.Theta certificate.delta certificate.sf)
          t (certificate.Phi t u))) ≤ mapK kh * Gamma.m t),
    FiniteSmoothRearFamilyEnrichedOutput Gamma certificate.F
      certificate.Theta certificate.delta certificate.sf certificate.Ydot
      certificate.Phi certificate.periodValue certificate.costValue
      P0 kh khat a b

/-- Every enriched finite certificate canonically determines a deterministic
stage producer. -/
noncomputable def FiniteSmoothRearFamilyCertificate.toEnrichedStageProducer
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax Mtotal : ℝ}
    (C : FiniteSmoothRearFamilyCertificate Gamma P0 kh khat Qmax Mtotal) :
    EnrichedStageProducer Gamma P0 kh khat Qmax Mtotal where
  certificate := C
  output a b hinitial hterminal hsup :=
    Classical.choice (C.produceEnriched a b hinitial hterminal hsup)

/-- A provider of finite smooth rear-family certificates discharges the old
opaque `rawGauge` field.  All quantifiers and tube/domain restrictions remain
exactly those of `Residual`; the adapter changes only the analytic payload. -/
def Residual.ofFiniteSmoothRearFamily
    {P0 kh khat Qmax Mtotal c dlt : ℝ}
    (family : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 (mapRearP1 kh Qmax khat Mtotal) khat
        (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Gamma →
      cost Gamma ≤ Mtotal →
      Nonempty (FiniteSmoothRearFamilyCertificate
        Gamma P0 kh khat Qmax Mtotal)) :
    Residual P0 kh khat Qmax Mtotal c dlt where
  rawGauge := by
    intro p q Gamma hp hq hGamma hcost
    let C := Classical.choice (family p q Gamma hp hq hGamma hcost)
    obtain ⟨Delta, _hT, _hm, hDeltaCost, hDelta⟩ :=
      C.produce (SelectedInverseMap.selInv kh p)
        (SelectedInverseMap.selInv kh q)
        C.initial_marking C.terminal_marking C.normalRate_sup
    refine ⟨C.periodValue, C.costValue, C.period_nonneg, C.period_le,
      C.cost_nonneg, C.cost_le, Delta, ?_, hDelta⟩
    rw [hDeltaCost]
    exact C.cost_control

/-- Direct map-path form of the certificate adapter. -/
theorem exists_map_path_of_finiteSmoothRearFamily
    {P0 kh khat Qmax Mtotal c dlt : ℝ}
    (family : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 (mapRearP1 kh Qmax khat Mtotal) khat
        (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Gamma →
      cost Gamma ≤ Mtotal →
      Nonempty (FiniteSmoothRearFamilyCertificate
        Gamma P0 kh khat Qmax Mtotal))
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hkhat : 0 ≤ khat)
    {p q : Data} (Gamma : NormalPath p q)
    (hp : IsTubeMember c 0 dlt p) (hq : IsTubeMember c 0 dlt q)
    (hGamma : IsVariableSpeedNormalPath P0 (mapRearP1 kh Qmax khat Mtotal) khat
      (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Gamma)
    (hcost : cost Gamma ≤ Mtotal) :
    ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
        (SelectedInverseMap.selInv kh q),
      cost Delta ≤ mapK kh * cost Gamma ∧
      IsVariableSpeedNormalPath P0 (mapRearP1 kh Qmax khat Mtotal) khat
        (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Delta :=
  exists_map_path (Residual.ofFiniteSmoothRearFamily family)
    hkh0 hkh1 hkhat Gamma hp hq hGamma hcost

end SelectedInverseApproximateMapPath
