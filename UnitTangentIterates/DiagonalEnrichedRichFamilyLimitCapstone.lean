import UnitTangentIterates.DiagonalEnrichedRichFamilyCapstone
import UnitTangentIterates.EnrichedPhysicalRowConvergence
import UnitTangentIterates.EnrichedGaugeFirstFinitePhysicalCertificate

/-!
# Diagonal enriched capstone with constructed retained physical limits

This companion removes the separately supplied retained-row limit from the
direct diagonal capstone.  Uniform row geometry comes from the bounded
enriched construction, while convergence follows from the vanishing terminal
marking defect and the already constructed variable-terminal row limit.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace DiagonalEnrichedRichFamilyLimitCapstone

open VariableMarkedTube GaugeRearFamilyVariableTerminal
open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
open EnrichedPhysicalChosenRichFamily
open ExponentialDiagonalLargeSeparation
open VariableTerminalRowTubeAdapter

theorem exists_paperFacingOutput
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    {Q : ℕ → Data}
    {P0 P1 khat G1 Cg Cup : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q
      (rowError (shiftSequence diagonal L.N))
      P0 P1 khat G1 Cg Cup c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (E : Construction Q
      (rowError (shiftSequence diagonal L.N))
      P0 P1 khat G1 Cg Cup c dlt period
      (shiftSequence diagonal L.N) GaugeCertificate a MA NA K0 K1 K2)
    {c0 d0 A0 rho : ℕ → ℝ}
    (RB : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0
      (rowRadius (shiftSequence conversion L.N)
        (shiftSequence diagonal L.N))
      rho Cup c dlt)
    (hconversion : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) =
        shiftSequence conversion L.N n)
    (hbaseTube : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    {cb db kh : ℝ} (hcb : 0 < cb) (hdb : 0 < db)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (B : EnrichedPhysicalRowBounds.BoundedConstruction E cb db)
    (hphysicalBase : ∀ n, Nonempty
      (PhysicalRearLimitKinematics kh
        ((E.chosenColumn 0).step.richStage n).terminalBase (Q (n + 1))))
    (hphysicalTransition : ∀ k,
      EnrichedGaugeFirstFinitePhysicalCertificate.PhysicalTransitionCertificate
        (E.chosenColumn k)
        (E.mapProvider.map k (E.chosenColumn k)).val kh)
    {endpointError : ℕ → ℕ → ℝ} {Xphys : ℕ → Data}
    (endpointDefect :
      EnrichedPhysicalRowConvergence.EndpointDefectCertificate
        E.toRichFamily endpointError)
    (hterminalLimit : ∀ n, Tendsto
      (fun k => E.toRichFamily.P n (k + 1)) atTop (nhds (Xphys n)))
    (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u => (Q 0).2.1 u))
    (hmodelWidth : modelWidth = Cw)
    (hH : H =
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D L.N).Hs 0) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        Q E.toRichFamily.P (rowError (shiftSequence diagonal L.N))
        P0 P1 khat G1 Cg Cup c dlt,
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let limit :=
    EnrichedPhysicalRowConvergence.LimitPackage.of_boundedConstruction B
      endpointDefect hterminalLimit
  let physical :=
    EnrichedGaugeFirstFinitePhysicalCertificate.correctedCertificate_of_enriched
      E hphysicalBase hphysicalTransition limit.bounds
  exact DiagonalEnrichedRichFamilyCapstone.exists_paperFacingOutput
    L E RB hconversion hbaseTube hbaseAcc hcb hdb hkh0 hkh1
    physical limit.physical_limit hc hdirection hQbounded hQwidth hQlength
    hmodelWidth hH

end DiagonalEnrichedRichFamilyLimitCapstone
