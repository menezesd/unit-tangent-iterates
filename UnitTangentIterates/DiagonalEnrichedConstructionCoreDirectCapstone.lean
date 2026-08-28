import UnitTangentIterates.GenericVariableTerminalDirectCapstone
import UnitTangentIterates.DiagonalEnrichedRichFamilyEndpointDefectCapstone

/-!
# Direct diagonal capstone from an enriched construction core

`EnrichedStageProducer` is the exact post-construction interface required from
the recursive gauge analysis.  It retains the marked-column tube, the
physical terminal-row geometry, aligned finite pullback kinematics, and the
terminal marking defect.  No Harnack or convergence callback is present.
-/

noncomputable section

open Set Filter MarkedSpace PathMetric
open VariableMarkedTube
open EnrichedPhysicalChosenRichFamily
open EnrichedPhysicalHarnackClosure
open RichFamilyPhysicalMarkingIntegration
open NormalizedTerminalMarkingComposition
open ExponentialDiagonalLargeSeparation
open NormalPathC2IncrementVariableSpeed

namespace DiagonalEnrichedConstructionCoreDirectCapstone

structure EnrichedStageProducer
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    (kh cb db : ℝ) : Type where
  columnsTube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt
    (columns F.baseProvider F.mapProvider k n)
  physicalBounds : PhysicalRowBounds
    (retainedRows F.baseProvider F.mapProvider)
    (fun n k => columns F.baseProvider F.mapProvider k n) cb db
  finite : FinitePullbackPhysicalRearKinematics kh
    (retainedRows F.baseProvider F.mapProvider)
  endpointDefect : F.EndpointDefectCertificate

def directMarkings
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2) :
    DirectPhysicalTerminalMarkingFamily
      (retainedRows F.baseProvider F.mapProvider)
      (fun n k => columns F.baseProvider F.mapProvider k n) where
  lambda n
    | 0 => 1
    | k + 1 => (F.chosenColumn k).step.richStage n |>.lambda
  Lambda n
    | 0 => 1
    | k + 1 => (F.chosenColumn k).step.richStage n |>.Lambda
  marking n
    | 0 => by
        simpa [retainedRows, columns_zero] using
          NormalizedC2Marking.refl (Q n)
    | k + 1 => by
        simpa [retainedRows, columns_succ] using
          (F.chosenColumn k).step.richStage n |>.marking

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
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh cb db : ℝ}
    (F : ConstructionCore Q
      (rowError (shiftSequence diagonal L.N))
      P0 P1 khat G1 Cg Cup c dlt period
      (shiftSequence diagonal L.N) GaugeCertificate a MA NA K0 K1 K2)
    (G : EnrichedStageProducer F kh cb db)
    (hconversion : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
        shiftSequence conversion L.N n)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hc : 0 < c)
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
        Q (fun n k => columns F.baseProvider F.mapProvider k n)
        (rowError (shiftSequence diagonal L.N))
        P0 P1 khat G1 Cg Cup c dlt,
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let S := EnrichedPhysicalConstructionCoreDirect.toDirectScheme F
    G.columnsTube hkh0 hkh1 hcb hdb G.physicalBounds.physical_tube
    G.finite G.endpointDefect
  apply GenericVariableTerminalDirectCapstone.exists_paperFacingOutput
    S (directMarkings F) G.physicalBounds hkh0 hkh1 hcb hdb G.finite
    G.endpointDefect.tendsToZero hc hdirection hQbounded hQwidth hQlength
  intro O
  have hshadow : PaperFacingVariableTerminalOutput.shadowSize O ≤
      rowRadius (shiftSequence conversion L.N)
        (shiftSequence diagonal L.N) 0 := by
    change c2ConstVar (P0 0) (P1 0) (khat 0) (G1 0) (Cg 0) *
        ShadowingTails.tail
          (rowError (shiftSequence diagonal L.N) 0) 0 ≤ _
    exact mul_le_mul_of_nonneg_right (hconversion 0)
      (ShadowingTails.tail_nonneg
        (fun k ↦ F.defect.nonnegative 0 k) 0)
  rw [hmodelWidth, hH]
  have hleft : Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize O ≤
      Cw + 2 * rowRadius (shiftSequence conversion L.N)
        (shiftSequence diagonal L.N) 0 := by linarith
  have hright :
      (2 * (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D L.N).Hs 0 -
          rowRadius (shiftSequence conversion L.N)
            (shiftSequence diagonal L.N) 0) / Real.pi ≤
      (2 * (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D L.N).Hs 0 -
          PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi := by
    exact div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
  exact hleft.trans_lt (L.width_gap.trans_le hright)

end DiagonalEnrichedConstructionCoreDirectCapstone
