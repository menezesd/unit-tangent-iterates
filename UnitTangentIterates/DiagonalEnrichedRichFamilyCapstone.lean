import UnitTangentIterates.EnrichedPhysicalChosenRichFamily
import UnitTangentIterates.GenericVariableTerminalCapstoneFromRichFamily
import UnitTangentIterates.ConfiguredPhysicalDiagonalLargeSeparation

/-!
# Diagonal stable capstone for an enriched chosen family

This is the composition point between the non-multiplicative scalar
large-separation theorem and the chosen recursive family.  The scalar output
discharges the full-tail radius and width gap; the enriched construction is
forgotten only at the call to the limit-facing capstone.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace DiagonalEnrichedRichFamilyCapstone

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
    (physical : RichFamilyRetainedPhysicalCertificate.CorrectedCertificate
      E.toRichFamily kh cb db)
    {Xphys : ℕ → Data}
    (hphysicalLimit : ∀ n, Tendsto
      (RichFamilyRetainedPhysicalRows.rows E.toRichFamily n)
      atTop (nhds (Xphys n)))
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
  let F := E.toRichFamily
  have hpartial : ∀ n k,
      (∑ j ∈ Finset.range k,
        rowError (shiftSequence diagonal L.N) n j) ≤
      ShadowingTails.tail
        (rowError (shiftSequence diagonal L.N) n) 0 := by
    intro n k
    simpa [ShadowingTails.tail] using
      ((F.defect.summable n).sum_le_tsum (Finset.range k)
        (fun j _ => F.defect.nonnegative n j))
  have hradius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) *
          ShadowingTails.tail
            (rowError (shiftSequence diagonal L.N) n) 0 ≤
        rowRadius (shiftSequence conversion L.N)
          (shiftSequence diagonal L.N) n := by
    intro n
    rw [hconversion n]
    exact le_rfl
  apply GenericVariableTerminalCapstoneFromRichFamily.exists_paperFacingOutput_from_richFamily
      F RB hbaseTube hbaseAcc
      hpartial hradius hcb hdb hkh0 hkh1 physical hphysicalLimit hc
      hdirection hQbounded hQwidth hQlength
  intro O
  have hshadow : PaperFacingVariableTerminalOutput.shadowSize O =
      rowRadius (shiftSequence conversion L.N)
        (shiftSequence diagonal L.N) 0 := by
    change c2ConstVar (P0 0) (P1 0) (khat 0) (G1 0) (Cg 0) *
        ShadowingTails.tail
          (rowError (shiftSequence diagonal L.N) 0) 0 = _
    rw [hconversion 0]
    rfl
  rw [hshadow, hmodelWidth, hH]
  exact L.width_gap

end DiagonalEnrichedRichFamilyCapstone
