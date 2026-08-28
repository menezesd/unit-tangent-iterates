import UnitTangentIterates.ConfiguredRecursiveEdgePresentedArrayScalarSidecars
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
import UnitTangentIterates.GenericVariableTerminalDirectCapstoneExplicitFrontPaperMain

/-!
# Paper theorem from one concrete presented array

This is the immediate capstone for the finite nonaffine construction.  Its
inputs are the actual presented array, the explicit retained physical-array
package, and the configured scalar closing output.  No recursive core,
selected-inverse grid, or universal map callback appears in the statement.
-/

noncomputable section

open Function Set Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArrayPaperMain

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  ConfiguredRecursiveEdgePresentedArrayScalarSidecars
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
  GenericVariableTerminalDirectCapstoneExplicitFrontPaperMain

variable {MA NA : ℝ}

/-- The paper theorem from the actual finite presented array.  The single
row-error hypothesis is independent of the eventual limit output and is
converted internally to the universal paper gap. -/
theorem paperMain
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data)
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {G : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output J E0
      (configuredSourceMassTarget E0 C0 C1 C2)}
    (S : ClosingOutput J G E0 C0 C1 C2)
    {kh cb db cp dp : ℝ}
    (R :
      FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray.Package
        A B0 kh cb db cp dp)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp) (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ J.scalar.Cw)
    (hQlength : 2 * S.data.Hs 0 ≤
      MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hrow : c2ConstVar (P0 0) (P1 0) (khat 0) (G1 0) (Cg 0) *
      (∑' k, e 0 k) ≤ S.radius 0) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  apply GenericVariableTerminalDirectCapstoneExplicitFrontPaperMain.paperMainDistance
    A.toGeometricScheme R.markings R.physical hkh0 hkh1 hcb hdb hcp
    R.frontTube R.mixed R.physicalDefect hc hdirection hQbounded hQwidth
    hQlength
  exact ScalarClosing.universalPaperGap_of_rowError S hrow

end FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArrayPaperMain
