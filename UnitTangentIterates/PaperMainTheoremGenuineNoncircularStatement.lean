import UnitTangentIterates.PaperMainTheoremFinalStatement
import UnitTangentIterates.CircleRangeSimplePeriod

/-!
# Genuine noncircular paper-facing main statement

This strengthens the stable perimeter-aware conclusion without replacing it.
-/

noncomputable section

open Function Set

namespace PaperMainTheoremGenuineNoncircularStatement

/-- The full paper-facing conclusion, retaining both the original same-period
closing fact and parameter-independent geometric noncircularity. -/
def MainConclusion : Prop :=
  ∃ (gamma0 : ℝ → ℂ) (L : ℝ),
    0 < L ∧
    Periodic gamma0 L ∧
    InjOn gamma0 (Ico 0 L) ∧
    PaperMainTheoremFinalStatement.IsSmoothOval gamma0 ∧
    PaperMainTheoremC2Projection.IsNoncircular gamma0 ∧
    ¬ ClosingArgument.IsCircleOfPerimeter (range gamma0) L ∧
    Nonempty (PaperMainTheoremFinalStatement.SmoothForwardUnitTangentOrbit gamma0)

/-- The stable perimeter-aware conclusion strengthens to genuine geometric
noncircularity by the simple-circle-period theorem. -/
theorem of_perimeterAware
    (h : PaperMainTheoremFinalStatement.MainConclusion) : MainConclusion := by
  obtain ⟨gamma0, L, hL, hperiod, hinj, hsmooth, hnoncircle, horbit⟩ := h
  have hgenuine :=
    CircleRangeSimplePeriod.isNoncircular_of_not_isCircleOfPerimeter
      hL hperiod hinj hsmooth.1 hnoncircle
  exact ⟨gamma0, L, hL, hperiod, hinj, hsmooth, hgenuine,
    hnoncircle, horbit⟩

/-- Projection from the configured smooth physical capstone to the genuine
paper-facing conclusion. -/
theorem of_smoothPhysicalBaseInput
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {GO : ConfiguredRecursiveEdgeRecostMultiplierClosing.GaugeOutput J}
    (R : ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput J GO)
    (I : ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone.SmoothPhysicalBaseInput R) :
    MainConclusion :=
  of_perimeterAware
    (PaperMainTheoremFinalStatement.of_smoothPhysicalBaseInput R I)

end PaperMainTheoremGenuineNoncircularStatement
