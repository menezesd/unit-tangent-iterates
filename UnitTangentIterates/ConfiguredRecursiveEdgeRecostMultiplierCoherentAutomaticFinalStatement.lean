import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCoherentAutomaticSmoothAdapter
import UnitTangentIterates.PaperMainTheoremGenuineNoncircularStatement

/-!
# Genuine final statement from a coherent automatic physical grid

This leaf hides the intermediate `SmoothPhysicalBaseInput`.  A direct
canonical builder only has to construct the single coherent automatic input
record and may then invoke `Input.mainConclusion`.
-/

noncomputable section

namespace ConfiguredRecursiveEdgeRecostMultiplierCoherentAutomaticSmoothAdapter

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {GO : GaugeOutput J} (R : RecostClosingOutput J GO)

/-- Final conditional paper theorem from the packaged coherent metric grid
and its retained finite physical rows.  The conclusion includes genuine
parameter-independent noncircularity and a smooth forward unit-tangent range
orbit. -/
theorem Input.mainConclusion (I : Input R) :
    PaperMainTheoremGenuineNoncircularStatement.MainConclusion :=
  PaperMainTheoremGenuineNoncircularStatement.of_smoothPhysicalBaseInput R
    I.toSmoothPhysicalBaseInput

end ConfiguredRecursiveEdgeRecostMultiplierCoherentAutomaticSmoothAdapter
