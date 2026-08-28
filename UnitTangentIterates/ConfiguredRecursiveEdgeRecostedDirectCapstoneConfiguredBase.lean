import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalGeometricBase

/-!
# Configured depth-zero data for the recosted direct capstone

The abstract diagonal rows do not prescribe their root stage.  A configured
constructor retains its exact slices, ordinary base tubes, and the three
parameterization-invariant closing facts about the actual moved-rear display.
No marked equality with the aligned model is asserted.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedDirectCapstoneConfiguredBase

open ConfiguredCanonicalPairSource
  ConfiguredRecursiveEdgeRecostedDirectCapstoneAdapter
  ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}

/-- Exact root-stage and closing facts retained by a configured diagonal-row
constructor.  They concern the actual displayed moved rear. -/
structure BaseAlignment (H : Grid J) where
  slice : ∀ n, AnalyticSuccessorSliceFacts (H.stage n 0).source
  baseTube : ∀ n,
    IsTubeMember (commonC (rowData J)) 0 (commonDlt (rowData J)) (H.P n 0)
  direction : ℂ
  direction_norm : ‖direction‖ = 1
  bounded : Bornology.IsBounded (range (⇑(H.P 0 0).1))
  width : Width.width (range (⇑(H.P 0 0).1)) direction ≤ J.scalar.Cw
  length : 2 *
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
        (rowData J)
        (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.large J).N).Hs 0 ≤
    MarkedReparam.totalLength (fun u ↦ (H.P 0 0).2.1 u)

namespace BaseAlignment

variable {J : RowJetScalarOutput choice.MA0 choice.NA0} {H : Grid J}

/-- Construct every depth-zero nonaffine and common-tube fact. -/
def baseFacts (A : BaseAlignment (J := J) H) : BaseFacts H where
  P1 := fun n => (A.slice n).periodUpper
  markingLower := fun n => (A.slice n).markingLower
  markingUpper := fun n => (A.slice n).markingUpper
  facts := fun n => Nonaffine.Facts.ofAnalytic (A.slice n) le_rfl
  baseTube := A.baseTube

/-- Transport the three truthful closing facts through the assembly's
definition of its base row. -/
def closingFacts
    (A : BaseAlignment (J := J) H) (F : FrontFacts H)
    (C : ℕ → ℝ)
    (htube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      (commonC (rowData J)) (C n) 0 (commonDlt (rowData J)) (H.P n k)) :
    ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts.BaseFacts
      (ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars.assembly
        H A.baseFacts F C htube).core where
  direction := A.direction
  direction_norm := A.direction_norm
  bounded := by
    change Bornology.IsBounded (range (⇑(H.P 0 0).1))
    exact A.bounded
  width := by
    change Width.width (range (⇑(H.P 0 0).1)) A.direction ≤ J.scalar.Cw
    exact A.width
  length := by
    change 2 *
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          (rowData J)
          (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.large J).N).Hs 0 ≤
      MarkedReparam.totalLength (fun u ↦ (H.P 0 0).2.1 u)
    exact A.length

end BaseAlignment

/-- Construct the final concrete input from configured root coherence. -/
def concreteInput
    (H : Grid J) (A : BaseAlignment (J := J) H) (F : FrontFacts H)
    (C : ℕ → ℝ)
    (htube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      (commonC (rowData J)) (C n) 0 (commonDlt (rowData J)) (H.P n k)) :
    ConfiguredRecursiveEdgeRecostedConcreteCapstoneInput.Input J :=
  ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars.concreteInput
    H A.baseFacts F C htube (A.closingFacts F C htube)

end ConfiguredRecursiveEdgeRecostedDirectCapstoneConfiguredBase
