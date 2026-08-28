import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedDirectCapstoneAdapter
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts

/-!
# Callback-free configured physical input for the recosted direct capstone

The geometric cells already retain every fact needed to construct the
explicit physical package.  This adapter fixes all physical constants to the
configured source curvature and common tube.  The closing data are the three
parameterization-invariant facts about the actual displayed base; no marked
identification with the aligned model is imposed.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedConcreteCapstoneInput

open ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredInductiveTubeBudget
  ConstructedConfiguredInductiveTubeBudget
  ConfiguredRecursiveEdgePresentedPhysicalSidecars
  ConfiguredRecursiveEdgeRecostedDirectCapstoneAdapter
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays

open FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray

/-- The configured common chord radius is strictly positive. -/
theorem commonDlt_pos (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 < commonDlt D := by
  have hk : 0 < D.model.kstar := configured_kstar_pos D.model
  have hc : 0 < chordBase D.model := by
    rw [chordBase_eq_min D.model hk]
    exact lt_min D.separation_zero_pos
      (div_pos Real.pi_pos (mul_pos (by norm_num) hk))
  exact div_pos hc (by norm_num)

namespace Assembly

/-- The cell facts of a recosted assembly determine its complete explicit
physical package with the configured curvature and common tube constants. -/
def physicalPackage
    (J : RowJetScalarOutput choice.MA0 choice.NA0)
    (A : Assembly J) :
    Package A.core.array A.core.B0 sourceKh
      (commonC (rowData J)) (commonDlt (rowData J))
      (commonC (rowData J)) (commonDlt (rowData J)) := by
  let S := A.cellFacts.toSidecars (rowData J) A.core.array
  exact presentedPackage A.core.array A.core.B0 (fun _ => rfl)
    S.physical S.mixed S.frontTube

end Assembly

/-- All non-scalar capstone data after the configured cell facts have been
used, including the truthful facts about the actual displayed base. -/
structure Input
    (J : RowJetScalarOutput choice.MA0 choice.NA0) where
  assembly : Assembly J
  baseFacts :
    ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts.BaseFacts
      assembly.core

namespace Input

/-- Construct the truthful-base capstone interface with every physical
constant and the complete physical package filled from configured data. -/
def capstoneInput
    {J : RowJetScalarOutput choice.MA0 choice.NA0}
    (I : Input J) :
    ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts.DirectInput J where
  core := I.assembly.core
  kh0 := sourceKh
  cb := commonC (rowData J)
  db := commonDlt (rowData J)
  cp := commonC (rowData J)
  dp := commonDlt (rowData J)
  physical := Assembly.physicalPackage J I.assembly
  kh0_nonnegative := sourceKh_nonnegative
  kh0_lt_one := sourceKh_lt_one
  cb_pos := (rowData J).separation_zero_pos
  db_pos := commonDlt_pos (rowData J)
  cp_pos := (rowData J).separation_zero_pos
  c_pos := (rowData J).separation_zero_pos
  baseFacts := I.baseFacts

theorem paper
    {J : RowJetScalarOutput choice.MA0 choice.NA0}
    (I : Input J) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts.DirectInput.paper
    I.capstoneInput

end Input

end ConfiguredRecursiveEdgeRecostedConcreteCapstoneInput
