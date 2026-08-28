import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalInitialWidth
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedDirectCapstoneConfiguredBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCommonTubeRows

/-! # Truthful physical base alignment for the direct-recost capstone -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedDirectCapstonePhysicalBaseAlignment

open ConfiguredCanonicalPairSource
  ConfiguredRecursiveEdgePhysicalInitialWidth
  ConfiguredRecursiveEdgeRecostScaledPaperCapstone
  ConfiguredRecursiveEdgeRecostedDirectCapstoneAdapter
  ConfiguredRecursiveEdgeRecostedDirectCapstoneConfiguredBase
  ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {H : Grid J}

abbrev tailIndex (J : RowJetScalarOutput choice.MA0 choice.NA0) : ℕ :=
  (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.large J).N

/-- Package the actual selected-rear base.  The grid equality is intentionally
with `initial`, not with the model front; width is transported through the
physical rear kinematics and the retained `+2` scalar reserve. -/
def baseAlignment
    (hPzero : ∀ n, H.P n 0 =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
        (tailIndex J + n))
    (hslice : ∀ n, AnalyticSuccessorSliceFacts (H.stage n 0).source) :
    BaseAlignment (J := J) H := by
  let N := tailIndex J
  have hbaseTube : ∀ n,
      IsTubeMember (commonC (rowData J)) 0 (commonDlt (rowData J)) (H.P n 0) := by
    intro n
    rw [hPzero n]
    simpa [rowData, ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
      ConfiguredBaseProfiledEdgeSourceFamily.data] using
      (ConfiguredRecursiveEdgePhysicalInitialData.initial_tube J.scalar (N + n))
  have hp := ConfiguredRecursiveEdgePhysicalInitialData.initial_tube J.scalar N
  have hboundedInitial : Bornology.IsBounded
      (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar N).1)) :=
    CurveDistance.isBounded_range_of_periodic
      (continuous_iff_continuousAt.2 fun u ↦
        (hp.hasDerivAt_curve u).continuousAt)
      hp.periodic one_pos
  have hP00 : H.P 0 0 =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar N := by
    simpa [N] using hPzero 0
  refine
    { slice := hslice
      baseTube := hbaseTube
      direction := initialDirection J.scalar N
      direction_norm := initialDirection_norm J.scalar N
      bounded := ?_
      width := ?_
      length := ?_ }
  · rw [hP00]
    exact hboundedInitial
  · rw [hP00]
    exact initial_width_le_Cw J.scalar N hboundedInitial
  · rw [hP00,
      VariableMarkedPhysicalLength.totalLength_eq_perim_of_tube hp,
      ConfiguredRecursiveEdgePhysicalInitialData.initial_perim_eq J.scalar N]
    simp [N, tailIndex, rowData,
      ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
      ConfiguredBaseProfiledEdgeSourceFamily.data,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift]

/-- Final paper theorem from a truthful shifted base row, exact depth-zero
slices, canonical terminal-front facts, and invariant-propagated common tubes.
All closing geometry is constructed internally. -/
theorem paper
    (H : Grid J)
    (hPzero : ∀ n, H.P n 0 =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
        (tailIndex J + n))
    (hslice : ∀ n, AnalyticSuccessorSliceFacts (H.stage n 0).source)
    (F : FrontFacts H)
    (R : ConfiguredRecursiveEdgeRecostedCommonTubeRows.CommonTubeRows H) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  let A := baseAlignment (H := H) hPzero hslice
  exact R.paper A.baseFacts F (A.closingFacts F R.C R.tube)

end ConfiguredRecursiveEdgeRecostedDirectCapstonePhysicalBaseAlignment
