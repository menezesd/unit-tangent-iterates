import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseFinalTailState
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalGeometricBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricStep

/-!
# Persistent provenance for recosted geometric successors

This module keeps the exact geometric column beside the row-local normalized
tail state.  A multiplier step then advances that column through the retained
`RecostedGeometricPresentedRowFamily`; no source or selected row is chosen a
second time.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierPersistentProvenance

open ConfiguredRecursiveEdgePhysicalBaseFinalTailState
  ConfiguredRecursiveEdgePhysicalGeometricBase
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  FiniteSmoothRearFamilyMarkingAwareRecostedGeometricPresentedRecursion

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

abbrev BaseState := State
  (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Q J.scalar)
  (ConfiguredRecursiveEdgePhysicalCompositionBase.compositionError J)
  (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
  (ConfiguredRecursiveEdgeSourceP0Growth.edgeP1
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
  (ConfiguredRecursiveEdgeSourceP0Growth.edgeG1
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
  (ConfiguredRecursiveEdgeSourceP0Growth.edgeCgWithKhat
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat J.scalar)
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
  (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
  (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax J.scalar)
  (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat J.scalar)
  (ConfiguredCanonicalPairSource.commonC
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
  (ConfiguredCanonicalPairSource.commonDlt
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
  ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh

/-- The exact physical geometric base before restricting to the final public
tail.  The tail restriction is performed only when a public row is queried. -/
noncomputable def physicalBaseState : BaseState (J := J) where
  current := baseCurrent J (K0 := K0) (K1 := K1) (K2 := K2)
  depth := 0
  column := base J (K0 := K0) (K1 := K1) (K2 := K2)
  invariant := invariant J (K0 := K0) (K1 := K1) (K2 := K2)

/-- The retained global base and the row-local normalized final-tail base have
the same displayed datum at every public row. -/
@[simp] theorem physicalBaseState_tail_displayed
    (R : RecostClosingOutput J O) (n : ℕ) :
    ((physicalBaseState (J := J) (K0 := K0) (K1 := K1)
      (K2 := K2)).stage (R.totalShift + n)).displayed =
      (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R n).displayed := by
  rw [finalStage_displayed]
  rfl

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}
  {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}

/-- A chosen multiplier input carries one and the same row family into the
successor column.  In particular its `recursiveFacts` field is not discarded
between layers. -/
def successorFamily (H : StepInput X) :
    RecostedGeometricPresentedRowFamily X.column := H.family

@[simp] theorem successor_column (H : StepInput X) :
    H.next.column = (successorFamily H).mappedColumn := rfl

@[simp] theorem successor_invariant (H : StepInput X) :
    H.next.invariant = (successorFamily H).mappedInvariant := rfl

@[simp] theorem successor_current (H : StepInput X) (n : ℕ) :
    H.next.current n = ((successorFamily H).row n).presented := rfl

/-- The exact next geometric input is already available from the retained
family and invariant, before choosing any further analytic source. -/
noncomputable def successorGeometricInput (H : StepInput X) (n : ℕ) :=
  H.next.geometricInput n

/-- Once regularity of the newly selected carrier is supplied, the next
pre-carrier is canonical.  This isolates the only datum not transported by
`RecostedGeometricPresentedRowFamily`. -/
noncomputable def successorPre
    (H : StepInput X) (Rnext : ∀ n, Regularity H.next n) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core (H.next.stage n) :=
  core H.next n (Rnext n)

/-- The family, successor state, and every next pre-carrier arise from the
same chosen step. -/
theorem exists_successor_provenance
    (H : StepInput X) (Rnext : ∀ n, Regularity H.next n) :
    ∃ F : RecostedGeometricPresentedRowFamily X.column,
      HEq H.next.column F.mappedColumn ∧
      HEq H.next.invariant F.mappedInvariant ∧
      (∀ n, Nonempty
        (ConfiguredRecursiveEdgeRecostedPreCarrier.Core (H.next.stage n))) := by
  refine ⟨successorFamily H, ?_, ?_, ?_⟩
  · exact heq_of_eq (successor_column H)
  · exact heq_of_eq (successor_invariant H)
  intro n
  exact ⟨successorPre H Rnext n⟩

end ConfiguredRecursiveEdgeRecostMultiplierPersistentProvenance
