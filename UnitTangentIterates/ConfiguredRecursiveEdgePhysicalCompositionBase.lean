import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFlowCeilings
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0CappedRowProduction
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant
import UnitTangentIterates.RichStageBoundMonotonicity

/-! # Physical composition-stable configured base column -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalCompositionBase

open ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily
  ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgePhysicalFlowCeilings
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider
  ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyEnrichedMapProvider
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

variable {MA NA : ℝ}

/-- The physical gauge-origin-normalized sources attached to the configured
base column. -/
noncomputable def baseSource
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :=
  ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source
    J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) n

/-- The ordinary configured correlated base column with the physical sources
installed definitionally. -/
noncomputable def baseCorrelated
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} :=
  ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseCorrelated
    J.scalar.pair.input J.scalar.model_data (rowC J.scalar)
    (MA0 := MA) (NA0 := NA) (K0 := K0) (K1 := K1) (K2 := K2)
    (separation_one J.scalar) (kstar_le_pathKhat J.scalar)
    khRow (Qmax J.scalar) (baseSource J)

@[simp] theorem baseCorrelated_source
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    (baseCorrelated J (K0 := K0) (K1 := K1) (K2 := K2)).source n =
      ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source
        J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
          (K0 := K0) (K1 := K1) (K2 := K2) n := rfl

@[simp] theorem baseCorrelated_path
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    (((baseCorrelated J (K0 := K0) (K1 := K1) (K2 := K2)).column.step.richStage
      (n + 1)).stage.increment) =
      sourcePath J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
        (K0 := K0) (K1 := K1) (K2 := K2) n := rfl

/-- The composition branch charges both the physical component budget and
the scaled source mass to one common diagonal coefficient. -/
def compositionError
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA) :
    ℕ → ℕ → ℝ :=
  ConfiguredDiagonalStableRowDefectProvider.error (D J.scalar)
    (edgeCompositionPhysicalCoeff (D J.scalar))

def compositionDiagonal
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA) :
    ℕ → ℝ :=
  edgeCompositionPhysicalDefect (D J.scalar)

/-- The same selected physical base column, with its scalar error and
component diagonal enlarged to the composition-stable coefficient. -/
noncomputable def compositionBaseCorrelated
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} :
    CorrelatedColumn (Q J.scalar) (Q J.scalar) (compositionError J) 0
      (edgeSourceP0 (D J.scalar)) (edgeP1 (D J.scalar) MA)
      (fun _ ↦ pathKhat J.scalar) (edgeG1 (D J.scalar) MA NA)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA)
      (rowC J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      (period J.scalar) (compositionDiagonal J) khRow (Qmax J.scalar)
      K0 K1 K2 := by
  let B := baseCorrelated J (K0 := K0) (K1 := K1) (K2 := K2)
  have he : ∀ n,
      ConfiguredDiagonalStableRowDefectProvider.error (D J.scalar)
          (physicalCoeff (D J.scalar)) n 0 ≤ compositionError J n 0 := by
    intro n
    unfold compositionError ConfiguredDiagonalStableRowDefectProvider.error
      edgeCompositionPhysicalCoeff
    have hrow := ConfiguredRowDefectProvider.rowDefect_nonneg (D J.scalar) n
    have hcoeff := edgeCompositionCoeff_one_le (D J.scalar) n
    simp only [Nat.add_zero]
    nlinarith
  let step := B.column.step.monoError he
  let column : CertifiedColumn (Q J.scalar) (Q J.scalar)
      (compositionError J) 0 (edgeSourceP0 (D J.scalar))
      (edgeP1 (D J.scalar) MA) (fun _ ↦ pathKhat J.scalar)
      (edgeG1 (D J.scalar) MA NA)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA)
      (rowC J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      (period J.scalar) (compositionDiagonal J)
      (GaugeFamily (period J.scalar) K0 K1 K2) := by
    refine
      { step := step
        period_ge_one := B.column.period_ge_one
        components_nonnegative := ?_
        components_bound := ?_
        gauge := ?_ }
    · intro n
      simpa [step, TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep.monoError]
        using B.column.components_nonnegative n
    · intro n
      have H := B.column.components_bound n
      have hrow := ConfiguredRowDefectProvider.rowDefect_nonneg (D J.scalar) n
      have hcoeff := edgeCompositionCoeff_one_le (D J.scalar) n
      have hcoefficient : physicalCoeff (D J.scalar) n ≤
          edgeCompositionPhysicalCoeff (D J.scalar) n := by
        unfold edgeCompositionPhysicalCoeff
        nlinarith
      have hdiag : physicalDefect (D J.scalar) n ≤
          edgeCompositionPhysicalDefect (D J.scalar) n := by
        unfold physicalDefect edgeCompositionPhysicalDefect
        exact mul_le_mul_of_nonneg_right hcoefficient hrow
      have hdiag' :
          ConfiguredEnrichedConstructionCoreProvider.diagonal
              (D J.scalar) (n + 0) ≤ compositionDiagonal J (n + 0) := by
        simpa [ConfiguredEnrichedConstructionCoreProvider.diagonal,
          compositionDiagonal] using hdiag
      exact ⟨H.w.trans hdiag', H.s0.trans hdiag', H.s1.trans hdiag',
        H.s2.trans hdiag'⟩
    · intro n
      cases B.column.gauge n with
      | base G =>
          apply GaugeCertificate.base
          exact
            { terminalBase := G.terminalBase
              terminalBase_eq := by
                simpa [step,
                  TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep.monoError]
                  using G.terminalBase_eq
              terminalPhysical := G.terminalPhysical }
      | mapped G =>
          apply GaugeCertificate.mapped
          refine { G with output := ?_, terminalBase_eq := ?_ }
          · simpa [step,
              TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep.monoError]
              using G.output
          · simpa [step,
              TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep.monoError]
              using G.terminalBase_eq
  refine { column := column, source := ?_ }
  intro n
  simpa [column, step, baseCorrelated, baseSource,
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.ColumnStep.monoError,
    B] using (B.source n)

@[simp] theorem compositionBaseCorrelated_source
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    (compositionBaseCorrelated J (K0 := K0) (K1 := K1) (K2 := K2)).source n =
      (baseCorrelated J (K0 := K0) (K1 := K1) (K2 := K2)).source n := by
  rfl

@[simp] theorem compositionBaseCorrelated_path
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    (((compositionBaseCorrelated J (K0 := K0) (K1 := K1)
      (K2 := K2)).column.step.richStage (n + 1)).stage.increment) =
      (((baseCorrelated J (K0 := K0) (K1 := K1)
        (K2 := K2)).column.step.richStage (n + 1)).stage.increment) := by
  rfl

/-- The widened base error is exactly the diagonal budget already proved for
the composition-scaled physical source density. -/
theorem compositionBase_source_cost_le
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    (∫ t in (0 : ℝ)..
        ((compositionBaseCorrelated J (K0 := K0) (K1 := K1)
          (K2 := K2)).column.step.richStage (n + 1)).stage.increment.T,
      ((compositionBaseCorrelated J (K0 := K0) (K1 := K1)
        (K2 := K2)).source n).m t) ≤ compositionError J n 1 := by
  have H := ConfiguredBaseProfiledEdgeSourceFamily.edgeSource_cost_le_compositionPhysicalDefect
    J.scalar n
  simpa [compositionBaseCorrelated, compositionError, D,
    ConfiguredBaseProfiledEdgeSourceFamily.data,
    ConfiguredDiagonalStableRowDefectProvider.error,
    ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source,
    ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.presentation,
    ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily.edgeSourceAt,
    ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily.edgeScaledBoundsAt,
    ConfiguredBaseProfiledEdgeSourceFamily.edgeSourceFamily,
    ConfiguredBaseProfiledEdgeSourceFamily.edgeScaledBounds,
    Nat.add_assoc] using H

/-- A definitionally normalized copy of the transported slice.  Resetting the
scalar ceiling avoids exposing the dependent path cast while preserving every
analytic field. -/
noncomputable def baseSlice
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    AnalyticSuccessorSliceFacts
      ((compositionBaseCorrelated J (K0 := K0) (K1 := K1)
        (K2 := K2)).source n) := by
  let X := compositionRecursiveAnalyticSuccessor J (rowC J.scalar)
    (MA0 := MA) (NA0 := NA) (K0 := K0) (K1 := K1) (K2 := K2) n
  let H : AnalyticSuccessorSliceFacts
      ((compositionBaseCorrelated J (K0 := K0) (K1 := K1)
        (K2 := K2)).source n) := by
    simpa [X, compositionBaseCorrelated_source, baseCorrelated_source] using X.slice
  exact
    { H with
      periodUpper := 2 * (data J.scalar).Hs (n + 1)
      period_upper := by
        intro t
        change (ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily.edgeSourceAt
          J.scalar n (initialRearPhase J.scalar n)).P t ≤
            2 * (data J.scalar).Hs (n + 1)
        rw [ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.edgeSourceAt_period_eq]
        rfl }

end ConfiguredRecursiveEdgePhysicalCompositionBase
