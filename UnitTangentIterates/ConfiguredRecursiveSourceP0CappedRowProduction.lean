import UnitTangentIterates.ConfiguredRecursiveSourceP0MergedAssembly
import UnitTangentIterates.ConfiguredRecursiveSourceP0BaseColumnCap
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCappedProvider
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider
import UnitTangentIterates.ConfiguredRecursiveSourceP0ScalarStart
import UnitTangentIterates.ConfiguredActualHalfScalarChoice
import UnitTangentIterates.ConfiguredRecursiveSourceP0RowJetTail
import UnitTangentIterates.PaperMainTheoremDirectProjection

/-! # Coherent marking-aware row production at the recursive speed floor -/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredRecursiveSourceP0CappedRowProduction

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredCorrelatedBaseColumnCap
  ConfiguredEnrichedConstructionCoreProvider
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredInductiveTubeBudget
  ConfiguredMarkingAwareMergedEndpointGrowth
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveSourceP0
  ConfiguredRecursiveSourceP0ScalarStart
  ConfiguredRowCeilingPolynomialEnvelopes
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareCappedProvider
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
  ConfiguredRecursiveSourceP0RowJetTail

variable {MA0 NA0 : ℝ} (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA0 NA0)

def D : ConstructedConfiguredSequenceWeighted.Data := shift O.E.data O.large.N

def Q : ℕ → Data := alignedQ O.pair.input O.model_data

def rowC : ℕ → ℝ := outputUpper O.E.data O.large

def period : ℕ → ℕ → ℝ :=
  ConfiguredEnrichedConstructionCoreProvider.period (D O)

def diagonal : ℕ → ℝ :=
  ConfiguredEnrichedConstructionCoreProvider.diagonal (D O)

def khRow : ℕ → ℝ := fun _ ↦ sourceKh

def Qmax : ℕ → ℝ := rowC O

def pathKhat : ℝ := analyticKhat O.E.data

theorem separation_one : 1 ≤ (D O).Hs 0 := by
  simpa [D] using O.large.separation_one

theorem kstar_le_pathKhat : (D O).kstar ≤ pathKhat O := by
  simpa [D, pathKhat] using kstar_le_analyticKhat O.E.data

structure RowPackage where
  a : ℕ → ℕ → ℝ
  MA : ℕ → ℕ → ℝ
  NA : ℕ → ℕ → ℝ
  K0 : ℝ
  K1 : ℝ
  K2 : ℝ
  source : ∀ n, MarkingAwareSource
    (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one O) (kstar_le_pathKhat O)).base.step.richStage
      (n + 1)).stage.increment)
    (sourceP0 (D O) n) sourceKh (pathKhat O) (Qmax O n)
  provider : CappedProvider (Q O)
    (ConfiguredDiagonalStableRowDefectProvider.error (D O) (physicalCoeff (D O)))
    (sourceP0 (D O))
    (wideP1 (D O) MA0) (fun _ ↦ pathKhat O)
    (wideG1 (D O) MA0 NA0)
    (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
    (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
    (period O) (diagonal O) khRow (Qmax O) a MA NA K0 K1 K2
    (endpointConversion (D O) sourceKh O.Mend) (physicalDefect (D O))

/-- Invariant-indexed row package used by the nonaffine recursive path.  It
keeps the depth-zero slice facts and never asks for rows at arbitrary columns. -/
structure SlicedRowPackage where
  a : ℕ → ℕ → ℝ
  MA : ℕ → ℕ → ℝ
  NA : ℕ → ℕ → ℝ
  K0 : ℝ
  K1 : ℝ
  K2 : ℝ
  source : ∀ n, MarkingAwareSource
    (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one O) (kstar_le_pathKhat O)).base.step.richStage
      (n + 1)).stage.increment)
    (sourceP0 (D O) n) sourceKh (pathKhat O) (Qmax O n)
  baseSlice : SlicedCorrelatedColumn
    (ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O) source)
  provider : SlicedCappedProvider (Q O)
    (ConfiguredDiagonalStableRowDefectProvider.error (D O) (physicalCoeff (D O)))
    (sourceP0 (D O))
    (wideP1 (D O) MA0) (fun _ ↦ pathKhat O)
    (wideG1 (D O) MA0 NA0)
    (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
    (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
    (period O) (diagonal O) khRow (Qmax O) a MA NA K0 K1 K2
    (endpointConversion (D O) sourceKh O.Mend) (physicalDefect (D O))

namespace SlicedRowPackage

/-- Install theorem-produced capped nonaffine rows into the invariant-indexed
configured row package. -/
def ofSlicedCappedNonaffineRows
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (source : ∀ n, MarkingAwareSource
      (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
        O.pair.input O.model_data (rowC O)
        (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
        (separation_one O) (kstar_le_pathKhat O)).base.step.richStage
        (n + 1)).stage.increment)
      (sourceP0 (D O) n) sourceKh (pathKhat O) (Qmax O n))
    (baseSlice : SlicedCorrelatedColumn
      (ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
        O.pair.input O.model_data (rowC O)
        (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
        (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O) source))
    (G : SlicedCappedNonaffineRowProvider (Q O)
        (ConfiguredDiagonalStableRowDefectProvider.error (D O) (physicalCoeff (D O)))
        (sourceP0 (D O)) (wideP1 (D O) MA0) (fun _ ↦ pathKhat O)
        (wideG1 (D O) MA0 NA0)
        (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
        (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
        (period O) (diagonal O) khRow (Qmax O) a MA NA K0 K1 K2
        (endpointConversion (D O) sourceKh O.Mend) (physicalDefect (D O))) :
    SlicedRowPackage O where
  a := a
  MA := MA
  NA := NA
  K0 := K0
  K1 := K1
  K2 := K2
  source := source
  baseSlice := baseSlice
  provider := G.slicedCappedProvider

def core (P : SlicedRowPackage O) :
    SlicedConstructionCore (Q O)
      (ConfiguredDiagonalStableRowDefectProvider.error (D O) (physicalCoeff (D O)))
      (sourceP0 (D O)) (wideP1 (D O) MA0) (fun _ ↦ pathKhat O)
      (wideG1 (D O) MA0 NA0)
      (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
      (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
      (period O) (diagonal O) khRow (Qmax O)
      P.a P.MA P.NA P.K0 P.K1 P.K2 where
  defect := ConfiguredDiagonalStableRowDefectProvider.provider
    (D O) (physicalCertificate (D O))
  base := ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
    O.pair.input O.model_data (rowC O)
    (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O) P.source
  baseSlice := P.baseSlice
  provider := P.provider.provider

theorem baseCap (P : SlicedRowPackage O)
    (hrow : ∀ n, ConfiguredApproximateDefectPathRowwise.rowDefect (D O) n ≤ O.Mend) :
    ColumnCap (core O P).base
      (baseEndpointConversion (D O) O.Mend) (physicalDefect (D O)) := by
  simpa [core] using
    (ConfiguredRecursiveSourceP0BaseColumnCap.baseColumnCap
      (S := O.pair.input) (hQ := O.model_data) (C := rowC O)
      (hH := separation_one O) (hkhat := kstar_le_pathKhat O)
      (MA0 := MA0) (NA0 := NA0)
      (K0 := P.K0) (K1 := P.K1) (K2 := P.K2)
      (khRow := khRow) (Qmax := Qmax O) (source := P.source)
      (M := O.Mend) hrow)

def caps (P : SlicedRowPackage O)
    (hrow : ∀ n, ConfiguredApproximateDefectPathRowwise.rowDefect (D O) n ≤ O.Mend) :
    SlicedCapFamily (core O P)
      (mergedEndpointConversion (D O) sourceKh O.Mend)
      (physicalDefect (D O)) := by
  simpa [core, mergedEndpointConversion] using
    P.provider.capFamilyOfSeparate
      (ConfiguredDiagonalStableRowDefectProvider.provider (D O)
        (physicalCertificate (D O)))
      (ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
        O.pair.input O.model_data (rowC O)
        (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O) P.source)
      P.baseSlice (baseCap O P hrow) (physicalDefect_nonneg (D O))

end SlicedRowPackage

namespace RowPackage

/-- Install a concrete all-depth chosen-row provider into the configured row
package.  The base-column source family remains separate because it belongs
to depth zero, while `G` provides every recursively selected successor. -/
def ofCappedChosenRows
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (source : ∀ n, MarkingAwareSource
      (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
        O.pair.input O.model_data (rowC O)
        (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
        (separation_one O) (kstar_le_pathKhat O)).base.step.richStage
        (n + 1)).stage.increment)
      (sourceP0 (D O) n) sourceKh (pathKhat O) (Qmax O n))
    (G :
      FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider.CappedChosenRowProvider
        (Q O)
        (ConfiguredDiagonalStableRowDefectProvider.error
          (D O) (physicalCoeff (D O)))
        (sourceP0 (D O)) (wideP1 (D O) MA0) (fun _ ↦ pathKhat O)
        (wideG1 (D O) MA0 NA0)
        (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
        (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
        (period O) (diagonal O) khRow (Qmax O) a MA NA K0 K1 K2
        (endpointConversion (D O) sourceKh O.Mend)
        (physicalDefect (D O))) :
    RowPackage O where
  a := a
  MA := MA
  NA := NA
  K0 := K0
  K1 := K1
  K2 := K2
  source := source
  provider := G.cappedProvider

def core (P : RowPackage O) :
    ConstructionCore (Q O)
      (ConfiguredDiagonalStableRowDefectProvider.error (D O) (physicalCoeff (D O)))
      (sourceP0 (D O))
      (wideP1 (D O) MA0) (fun _ ↦ pathKhat O)
      (wideG1 (D O) MA0 NA0)
      (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
      (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
      (period O) (diagonal O) khRow (Qmax O)
      P.a P.MA P.NA P.K0 P.K1 P.K2 :=
  ConfiguredRecursiveSourceP0ConstructionCoreProvider.constructionCore
    O.pair.input O.model_data (rowC O)
    (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O)
    P.a P.MA P.NA P.K0 P.K1 P.K2 P.source P.provider.provider

theorem basePhysical (P : RowPackage O) (n : ℕ) :
    Nonempty (PhysicalRearLimitKinematics sourceKh
      ((core O P).base.column.step.richStage n).terminalBase (Q O (n + 1))) := by
  simpa [core, Q, D, rowC, pathKhat] using
    (ConfiguredRecursiveSourceP0ConstructionCoreProvider.basePhysical
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0)
      (K0 := P.K0) (K1 := P.K1) (K2 := P.K2)
      (separation_one O) (kstar_le_pathKhat O) n)

theorem rowDefect_le_Mend (n : ℕ) :
    ConfiguredApproximateDefectPathRowwise.rowDefect (D O) n ≤ O.Mend := by
  have hscale : ConfiguredApproximateDefectPathRowwise.rowDefect (D O) n ≤
      physicalDefect (D O) n := by
    unfold physicalDefect physicalCoeff
    have hrow0 := ConfiguredRowDefectProvider.rowDefect_nonneg (D O) n
    have hH : 1 ≤ 2 * (D O).Hs n := by
      have hs := (separation_one O).trans ((D O).separation_lower n)
      linarith
    nlinarith
  have hstrict : physicalDefect (D O) n < O.Mend := by
    simpa [D, ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      physicalDefect, physicalCoeff,
      ConfiguredApproximateDefectPathRowwise.rowDefect] using
      O.physicalDefect_lt (O.large.N + n)
  exact hscale.trans hstrict.le

theorem baseCap (P : RowPackage O) :
    ColumnCap (core O P).base
      (baseEndpointConversion (D O) O.Mend) (physicalDefect (D O)) := by
  simpa [core] using
    (ConfiguredRecursiveSourceP0BaseColumnCap.baseColumnCap
      (S := O.pair.input) (hQ := O.model_data) (C := rowC O)
      (hH := separation_one O) (hkhat := kstar_le_pathKhat O)
      (MA0 := MA0) (NA0 := NA0)
      (K0 := P.K0) (K1 := P.K1) (K2 := P.K2)
      (khRow := khRow) (Qmax := Qmax O) (source := P.source)
      (M := O.Mend) (rowDefect_le_Mend O))

def caps (P : RowPackage O) :
    CapFamily (core O P)
      (mergedEndpointConversion (D O) sourceKh O.Mend)
      (physicalDefect (D O)) := by
  simpa [core, mergedEndpointConversion] using
    P.provider.capFamilyOfSeparate
      (ConfiguredDiagonalStableRowDefectProvider.provider (D O)
        (physicalCertificate (D O)))
      (ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
        O.pair.input O.model_data (rowC O)
        (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O) P.source)
      (baseCap O P) (physicalDefect_nonneg (D O))

end RowPackage

namespace SlicedRowPackage

/-- Fully configured reachable cap family; the row-defect comparison is the
same scalar theorem used by the legacy package. -/
def configuredCaps (P : SlicedRowPackage O) :
    SlicedCapFamily (core O P)
      (mergedEndpointConversion (D O) sourceKh O.Mend)
      (physicalDefect (D O)) :=
  caps O P (RowPackage.rowDefect_le_Mend O)

theorem basePhysical (P : SlicedRowPackage O) (n : ℕ) :
    Nonempty (PhysicalRearLimitKinematics sourceKh
      ((core O P).base.column.step.richStage n).terminalBase (Q O (n + 1))) := by
  simpa [core, Q, D, rowC, pathKhat] using
    (ConfiguredRecursiveSourceP0ConstructionCoreProvider.basePhysical
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0)
      (K0 := P.K0) (K1 := P.K1) (K2 := P.K2)
      (separation_one O) (kstar_le_pathKhat O) n)

end SlicedRowPackage

structure CoherentPackage (MA0 NA0 : ℝ) where
  scalar : ConfiguredRecursiveSourceP0ScalarStart.Output MA0 NA0
  row : RowPackage scalar

/-- Coherent package for the invariant-indexed recursive path. -/
structure SlicedCoherentPackage (MA0 NA0 : ℝ) where
  scalar : ConfiguredRecursiveSourceP0ScalarStart.Output MA0 NA0
  row : SlicedRowPackage scalar

theorem conclude (P : CoherentPackage MA0 NA0) :
    Nonempty (
      Σ X : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (Q P.scalar)
        (fun n k ↦ (RowPackage.core P.scalar P.row).columns k n)
        (rowError (shiftSequence (physicalDefect P.scalar.E.data) P.scalar.large.N))
        (sourceP0 (D P.scalar))
        (wideP1 (D P.scalar) MA0) (fun _ ↦ pathKhat P.scalar)
        (wideG1 (D P.scalar) MA0 NA0)
        (wideCgWithKhat (D P.scalar) (pathKhat P.scalar) MA0 NA0)
        (rowC P.scalar) ((D P.scalar).Hs 0)
        (chordBase (D P.scalar).model / 2),
        PaperFacingVariableTerminalOutput.Output X
          (P.scalar.direction P.scalar.large.N) P.scalar.Cw
          ((D P.scalar).Hs 0)) := by
  apply ConfiguredRecursiveSourceP0MergedAssembly.conclude
    P.scalar.large P.scalar.pair P.scalar.model_data
    (RowPackage.core P.scalar P.row)
    (by simpa [D] using RowPackage.caps P.scalar P.row)
  · exact RowPackage.basePhysical P.scalar P.row
  · exact P.scalar.direction_unit
  · exact P.scalar.model_width

theorem paperMain (P : CoherentPackage MA0 NA0) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  obtain ⟨X, A⟩ := conclude P
  exact PaperMainTheoremDirectProjection.of_output A

theorem slicedConclude (P : SlicedCoherentPackage MA0 NA0) :
    Nonempty (Σ X : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (Q P.scalar)
      (fun n k ↦ (SlicedRowPackage.core P.scalar P.row).columns k n)
      (rowError (shiftSequence (physicalDefect P.scalar.E.data) P.scalar.large.N))
      (sourceP0 (D P.scalar)) (wideP1 (D P.scalar) MA0)
      (fun _ ↦ pathKhat P.scalar) (wideG1 (D P.scalar) MA0 NA0)
      (wideCgWithKhat (D P.scalar) (pathKhat P.scalar) MA0 NA0)
      (rowC P.scalar) ((D P.scalar).Hs 0)
      (chordBase (D P.scalar).model / 2),
      PaperFacingVariableTerminalOutput.Output X
        (P.scalar.direction P.scalar.large.N) P.scalar.Cw
        ((D P.scalar).Hs 0)) := by
  apply ConfiguredRecursiveSourceP0MergedAssembly.sliced_conclude
    P.scalar.large P.scalar.pair P.scalar.model_data
    (SlicedRowPackage.core P.scalar P.row)
    (by simpa [D] using SlicedRowPackage.configuredCaps P.scalar P.row)
  · exact SlicedRowPackage.basePhysical P.scalar P.row
  · exact P.scalar.direction_unit
  · exact P.scalar.model_width

theorem slicedPaperMain (P : SlicedCoherentPackage MA0 NA0) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  obtain ⟨X, A⟩ := slicedConclude P
  exact PaperMainTheoremDirectProjection.of_output A

structure FinalPackage where
  choice : ConfiguredActualHalfScalarChoice.Choice
  coherent : CoherentPackage choice.MA0 choice.NA0

/-- Final package for the invariant-indexed recursive construction. -/
structure SlicedFinalPackage where
  choice : ConfiguredActualHalfScalarChoice.Choice
  coherent : SlicedCoherentPackage choice.MA0 choice.NA0

/-- The genuinely geometric remainder after the scalar row-jet tail has been
constructed.  All cap weakening and final-package assembly are automatic. -/
structure ConfiguredSlicedRows
    (J : RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0) where
  a : ℕ → ℕ → ℝ
  MA : ℕ → ℕ → ℝ
  NA : ℕ → ℕ → ℝ
  K0 : ℝ
  K1 : ℝ
  K2 : ℝ
  source : ∀ n, MarkingAwareSource
    (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
      J.scalar.pair.input J.scalar.model_data (rowC J.scalar)
      (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one J.scalar) (kstar_le_pathKhat J.scalar)).base.step.richStage
      (n + 1)).stage.increment)
    (sourceP0 (D J.scalar) n) sourceKh (pathKhat J.scalar) (Qmax J.scalar n)
  baseSlice : SlicedCorrelatedColumn
    (ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
      J.scalar.pair.input J.scalar.model_data (rowC J.scalar)
      (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one J.scalar) (kstar_le_pathKhat J.scalar)
      khRow (Qmax J.scalar) source)
  rows : RecursiveSlicedNonaffineRowProvider (Q J.scalar)
    (ConfiguredDiagonalStableRowDefectProvider.error
      (D J.scalar) (physicalCoeff (D J.scalar)))
    (sourceP0 (D J.scalar))
    (wideP1 (D J.scalar) ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
    (fun _ ↦ pathKhat J.scalar)
    (wideG1 (D J.scalar) ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    (wideCgWithKhat (D J.scalar) (pathKhat J.scalar)
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    (rowC J.scalar) ((D J.scalar).Hs 0) (chordBase (D J.scalar).model / 2)
    (period J.scalar) (diagonal J.scalar) khRow (Qmax J.scalar)
    a MA NA K0 K1 K2
  capBounds : ∀ {current depth}
    {S : CorrelatedColumn (Q J.scalar) current
      (ConfiguredDiagonalStableRowDefectProvider.error
        (D J.scalar) (physicalCoeff (D J.scalar))) depth
      (sourceP0 (D J.scalar))
      (wideP1 (D J.scalar) ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (fun _ ↦ pathKhat J.scalar)
      (wideG1 (D J.scalar) ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (wideCgWithKhat (D J.scalar) (pathKhat J.scalar)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (rowC J.scalar) ((D J.scalar).Hs 0) (chordBase (D J.scalar).model / 2)
      (period J.scalar) (diagonal J.scalar) khRow (Qmax J.scalar)
      K0 K1 K2} (H : SlicedCorrelatedColumn S) (n : ℕ),
    ConfiguredCapBounds ((rows.rows.family H).chosenFamily.row n)
      (D J.scalar) J.scalar.Mend sourceKh

def ConfiguredSlicedRows.capped
    {J : RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    (G : ConfiguredSlicedRows J) :
    SlicedCappedNonaffineRowProvider (Q J.scalar)
      (ConfiguredDiagonalStableRowDefectProvider.error
        (D J.scalar) (physicalCoeff (D J.scalar)))
      (sourceP0 (D J.scalar))
      (wideP1 (D J.scalar) ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (fun _ ↦ pathKhat J.scalar)
      (wideG1 (D J.scalar) ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (wideCgWithKhat (D J.scalar) (pathKhat J.scalar)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (rowC J.scalar) ((D J.scalar).Hs 0) (chordBase (D J.scalar).model / 2)
      (period J.scalar) (diagonal J.scalar) khRow (Qmax J.scalar)
      G.a G.MA G.NA G.K0 G.K1 G.K2
      (endpointConversion (D J.scalar) sourceKh J.scalar.Mend)
      (physicalDefect (D J.scalar)) where
  rows := G.rows
  M := J.scalar.Mend
  M_nonnegative := J.scalar.Mend_positive.le
  cap H n := (G.capBounds H n).rowCap

def ConfiguredSlicedRows.rowPackage
    {J : RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    (G : ConfiguredSlicedRows J) : SlicedRowPackage J.scalar :=
  SlicedRowPackage.ofSlicedCappedNonaffineRows J.scalar G.source G.baseSlice G.capped

def ConfiguredSlicedRows.finalPackage
    {J : RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    (G : ConfiguredSlicedRows J) : SlicedFinalPackage where
  choice := ConfiguredRecursiveSourceP0FixedDistortion.choice
  coherent := ⟨J.scalar, G.rowPackage⟩

theorem paperMain_of_configuredSlicedRows
    {J : RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    (G : ConfiguredSlicedRows J) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  slicedPaperMain G.finalPackage.coherent

/-- Single remaining provider boundary after unconditional scalar-tail
selection. -/
structure ConfiguredSlicedRowsProvider where
  rows : ∀ J : RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0,
    ConfiguredSlicedRows J

theorem paperMain_of_configuredSlicedRowsProvider
    (G : ConfiguredSlicedRowsProvider)
    {eps0 : ℝ} (heps : 0 < eps0) (heps10 : eps0 ≤ 1 / 10) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  obtain ⟨J⟩ := exists_fixed_rowJetScalarOutput_of_eps heps heps10
  exact paperMain_of_configuredSlicedRows (G.rows J)

theorem paperMain_of_nonempty_finalPackage (hP : Nonempty FinalPackage) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  paperMain hP.some.coherent

theorem paperMain_of_nonempty_slicedFinalPackage
    (hP : Nonempty SlicedFinalPackage) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  slicedPaperMain hP.some.coherent

end ConfiguredRecursiveSourceP0CappedRowProduction
