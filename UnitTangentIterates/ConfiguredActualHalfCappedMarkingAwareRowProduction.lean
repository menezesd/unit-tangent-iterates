import UnitTangentIterates.ConfiguredMarkingAwareMergedAnalyticAssembly
import UnitTangentIterates.ConfiguredMarkingAwareAnalyticKhatBaseColumnCap
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCappedProvider
import UnitTangentIterates.ConfiguredActualHalfScalarChoice
import UnitTangentIterates.PaperMainTheoremDirectProjection

/-!
# Sound coherent marking-aware row production

All scalar sequences are definitions of the actual-half scalar start.  The
only remaining analytic data are the base marking-aware sources, the concrete
successor provider, and caps on those same selected columns.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredActualHalfCappedMarkingAwareRowProduction

open ConfiguredActualHalfMergedScalarStart
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredCorrelatedBaseColumnCap
  ConfiguredEnrichedConstructionCoreProvider
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredInductiveTubeBudget
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRowCeilingPolynomialEnvelopes
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareCappedProvider
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA0 NA0 : ℝ} (O : ConfiguredActualHalfMergedScalarStart.Output MA0 NA0)

def D : ConstructedConfiguredSequenceWeighted.Data :=
  shift O.E.data O.large.N

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

/-- Intrinsic coefficients and analytic choices selected together by the
genuine marking-aware row theorem. -/
structure RowPackage where
  a : ℕ → ℕ → ℝ
  MA : ℕ → ℕ → ℝ
  NA : ℕ → ℕ → ℝ
  K0 : ℝ
  K1 : ℝ
  K2 : ℝ
  source : ∀ n, MarkingAwareSource
    (((ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one O) (kstar_le_pathKhat O)).base.step.richStage
      (n + 1)).stage.increment)
    (ConfiguredApproximateDefectPathRowwise.rowP0 (D O) n)
    sourceKh (pathKhat O) (Qmax O n)
  provider : CappedProvider (Q O)
    (ConfiguredDiagonalStableRowDefectProvider.error (D O)
      (physicalCoeff (D O)))
    (ConfiguredApproximateDefectPathRowwise.rowP0 (D O))
    (wideP1 (D O) MA0) (fun _ ↦ pathKhat O)
    (wideG1 (D O) MA0 NA0)
    (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
    (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
    (period O) (diagonal O) khRow (Qmax O) a MA NA K0 K1 K2
    (endpointConversion (D O) sourceKh O.Mend) (physicalDefect (D O))

namespace RowPackage

def core (P : RowPackage O) :
    ConstructionCore (Q O)
      (ConfiguredDiagonalStableRowDefectProvider.error (D O)
        (physicalCoeff (D O)))
      (ConfiguredApproximateDefectPathRowwise.rowP0 (D O))
      (wideP1 (D O) MA0) (fun _ ↦ pathKhat O)
      (wideG1 (D O) MA0 NA0)
      (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
      (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
      (period O) (diagonal O) khRow (Qmax O)
      P.a P.MA P.NA P.K0 P.K1 P.K2 :=
  ConfiguredMarkingAwareAnalyticKhatConstructionCoreProvider.constructionCore
    O.pair.input O.model_data (rowC O)
    (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O)
    P.a P.MA P.NA P.K0 P.K1 P.K2 P.source P.provider.provider

theorem basePhysical (P : RowPackage O) (n : ℕ) :
    Nonempty (PhysicalRearLimitKinematics sourceKh
      ((core O P).base.column.step.richStage n).terminalBase (Q O (n + 1))) := by
  simpa [core, Q, D, rowC, pathKhat] using
    (ConfiguredMarkingAwareAnalyticKhatConstructionCoreProvider.basePhysical
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
    (ConfiguredMarkingAwareAnalyticKhatBaseColumnCap.baseColumnCap
      (S := O.pair.input) (hQ := O.model_data) (C := rowC O)
      (hH := separation_one O) (hkhat := kstar_le_pathKhat O)
      (MA0 := MA0) (NA0 := NA0)
      (K0 := P.K0) (K1 := P.K1) (K2 := P.K2)
      (khRow := khRow) (Qmax := Qmax O) (source := P.source)
      (M := O.Mend) (rowDefect_le_Mend O))

/-- Automatic cap family from the configured base estimate and the caps
retained by the same concrete successor provider. -/
def caps (P : RowPackage O) :
    CapFamily (core O P)
      (ConfiguredMarkingAwareMergedEndpointGrowth.mergedEndpointConversion
        (D O) sourceKh O.Mend)
      (physicalDefect (D O)) := by
  simpa [core,
    ConfiguredMarkingAwareMergedEndpointGrowth.mergedEndpointConversion] using
    P.provider.capFamilyOfSeparate
      (ConfiguredDiagonalStableRowDefectProvider.provider (D O)
        (physicalCertificate (D O)))
      (ConfiguredMarkingAwareAnalyticKhatConstructionCoreProvider.baseCorrelated
        O.pair.input O.model_data (rowC O)
        (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O) P.source)
      (baseCap O P) (physicalDefect_nonneg (D O))

end RowPackage

/-- One coherent sound producer package. -/
structure CoherentPackage (MA0 NA0 : ℝ) where
  scalar : ConfiguredActualHalfMergedScalarStart.Output MA0 NA0
  row : RowPackage scalar

theorem conclude (P : CoherentPackage MA0 NA0) :
    Nonempty (
      Σ X : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (Q P.scalar)
        (fun n k ↦ (RowPackage.core P.scalar P.row).columns k n)
        (rowError
          (shiftSequence (physicalDefect P.scalar.E.data) P.scalar.large.N))
        (ConfiguredApproximateDefectPathRowwise.rowP0 (D P.scalar))
        (wideP1 (D P.scalar) MA0) (fun _ ↦ pathKhat P.scalar)
        (wideG1 (D P.scalar) MA0 NA0)
        (wideCgWithKhat (D P.scalar) (pathKhat P.scalar) MA0 NA0)
        (rowC P.scalar) ((D P.scalar).Hs 0)
        (chordBase (D P.scalar).model / 2),
        PaperFacingVariableTerminalOutput.Output X
          (P.scalar.direction P.scalar.large.N) P.scalar.Cw
          ((D P.scalar).Hs 0)) := by
  apply ConfiguredMarkingAwareMergedAnalyticAssembly.conclude
    P.scalar.large P.scalar.pair P.scalar.model_data
    (RowPackage.core P.scalar P.row)
    (by simpa [D] using RowPackage.caps P.scalar P.row)
  · exact RowPackage.basePhysical P.scalar P.row
  · exact P.scalar.direction_unit
  · exact P.scalar.model_width

/-- The exact ordinary-curve statement of the paper from one sound coherent
row-production package. -/
theorem paperMain (P : CoherentPackage MA0 NA0) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  obtain ⟨X, A⟩ := conclude P
  exact PaperMainTheoremDirectProjection.of_output A

/-- Envelope values and the sound producer are selected coherently.  This is
the exact final existential left to the analytic row-construction branch. -/
structure FinalPackage where
  choice : ConfiguredActualHalfScalarChoice.Choice
  coherent : CoherentPackage choice.MA0 choice.NA0

theorem paperMain_of_nonempty_finalPackage
    (hP : Nonempty FinalPackage) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  exact paperMain hP.some.coherent

end ConfiguredActualHalfCappedMarkingAwareRowProduction
