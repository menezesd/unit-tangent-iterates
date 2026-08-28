import UnitTangentIterates.ConfiguredAnalyticKhatCombinedCorrelatedAssembly

/-!
# Legacy affine correlated row packaging after the scalar start

This module canonicalizes scalar sequences for the older affine correlated
provider.  That provider is retained as an auxiliary migration target only:
the paper-facing construction must instead use the marking-aware sibling with
an explicit physical front.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredActualHalfAnalyticRowProduction

open ConfiguredActualHalfScalarStart
  ConfiguredAnalyticKhatConstructionCoreProvider
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredEnrichedConstructionCoreProvider
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredInductiveTubeBudget
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRowCeilingPolynomialEnvelopes
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyAnalyticSource
  FiniteSmoothRearFamilyCorrelatedPhysicalCore
  FiniteSmoothRearFamilyCorrelatedRecursion

variable {MA0 NA0 : ℝ} (O : ConfiguredActualHalfScalarStart.Output MA0 NA0)

def D : ConstructedConfiguredSequenceWeighted.Data :=
  shift O.E.data O.large.N

def Q : ℕ → Data := alignedQ O.pair.input O.model_data

def rowC : ℕ → ℝ := outputUpper O.E.data O.large

def period : ℕ → ℕ → ℝ :=
  ConfiguredEnrichedConstructionCoreProvider.period (D O)

def diagonal : ℕ → ℝ :=
  ConfiguredEnrichedConstructionCoreProvider.diagonal (D O)

def khRow : ℕ → ℝ := fun _ ↦ sourceKh

/-- The selected rear period is bounded by the same configured row upper cap
reserved by the scalar large-separation output. -/
def Qmax : ℕ → ℝ := (rowC O)

/-- Every shifted diagonal stage cost is below the scalar cap `Mend`. -/
def Mtotal : ℕ → ℝ := fun _ ↦ O.Mend

def pathKhat : ℝ := analyticKhat O.E.data

theorem separation_one : 1 ≤ (D O).Hs 0 := O.large.separation_one

theorem kstar_le_pathKhat : (D O).kstar ≤ (pathKhat O) := by
  simpa [D, pathKhat] using kstar_le_analyticKhat O.E.data

/-- Legacy correlated analytic data selected by the recursive long
rear-family theorem.  `a`, `MA`, `NA`, and `K0..K2` are not chosen separately:
they are the coefficients of this same selected family. -/
structure LegacyPackage where
  a : ℕ → ℕ → ℝ
  MA : ℕ → ℕ → ℝ
  NA : ℕ → ℕ → ℝ
  K0 : ℝ
  K1 : ℝ
  K2 : ℝ
  source : ∀ n, Source
    (((ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider
        O.pair.input O.model_data (rowC O)
        (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
        (separation_one O) (kstar_le_pathKhat O)).base.step.richStage
        (n + 1)).stage.increment)
    (ConfiguredApproximateDefectPathRowwise.rowP0 (D O) n)
    sourceKh (pathKhat O) ((Qmax O) n)
  provider : FiniteSmoothRearFamilyCorrelatedRecursion.Provider
    (Q O)
    (ConfiguredDiagonalStableRowDefectProvider.error (D O)
      (physicalCoeff (D O)))
    (ConfiguredApproximateDefectPathRowwise.rowP0 (D O))
    (wideP1 (D O) MA0) (fun _ ↦ (pathKhat O))
    (wideG1 (D O) MA0 NA0) (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
    (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
    (period O) (diagonal O) khRow (Qmax O) (Mtotal O) a MA NA K0 K1 K2

namespace LegacyPackage

def core (P : LegacyPackage O) :
    FiniteSmoothRearFamilyCorrelatedPhysicalCore.ConstructionCore
      (Q O)
      (ConfiguredDiagonalStableRowDefectProvider.error (D O)
        (physicalCoeff (D O)))
      (ConfiguredApproximateDefectPathRowwise.rowP0 (D O))
      (wideP1 (D O) MA0) (fun _ ↦ (pathKhat O))
      (wideG1 (D O) MA0 NA0) (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
      (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
      (period O) (diagonal O) khRow (Qmax O) (Mtotal O)
      P.a P.MA P.NA P.K0 P.K1 P.K2 :=
  ConfiguredAnalyticKhatConstructionCoreProvider.constructionCore
    O.pair.input O.model_data (rowC O) (separation_one O) (kstar_le_pathKhat O)
    khRow (Qmax O) (Mtotal O) P.a P.MA P.NA P.K0 P.K1 P.K2
    P.source P.provider

/-- The only quantitative projection required from the same selected row
outputs: terminal marking distance and nonnegative terminal curvature. -/
structure Capped (P : LegacyPackage O) : Prop where
  caps : CapFamily (core O P)
    (shiftSequence (endpointConversion O.E.data sourceKh O.Mend) O.large.N)
    (shiftSequence (physicalDefect O.E.data) O.large.N)

theorem basePhysical (P : LegacyPackage O) (n : ℕ) :
    Nonempty (PhysicalRearLimitKinematics sourceKh
      ((core O P).base.column.step.richStage n).terminalBase ((Q O) (n + 1))) := by
  simpa [core, Q, D, rowC, pathKhat] using
    (ConfiguredAnalyticKhatConstructionCoreProvider.basePhysical
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := P.K0) (K1 := P.K1) (K2 := P.K2)
      (separation_one O) (kstar_le_pathKhat O) n)

/-- Auxiliary conclusion for the legacy affine provider.  This is not the
paper's final construction: the sound marking-aware recursion cannot be
projected into this provider because its physical front is independent of the
affinely marked endpoint. -/
theorem legacyConclude (P : LegacyPackage O) (R : Capped O P) :
    Nonempty (
      Σ X : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (Q O) (fun n k ↦ (core O P).columns k n)
        (ExponentialDiagonalLargeSeparation.rowError
          (shiftSequence (physicalDefect O.E.data) O.large.N))
        (ConfiguredApproximateDefectPathRowwise.rowP0 (D O))
        (wideP1 (D O) MA0) (fun _ ↦ (pathKhat O))
        (wideG1 (D O) MA0 NA0) (wideCgWithKhat (D O) (pathKhat O) MA0 NA0)
        (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2),
        PaperFacingVariableTerminalOutput.Output X
          (O.direction O.large.N) O.Cw ((D O).Hs 0)) := by
  apply ConfiguredAnalyticKhatCombinedCorrelatedAssembly.conclude
    O.large O.pair O.model_data (core O P) R.caps
  · exact basePhysical O P
  · exact O.direction_unit
  · exact O.model_width

end LegacyPackage

/-- A coherent package for the legacy affine provider, retained only for API
migration and regression checks. -/
structure LegacyCoherentPackage (MA0 NA0 : ℝ) where
  scalar : ConfiguredActualHalfScalarStart.Output MA0 NA0
  row : LegacyPackage scalar
  caps : CapFamily (LegacyPackage.core scalar row)
    (shiftSequence
      (endpointConversion scalar.E.data sourceKh scalar.Mend) scalar.large.N)
    (shiftSequence (physicalDefect scalar.E.data) scalar.large.N)

/-- Auxiliary composition through the legacy affine provider. -/
theorem legacyConclude_of_coherentPackage {MA0 NA0 : ℝ}
    (P : LegacyCoherentPackage MA0 NA0) :
    Nonempty (
      Σ X : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (Q P.scalar) (fun n k ↦ (LegacyPackage.core P.scalar P.row).columns k n)
        (ExponentialDiagonalLargeSeparation.rowError
          (shiftSequence (physicalDefect P.scalar.E.data) P.scalar.large.N))
        (ConfiguredApproximateDefectPathRowwise.rowP0 (D P.scalar))
        (wideP1 (D P.scalar) MA0) (fun _ ↦ pathKhat P.scalar)
        (wideG1 (D P.scalar) MA0 NA0)
        (wideCgWithKhat (D P.scalar) (pathKhat P.scalar) MA0 NA0)
        (rowC P.scalar) ((D P.scalar).Hs 0) (chordBase (D P.scalar).model / 2),
        PaperFacingVariableTerminalOutput.Output X
          (P.scalar.direction P.scalar.large.N) P.scalar.Cw
          ((D P.scalar).Hs 0)) :=
  LegacyPackage.legacyConclude P.scalar P.row ⟨P.caps⟩

end ConfiguredActualHalfAnalyticRowProduction
