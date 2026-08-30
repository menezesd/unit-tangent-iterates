import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0MergedAssembly
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0BaseColumnCap
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0RowJetTail
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0BaseSliceFactsAdapter
import UnitTangentIterates.ConfiguredBaseProfiledEdgeSourceFamily
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider
import UnitTangentIterates.PaperMainTheoremDirectProjection

/-! # Coherent sliced row production at the genuine successor-edge floor -/

noncomputable section

open Set MarkedSpace PathMetric RearOwnArclength

namespace ConfiguredRecursiveEdgeSourceP0CappedRowProduction

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredCorrelatedBaseColumnCap
  ConfiguredEnrichedConstructionCoreProvider
  ConfiguredInductiveTubeBudget
  ConfiguredMarkingAwareMergedEndpointGrowth
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveEdgeSourceP0ScalarStart
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCappedProvider
  FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily

variable {MA0 NA0 : ℝ} (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA0 NA0)

def D : ConstructedConfiguredSequenceWeighted.Data := shift O.E.data O.large.N
def Q : ℕ → Data := ConfiguredGaugeFirstPhysicalSequence.alignedQ O.pair.input O.model_data
def rowC : ℕ → ℝ := outputUpper O.E.data O.large
def period : ℕ → ℕ → ℝ := ConfiguredEnrichedConstructionCoreProvider.period (D O)
def diagonal : ℕ → ℝ := edgePhysicalDefect (D O)
def khRow : ℕ → ℝ := fun _ ↦ sourceKh
def Qmax : ℕ → ℝ := edgeSpeedCap (D O)
def pathKhat : ℝ := analyticKhat O.E.data

theorem separation_one : 1 ≤ (D O).Hs 0 := by
  simpa [D] using O.large.separation_one

theorem kstar_le_pathKhat : (D O).kstar ≤ pathKhat O := by
  simpa [D, pathKhat] using kstar_le_analyticKhat O.E.data

/-- The unconditional genuine-gauge edge sources transported into the exact
phase/rigid presentation selected by the configured base column. -/
noncomputable def baseSource
    {K0 K1 K2 : ℝ} : ∀ n, MarkingAwareSource
    (((ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one O) (kstar_le_pathKhat O)).base.step.richStage
      (n + 1)).stage.increment)
    (edgeSourceP0 (D O) n) sourceKh (pathKhat O) (Qmax O n) := by
  simpa [D, pathKhat, Qmax, ConfiguredBaseProfiledEdgeSourceFamily.data] using
    (ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourcesOfOutputs
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O)
      (ConfiguredBaseProfiledEdgeSourceFamily.edgeSourceFamily O))

/-- The exact slice invariant of the normalized edge source family.  No
additional base-column regularity input is required. -/
noncomputable def baseSlice
    {K0 K1 K2 : ℝ} : SlicedCorrelatedColumn
    (ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseCorrelated
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O)
      (baseSource O)) where
  slice n := by
    simpa [baseSource, D, pathKhat, Qmax,
      ConfiguredBaseProfiledEdgeSourceFamily.data] using
      (ConfiguredRecursiveEdgeSourceP0BaseSliceFactsAdapter.edgeTransportedSliceFacts
        O (rowC O) (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n)
  periodUpper_le n := by
    simpa [baseSource, D, pathKhat, Qmax,
      ConfiguredBaseProfiledEdgeSourceFamily.data] using
      (ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily.edgePeriodUpper_le_edgeP1
        O n)

structure SlicedRowPackage where
  a : ℕ → ℕ → ℝ
  MA : ℕ → ℕ → ℝ
  NA : ℕ → ℕ → ℝ
  K0 : ℝ
  K1 : ℝ
  K2 : ℝ
  source : ∀ n, MarkingAwareSource
    (((ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one O) (kstar_le_pathKhat O)).base.step.richStage
      (n + 1)).stage.increment)
    (edgeSourceP0 (D O) n) sourceKh (pathKhat O) (Qmax O n)
  baseSlice : SlicedCorrelatedColumn
    (ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseCorrelated
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
      (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O) source)
  provider : SlicedCappedProvider (Q O)
    (ConfiguredDiagonalStableRowDefectProvider.error (D O) (physicalCoeff (D O)))
    (edgeSourceP0 (D O)) (edgeP1 (D O) MA0) (fun _ ↦ pathKhat O)
    (edgeG1 (D O) MA0 NA0) (edgeCgWithKhat (D O) (pathKhat O) MA0 NA0)
    (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
    (period O) (diagonal O) khRow (Qmax O) a MA NA K0 K1 K2
    (endpointConversion (D O) sourceKh O.Mend) (diagonal O)

namespace SlicedRowPackage

/-- Install a reachable provider once the exact transported base slice has
been retained.  The base source family itself is unconditional. -/
def ofAutomaticBase
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (provider : SlicedCappedProvider (Q O)
      (ConfiguredDiagonalStableRowDefectProvider.error (D O) (physicalCoeff (D O)))
      (edgeSourceP0 (D O)) (edgeP1 (D O) MA0) (fun _ ↦ pathKhat O)
      (edgeG1 (D O) MA0 NA0) (edgeCgWithKhat (D O) (pathKhat O) MA0 NA0)
      (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
      (period O) (diagonal O) khRow (Qmax O) a MA NA K0 K1 K2
      (endpointConversion (D O) sourceKh O.Mend) (diagonal O)) :
    SlicedRowPackage O where
  a := a
  MA := MA
  NA := NA
  K0 := K0
  K1 := K1
  K2 := K2
  source := baseSource O
  baseSlice := ConfiguredRecursiveEdgeSourceP0CappedRowProduction.baseSlice
    (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) O
  provider := provider

def core (P : SlicedRowPackage O) :
    SlicedConstructionCore (Q O)
      (ConfiguredDiagonalStableRowDefectProvider.error (D O) (physicalCoeff (D O)))
      (edgeSourceP0 (D O)) (edgeP1 (D O) MA0) (fun _ ↦ pathKhat O)
      (edgeG1 (D O) MA0 NA0) (edgeCgWithKhat (D O) (pathKhat O) MA0 NA0)
      (rowC O) ((D O).Hs 0) (chordBase (D O).model / 2)
      (period O) (diagonal O) khRow (Qmax O)
      P.a P.MA P.NA P.K0 P.K1 P.K2 where
  defect := ConfiguredDiagonalStableRowDefectProvider.provider
    (D O) (physicalCertificate (D O))
  base := ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseCorrelated
    O.pair.input O.model_data (rowC O)
    (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O) P.source
  baseSlice := P.baseSlice
  provider := P.provider.provider

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
    simpa [D, edgePhysicalDefect, shift,
      physicalDefect, physicalCoeff,
      ConfiguredApproximateDefectPathRowwise.rowDefect] using
      O.physicalDefect_lt (O.large.N + n)
  exact hscale.trans hstrict.le

theorem diagonal_lt_Mend (n : ℕ) : diagonal O n < O.Mend := by
  simpa [D, diagonal, edgePhysicalDefect, shift,
    physicalDefect, physicalCoeff,
    ConfiguredApproximateDefectPathRowwise.rowDefect] using
    O.physicalDefect_lt (O.large.N + n)

theorem baseCap (P : SlicedRowPackage O) :
    ColumnCap (core O P).base
      (baseEndpointConversion (D O) O.Mend) (diagonal O) := by
  simpa [core, diagonal, edgePhysicalDefect] using
    (ConfiguredRecursiveEdgeSourceP0BaseColumnCap.baseColumnCap
      (S := O.pair.input) (hQ := O.model_data) (C := rowC O)
      (hH := separation_one O) (hkhat := kstar_le_pathKhat O)
      (MA0 := MA0) (NA0 := NA0)
      (K0 := P.K0) (K1 := P.K1) (K2 := P.K2)
      (khRow := khRow) (Qmax := Qmax O) (source := P.source)
      (M := O.Mend) (rowDefect_le_Mend O))

def configuredCaps (P : SlicedRowPackage O) :
    SlicedCapFamily (core O P)
      (edgeEndpointConversion (D O) sourceKh O.Mend) (diagonal O) := by
  let oldCaps : SlicedCapFamily (core O P)
      (mergedEndpointConversion (D O) sourceKh O.Mend) (diagonal O) := by
    simpa [core, mergedEndpointConversion, diagonal, edgePhysicalDefect] using
      P.provider.capFamilyOfSeparate
        (ConfiguredDiagonalStableRowDefectProvider.provider (D O)
          (physicalCertificate (D O)))
        (ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseCorrelated
          O.pair.input O.model_data (rowC O)
          (separation_one O) (kstar_le_pathKhat O) khRow (Qmax O) P.source)
        P.baseSlice (baseCap O P) (physicalDefect_nonneg (D O))
  have hdiag : ∀ j, 0 ≤ diagonal O j := by
    intro j
    exact edgePhysicalDefect_nonnegative (D O) j
  refine
    { base :=
        { endpoint_dist := ?_
          terminal_curvature := oldCaps.base.terminal_curvature }
      successor := ?_ }
  · intro n
    exact (oldCaps.base.endpoint_dist n).trans
      (mul_le_mul_of_nonneg_right
        (mergedEndpointConversion_le_edgeEndpointConversion
          (D O) sourceKh O.Mend n) (hdiag _))
  · intro k
    refine
      { endpoint_dist := ?_
        terminal_curvature := (oldCaps.successor k).terminal_curvature }
    intro n
    exact ((oldCaps.successor k).endpoint_dist n).trans
      (mul_le_mul_of_nonneg_right
        (mergedEndpointConversion_le_edgeEndpointConversion
          (D O) sourceKh O.Mend n) (hdiag _))

theorem basePhysical (P : SlicedRowPackage O) (n : ℕ) :
    Nonempty (PhysicalRearLimitKinematics sourceKh
      ((core O P).base.column.step.richStage n).terminalBase (Q O (n + 1))) := by
  simpa [core, Q, D, rowC, pathKhat] using
    (ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.basePhysical
      O.pair.input O.model_data (rowC O)
      (MA0 := MA0) (NA0 := NA0)
      (K0 := P.K0) (K1 := P.K1) (K2 := P.K2)
      (separation_one O) (kstar_le_pathKhat O) n)

end SlicedRowPackage

structure SlicedCoherentPackage (MA0 NA0 : ℝ) where
  scalar : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA0 NA0
  row : SlicedRowPackage scalar

theorem slicedConclude (P : SlicedCoherentPackage MA0 NA0) :
    Nonempty (Σ X : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (Q P.scalar)
      (fun n k ↦ (SlicedRowPackage.core P.scalar P.row).columns k n)
      (rowError (shiftSequence (edgePhysicalDefect P.scalar.E.data) P.scalar.large.N))
      (edgeSourceP0 (D P.scalar)) (edgeP1 (D P.scalar) MA0)
      (fun _ ↦ pathKhat P.scalar) (edgeG1 (D P.scalar) MA0 NA0)
      (edgeCgWithKhat (D P.scalar) (pathKhat P.scalar) MA0 NA0)
      (rowC P.scalar) ((D P.scalar).Hs 0)
      (chordBase (D P.scalar).model / 2),
      PaperFacingVariableTerminalOutput.Output X
        (P.scalar.direction P.scalar.large.N) P.scalar.Cw
        ((D P.scalar).Hs 0)) := by
  apply ConfiguredRecursiveEdgeSourceP0MergedAssembly.sliced_conclude
    P.scalar.large P.scalar.pair P.scalar.model_data
    (SlicedRowPackage.core P.scalar P.row)
    (by simpa [D, diagonal] using SlicedRowPackage.configuredCaps P.scalar P.row)
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
  /-- The genuinely recursive geometric input.  Its row data contain the
  configured terminal input, functional facts, scalar domination, and exact
  analytic successor for each reachable sliced column; the library then
  constructs the applied paths, chosen outputs, transitions, and successors. -/
  rows : RecursiveSlicedNonaffineRowProvider (Q J.scalar)
    (ConfiguredDiagonalStableRowDefectProvider.error
      (D J.scalar) (physicalCoeff (D J.scalar)))
    (edgeSourceP0 (D J.scalar))
    (edgeP1 (D J.scalar)
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
    (fun _ ↦ pathKhat J.scalar)
    (edgeG1 (D J.scalar)
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar)
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    (rowC J.scalar) ((D J.scalar).Hs 0)
    (chordBase (D J.scalar).model / 2)
    (period J.scalar) (diagonal J.scalar) khRow (Qmax J.scalar)
    a MA NA K0 K1 K2
  /-- The sole cap datum not implied by the chosen output's cost bound and
  the configured scalar tail. -/
  coefficient_le : ∀ {current depth}
    {S : CorrelatedColumn (Q J.scalar) current
      (ConfiguredDiagonalStableRowDefectProvider.error
        (D J.scalar) (physicalCoeff (D J.scalar))) depth
      (edgeSourceP0 (D J.scalar))
      (edgeP1 (D J.scalar)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (fun _ ↦ pathKhat J.scalar)
      (edgeG1 (D J.scalar)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (rowC J.scalar) ((D J.scalar).Hs 0)
      (chordBase (D J.scalar).model / 2)
      (period J.scalar) (diagonal J.scalar) khRow (Qmax J.scalar)
      K0 K1 K2} (H : SlicedCorrelatedColumn S) (n : ℕ),
    let R := ((rows.rows.family H).chosenFamily.row n)
    InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
      R.terminalInput.Lmax (rearPeriod (S.source n) 0)
      (rearKappa1 sourceKh) (rearKappa2 sourceKh) J.scalar.Mend
      R.terminalInput.physical.L R.terminalInput.physical.kb
      R.terminalInput.physical.kL ≤
        endpointConversion (D J.scalar) sourceKh J.scalar.Mend n

def ConfiguredSlicedRows.capped
    {J : RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    (G : ConfiguredSlicedRows J) :
    SlicedCappedNonaffineRowProvider (Q J.scalar)
      (ConfiguredDiagonalStableRowDefectProvider.error
        (D J.scalar) (physicalCoeff (D J.scalar)))
      (edgeSourceP0 (D J.scalar))
      (edgeP1 (D J.scalar)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (fun _ ↦ pathKhat J.scalar)
      (edgeG1 (D J.scalar)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (rowC J.scalar) ((D J.scalar).Hs 0)
      (chordBase (D J.scalar).model / 2)
      (period J.scalar) (diagonal J.scalar) khRow (Qmax J.scalar)
      G.a G.MA G.NA G.K0 G.K1 G.K2
      (endpointConversion (D J.scalar) sourceKh J.scalar.Mend)
      (diagonal J.scalar) where
  rows := G.rows
  M := J.scalar.Mend
  M_nonnegative := J.scalar.Mend_positive.le
  cap {current} {k} {S} H n := by
    let R := ((G.rows.rows.family H).chosenFamily.row n)
    have hcost : R.output.chosen.Delta.cost ≤
        ConfiguredDiagonalStableRowDefectProvider.error
          (D J.scalar) (physicalCoeff (D J.scalar)) n (k + 1) := by
      rw [R.output.chosen.cost_eq]
      exact R.terminalInput.cost_le
    have heq : ConfiguredDiagonalStableRowDefectProvider.error
          (D J.scalar) (physicalCoeff (D J.scalar)) n (k + 1) =
        diagonal J.scalar (n + (k + 1)) := by
      rfl
    refine
      { cost_le_M := hcost.trans_eq heq |>.trans
          (SlicedRowPackage.diagonal_lt_Mend J.scalar _).le
        coefficient_le := ?_
        cost_le_diagonal := hcost.trans_eq heq }
    simpa [R, khRow] using G.coefficient_le H n

def ConfiguredSlicedRows.rowPackage
    {J : RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    (G : ConfiguredSlicedRows J) : SlicedRowPackage J.scalar :=
  SlicedRowPackage.ofAutomaticBase J.scalar G.capped.slicedCappedProvider

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
  exact slicedPaperMain ⟨J.scalar, (G.rows J).rowPackage⟩

end ConfiguredRecursiveEdgeSourceP0CappedRowProduction
