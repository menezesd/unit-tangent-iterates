import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalGeometricBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput

/-! # Canonical depth-zero stage for the truthful recost diagonal -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedRawDiagonalBase

open ConfiguredRecursiveEdgePhysicalGeometricBase
  ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
  FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows

variable {MA NA K0 K1 K2 : ℝ}

private theorem half_khat_eq_sourceKh :
    TubeConstants.khat ((1 : ℝ) / 2) =
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
  rw [ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq]
  norm_num [TubeConstants.khat]

def unaryStage
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :=
  ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage
    (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
      (K0 := K0) (K1 := K1) (K2 := K2)) n

/-- The synchronized depth-zero stage is the configured physical initial
representative.  Its rear remains the next moved-rear representative. -/
def stage
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    Stage (Profiles.P0 (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
      (Profiles.kh (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
      (Profiles.khat (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
      (Profiles.Qmax (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
      n 0 where
  start := (unaryStage (K0 := K0) (K1 := K1) (K2 := K2) J n).start
  rear := (unaryStage (K0 := K0) (K1 := K1) (K2 := K2) J n).rear
  Gamma := (unaryStage (K0 := K0) (K1 := K1) (K2 := K2) J n).Gamma
  source := by
    convert (unaryStage (K0 := K0) (K1 := K1) (K2 := K2) J n).source using 1 <;>
      simp [unaryStage, Profiles.P0, Profiles.kh, Profiles.khat, Profiles.Qmax,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.P0,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.kh,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.khat,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.Qmax,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq,
      half_khat_eq_sourceKh, TubeConstants.khat] <;> norm_num
  applied := by
    convert (unaryStage (K0 := K0) (K1 := K1) (K2 := K2) J n).applied using 1 <;>
      simp [unaryStage, Profiles.P0, Profiles.kh, Profiles.khat, Profiles.Qmax,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.P0,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.kh,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.khat,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.Qmax,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq,
      half_khat_eq_sourceKh, TubeConstants.khat] <;> norm_num
  displayed := ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar n

@[simp] theorem stage_displayed
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    (stage (K0 := K0) (K1 := K1) (K2 := K2) J n).displayed =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar n := rfl

theorem stage_displayed_range_baseCurrent
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    range (stage (K0 := K0) (K1 := K1) (K2 := K2) J n).displayed.1 =
      range (ConfiguredRecursiveEdgePhysicalGeometricBase.baseCurrent J
        (K0 := K0) (K1 := K1) (K2 := K2) n).1 := by
  simpa using
    (ConfiguredRecursiveEdgePhysicalGeometricBase.initial_range_baseCurrent J
      (K0 := K0) (K1 := K1) (K2 := K2) n)

theorem stage_displayed_tube
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    IsTubeMember
      (ConfiguredCanonicalPairSource.commonC
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)) 0
      (ConfiguredCanonicalPairSource.commonDlt
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
      (stage (K0 := K0) (K1 := K1) (K2 := K2) J n).displayed := by
  simpa [stage, ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D] using
    (ConfiguredRecursiveEdgePhysicalInitialData.initial_tube J.scalar n)

theorem stage_rear_range
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    range (stage (K0 := K0) (K1 := K1) (K2 := K2) J n).rear.1 =
      range (stage (K0 := K0) (K1 := K1) (K2 := K2) J (n + 1)).displayed.1 := by
  simpa [stage, unaryStage,
    ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
    ConfiguredRecursiveEdgePhysicalGeometricBase.base] using
    (ConfiguredRecursiveEdgePhysicalGeometricBase.initial_range_baseCurrent J
      (K0 := K0) (K1 := K1) (K2 := K2) (n + 1)).symm

def slice
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessorSliceFacts
      (stage (K0 := K0) (K1 := K1) (K2 := K2) J n).source := by
  convert (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
      (K0 := K0) (K1 := K1) (K2 := K2)).slice n using 1 <;>
    simp [stage, unaryStage, Profiles.P0, Profiles.kh, Profiles.khat, Profiles.Qmax,
    ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.P0,
    ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.kh,
    ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.khat,
    ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.Qmax,
    ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat,
    ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax,
    ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat,
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq,
    half_khat_eq_sourceKh, TubeConstants.khat] <;> norm_num

variable {E0 C00 C10 C20 : ℕ → ℝ} {d0 : ℕ → ℕ → ℝ}

/-- Install the canonical physical base into the truthful diagonal recursion.
The remaining argument is exactly the dependent recursive step family. -/
def rows
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (next : ∀ k (S : ∀ n,
      Stage
        (Profiles.P0 (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        (Profiles.kh (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        (Profiles.khat (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        (Profiles.Qmax (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        n k),
      Step (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
        S E0 C00 C10 C20 d0) :
    Rows (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
      E0 C00 C10 C20 d0 where
  base := stage (K0 := K0) (K1 := K1) (K2 := K2) J
  base_range := stage_rear_range J
  step := next

@[simp] theorem rows_P_zero
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (next : ∀ k (S : ∀ n,
      Stage
        (Profiles.P0 (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        (Profiles.kh (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        (Profiles.khat (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        (Profiles.Qmax (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        n k),
      Step (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
        S E0 C00 C10 C20 d0)
    (n : ℕ) :
    (rows (K0 := K0) (K1 := K1) (K2 := K2) J next).P n 0 =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar n := rfl

def rowsBaseSlice
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (next : ∀ k (S : ∀ n,
      Stage
        (Profiles.P0 (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        (Profiles.kh (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        (Profiles.khat (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        (Profiles.Qmax (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
        n k),
      Step (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
        S E0 C00 C10 C20 d0)
    (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessorSliceFacts
      ((rows (K0 := K0) (K1 := K1) (K2 := K2) J next).stages 0 n).source :=
  slice J n

end ConfiguredRecursiveEdgeRecostedRawDiagonalBase
