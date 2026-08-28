import UnitTangentIterates.ConfiguredPhysicalDiagonalRowBudget
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalInitialData
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing

/-!
# Final row budget for multiplier-aware recost closing

The final closing output has already selected both scalar tails.  This module
specializes the generic diagonal row-budget theorem to that final data and to
the truthful physical initial rear.  It also exposes the finite-prefix
inequality used by the outer tube induction.
-/

noncomputable section

set_option maxHeartbeats 2000000

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierRowBudget

open ConfiguredPhysicalDiagonalRowBudget
  ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeFullRecostMetricDiagonal
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  VariableTerminalRowTubeAdapter

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J}

/-- The truthful fixed model for row `n` after all closing shifts. -/
def base (R : RecostClosingOutput J O) (n : ℕ) : Data :=
  ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
    (R.totalShift + n)

/-- The local-stability interpolation parameter selected by the final
large-separation output. -/
def rho (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  ConstructedRowDefectLargeSeparation.rowRhoVariable
    R.data.model R.radius n

/-- Fixed upper speed used throughout row `n`. -/
def upper (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  2 * R.data.Hs n + R.radius n

/-- The complete final RowBudget type.  The paper-facing path coefficient is
one because `R.error` already contains all physical and recost conversions. -/
abbrev BudgetType (R : RecostClosingOutput J O) :=
  RowBudget (base R)
    ActualStageProvider.paperP0 ActualStageProvider.paperP1
    ActualStageProvider.paperKhat ActualStageProvider.paperG1
    ActualStageProvider.paperCg
    (fun _ ↦ 2 * R.data.Hs 0)
    (fun _ ↦ ConfiguredInductiveTubeBudget.chordBase R.data.model)
    (ConfiguredInductiveTubeBudget.accBound R.data.model)
    R.radius (rho R) (upper R)
    (R.data.Hs 0)
    (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)

theorem exists_rowBudget (R : RecostClosingOutput J O) :
    Nonempty (BudgetType R) := by
  let Dpre := shift O.data R.preShift
  have hdiag : ∀ q, 0 ≤ shiftSequence
      (fullRecostMetricDiagonal O.data
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
        J.scalar.Mend) R.preShift q := by
    intro q
    exact fullRecostMetricDiagonal_nonnegative O.data _
  have hperim : ∀ n, perim (base R n) =
      2 * (shift Dpre R.large.N).Hs n := by
    intro n
    rw [base, ConfiguredRecursiveEdgePhysicalInitialData.initial_perim_eq]
    simp [Dpre, RecostClosingOutput.totalShift,
      ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
      ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
      ConfiguredBaseProfiledEdgeSourceFamily.data,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      Nat.add_assoc]
  obtain ⟨B⟩ := exists_rowBudget_of_output Dpre R.large
    (fun _ ↦ by norm_num) hdiag (base R)
    ActualStageProvider.paperP1 ActualStageProvider.paperG1
    ActualStageProvider.paperCg hperim
    (P0 := ActualStageProvider.paperP0)
    (khat := ActualStageProvider.paperKhat)
  refine ⟨{
    radius_nonnegative := ?_
    local_speed_positive := ?_
    target_speed := ?_
    acceleration_nonnegative := ?_
    rho_positive := ?_
    rho_half := ?_
    acceleration_radius := ?_
    chord_nonnegative := ?_
    chord_speed := ?_
    chord_margin := ?_
    upper_speed := ?_ }⟩
  all_goals
    first
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.radius_nonnegative
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.local_speed_positive
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.target_speed
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.acceleration_nonnegative
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.rho_positive
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.rho_half
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.acceleration_radius
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.chord_nonnegative
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.chord_speed
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.chord_margin
    | simpa [rho, upper, RecostClosingOutput.radius,
        RecostClosingOutput.data, RecostClosingOutput.totalShift, Dpre,
        ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
        ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
        ConfiguredBaseProfiledEdgeSourceFamily.data,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        outputRadius, outputRho, outputUpper,
        ConstructedRowDefectLargeSeparation.rowRhoVariable,
        ConfiguredInductiveTubeBudget.chordBase,
        ConfiguredInductiveTubeBudget.chordCoeff,
        ConfiguredInductiveTubeBudget.accBound, Nat.add_assoc]
        using B.upper_speed

/-- Canonical callback-free final row budget. -/
noncomputable def rowBudget (R : RecostClosingOutput J O) : BudgetType R :=
  Classical.choice (exists_rowBudget R)

/-- Every finite row prefix is bounded by the radius selected at closing. -/
theorem error_partialSum_le_radius
    (R : RecostClosingOutput J O) (n k : ℕ) :
    (∑ j ∈ Finset.range k, R.error n j) ≤ R.radius n := by
  have H := (R.error_summable n).sum_le_tsum (Finset.range k)
    (fun j _ ↦ R.error_nonnegative n j)
  exact H.trans_eq (by
    simp [RecostClosingOutput.radius, RecostClosingOutput.error,
      rowRadius, rowError, ShadowingTails.tail, shiftSequence,
      Nat.add_assoc])

/-- Successor form used verbatim by the outer induction. -/
theorem error_prefix_add_step_le_radius
    (R : RecostClosingOutput J O) (n k : ℕ) :
    (∑ j ∈ Finset.range k, R.error n j) + R.error n k ≤
      R.radius n := by
  rw [← Finset.sum_range_succ]
  exact error_partialSum_le_radius R n (k + 1)

end ConfiguredRecursiveEdgeRecostMultiplierRowBudget
