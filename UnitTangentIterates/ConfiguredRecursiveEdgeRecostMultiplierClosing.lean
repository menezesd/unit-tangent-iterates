import UnitTangentIterates.ConfiguredRecursiveEdgeFullRecostMetricDiagonal
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostScaledPaperCapstone

/-! # Final multiplier-aware recost closing shift -/

noncomputable section

open Filter Real

namespace ConfiguredRecursiveEdgeRecostMultiplierClosing

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeFullRecostMetricDiagonal
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeRecostScaledPaperCapstone
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation

abbrev GaugeOutput
    (J : RowJetScalarOutput choice.MA0 choice.NA0) :=
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output J distortionTotal
    (configuredSourceMassTarget distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2)

/-- First select the actual multiplier-mass tail on `O.data`, then select the
large-separation tail for the updated multiplier diagonal. -/
structure RecostClosingOutput
    (J : RowJetScalarOutput choice.MA0 choice.NA0) (O : GaugeOutput J) where
  preShift : ℕ
  large : ExponentialDiagonalLargeSeparation.Output
    (shift O.data preShift) (fun _ ↦ 1)
    (shiftSequence
      (fullRecostMetricDiagonal O.data choice.MA0 choice.NA0
        distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        J.scalar.Mend) preShift)
    J.scalar.Cw
  mass_curvature : ∀ q,
    multiplierRecostSourceAllowance O.data distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 (preShift + large.N + q) ≤
        configuredCurvatureSourceMassBudget
  mass_small : ∀ q,
    multiplierRecostSourceAllowance O.data distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 (preShift + large.N + q) ≤ 1

namespace RecostClosingOutput

variable {J : RowJetScalarOutput choice.MA0 choice.NA0} {O : GaugeOutput J}

/-- Total shift measured from the row-jet capstone root. -/
def totalShift (R : RecostClosingOutput J O) : ℕ :=
  O.N + R.preShift + R.large.N

/-- Final scalar data after gauge, multiplier-mass, and exponential tails. -/
def data (R : RecostClosingOutput J O) :
    ConstructedConfiguredSequenceWeighted.Data :=
  shift (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data J) R.totalShift

@[simp] theorem data_eq_shift_capstoneData (R : RecostClosingOutput J O) :
    R.data = shift (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data J)
      R.totalShift := by
  rfl

/-- Final cell error on the updated public diagonal. -/
def error (R : RecostClosingOutput J O) (n k : ℕ) : ℝ :=
  shiftSequence
    (shiftSequence
      (fullRecostMetricDiagonal O.data choice.MA0 choice.NA0
        distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        J.scalar.Mend) R.preShift)
    R.large.N (n + k)

/-- Public row-jet index represented by cell `(n,k)`. -/
def publicIndex (R : RecostClosingOutput J O) (n k : ℕ) : ℕ :=
  R.totalShift + n + k

theorem error_eq_multiplierDiagonal
    (R : RecostClosingOutput J O) (n k : ℕ) :
    R.error n k =
      fullRecostMetricDiagonal O.data choice.MA0 choice.NA0
        distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        J.scalar.Mend (R.preShift + R.large.N + n + k) := by
  simp [error, shiftSequence, Nat.add_assoc]

/-- The local multiplier source allowance is one of the summands paid by the
public cell error.  The statement is indexed on the final shifted data, so
downstream recursive steps need no further prefix arithmetic. -/
theorem multiplierRecostSourceAllowance_le_error
    (R : RecostClosingOutput J O) (n k : ℕ) :
    multiplierRecostSourceAllowance R.data distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 (n + k) ≤ R.error n k := by
  rw [R.error_eq_multiplierDiagonal]
  have hshift :
      multiplierRecostSourceAllowance R.data distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2 (n + k) =
        multiplierRecostSourceAllowance O.data distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2
            (R.preShift + R.large.N + n + k) := by
    simp only [data, ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
      ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data]
    rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
    rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
    rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
    rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
    simp [totalShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hshift]
  exact
    ConfiguredRecursiveEdgeFullRecostMetricDiagonal.multiplierRecostSourceAllowance_le_fullRecostMetricDiagonal
      O.data choice.MA0 choice.NA0 distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 J.scalar.Mend
      (R.preShift + R.large.N + n + k)

/-- The configured curvature source-mass budget on the final shifted data. -/
theorem mass_curvature_final
    (R : RecostClosingOutput J O) (q : ℕ) :
    multiplierRecostSourceAllowance R.data distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 q ≤
        configuredCurvatureSourceMassBudget := by
  have hshift :
      multiplierRecostSourceAllowance R.data distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2 q =
        multiplierRecostSourceAllowance O.data distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2
            (R.preShift + R.large.N + q) := by
    simp only [data, ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
      ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data]
    rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
    rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
    rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
    rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
    simp [totalShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hshift]
  exact R.mass_curvature q

theorem error_nonnegative (R : RecostClosingOutput J O) :
    ∀ n k, 0 ≤ R.error n k := by
  intro n k
  rw [R.error_eq_multiplierDiagonal]
  exact fullRecostMetricDiagonal_nonnegative O.data _

theorem error_summable (R : RecostClosingOutput J O) :
    ∀ n, Summable (R.error n) := by
  intro n
  have H := fullRecostMetricDiagonal_summable O.data
    (E0 := distortionTotal) (C0 := physicalTransitionCeilings.C0)
    (C1 := physicalTransitionCeilings.C1)
    (C2 := physicalTransitionCeilings.C2)
    choice.MA0_nonnegative choice.NA0_nonnegative J.scalar.Mend_positive.le
  exact ShadowingTails.summable_shift
    (ShadowingTails.summable_shift H R.preShift) (R.large.N + n) |>.congr
      (fun k ↦ by simp [error, shiftSequence, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm])

/-- Radius of the final multiplier diagonal. -/
def radius (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  rowRadius (shiftSequence (fun _ ↦ 1) R.large.N)
    (shiftSequence (shiftSequence
      (fullRecostMetricDiagonal O.data choice.MA0 choice.NA0
        distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        J.scalar.Mend) R.preShift) R.large.N) n

theorem radius_nonnegative (R : RecostClosingOutput J O) (n : ℕ) :
    0 ≤ R.radius n := by
  unfold radius rowRadius rowError
  apply mul_nonneg
  · simp [shiftSequence]
  · apply ShadowingTails.tail_nonneg
    intro k
    exact fullRecostMetricDiagonal_nonnegative O.data _

theorem data_Hs_zero (R : RecostClosingOutput J O) :
    R.data.Hs 0 = (shift (shift O.data R.preShift) R.large.N).Hs 0 := by
  simp [data, totalShift,
    ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
    ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
    Nat.add_assoc]

theorem speed_tail (R : RecostClosingOutput J O) (n : ℕ) :
    R.radius n ≤ R.data.Hs 0 := by
  rw [R.data_Hs_zero]
  simpa [radius, data, PullbackTubeTailBudget.radius,
    ShadowingTails.tail, rowRadius, rowError, shiftSequence, Nat.add_assoc]
    using R.large.speed_tail n

theorem width_gap (R : RecostClosingOutput J O) :
    J.scalar.Cw + 2 * R.radius 0 <
      (2 * R.data.Hs 0 - R.radius 0) / Real.pi := by
  rw [R.data_Hs_zero]
  simpa [radius, data, PullbackTubeTailBudget.radius,
    ShadowingTails.tail, rowRadius, rowError, shiftSequence, Nat.add_assoc]
    using R.large.width_gap

theorem radius_small (R : RecostClosingOutput J O) (n : ℕ) :
    R.radius n < 1 / 10 := by
  simpa [RecostClosingOutput.radius, RecostClosingOutput.data,
    PullbackTubeTailBudget.radius, ShadowingTails.tail,
    rowRadius, rowError, shiftSequence, Nat.add_assoc] using
    R.large.radius_small n

theorem separation_one (R : RecostClosingOutput J O) :
    1 ≤ R.data.Hs 0 := by
  rw [R.data_Hs_zero]
  exact R.large.separation_one

end RecostClosingOutput

/-- Callback-free existence of the multiplier-aware closing output. -/
theorem exists_recostClosingOutput
    (J : RowJetScalarOutput choice.MA0 choice.NA0) (O : GaugeOutput J) :
    Nonempty (RecostClosingOutput J O) := by
  obtain ⟨N, hN⟩ := exists_multiplierRecostSourceAllowance_tail_le O.data
    (ε := configuredCurvatureSourceMassBudget)
    (E0 := distortionTotal) (C0 := physicalTransitionCeilings.C0)
    (C1 := physicalTransitionCeilings.C1)
    (C2 := physicalTransitionCeilings.C2)
    configuredCurvatureSourceMassBudget_positive
    choice.MA0_nonnegative choice.NA0_nonnegative J.scalar.Mend_positive.le
  obtain ⟨L⟩ := exists_fullRecostMetricOutputAfter O.data N
    (E0 := distortionTotal) (C0 := physicalTransitionCeilings.C0)
    (C1 := physicalTransitionCeilings.C1)
    (C2 := physicalTransitionCeilings.C2)
    choice.MA0_nonnegative choice.NA0_nonnegative J.scalar.Mend_positive.le
    J.scalar.Cw_nonnegative
  exact ⟨{
    preShift := N
    large := L
    mass_curvature := fun q ↦ hN (N + L.N + q) (by omega)
    mass_small := fun q ↦
      (hN (N + L.N + q) (by omega)).trans
        configuredCurvatureSourceMassBudget_le_one }
  ⟩

end ConfiguredRecursiveEdgeRecostMultiplierClosing
