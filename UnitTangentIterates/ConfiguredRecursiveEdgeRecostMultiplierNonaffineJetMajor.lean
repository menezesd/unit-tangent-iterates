import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds
import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant

/-! # Configured major for nonaffine chosen-flow jets -/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierNonaffineJetMajor

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveSourceP0RowJetTail
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

variable {MA NA Etotal Dtarget : ℝ}
  {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {p q a b : Data} {Gamma : NormalPath p q}
  {P0 khat Qmax : ℝ}
  {A : MarkingAwareSource Gamma P0 sourceKh khat Qmax}
  {E : Applied Gamma A}

/-- The configured row coefficient dominates the floor-one nonaffine chosen
jet error, provided the truthful recursive source-mass estimate is retained. -/
theorem floorJetLinear_mul_sourceMass_le_major
    (O : Output J Etotal Dtarget) (j : ℕ)
    (hperiod : rearPeriod A 0 ≤ ellCap O.data (j + 1))
    (hmass : sourceMass A ≤
      Dtarget * scaledSuccessorPhysicalDefect O.data j) :
    floorJetLinearConst A 1 J.scalar.Mend * sourceMass A ≤ O.major j := by
  have hcoeff : floorJetLinearConst A 1 J.scalar.Mend ≤
      rowJetCoeff O.data J.scalar.Mend (j + 1) := by
    have H := jetLinearConst_le_rowJetCoeff O.data J.scalar.Mend (j + 1)
      (ell := rearPeriod A 0) (L := 1)
      (A.rear_period_pos 0).le hperiod (by norm_num)
    simpa [floorJetLinearConst] using H
  have hrow : 0 ≤ rowJetCoeff O.data J.scalar.Mend (j + 1) :=
    (rowJetCoeffEnvelope O.data J.scalar.Mend).value_nonneg (j + 1)
  calc
    floorJetLinearConst A 1 J.scalar.Mend * sourceMass A ≤
        rowJetCoeff O.data J.scalar.Mend (j + 1) *
          (Dtarget * scaledSuccessorPhysicalDefect O.data j) :=
      mul_le_mul hcoeff hmass (sourceMass_nonnegative A) hrow
    _ = gaugeMajor O.data J.scalar.Mend Dtarget j := by
      simp [gaugeMajor, compositionRowEps]
      ring
    _ ≤ O.major j := by
      rw [Output.major, combinedGaugeMajor]
      exact le_add_of_nonneg_left
        (baseGaugeMajor_nonnegative O.data J.scalar.Mend j)

/-- Callback-free nonaffine chosen jets, enlarged directly to the configured
major. -/
def normalizedJetBounds_major
    (O : Output J Etotal Dtarget) (j : ℕ)
    (W : ChosenPath Gamma A E.Phi a b)
    (hfloor : ∀ t, 1 ≤ rearPeriod A t)
    (hunit : Gamma.T = 1)
    (hmass_one : sourceMass A ≤ 1)
    (hperiod : rearPeriod A 0 ≤ ellCap O.data (j + 1))
    (hmass : sourceMass A ≤
      Dtarget * scaledSuccessorPhysicalDefect O.data j) :
    NormalizedJetBounds W (O.major j) :=
  normalizedJetBounds_mono
    (normalizedJetBounds_linear_one W hfloor hunit
      (hmass_one.trans J.one_le_Mend))
    (floorJetLinear_mul_sourceMass_le_major O j hperiod hmass)

theorem major_le_quarter
    (O : Output J Etotal Dtarget) (j : ℕ)
    (hE : Etotal ≤ 1 / 8) : O.major j ≤ 1 / 4 := by
  have hterm : O.major j ≤ ∑' i, O.major i :=
    O.major_summable'.le_tsum j (fun i _ ↦ O.major_nonnegative' i)
  have H := hterm.trans (O.major_tsum_le'.trans hE)
  linarith

end ConfiguredRecursiveEdgeRecostMultiplierNonaffineJetMajor
