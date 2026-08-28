import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass

/-! # Combined base and successor gauge-error majorant -/

noncomputable section

open Function PathMetric

namespace ConfiguredRecursiveEdgeFiniteColumnCombinedGaugeMajorant

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePhysicalFiniteColumnBase
  ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveSourceP0RowJetTail
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ConstructedRowCPolynomialGrowth
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

/-- The depth-zero chosen-gauge error, charged to the composition-scaled
physical source mass at the successor row. -/
def baseGaugeMajor (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (j : ℕ) : ℝ :=
  rowJetCoeff D M (j + 1) * edgeCompositionPhysicalDefect D (j + 1)

/-- One summable sequence dominating both the depth-zero physical source and
all later successor-source gauge errors. -/
def combinedGaugeMajor (D : ConstructedConfiguredSequenceWeighted.Data)
    (M Dtarget : ℝ) (j : ℕ) : ℝ :=
  baseGaugeMajor D M j + gaugeMajor D M Dtarget j

theorem baseGaugeMajor_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (j : ℕ) :
    0 ≤ baseGaugeMajor D M j :=
  mul_nonneg (rowJetCoeff_nonnegative D M (j + 1))
    (edgeCompositionPhysicalDefect_nonnegative D (j + 1))

theorem combinedGaugeMajor_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M Dtarget : ℝ) (hDtarget : 0 ≤ Dtarget) (j : ℕ) :
    0 ≤ combinedGaugeMajor D M Dtarget j :=
  add_nonneg (baseGaugeMajor_nonnegative D M j)
    (gaugeMajor_nonnegative D M Dtarget hDtarget j)

theorem baseGaugeMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    Summable (baseGaugeMajor D M) := by
  let hjet := rowJetCoeffEnvelope D M
  let hcomposition := edgeCompositionPhysicalCoeffEnvelope D
  let hproduct : PolynomialEnvelope D.Hs (fun j ↦
      rowJetCoeff D M j * edgeCompositionPhysicalCoeff D j) :=
    { coeff := hjet.coeff * hcomposition.coeff
      degree := hjet.degree + hcomposition.degree
      coeff_nonneg := mul_nonneg hjet.coeff_nonneg hcomposition.coeff_nonneg
      value_nonneg := fun j ↦
        mul_nonneg (hjet.value_nonneg j) (hcomposition.value_nonneg j)
      bound := fun j ↦ by
        calc
          rowJetCoeff D M j * edgeCompositionPhysicalCoeff D j ≤
              (hjet.coeff * (1 + D.Hs j) ^ hjet.degree) *
                (hcomposition.coeff * (1 + D.Hs j) ^ hcomposition.degree) :=
            mul_le_mul (hjet.bound j) (hcomposition.bound j)
              (hcomposition.value_nonneg j)
              (mul_nonneg hjet.coeff_nonneg
                (pow_nonneg (by linarith [D.model.separation_pos j]) _))
          _ = (hjet.coeff * hcomposition.coeff) *
              (1 + D.Hs j) ^ (hjet.degree + hcomposition.degree) := by
            rw [pow_add]
            ring }
  have hsum : Summable (fun j ↦
      rowJetCoeff D M j * edgeCompositionPhysicalDefect D j) := by
    simpa [edgeCompositionPhysicalDefect, mul_assoc] using
      (summable_polynomial_mul_rowDefect D hproduct)
  simpa [baseGaugeMajor, Nat.add_comm] using
    hsum.comp_injective (add_left_injective 1)

theorem combinedGaugeMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) (M Dtarget : ℝ) :
    Summable (combinedGaugeMajor D M Dtarget) :=
  (baseGaugeMajor_summable D M).add (gaugeMajor_summable D M Dtarget)

theorem baseGaugeMajor_shift
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (N j : ℕ) :
    baseGaugeMajor (shift D N) M j = baseGaugeMajor D M (N + j) := by
  unfold baseGaugeMajor
  rw [edgeCompositionPhysicalDefect_shift]
  simp [rowJetCoeff, ellCap, shift, Nat.add_assoc]

theorem combinedGaugeMajor_shift
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M Dtarget : ℝ) (N j : ℕ) :
    combinedGaugeMajor (shift D N) M Dtarget j =
      combinedGaugeMajor D M Dtarget (N + j) := by
  unfold combinedGaugeMajor gaugeMajor
  rw [baseGaugeMajor_shift,
    ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.compositionRowEps_shift]
  congr 1
  simp [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.compositionRowEps,
    Nat.add_assoc, Nat.add_comm]

theorem chosenJetLinear_mul_sourceMass_le_baseGaugeMajor
    {p q : MarkedSpace.Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (j : ℕ)
    (hkh : kh = sourceKh)
    (hperiod : FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A 0 ≤
      ellCap D (j + 1))
    (hfloor : 1 ≤
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.rearPeriodFloor P0 kh)
    (hmass : sourceMass A ≤ edgeCompositionPhysicalDefect D (j + 1)) :
    chosenJetLinearConst A M * sourceMass A ≤ baseGaugeMajor D M j := by
  have hcoeff : chosenJetLinearConst A M ≤ rowJetCoeff D M (j + 1) := by
    simpa [chosenJetLinearConst, hkh, sourceKh_eq] using
      (jetLinearConst_le_rowJetCoeff D M (j + 1)
        (A.rear_period_pos 0).le hperiod hfloor)
  exact mul_le_mul hcoeff hmass (sourceMass_nonnegative A)
    (rowJetCoeff_nonnegative D M (j + 1))

variable {MA NA : ℝ}

/-- The depth-zero configured source is dominated by the base summand of the
combined majorant; no comparison with the smaller physical defect is used. -/
theorem configuredBaseError_le
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ)
    (hperiod : FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
        ((column J (K0 := K0) (K1 := K1) (K2 := K2)).source n) 0 ≤
      ellCap (D J.scalar) (n + 1))
    (hfloor : 1 ≤
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.rearPeriodFloor
        (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (D J.scalar) n) sourceKh) :
    chosenJetLinearConst
        ((column J (K0 := K0) (K1 := K1) (K2 := K2)).source n)
        J.scalar.Mend *
      sourceMass ((column J (K0 := K0) (K1 := K1) (K2 := K2)).source n) ≤
        baseGaugeMajor (D J.scalar) J.scalar.Mend n :=
  chosenJetLinear_mul_sourceMass_le_baseGaugeMajor
    (D J.scalar) J.scalar.Mend n rfl hperiod hfloor
    (sourceMass_le_compositionPhysicalDefect J
      (K0 := K0) (K1 := K1) (K2 := K2) n)

end ConfiguredRecursiveEdgeFiniteColumnCombinedGaugeMajorant
