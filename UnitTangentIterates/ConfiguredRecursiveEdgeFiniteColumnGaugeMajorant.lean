import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0RowJetTail
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
import UnitTangentIterates.NearIdentityDistortionBudgetMajorant

/-!
# Configured all-time gauge majorants for finite columns

The finite-column recurrence uses the genuine all-time gauge error
`chosenJetLinearConst * sourceMass`.  The configured row-jet polynomial is
used only after an explicit coefficient comparison.  A further common tail
shift makes the resulting stable-component-scaled majorant summable, bounded
termwise by `1/2`, and of total mass at most the prescribed distortion total.
-/

noncomputable section

open Filter MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant

open AnchoredJacobiStableTransition
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0RowJetTail
  ConstructedRowCPolynomialGrowth
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

/-- The depth-uniform physical-component multiplier determined before the
finite-column induction. -/
def D0 (E0 C0 C1 C2 : ℝ) : ℝ :=
  stableConst (2 * E0) E0 E0 C0 C1 C2

theorem D0_nonnegative (E0 C0 C1 C2 : ℝ) :
    0 ≤ D0 E0 C0 C1 C2 :=
  JacobiControlledJunctionComponents.stableConst_nonnegative
    (2 * E0) E0 E0 C0 C1 C2

/-- The exact recursive mass defect: composition scaling multiplies the
physical source defect rather than adding its coefficient. -/
def scaledSuccessorPhysicalDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) : ℝ :=
  edgeCompositionCoeff D j * edgePhysicalDefect D j

theorem scaledSuccessorPhysicalDefect_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    0 ≤ scaledSuccessorPhysicalDefect D j :=
  mul_nonneg ((edgeCompositionCoeffEnvelope D).value_nonneg j)
    (edgePhysicalDefect_nonnegative D j)

theorem scaledSuccessorPhysicalDefect_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (N j : ℕ) :
    scaledSuccessorPhysicalDefect (shift D N) j =
      scaledSuccessorPhysicalDefect D (N + j) := by
  unfold scaledSuccessorPhysicalDefect
  rw [edgeCompositionCoeff_shift]
  unfold edgePhysicalDefect physicalDefect physicalCoeff
  rw [show ConfiguredApproximateDefectPathRowwise.rowDefect (shift D N) j =
    ConfiguredApproximateDefectPathRowwise.rowDefect D (N + j) from rfl]
  rfl

def scaledSuccessorPhysicalCoeffEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (fun j ↦
      edgeCompositionCoeff D j * physicalCoeff D j) := by
  let hc := edgeCompositionCoeffEnvelope D
  let hp := physicalCoeffEnvelope D
  exact
    { coeff := hc.coeff * hp.coeff
      degree := hc.degree + hp.degree
      coeff_nonneg := mul_nonneg hc.coeff_nonneg hp.coeff_nonneg
      value_nonneg := fun j ↦ mul_nonneg (hc.value_nonneg j) (hp.value_nonneg j)
      bound := fun j ↦ by
        calc
          edgeCompositionCoeff D j * physicalCoeff D j ≤
              (hc.coeff * (1 + D.Hs j) ^ hc.degree) *
                (hp.coeff * (1 + D.Hs j) ^ hp.degree) :=
            mul_le_mul (hc.bound j) (hp.bound j) (hp.value_nonneg j)
              (mul_nonneg hc.coeff_nonneg
                (pow_nonneg (by linarith [D.model.separation_pos j]) _))
          _ = (hc.coeff * hp.coeff) *
              (1 + D.Hs j) ^ (hc.degree + hp.degree) := by
            rw [pow_add]
            ring }

theorem scaledSuccessorPhysicalDefect_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    Summable (scaledSuccessorPhysicalDefect D) := by
  simpa [scaledSuccessorPhysicalDefect, edgePhysicalDefect, physicalDefect,
    mul_assoc] using
    (summable_polynomial_mul_rowDefect D
      (scaledSuccessorPhysicalCoeffEnvelope D))

/-- Row-jet amplification of the scaled successor source defect. -/
def compositionRowEps (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (n k : ℕ) : ℝ :=
  rowJetCoeff D M (n + k + 1) *
    scaledSuccessorPhysicalDefect D (n + k)

theorem compositionRowEps_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n k : ℕ) :
    0 ≤ compositionRowEps D M n k :=
  mul_nonneg (rowJetCoeff_nonnegative D M (n + k + 1))
    (scaledSuccessorPhysicalDefect_nonnegative D (n + k))

theorem compositionRowEps_shift
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (N n k : ℕ) :
    compositionRowEps (shift D N) M n k =
      compositionRowEps D M (N + n) k := by
  unfold compositionRowEps
  rw [scaledSuccessorPhysicalDefect_shift]
  simp [rowJetCoeff, ellCap, shift, Nat.add_assoc]

/-- Configured scalar majorant for the actual all-time chosen gauge error. -/
def gaugeMajor (D : ConstructedConfiguredSequenceWeighted.Data) (M D0 : ℝ)
    (j : ℕ) : ℝ :=
  D0 * compositionRowEps D M 0 j

theorem gaugeMajor_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M D0 : ℝ)
    (hD0 : 0 ≤ D0) (j : ℕ) :
    0 ≤ gaugeMajor D M D0 j :=
  mul_nonneg hD0 (compositionRowEps_nonnegative D M 0 j)

theorem gaugeMajor_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (M D0 : ℝ)
    (N j : ℕ) :
    gaugeMajor (shift D N) M D0 j = gaugeMajor D M D0 (N + j) := by
  unfold gaugeMajor
  rw [compositionRowEps_shift]
  simp [compositionRowEps, Nat.add_assoc]

/-- The successor-indexed row-jet coefficient is still polynomial, hence its
product with the composition-scaled physical defect is summable. -/
theorem summable_compositionRowEps_zero
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    Summable (compositionRowEps D M 0) := by
  let hjet := nextEnvelope D (rowJetCoeffEnvelope D M)
  let hphysical := scaledSuccessorPhysicalCoeffEnvelope D
  have hcoeff : PolynomialEnvelope D.Hs (fun j ↦
      rowJetCoeff D M (j + 1) *
        (edgeCompositionCoeff D j * physicalCoeff D j)) :=
    { coeff := hjet.coeff * hphysical.coeff
      degree := hjet.degree + hphysical.degree
      coeff_nonneg := mul_nonneg hjet.coeff_nonneg hphysical.coeff_nonneg
      value_nonneg := fun j ↦ mul_nonneg (hjet.value_nonneg j)
        (hphysical.value_nonneg j)
      bound := fun j ↦ by
        calc
          rowJetCoeff D M (j + 1) *
              (edgeCompositionCoeff D j * physicalCoeff D j) ≤
              (hjet.coeff * (1 + D.Hs j) ^ hjet.degree) *
                (hphysical.coeff * (1 + D.Hs j) ^ hphysical.degree) := by
            exact mul_le_mul (hjet.bound j) (hphysical.bound j)
              (hphysical.value_nonneg j)
              (mul_nonneg hjet.coeff_nonneg
                (pow_nonneg (by linarith [D.model.separation_pos j]) _))
          _ = (hjet.coeff * hphysical.coeff) *
              (1 + D.Hs j) ^ (hjet.degree + hphysical.degree) := by
            rw [pow_add]
            ring }
  have H := summable_polynomial_mul_rowDefect D hcoeff
  refine H.congr ?_
  intro j
  simp [compositionRowEps, scaledSuccessorPhysicalDefect,
    edgePhysicalDefect, physicalDefect]
  ring

theorem gaugeMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) (M D0 : ℝ) :
    Summable (gaugeMajor D M D0) := by
  simpa [gaugeMajor] using
    (summable_compositionRowEps_zero D M).mul_left D0

variable {MA NA : ℝ}

/-- The depth-zero physical source is scaled by the composition coefficient,
so its chosen-gauge error requires a separate successor-indexed summand. -/
def baseGaugeMajor (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (j : ℕ) : ℝ :=
  rowJetCoeff D M (j + 1) * edgeCompositionPhysicalDefect D (j + 1)

/-- A single summable majorant for the depth-zero physical source and every
later recursively produced source. -/
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
  unfold combinedGaugeMajor
  rw [baseGaugeMajor_shift, gaugeMajor_shift]

structure Output
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (Etotal Dtarget : ℝ) where
  N : ℕ
  major_nonnegative : ∀ j, 0 ≤ combinedGaugeMajor
    (shift (shift J.scalar.E.data J.scalar.large.N) N)
    J.scalar.Mend Dtarget j
  major_summable : Summable (combinedGaugeMajor
    (shift (shift J.scalar.E.data J.scalar.large.N) N)
    J.scalar.Mend Dtarget)
  major_half : ∀ j, combinedGaugeMajor
    (shift (shift J.scalar.E.data J.scalar.large.N) N)
    J.scalar.Mend Dtarget j ≤ 1 / 2
  major_tsum_le : (∑' j, combinedGaugeMajor
    (shift (shift J.scalar.E.data J.scalar.large.N) N)
    J.scalar.Mend Dtarget j) ≤ Etotal

namespace Output

variable
  {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {Etotal Dtarget : ℝ}

def data (O : Output J Etotal Dtarget) :
    ConstructedConfiguredSequenceWeighted.Data :=
  shift (shift J.scalar.E.data J.scalar.large.N) O.N

def major (O : Output J Etotal Dtarget) : ℕ → ℝ :=
  combinedGaugeMajor O.data J.scalar.Mend Dtarget

theorem major_nonnegative' (O : Output J Etotal Dtarget) :
    ∀ j, 0 ≤ O.major j := O.major_nonnegative

theorem major_summable' (O : Output J Etotal Dtarget) :
    Summable O.major := O.major_summable

theorem major_half' (O : Output J Etotal Dtarget) :
    ∀ j, O.major j ≤ 1 / 2 := O.major_half

theorem major_tsum_le' (O : Output J Etotal Dtarget) :
    (∑' j, O.major j) ≤ Etotal := O.major_tsum_le

/-- Feed any nonnegative concrete gauge errors dominated by the configured
majorant directly into the near-identity distortion recurrence. -/
def budgetOfMajorant (O : Output J Etotal Dtarget)
    {eps : ℕ → ℝ} (heps : ∀ j, 0 ≤ eps j)
    (hle : ∀ j, eps j ≤ O.major j) :
    DistortionBudget
      (NearIdentityDistortionBudget.invLower eps)
      (NearIdentityDistortionBudget.upper eps) eps
      (2 * Etotal) Etotal Etotal :=
  NearIdentityDistortionBudgetMajorant.budgetOfMajorant
    heps O.major_half' O.major_summable' O.major_tsum_le' hle

end Output

theorem exists_output
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {Etotal Dtarget : ℝ}
    (hEtotal : 0 < Etotal) (hDtarget : 0 ≤ Dtarget) :
    Nonempty (Output J Etotal Dtarget) := by
  let D := shift J.scalar.E.data J.scalar.large.N
  let S := Dtarget
  let f := combinedGaugeMajor D J.scalar.Mend S
  have hS : 0 ≤ S := hDtarget
  have hf0 : ∀ j, 0 ≤ f j :=
    combinedGaugeMajor_nonnegative D J.scalar.Mend S hS
  have hfs : Summable f := combinedGaugeMajor_summable D J.scalar.Mend S
  have hevent : ∀ᶠ N in atTop,
      ShadowingTails.tail f N < min Etotal (1 / 2) :=
    ShadowingTails.tail_tendsto_zero.eventually
      (Iio_mem_nhds (lt_min hEtotal (by norm_num)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  have htail : ShadowingTails.tail f N ≤ min Etotal (1 / 2) :=
    (hN N le_rfl).le
  have hsummable : Summable
      (combinedGaugeMajor (shift D N) J.scalar.Mend S) := by
    have H := ShadowingTails.summable_shift hfs N
    refine H.congr ?_
    intro j
    exact (combinedGaugeMajor_shift D J.scalar.Mend S N j).symm
  refine ⟨{
    N := N
    major_nonnegative := fun j ↦
      combinedGaugeMajor_nonnegative (shift D N) J.scalar.Mend S hS j
    major_summable := hsummable
    major_half := ?_
    major_tsum_le := ?_ }⟩
  · intro j
    calc
      combinedGaugeMajor (shift D N) J.scalar.Mend S j = f (N + j) :=
        combinedGaugeMajor_shift D J.scalar.Mend S N j
      _ ≤ ShadowingTails.tail f (N + j) :=
        ShadowingTails.le_tail hfs hf0 (N + j)
      _ ≤ ShadowingTails.tail f N :=
        ShadowingTails.tail_antitone hfs hf0 (Nat.le_add_right N j)
      _ ≤ min Etotal (1 / 2) := htail
      _ ≤ 1 / 2 := min_le_right _ _
  · have heq : (∑' j, combinedGaugeMajor
        (shift D N) J.scalar.Mend S j) =
        ShadowingTails.tail f N := by
      unfold ShadowingTails.tail
      apply tsum_congr
      intro j
      exact combinedGaugeMajor_shift D J.scalar.Mend S N j
    rw [heq]
    exact htail.trans (min_le_left _ _)

/-- Explicit comparison with the genuine all-time chosen error.  The two
geometric hypotheses are exactly what justifies reuse of the configured
row-jet polynomial: the source period is below its row ceiling and the
normalized rear-period floor is at least one. -/
theorem chosenJetLinear_mul_sourceMass_le_major
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {Etotal Dtarget : ℝ}
    (O : Output J Etotal Dtarget) (j : ℕ)
    (hkh : kh = sourceKh)
    (hperiod : FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A 0 ≤
      ellCap O.data (j + 1))
    (hfloor : 1 ≤ rearPeriodFloor P0 kh)
    (hmass : sourceMass A ≤
      Dtarget * scaledSuccessorPhysicalDefect O.data j) :
    chosenJetLinearConst A J.scalar.Mend * sourceMass A ≤ O.major j := by
  have hcoeff : chosenJetLinearConst A J.scalar.Mend ≤
      rowJetCoeff O.data J.scalar.Mend (j + 1) := by
    have H := jetLinearConst_le_rowJetCoeff O.data J.scalar.Mend (j + 1)
      (A.rear_period_pos 0).le hperiod (by simpa [hkh] using hfloor)
    simpa [chosenJetLinearConst, hkh] using H
  have hrow : 0 ≤ rowJetCoeff O.data J.scalar.Mend (j + 1) :=
    (rowJetCoeffEnvelope O.data J.scalar.Mend).value_nonneg (j + 1)
  calc
    chosenJetLinearConst A J.scalar.Mend * sourceMass A ≤
        rowJetCoeff O.data J.scalar.Mend (j + 1) *
          (Dtarget * scaledSuccessorPhysicalDefect O.data j) :=
      mul_le_mul hcoeff hmass
        (FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.sourceMass_nonnegative A)
        hrow
    _ = gaugeMajor O.data J.scalar.Mend Dtarget j := by
      simp [gaugeMajor, compositionRowEps]
      ring
    _ ≤ O.major j := by
      rw [Output.major, combinedGaugeMajor]
      exact le_add_of_nonneg_left
        (baseGaugeMajor_nonnegative O.data J.scalar.Mend j)

/-- Base-source analogue of `chosenJetLinear_mul_sourceMass_le_major`.
It uses the composition defect directly, before the recursive mass multiplier
is introduced. -/
theorem chosenJetLinear_mul_compositionSourceMass_le_major
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {Etotal Dtarget : ℝ}
    (O : Output J Etotal Dtarget) (j : ℕ)
    (hDtarget : 0 ≤ Dtarget)
    (hkh : kh = sourceKh)
    (hperiod : FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A 0 ≤
      ellCap O.data (j + 1))
    (hfloor : 1 ≤ rearPeriodFloor P0 kh)
    (hmass : sourceMass A ≤ edgeCompositionPhysicalDefect O.data (j + 1)) :
    chosenJetLinearConst A J.scalar.Mend * sourceMass A ≤ O.major j := by
  have hcoeff : chosenJetLinearConst A J.scalar.Mend ≤
      rowJetCoeff O.data J.scalar.Mend (j + 1) := by
    have H := jetLinearConst_le_rowJetCoeff O.data J.scalar.Mend (j + 1)
      (A.rear_period_pos 0).le hperiod (by simpa [hkh] using hfloor)
    simpa [chosenJetLinearConst, hkh] using H
  have hrow : 0 ≤ rowJetCoeff O.data J.scalar.Mend (j + 1) :=
    rowJetCoeff_nonnegative O.data J.scalar.Mend (j + 1)
  calc
    chosenJetLinearConst A J.scalar.Mend * sourceMass A ≤
        rowJetCoeff O.data J.scalar.Mend (j + 1) *
          edgeCompositionPhysicalDefect O.data (j + 1) :=
      mul_le_mul hcoeff hmass
        (FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.sourceMass_nonnegative A)
        hrow
    _ = baseGaugeMajor O.data J.scalar.Mend j := rfl
    _ ≤ O.major j := by
      rw [Output.major, combinedGaugeMajor]
      exact le_add_of_nonneg_right
        (gaugeMajor_nonnegative O.data J.scalar.Mend Dtarget hDtarget j)

/-! ## Depthwise raw-source gauge majorants

The recursive source produced by the scaled successor is charged to the
actual next-column error, not to a depth-independent recost target.  For a
fixed spatial row `n`, the row-jet and composition coefficients are fixed,
while the diagonal is shifted by the recursive depth. -/

/-- Exact gauge majorant for a raw scaled-successor source at row `n` and
depth `k + 1`.  If the column error is `e n k = diagonal (n + k)`, then the
mass estimate uses `e (n + 1) (k + 1) = diagonal (n + k + 2)`. -/
def depthwiseRawGaugeMajor
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ)
    (diagonal : ℕ → ℝ) (n k : ℕ) : ℝ :=
  rowJetCoeff D M (n + 1) *
    (2 * edgeCompositionCoeff D n * diagonal (n + k + 2))

theorem depthwiseRawGaugeMajor_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ)
    {diagonal : ℕ → ℝ} (hdiagonal : ∀ j, 0 ≤ diagonal j)
    (n k : ℕ) :
    0 ≤ depthwiseRawGaugeMajor D M diagonal n k := by
  exact mul_nonneg (rowJetCoeff_nonnegative D M (n + 1))
    (mul_nonneg
      (mul_nonneg (by norm_num)
        ((edgeCompositionCoeffEnvelope D).value_nonneg n))
      (hdiagonal (n + k + 2)))

/-- For each fixed spatial row, raw recursive gauge errors remain summable
across all depths whenever the scalar diagonal is summable. -/
theorem depthwiseRawGaugeMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ)
    {diagonal : ℕ → ℝ} (hdiagonal : Summable diagonal) (n : ℕ) :
    Summable (depthwiseRawGaugeMajor D M diagonal n) := by
  have hshift : Summable (fun k : ℕ ↦ diagonal (n + 2 + k)) :=
    hdiagonal.comp_injective (by
      intro a b h
      omega)
  have hmul := hshift.mul_left
    (rowJetCoeff D M (n + 1) * (2 * edgeCompositionCoeff D n))
  refine hmul.congr ?_
  intro k
  unfold depthwiseRawGaugeMajor
  rw [show n + k + 2 = n + 2 + k by omega]
  ring

/-- The exact raw mass invariant of the depthwise tower implies its genuine
all-time chosen-gauge bound.  No comparison with a recosted path is used. -/
theorem chosenJetLinear_mul_depthwiseRawSourceMass_le
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ)
    {diagonal : ℕ → ℝ} (n k : ℕ)
    (hkh : kh = sourceKh)
    (hperiod : FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A 0 ≤
      ellCap D (n + 1))
    (hfloor : 1 ≤ rearPeriodFloor P0 kh)
    (hmass : sourceMass A ≤
      2 * edgeCompositionCoeff D n * diagonal (n + k + 2)) :
    chosenJetLinearConst A M * sourceMass A ≤
      depthwiseRawGaugeMajor D M diagonal n k := by
  have hcoeff : chosenJetLinearConst A M ≤ rowJetCoeff D M (n + 1) := by
    have H := jetLinearConst_le_rowJetCoeff D M (n + 1)
      (A.rear_period_pos 0).le hperiod (by simpa [hkh] using hfloor)
    simpa [chosenJetLinearConst, hkh] using H
  exact mul_le_mul hcoeff hmass
    (FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.sourceMass_nonnegative A)
    (rowJetCoeff_nonnegative D M (n + 1))

def configuredTarget (E C0 C1 C2 : ℝ) : ℝ :=
  stableConst (8 * E) (4 * E) (4 * E) C0 C1 C2

theorem configuredTarget_nonnegative (E C0 C1 C2 : ℝ) :
    0 ≤ configuredTarget E C0 C1 C2 :=
  JacobiControlledJunctionComponents.stableConst_nonnegative
    (8 * E) (4 * E) (4 * E) C0 C1 C2

/-- The automatic successor loses at most a factor eight when its chosen
path cost is converted into the next source mass at curvature `5/6`. -/
def configuredSourceMassTarget (E C0 C1 C2 : ℝ) : ℝ :=
  8 * configuredTarget E C0 C1 C2

theorem configuredSourceMassTarget_nonnegative (E C0 C1 C2 : ℝ) :
    0 ≤ configuredSourceMassTarget E C0 C1 C2 :=
  mul_nonneg (by norm_num) (configuredTarget_nonnegative E C0 C1 C2)

theorem exists_configuredOutput
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {E C0 C1 C2 : ℝ} (hE : 0 < E) (hEsmall : E ≤ 1 / 8) :
    Nonempty (Output J E (configuredSourceMassTarget E C0 C1 C2)) := by
  exact exists_output J hE
    (configuredSourceMassTarget_nonnegative E C0 C1 C2)

end ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
