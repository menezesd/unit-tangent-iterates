import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedScaledSuccessorClosed
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0Growth

/-!
# Configured widened defect for composition-scaled finite successors

The source density is multiplied by `edgeCompositionCoeff`, so its recursive
mass belongs to the correspondingly widened physical defect.  The older
additive composition defect is not used for this purpose.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeFiniteCorrelatedScaledSuccessorMass

open ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0Growth
  ConstructedRowCPolynomialGrowth

/-- The truthful recursive mass defect after composition scaling. -/
def scaledSuccessorPhysicalDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) : ℝ :=
  edgeCompositionCoeff D j * edgePhysicalDefect D j

def scaledSuccessorPhysicalCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) : ℝ :=
  edgeCompositionCoeff D j * physicalCoeff D j

def scaledSuccessorPhysicalCoeffEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (scaledSuccessorPhysicalCoeff D) where
  coeff := (edgeCompositionCoeffEnvelope D).coeff *
    (physicalCoeffEnvelope D).coeff
  degree := (edgeCompositionCoeffEnvelope D).degree +
    (physicalCoeffEnvelope D).degree
  coeff_nonneg := mul_nonneg (edgeCompositionCoeffEnvelope D).coeff_nonneg
    (physicalCoeffEnvelope D).coeff_nonneg
  value_nonneg j := mul_nonneg
    ((edgeCompositionCoeffEnvelope D).value_nonneg j)
    ((physicalCoeffEnvelope D).value_nonneg j)
  bound j := by
    let x : ℝ := 1 + D.Hs j
    have hx0 : 0 ≤ x := by
      dsimp [x]
      linarith [(D.model.separation_pos j).le]
    have hc := (edgeCompositionCoeffEnvelope D).bound j
    have hp := (physicalCoeffEnvelope D).bound j
    calc
      scaledSuccessorPhysicalCoeff D j ≤
          ((edgeCompositionCoeffEnvelope D).coeff *
              x ^ (edgeCompositionCoeffEnvelope D).degree) *
            ((physicalCoeffEnvelope D).coeff *
              x ^ (physicalCoeffEnvelope D).degree) :=
        mul_le_mul hc hp
          ((physicalCoeffEnvelope D).value_nonneg j)
          (mul_nonneg (edgeCompositionCoeffEnvelope D).coeff_nonneg
            (pow_nonneg hx0 _))
      _ = ((edgeCompositionCoeffEnvelope D).coeff *
            (physicalCoeffEnvelope D).coeff) *
          x ^ ((edgeCompositionCoeffEnvelope D).degree +
            (physicalCoeffEnvelope D).degree) := by
        rw [pow_add]
        ring

theorem scaledSuccessorPhysicalDefect_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    0 ≤ scaledSuccessorPhysicalDefect D j :=
  mul_nonneg ((edgeCompositionCoeffEnvelope D).value_nonneg j)
    (edgePhysicalDefect_nonnegative D j)

theorem summable_scaledSuccessorPhysicalDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    Summable (scaledSuccessorPhysicalDefect D) := by
  simpa [scaledSuccessorPhysicalDefect, edgePhysicalDefect, physicalDefect,
    scaledSuccessorPhysicalCoeff, mul_assoc] using
    (summable_polynomial_mul_rowDefect D
      (scaledSuccessorPhysicalCoeffEnvelope D))

theorem scaledSuccessorPhysicalDefect_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (N j : ℕ) :
    scaledSuccessorPhysicalDefect
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N) j =
      scaledSuccessorPhysicalDefect D (N + j) := by
  unfold scaledSuccessorPhysicalDefect
  rw [edgeCompositionCoeff_shift]
  congr 1

open FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

/-- The stable-component recost bound and the configured coefficient estimate
produce the exact widened recursive mass domination. -/
def configuredRecostedMassData
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt stableTarget : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H}
    (X : PhaseScaledSuccessorBundles H B)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (hstable : 0 ≤ stableTarget)
    (hscaledCoeff0 : ∀ n, 0 ≤
      (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2))
    (hscaledCoeff : ∀ n,
      (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) ≤
        2 * edgeCompositionCoeff D n)
    (hrecost : ∀ n, (H.row (n + 1)).output.chosen.Delta.cost ≤
      4 * stableTarget * edgePhysicalDefect D n) :
    RecostedScaledSuccessorMassData
      (stableTarget := stableTarget) (rawDefect := edgePhysicalDefect D)
      (defect := scaledSuccessorPhysicalDefect D) X where
  coeffBound := edgeCompositionCoeff D
  stableTarget_nonnegative := hstable
  rawDefect_nonnegative := edgePhysicalDefect_nonnegative D
  coeffBound_nonnegative := (edgeCompositionCoeffEnvelope D).value_nonneg
  scaledCoeff_nonnegative := hscaledCoeff0
  scaledCoeff_le := hscaledCoeff
  recost_cost_le := hrecost
  coeff_rawDefect_le := fun _ ↦ le_rfl

/-- Single configured scaled step with closed geometry, iterative Ready data,
and mass bounded by `8 * stableTarget` times the widened defect. -/
noncomputable def closedConfiguredRecostedStep
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt stableTarget : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H}
    (X : PhaseScaledSuccessorBundles H B)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1)
    (hstable : 0 ≤ stableTarget)
    (hscaledCoeff0 : ∀ n, 0 ≤
      (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2))
    (hscaledCoeff : ∀ n,
      (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) ≤
        2 * edgeCompositionCoeff D n)
    (hrecost : ∀ n, (H.row (n + 1)).output.chosen.Delta.cost ≤
      4 * stableTarget * edgePhysicalDefect D n) :
    ClosedScaledSuccessorStep (target := 8 * stableTarget)
      (defect := scaledSuccessorPhysicalDefect D) H B :=
  X.closedStep hkh0 hkh1
    ((configuredRecostedMassData X D hstable hscaledCoeff0 hscaledCoeff hrecost).toMassDomination)

/-! ## Depthwise raw-cost invariant

The recursive source is built from the theorem-produced chosen path, so its
mass is controlled by the row's own diagonal cost bound.  Canonical recosting
is intentionally absent from this statement. -/

/-- Exact mass invariant for one depthwise scaled successor. -/
structure DepthwiseRawSourceMass
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H}
    (X : PhaseScaledSuccessorBundles H B)
    (D : ConstructedConfiguredSequenceWeighted.Data) : Prop where
  sourceMass_le : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (X.toScaled.nextColumn.source n) ≤
      2 * edgeCompositionCoeff D n * e (n + 1) (k + 1)

/-- A positive diagonal allowance cannot absorb the raw recursive mass
multiplier.  This is the precise obstruction to deriving the next
`RowBounds.cost_le` merely from diagonal coherence. -/
theorem diagonal_lt_rawMassMultiplier
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    {diagonal : ℝ} (hdiagonal : 0 < diagonal) :
    diagonal < 2 * edgeCompositionCoeff D n * diagonal := by
  have hcoeff : 1 ≤ edgeCompositionCoeff D n :=
    edgeCompositionCoeff_one_le D n
  calc
    diagonal < 2 * diagonal := by linarith
    _ ≤ 2 * (edgeCompositionCoeff D n * diagonal) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa using mul_le_mul_of_nonneg_right hcoeff hdiagonal.le
    _ = 2 * edgeCompositionCoeff D n * diagonal := by ring

theorem not_rawMassMultiplier_le_diagonal
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    {diagonal : ℝ} (hdiagonal : 0 < diagonal) :
    ¬ 2 * edgeCompositionCoeff D n * diagonal ≤ diagonal :=
  not_le_of_gt (diagonal_lt_rawMassMultiplier D n hdiagonal)

/-! ## The forced depth-amplified triangular error

If raw scaled sources are retained, the error allowance must absorb the full
composition multiplier at every recursive step. -/

def amplifiedTriangularError
    (D : ConstructedConfiguredSequenceWeighted.Data) (base : ℕ → ℝ)
    (n : ℕ) : ℕ → ℝ
  | 0 => base n
  | k + 1 =>
      2 * edgeCompositionCoeff D n *
        amplifiedTriangularError D base (n + 1) k

@[simp] theorem amplifiedTriangularError_zero
    (D : ConstructedConfiguredSequenceWeighted.Data) (base : ℕ → ℝ)
    (n : ℕ) :
    amplifiedTriangularError D base n 0 = base n := rfl

@[simp] theorem amplifiedTriangularError_succ
    (D : ConstructedConfiguredSequenceWeighted.Data) (base : ℕ → ℝ)
    (n k : ℕ) :
    amplifiedTriangularError D base n (k + 1) =
      2 * edgeCompositionCoeff D n *
        amplifiedTriangularError D base (n + 1) k := rfl

theorem amplifiedTriangularError_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) {base : ℕ → ℝ}
    (hbase : ∀ n, 0 ≤ base n) :
    ∀ n k, 0 ≤ amplifiedTriangularError D base n k := by
  intro n k
  induction k generalizing n with
  | zero => exact hbase n
  | succ k ih =>
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          ((edgeCompositionCoeffEnvelope D).value_nonneg n))
        (ih (n + 1))

/-- The raw source-mass estimate is exactly the next allowance for the
depth-amplified recurrence; no coefficient is discarded. -/
theorem rawMassMultiplier_eq_nextAmplifiedError
    (D : ConstructedConfiguredSequenceWeighted.Data) (base : ℕ → ℝ)
    (n k : ℕ) :
    2 * edgeCompositionCoeff D n *
        amplifiedTriangularError D base (n + 1) k =
      amplifiedTriangularError D base n (k + 1) := rfl

/-- `RowBounds.cost_le` and the configured scalar estimate give the exact
depthwise mass bound, with no fixed stable target and no recost comparison. -/
def depthwiseRawSourceMass
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H}
    (X : PhaseScaledSuccessorBundles H B)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (hscaledCoeff : ∀ n,
      (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) ≤
        2 * edgeCompositionCoeff D n) :
    DepthwiseRawSourceMass X D := by
  constructor
  intro n
  have hcost0 : 0 ≤ (H.row (n + 1)).output.chosen.Delta.cost :=
    (H.row (n + 1)).output.chosen.Delta.cost_nonneg
  have hcoeff0 : 0 ≤ 2 * edgeCompositionCoeff D n :=
    mul_nonneg (by norm_num) ((edgeCompositionCoeffEnvelope D).value_nonneg n)
  calc
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (X.toScaled.nextColumn.source n) =
        (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) *
          (H.row (n + 1)).output.chosen.Delta.cost := by
      simpa [PhaseScaledSuccessorBundles.toScaled,
        ScaledSuccessorBundles.nextColumn] using
        (X.bundle n).scaled.sourceMass_eq
    _ ≤ (2 * edgeCompositionCoeff D n) * e (n + 1) (k + 1) :=
      mul_le_mul (hscaledCoeff n) (B.cost_le (n + 1)) hcost0 hcoeff0

/-- One closed scaled successor carrying the depth-indexed raw source mass. -/
structure DepthwiseClosedScaledSuccessorStep
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (B : RowBounds H)
    (D : ConstructedConfiguredSequenceWeighted.Data) where
  phaseBundles : PhaseScaledSuccessorBundles H B
  nextReady : ReadyColumn phaseBundles.toScaled.nextColumn
  sourceMass : DepthwiseRawSourceMass phaseBundles D

noncomputable def PhaseScaledSuccessorBundles.depthwiseClosedStep
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H}
    (X : PhaseScaledSuccessorBundles H B)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1)
    (hscaledCoeff : ∀ n,
      (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) ≤
        2 * edgeCompositionCoeff D n) :
    DepthwiseClosedScaledSuccessorStep H B D where
  phaseBundles := X
  nextReady := X.toScaled.nextReadyColumn (X.readySidecars hkh0 hkh1)
  sourceMass := depthwiseRawSourceMass X D hscaledCoeff

end ConfiguredRecursiveEdgeFiniteCorrelatedScaledSuccessorMass
