import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnScalarClosing
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnBase
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumnShift
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArrayPaperMain
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

/-!
# Final configured finite-presented assembly

This file fixes the universal scalar choices which are independent of the
finite-column recursion, composes all scalar tail shifts, and exposes the
truthful depth-zero physical `ReadyColumn`.  The only remaining parameters are
the three nonnegative transition ceilings and the concrete infinite presented
array built by the finite recursion.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeFinitePresentedFinalAssembly

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePhysicalFiniteColumnBase
  ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

/-- The fixed total marking-distortion budget used by the finite construction. -/
def distortionTotal : ℝ := 1 / 16

theorem distortionTotal_pos : 0 < distortionTotal := by
  norm_num [distortionTotal]

theorem distortionTotal_le_eighth : distortionTotal ≤ 1 / 8 := by
  norm_num [distortionTotal]

/-- The same explicit small scalar is used to start the configured model. -/
def modelEpsilon : ℝ := 1 / 16

theorem modelEpsilon_pos : 0 < modelEpsilon := by
  norm_num [modelEpsilon]

theorem modelEpsilon_le_tenth : modelEpsilon ≤ 1 / 10 := by
  norm_num [modelEpsilon]

/-- The component ceilings are selected by the concrete nonaffine transition
construction.  Their nonnegativity is the only scalar fact needed here. -/
structure TransitionCeilings where
  C0 : ℝ
  C1 : ℝ
  C2 : ℝ
  C0_nonnegative : 0 ≤ C0
  C1_nonnegative : 0 ≤ C1
  C2_nonnegative : 0 ≤ C2

/-- The explicit fixed inverse-Jacobi ceilings from the paper.  Unlike the
unit-parameter derivative gains, these are uniform because the first and
second derivative channels are normalized by the physical period and its
square. -/
def physicalTransitionCeilings : TransitionCeilings where
  C0 := FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
  C1 := FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
  C2 := FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2
  C0_nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0_nonnegative
  C1_nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1_nonnegative
  C2_nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2_nonnegative

/-- All scalar choices and all scalar tails, with no recursive geometric
callback hidden in the package. -/
structure ScalarPackage (T : TransitionCeilings) where
  jet : RowJetScalarOutput choice.MA0 choice.NA0
  gauge : Output jet distortionTotal
    (configuredSourceMassTarget distortionTotal T.C0 T.C1 T.C2)
  closing : ClosingOutput jet gauge distortionTotal T.C0 T.C1 T.C2

/-- The scalar package exists for every truthful nonnegative choice of the
three transition ceilings. -/
theorem exists_scalarPackage (T : TransitionCeilings) :
    Nonempty (ScalarPackage T) := by
  obtain ⟨J⟩ := exists_fixed_rowJetScalarOutput_of_eps
    modelEpsilon_pos modelEpsilon_le_tenth
  obtain ⟨G⟩ := exists_configuredOutput J distortionTotal_pos
    distortionTotal_le_eighth
  obtain ⟨S⟩ := exists_closingOutput J G
    choice.MA0_nonnegative choice.NA0_nonnegative distortionTotal_pos
  exact ⟨⟨J, G, S⟩⟩

namespace ScalarPackage

variable {T : TransitionCeilings}

/-- The tail added after the corrected gauge-majorant output. -/
def closingShift (X : ScalarPackage T) : ℕ :=
  X.closing.preShift + X.closing.large.N

/-- The complete row-tail shift measured from the physical finite base. -/
def totalRowShift (X : ScalarPackage T) : ℕ :=
  X.gauge.N + X.closingShift

/-- The scalar data used by the capstone. -/
def data (X : ScalarPackage T) :
    ConstructedConfiguredSequenceWeighted.Data :=
  X.closing.data

/-- The depth-zero physical column before the common scalar tail is applied. -/
def rawReadyColumn (X : ScalarPackage T) {K0 K1 K2 : ℝ} :
    ReadyColumn (column X.jet (K0 := K0) (K1 := K1) (K2 := K2)) where
  ready := fun n => readyAt X.jet (K0 := K0) (K1 := K1) (K2 := K2) n
  initial_range_current := fun n =>
    initial_range_next X.jet (K0 := K0) (K1 := K1) (K2 := K2) n

/-- The physical finite base reindexed by the complete scalar row tail. -/
def baseColumn (X : ScalarPackage T) {K0 K1 K2 : ℝ} :=
  (column X.jet (K0 := K0) (K1 := K1) (K2 := K2)).shiftRows
    (N := X.totalRowShift)

/-- Analytic readiness is preserved by the same common reindexing. -/
def baseReadyColumn (X : ScalarPackage T) {K0 K1 K2 : ℝ} :
    ReadyColumn (X.baseColumn (K0 := K0) (K1 := K1) (K2 := K2)) :=
  (X.rawReadyColumn (K0 := K0) (K1 := K1) (K2 := K2)).shiftRows
    (N := X.totalRowShift)

/-- The reindexed depth-zero source is charged to the successor-indexed
composition defect of the final scalar data. -/
theorem base_sourceMass_le
    (X : ScalarPackage T) {K0 K1 K2 : ℝ} (n : ℕ) :
    sourceMass ((X.baseColumn (K0 := K0) (K1 := K1) (K2 := K2)).source n) ≤
      edgeCompositionPhysicalDefect X.data (n + 1) := by
  have H := sourceMass_le_compositionPhysicalDefect X.jet
    (K0 := K0) (K1 := K1) (K2 := K2) (X.totalRowShift + n)
  calc
    sourceMass
        ((X.baseColumn (K0 := K0) (K1 := K1) (K2 := K2)).source n) ≤
        edgeCompositionPhysicalDefect (D X.jet.scalar)
          (X.totalRowShift + n + 1) := by
      simpa [baseColumn, Nat.add_assoc] using H
    _ = edgeCompositionPhysicalDefect X.data (n + 1) := by
      simp [data, ClosingOutput.data, Output.data, D, totalRowShift,
        closingShift, edgeCompositionPhysicalDefect_shift, Nat.add_assoc]

/-- Enlarge only the stored depth-zero row error.  This is the adapter used
when the concrete array builder chooses its final common error sequence. -/
def enlargedBaseColumn
    (X : ScalarPackage T) {K0 K1 K2 : ℝ}
    {e' : ℕ → ℕ → ℝ}
    (he : ∀ n,
      compositionError X.jet (X.totalRowShift + n) 0 ≤ e' n 0) :=
  (X.baseColumn (K0 := K0) (K1 := K1) (K2 := K2)).monoError he

/-- Readiness survives the final monotone enlargement of the cost allowance. -/
def enlargedBaseReadyColumn
    (X : ScalarPackage T) {K0 K1 K2 : ℝ}
    {e' : ℕ → ℕ → ℝ}
    (he : ∀ n,
      compositionError X.jet (X.totalRowShift + n) 0 ≤ e' n 0) :
    ReadyColumn (X.enlargedBaseColumn (K0 := K0) (K1 := K1) (K2 := K2) he) :=
  X.baseReadyColumn.monoError he

end ScalarPackage

end ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
