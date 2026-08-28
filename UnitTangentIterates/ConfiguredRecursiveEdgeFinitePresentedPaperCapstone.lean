import UnitTangentIterates.ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
import UnitTangentIterates.ConfiguredRecursiveEdgePresentedPhysicalSidecars
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows
import UnitTangentIterates.WeightedRecursiveDefect
import UnitTangentIterates.WeightedRecursiveDefectCapAwareActualPullbackStages

/-!
# Final depthwise finite-presented paper capstone

This module joins the canonical dependent successor tower to the configured
scalar closing package.  The displayed error is the closing defect itself,
read diagonally as `defect (n + k)`.  Consequently nonnegativity and
summability are consequences of the scalar package and are not fields of the
analytic provider.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace ConfiguredRecursiveEdgeFinitePresentedPaperCapstone

open ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  ConfiguredRecursiveEdgeFiniteCorrelatedDepthwisePresentedArray
  ConfiguredRecursiveEdgeFiniteCorrelatedScaledSuccessorTower
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePresentedPhysicalSidecars
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays

open FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray
open PathMetric.WeightedRecursiveDefect

/-- The public two-dimensional error is exactly the scalar closing defect,
with the usual row-diagonal indexing. -/
def publicError
    (X : ScalarPackage physicalTransitionCeilings) (n k : ℕ) : ℝ :=
  X.closing.defect (n + k)

/-- The unshifted scalar index represented by a displayed array cell. -/
def publicIndex
    (X : ScalarPackage physicalTransitionCeilings) (n k : ℕ) : ℕ :=
  X.closing.preShift + X.closing.large.N + (n + k)

theorem publicError_eq_directDiagonal
    (X : ScalarPackage physicalTransitionCeilings) (n k : ℕ) :
    publicError X n k =
      directDiagonal X.gauge.data choice.MA0 choice.NA0 distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 X.jet.scalar.Mend
        (publicIndex X n k) := by
  simp [publicError, publicIndex, ClosingOutput.defect, shiftSequence,
    Nat.add_assoc]

theorem publicError_nonnegative
    (X : ScalarPackage physicalTransitionCeilings) :
    ∀ n k, 0 ≤ publicError X n k := by
  intro n k
  unfold publicError ClosingOutput.defect shiftSequence
  exact directDiagonal_nonnegative X.gauge.data choice.MA0_nonnegative
    choice.NA0_nonnegative X.jet.scalar.Mend_positive.le _

theorem publicError_summable
    (X : ScalarPackage physicalTransitionCeilings) :
    ∀ n, Summable (publicError X n) := by
  have hdirect := directDiagonal_summable X.gauge.data
    (E0 := distortionTotal)
    (C0 := physicalTransitionCeilings.C0)
    (C1 := physicalTransitionCeilings.C1)
    (C2 := physicalTransitionCeilings.C2)
    choice.MA0_nonnegative choice.NA0_nonnegative
    X.jet.scalar.Mend_positive.le
  have hdefect : Summable X.closing.defect := by
    simpa [ClosingOutput.defect, shiftSequence, Nat.add_assoc] using
      ShadowingTails.summable_shift hdirect
        (X.closing.preShift + X.closing.large.N)
  intro n
  simpa [publicError] using ShadowingTails.summable_shift hdefect n

/-- The exact superdiagonal allowance required by a raw scaled successor.
It is the triangular form of the paper's propagated-budget recurrence: the
next displayed row must absorb the coefficient-weighted mass of the row one
level above it. -/
def AmplifiedErrorRecurrence
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (e : ℕ → ℕ → ℝ) : Prop :=
  ∀ n k, 2 * edgeCompositionCoeff D n * e (n + 1) (k + 1) ≤
    e n (k + 2)

/-- A positive diagonal error cannot itself satisfy the raw amplified
recurrence: both entries have the same diagonal index, while the raw source
multiplier is strictly larger than one.  Thus the closing defect is the
public shadowing error, not a valid unrecosted internal tower allowance. -/
theorem not_publicError_amplified_at
    (X : ScalarPackage physicalTransitionCeilings) (n k : ℕ)
    (hpos : 0 < publicError X n (k + 2)) :
    ¬ 2 * edgeCompositionCoeff X.data n * publicError X (n + 1) (k + 1) ≤
      publicError X n (k + 2) := by
  have H := ConfiguredRecursiveEdgeFiniteCorrelatedScaledSuccessorMass.not_rawMassMultiplier_le_diagonal
    X.data n hpos
  simpa [publicError, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H

/-- The only recursive analytic input.  Its last field is the concrete
estimate which says that the genuine chosen cost and terminal marking cap fit
inside the already configured closing defect. -/
structure FullyPhysicalProvider
    (X : ScalarPackage physicalTransitionCeilings) where
  Q : ℕ → Data
  e : ℕ → ℕ → ℝ
  P0 : ℕ → ℝ
  P1 : ℕ → ℝ
  khat : ℕ → ℝ
  G1 : ℕ → ℝ
  Cg : ℕ → ℝ
  C : ℕ → ℝ
  Qmax : ℕ → ℝ
  base : DepthwiseDepth X.data
    (fun n ↦ edgeCompositionPhysicalDefect X.data (n + 1))
    Q e 0 P0 P1 khat G1 Cg C (commonC (D X.jet.scalar))
      (commonDlt (D X.jet.scalar))
    (fun _ ↦ sourceKh) Qmax
  tower : DepthwiseProvider X.data
    (fun n ↦ edgeCompositionPhysicalDefect X.data (n + 1))
    Q e P0 P1 khat G1 Cg C (commonC (D X.jet.scalar))
      (commonDlt (D X.jet.scalar))
    (fun _ ↦ sourceKh) Qmax (fun _ ↦ sourceKh_nonnegative)
      (fun _ ↦ sourceKh_lt_one)
  tube : ∀ n k, IsVariableTubeMember (commonC X.data) (C n) 0
    (commonDlt X.data) (P base tower n k)
  domination : ∀ n k,
    (rowPath base tower n k).cost + endpointCap base tower n k ≤
      publicError X n k

namespace FullyPhysicalProvider

variable {X : ScalarPackage physicalTransitionCeilings}

/-- The displayed step estimate follows from the actual shifted chosen path,
the terminal cap, and the provider's sole scalar domination theorem. -/
theorem stepDistance (F : FullyPhysicalProvider X) : ∀ n k,
    dist (P F.base F.tower n k) (P F.base F.tower n (k + 1)) ≤
      TriangularMarkedPathSchemeVariableTerminal.rowC
        F.P0 F.P1 F.khat F.G1 F.Cg n * publicError X n k := by
  intro n k
  let R := (depthwiseDepths F.base F.tower k).ready.row n
  let K := TriangularMarkedPathSchemeVariableTerminal.rowC
    F.P0 F.P1 F.khat F.G1 F.Cg n
  have hK0 : 0 ≤ K := by
    simpa [K, TriangularMarkedPathSchemeVariableTerminal.rowC] using
      c2ConstVar_nonneg (F.P0 n) (F.P1 n) (F.khat n) (F.G1 n) (F.Cg n)
  have hK1 : 1 ≤ K := by
    simpa [K, TriangularMarkedPathSchemeVariableTerminal.rowC] using
      one_le_c2ConstVar (F.P0 n) (F.P1 n) (F.khat n) (F.G1 n) (F.Cg n)
  have hselected : dist (P F.base F.tower n k)
      (selectedRear F.base F.tower n k) ≤
        K * (rowPath F.base F.tower n k).cost := by
    apply dist_le_cost_variableSpeed (rowPath F.base F.tower n k)
    · exact (F.tube n k).hasDerivAt_curve
    · intro u
      have hi : HasDerivAt
          (fun y : ℝ ↦ y + coherentPhase F.base F.tower n k) 1 u := by
        simpa using (hasDerivAt_id u).add_const
          (coherentPhase F.base F.tower n k)
      simpa [selectedRear, R] using
        (R.output.stage.rear_curve_deriv
          (u + coherentPhase F.base F.tower n k)).scomp u hi
    · exact (F.tube n k).hasDerivAt_vel
    · intro u
      have hi : HasDerivAt
          (fun y : ℝ ↦ y + coherentPhase F.base F.tower n k) 1 u := by
        simpa using (hasDerivAt_id u).add_const
          (coherentPhase F.base F.tower n k)
      simpa [selectedRear, R] using
        (R.output.stage.rear_vel_deriv
          (u + coherentPhase F.base F.tower n k)).scomp u hi
    · simpa [rowPath, R] using
        NormalPathC2IncrementVariableSpeed.isVariableSpeedNormalPath_shift
          R.output.chosen.Delta
          ((depthwiseDepths F.base F.tower k).bounds.geometry n)
  have hcap := endpointCap_nonnegative F.base F.tower n k
  calc
    dist (P F.base F.tower n k) (P F.base F.tower n (k + 1)) ≤
        dist (P F.base F.tower n k) (selectedRear F.base F.tower n k) +
          dist (selectedRear F.base F.tower n k)
            (P F.base F.tower n (k + 1)) := dist_triangle _ _ _
    _ ≤ K * (rowPath F.base F.tower n k).cost +
        endpointCap F.base F.tower n k :=
      add_le_add hselected (selectedRear_dist_next F.base F.tower n k)
    _ ≤ K * ((rowPath F.base F.tower n k).cost +
        endpointCap F.base F.tower n k) := by
      nlinarith
    _ ≤ K * publicError X n k :=
      mul_le_mul_of_nonneg_left (F.domination n k) hK0

/-- The exact finite presented array delivered by the provider. -/
def array (F : FullyPhysicalProvider X) :=
  toArray F.base F.tower (publicError_nonnegative X)
    (publicError_summable X) F.tube F.stepDistance

end FullyPhysicalProvider

/-- The genuinely physical and initial paper-facing facts.  No scalar tail,
summability, or recursive-source bound is repeated here. -/
structure PhysicalSidecars
    {X : ScalarPackage physicalTransitionCeilings}
    (F : FullyPhysicalProvider X) where
  baseCoherence : Depthwise.ConfiguredBaseCoherence F.base
  direction : ℂ
  direction_norm : ‖direction‖ = 1
  base_bounded : Bornology.IsBounded
    (range (⇑((depthwiseDepths F.base F.tower 0).ready.row 0).p.1))
  base_width : Width.width
      (range (⇑((depthwiseDepths F.base F.tower 0).ready.row 0).p.1))
      direction ≤ X.jet.scalar.Cw
  base_length : 2 * X.closing.data.Hs 0 ≤
    MarkedReparam.totalLength
      (fun u ↦ ((depthwiseDepths F.base F.tower 0).ready.row 0).p.2.1 u)
  row_gap : c2ConstVar (F.P0 0) (F.P1 0) (F.khat 0) (F.G1 0) (F.Cg 0) *
      (∑' k, publicError X 0 k) ≤ X.closing.radius 0

/-- Final paper theorem.  Its only arguments beyond the constructed scalar
package are the concrete recursive analytic provider and its physical
sidecars. -/
theorem paper
    (X : ScalarPackage physicalTransitionCeilings)
    (F : FullyPhysicalProvider X) (H : PhysicalSidecars F) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  let cells := Depthwise.cellFactsOfBasePhase F.base F.tower
    (publicError_nonnegative X) (publicError_summable X) F.tube
    F.stepDistance
    (Depthwise.ConfiguredBaseCoherence.base_speed
      F.base F.tower H.baseCoherence)
    (Depthwise.ConfiguredBaseCoherence.baseFrontPhaseLink
      F.base F.tower H.baseCoherence)
  let S := cells.toSidecars X.data F.array
  let R := presentedPackage F.array
    (fun n ↦ P F.base F.tower n 0) (fun _ ↦ rfl)
    S.physical S.mixed S.frontTube
  apply FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArrayPaperMain.paperMain
    F.array (fun n ↦ P F.base F.tower n 0) X.closing R
    sourceKh_nonnegative sourceKh_lt_one
  · exact X.data.separation_zero_pos
  · rw [commonDlt, chordBase_eq_min X.data.model
        (configured_kstar_pos X.data.model)]
    exact half_pos (lt_min X.data.separation_zero_pos
      (div_pos Real.pi_pos
        (mul_pos (by norm_num) (configured_kstar_pos X.data.model))))
  · exact X.data.separation_zero_pos
  · exact X.data.separation_zero_pos
  · exact H.direction_norm
  · simpa [FullyPhysicalProvider.array] using H.base_bounded
  · simpa [FullyPhysicalProvider.array] using H.base_width
  · simpa [FullyPhysicalProvider.array] using H.base_length
  · exact H.row_gap

/-! ## Paper-faithful actual-stage capstone

The following route is independent of recursive source mass and `RowBounds`.
It is designed for the direct finite path/source iteration: each cell already
contains the actual chosen increment, while the scalar closing package fixes
its displayed defect and summable tail. -/

/-- A complete dependent family of actual finite stages.  No raw recursive
source tower or transport operation on arbitrary paths is retained. -/
structure ActualStageProvider
    (X : ScalarPackage physicalTransitionCeilings) where
  Q : ℕ → Data
  P : ℕ → ℕ → Data
  R : ℕ → ℕ → Data
  pathError : ℕ → ℕ → ℝ
  capError : ℕ → ℕ → ℝ
  C : ℕ → ℝ
  stages : WeightedRecursiveDefect.CapAwareActualPullbackStages
    Q P R pathError capError (publicError X)
  cell : ∀ n k, Cell P n k
  tube : ∀ n k, IsVariableTubeMember (commonC X.data) (C n) 0
    (commonDlt X.data) (P n k)

namespace ActualStageProvider

variable {X : ScalarPackage physicalTransitionCeilings}

/-- Package a row-indexed actual source recursion as the direct capstone
provider.  The only scalar compatibility required here is the combined
physical-path-plus-endpoint-cap domination by the public closing defect. -/
def ofRows
    {P0 kh khat Qmax : ℕ → ℕ → ℝ}
    {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}
    (R : FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray.Rows
      P0 kh khat Qmax E C0 C1 C2 d)
    (Q : ℕ → Data) (C : ℕ → ℝ)
    (hbase : ∀ n, R.P n 0 = Q n)
    (hcombined : ∀ n k,
      R.pathError n k + R.endpointCap n k ≤ publicError X n k)
    (hrange : ∀ n k,
      GeometricUnitTangentRangeEdge (R.P (n + 1) k) (R.P n (k + 1)))
    (cell : ∀ n k, Cell R.P n k)
    (tube : ∀ n k, IsVariableTubeMember (commonC X.data) (C n) 0
      (commonDlt X.data) (R.P n k)) :
    ActualStageProvider X where
  Q := Q
  P := R.P
  R := R.intermediateRear
  pathError := R.pathError
  capError := R.endpointCap
  C := C
  stages := R.toCapAwareActualPullbackStages Q (publicError X)
    hbase hcombined hrange
  cell := cell
  tube := tube

/-- Package the paper-indexed synchronized recursion.  Its diagonal range
edge is theorem-produced by reachability and is not a constructor argument. -/
def ofSynchronizedRows
    {P0 kh khat Qmax : ℕ → ℕ → ℝ}
    {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}
    (R : FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Rows
      P0 kh khat Qmax E C0 C1 C2 d)
    (Q : ℕ → Data) (C : ℕ → ℝ)
    (hbase : ∀ n, R.P n 0 = Q n)
    (hcombined : ∀ n k,
      R.pathError n k + R.endpointCap n k ≤ publicError X n k)
    (cell : ∀ n k, Cell R.P n k)
    (tube : ∀ n k, IsVariableTubeMember (commonC X.data) (C n) 0
      (commonDlt X.data) (R.P n k)) :
    ActualStageProvider X where
  Q := Q
  P := R.P
  R := R.intermediateRear
  pathError := R.pathError
  capError := R.endpointCap
  C := C
  stages := R.toCapAwareActualPullbackStages Q (publicError X)
    hbase hcombined
  cell := cell
  tube := tube

/-- Configured row ceilings give the public closing-defect domination
automatically.  This is the scalar/analytic boundary of the direct proof:
the actual row provider supplies only the path-conversion and endpoint-cap
ceilings at `publicIndex`. -/
def ofConfiguredRows
    {P0 kh khat Qmax : ℕ → ℕ → ℝ}
    {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}
    (R : FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray.Rows
      P0 kh khat Qmax E C0 C1 C2 d)
    (H : FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray.Rows.Ceilings
      R
      (fun n k ↦ edgeConversion X.gauge.data
        (analyticKhat X.gauge.data) choice.MA0 choice.NA0 (publicIndex X n k))
      (fun n k ↦ edgeEndpointConversion X.gauge.data sourceKh
        X.jet.scalar.Mend (publicIndex X n k))
      (fun n k ↦ edgePhysicalDefect X.gauge.data
        (publicIndex X n k + 1)))
    (hE : ∀ n, E n = distortionTotal)
    (hC0 : ∀ n, C0 n = physicalTransitionCeilings.C0)
    (hC1 : ∀ n, C1 n = physicalTransitionCeilings.C1)
    (hC2 : ∀ n, C2 n = physicalTransitionCeilings.C2)
    (hd : ∀ n k, d n k = edgePhysicalDefect X.gauge.data
      (publicIndex X n k + 1))
    (Q : ℕ → Data) (C : ℕ → ℝ)
    (hbase : ∀ n, R.P n 0 = Q n)
    (hrange : ∀ n k,
      GeometricUnitTangentRangeEdge (R.P (n + 1) k) (R.P n (k + 1)))
    (cell : ∀ n k, Cell R.P n k)
    (tube : ∀ n k, IsVariableTubeMember (commonC X.data) (C n) 0
      (commonDlt X.data) (R.P n k)) :
    ActualStageProvider X := by
  apply ofRows R Q C hbase _ hrange cell tube
  intro n k
  rw [publicError_eq_directDiagonal]
  exact R.configured_combined_le X.gauge.data choice.MA0 choice.NA0
    distortionTotal physicalTransitionCeilings.C0
    physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
    X.jet.scalar.Mend (publicIndex X) H hE hC0 hC1 hC2 hd n k

/-- The synchronized actual recursion plus its two row ceilings gives the
complete direct provider.  Base and range coherence are internal to the
synchronized recurrence. -/
def ofConfiguredSynchronizedRows
    {P0 kh khat Qmax : ℕ → ℕ → ℝ}
    {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}
    (R : FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Rows
      P0 kh khat Qmax E C0 C1 C2 d)
    (H : FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Rows.Ceilings
      R
      (fun n k ↦ edgeConversion X.gauge.data
        (analyticKhat X.gauge.data) choice.MA0 choice.NA0 (publicIndex X n k))
      (fun n k ↦ edgeEndpointConversion X.gauge.data sourceKh
        X.jet.scalar.Mend (publicIndex X n k))
      (fun n k ↦ edgePhysicalDefect X.gauge.data
        (publicIndex X n k + 1)))
    (hE : ∀ n, E n = distortionTotal)
    (hC0 : ∀ n, C0 n = physicalTransitionCeilings.C0)
    (hC1 : ∀ n, C1 n = physicalTransitionCeilings.C1)
    (hC2 : ∀ n, C2 n = physicalTransitionCeilings.C2)
    (hd : ∀ n k, d n k = edgePhysicalDefect X.gauge.data
      (publicIndex X n k + 1))
    (Q : ℕ → Data) (C : ℕ → ℝ)
    (hbase : ∀ n, R.P n 0 = Q n)
    (cell : ∀ n k, Cell R.P n k)
    (tube : ∀ n k, IsVariableTubeMember (commonC X.data) (C n) 0
      (commonDlt X.data) (R.P n k)) :
    ActualStageProvider X := by
  apply ofSynchronizedRows R Q C hbase _ cell tube
  intro n k
  rw [publicError_eq_directDiagonal]
  exact R.configured_combined_le X.gauge.data choice.MA0 choice.NA0
    distortionTotal physicalTransitionCeilings.C0
    physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
    X.jet.scalar.Mend (publicIndex X) H hE hC0 hC1 hC2 hd n k

/-- The final geometric distance scheme has already paid the variable-speed
conversion inside `publicError`; its bookkeeping coefficient is therefore
exactly one. -/
def paperP0 : ℕ → ℝ := fun _ ↦ 1
def paperP1 : ℕ → ℝ := fun _ ↦ 0
def paperKhat : ℕ → ℝ := fun _ ↦ 0
def paperG1 : ℕ → ℝ := fun _ ↦ 0
def paperCg : ℕ → ℝ := fun _ ↦ 0

@[simp] theorem paper_rowC (n : ℕ) :
    TriangularMarkedPathSchemeVariableTerminal.rowC
      paperP0 paperP1 paperKhat paperG1 paperCg n = 1 := by
  norm_num [TriangularMarkedPathSchemeVariableTerminal.rowC,
    paperP0, paperP1, paperKhat, paperG1, paperCg, c2ConstVar,
    NormalPathC2Increment.velConst, accConstVar]

/-- Marked step distance derived from the actual path, rather than supplied
as an independent domination callback. -/
theorem stepDistance (F : ActualStageProvider X) : ∀ n k,
    dist (F.P n k) (F.P n (k + 1)) ≤
      TriangularMarkedPathSchemeVariableTerminal.rowC
        paperP0 paperP1 paperKhat paperG1 paperCg n * publicError X n k := by
  intro n k
  simpa using F.stages.stepDistance n k

/-- The geometric presented array carried by actual stages.  Error
nonnegativity and summability come solely from the scalar closing package. -/
def array (F : ActualStageProvider X) :
    Array F.Q F.P (publicError X)
      paperP0 paperP1 paperKhat paperG1 paperCg F.C
      (commonC X.data) (commonDlt X.data) where
  cell := F.cell
  base := F.stages.base
  error_nonnegative := publicError_nonnegative X
  error_summable := publicError_summable X
  tube := F.tube
  stepDistance := F.stepDistance

end ActualStageProvider

/-- Physical finite-row data and the initial closing facts for an actual-stage
array.  These are independent of how its paths were constructed. -/
structure ActualStagePhysicalSidecars
    {X : ScalarPackage physicalTransitionCeilings}
    (F : ActualStageProvider X) where
  cells : CellFacts X.data F.array
  direction : ℂ
  direction_norm : ‖direction‖ = 1
  base_width : Width.width (range (⇑(F.Q 0).1)) direction ≤ X.jet.scalar.Cw
  base_length : 2 * X.closing.data.Hs 0 ≤
    MarkedReparam.totalLength (fun u ↦ (F.Q 0).2.1 u)

/-- The minimal configured depth-zero input.  All quantitative base facts are
read from the scalar package after identifying the displayed base datum. -/
structure ConfiguredActualBase
    {X : ScalarPackage physicalTransitionCeilings}
    (F : ActualStageProvider X) where
  cells : CellFacts X.data F.array
  Q_zero : F.Q 0 = X.jet.scalar.Q X.totalRowShift

namespace ConfiguredActualBase

variable {X : ScalarPackage physicalTransitionCeilings}
  {F : ActualStageProvider X}

/-- The configured base identity supplies direction, unit norm, width, and
length; only the already aggregated physical cell facts remain analytic. -/
def toPhysicalSidecars (B : ConfiguredActualBase F) :
    ActualStagePhysicalSidecars F where
  cells := B.cells
  direction := X.jet.scalar.direction
    (X.jet.scalar.large.N + X.totalRowShift)
  direction_norm := X.jet.scalar.direction_unit _
  base_width := by
    rw [B.Q_zero]
    have hper : perim (X.jet.scalar.Q X.totalRowShift) ≠ 0 := by
      rw [(X.jet.scalar.model_data X.totalRowShift).1]
      exact (mul_pos (by norm_num)
        ((ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          X.jet.scalar.E.data X.jet.scalar.large.N).model.separation_pos
            X.totalRowShift)).ne'
    rw [← MarkedSpace.range_ev_of_perim_ne_zero hper]
    rw [(X.jet.scalar.model_data X.totalRowShift).2]
    simpa [ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      Nat.add_assoc] using
      X.jet.scalar.model_width (X.jet.scalar.large.N + X.totalRowShift)
  base_length := by
    rw [B.Q_zero,
      VariableMarkedPhysicalLength.totalLength_eq_perim_of_tube
        (X.jet.scalar.pair.input.front_tube X.totalRowShift),
      (X.jet.scalar.model_data X.totalRowShift).1]
    simp [ConfiguredRecursiveEdgeFiniteColumnScalarClosing.ClosingOutput.data,
      ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
      ScalarPackage.totalRowShift, ScalarPackage.closingShift,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      Nat.add_assoc]

end ConfiguredActualBase

/-- One concrete direct-stage argument for the final theorem. -/
def DirectStagePackage
    (X : ScalarPackage physicalTransitionCeilings) :=
  { F : ActualStageProvider X // ConfiguredActualBase F }

namespace DirectStagePackage

/-- Bundle configured actual rows and their two remaining physical base facts
as the single concrete argument consumed by `paper_of_actual_stages`. -/
def ofConfiguredRows
    {X : ScalarPackage physicalTransitionCeilings}
    {P0 kh khat Qmax : ℕ → ℕ → ℝ}
    {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}
    (R : FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray.Rows
      P0 kh khat Qmax E C0 C1 C2 d)
    (H : FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray.Rows.Ceilings
      R
      (fun n k ↦ edgeConversion X.gauge.data
        (analyticKhat X.gauge.data) choice.MA0 choice.NA0 (publicIndex X n k))
      (fun n k ↦ edgeEndpointConversion X.gauge.data sourceKh
        X.jet.scalar.Mend (publicIndex X n k))
      (fun n k ↦ edgePhysicalDefect X.gauge.data
        (publicIndex X n k + 1)))
    (hE : ∀ n, E n = distortionTotal)
    (hC0 : ∀ n, C0 n = physicalTransitionCeilings.C0)
    (hC1 : ∀ n, C1 n = physicalTransitionCeilings.C1)
    (hC2 : ∀ n, C2 n = physicalTransitionCeilings.C2)
    (hd : ∀ n k, d n k = edgePhysicalDefect X.gauge.data
      (publicIndex X n k + 1))
    (Q : ℕ → Data) (C : ℕ → ℝ)
    (hbase : ∀ n, R.P n 0 = Q n)
    (hrange : ∀ n k,
      GeometricUnitTangentRangeEdge (R.P (n + 1) k) (R.P n (k + 1)))
    (cell : ∀ n k, Cell R.P n k)
    (tube : ∀ n k, IsVariableTubeMember (commonC X.data) (C n) 0
      (commonDlt X.data) (R.P n k)) :
    let F := ActualStageProvider.ofConfiguredRows R H hE hC0 hC1 hC2 hd
      Q C hbase hrange cell tube
    CellFacts X.data F.array →
      F.Q 0 = X.jet.scalar.Q X.totalRowShift →
        DirectStagePackage X := by
  let F := ActualStageProvider.ofConfiguredRows R H hE hC0 hC1 hC2 hd
    Q C hbase hrange cell tube
  exact fun cells Q_zero ↦ ⟨F, ⟨cells, Q_zero⟩⟩

/-- Single-record final package constructor for the paper-indexed
synchronized recursion. -/
def ofConfiguredSynchronizedRows
    {X : ScalarPackage physicalTransitionCeilings}
    {P0 kh khat Qmax : ℕ → ℕ → ℝ}
    {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}
    (R : FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Rows
      P0 kh khat Qmax E C0 C1 C2 d)
    (H : FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Rows.Ceilings
      R
      (fun n k ↦ edgeConversion X.gauge.data
        (analyticKhat X.gauge.data) choice.MA0 choice.NA0 (publicIndex X n k))
      (fun n k ↦ edgeEndpointConversion X.gauge.data sourceKh
        X.jet.scalar.Mend (publicIndex X n k))
      (fun n k ↦ edgePhysicalDefect X.gauge.data
        (publicIndex X n k + 1)))
    (hE : ∀ n, E n = distortionTotal)
    (hC0 : ∀ n, C0 n = physicalTransitionCeilings.C0)
    (hC1 : ∀ n, C1 n = physicalTransitionCeilings.C1)
    (hC2 : ∀ n, C2 n = physicalTransitionCeilings.C2)
    (hd : ∀ n k, d n k = edgePhysicalDefect X.gauge.data
      (publicIndex X n k + 1))
    (Q : ℕ → Data) (C : ℕ → ℝ)
    (hbase : ∀ n, R.P n 0 = Q n)
    (cell : ∀ n k, Cell R.P n k)
    (tube : ∀ n k, IsVariableTubeMember (commonC X.data) (C n) 0
      (commonDlt X.data) (R.P n k)) :
    let F := ActualStageProvider.ofConfiguredSynchronizedRows R H
      hE hC0 hC1 hC2 hd Q C hbase cell tube
    CellFacts X.data F.array →
      F.Q 0 = X.jet.scalar.Q X.totalRowShift →
        DirectStagePackage X := by
  let F := ActualStageProvider.ofConfiguredSynchronizedRows R H
    hE hC0 hC1 hC2 hd Q C hbase cell tube
  exact fun cells Q_zero ↦ ⟨F, ⟨cells, Q_zero⟩⟩

end DirectStagePackage

theorem publicError_tsum_eq_radius
    (X : ScalarPackage physicalTransitionCeilings) (n : ℕ) :
    (∑' k, publicError X n k) = X.closing.radius n := by
  simp [publicError, ClosingOutput.radius, rowRadius, rowError,
    ShadowingTails.tail, shiftSequence]

/-- Final paper theorem from direct actual stages.  The recursive
`DepthwiseProvider`, raw source-mass recurrence, and unrestricted selected-map
transport residual do not occur in its statement. -/
theorem paper_of_actual_stages
    (X : ScalarPackage physicalTransitionCeilings)
    (D : DirectStagePackage X) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  let F := D.1
  let H := D.2.toPhysicalSidecars
  let S := H.cells.toSidecars X.data F.array
  let R := presentedPackage F.array (fun n ↦ F.P n 0) (fun _ ↦ rfl)
    S.physical S.mixed S.frontTube
  have hbaseTube : IsVariableTubeMember (commonC X.data) (F.C 0) 0
      (commonDlt X.data) (F.Q 0) := by
    rw [← F.stages.base 0]
    exact F.tube 0 0
  have hbaseBounded : Bornology.IsBounded (range (⇑(F.Q 0).1)) := by
    apply CurveDistance.isBounded_range_of_periodic
    · exact continuous_iff_continuousAt.mpr fun u ↦
        (hbaseTube.hasDerivAt_curve u).continuousAt
    · exact hbaseTube.periodic
    · norm_num
  apply FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArrayPaperMain.paperMain
    F.array (fun n ↦ F.P n 0) X.closing R
    sourceKh_nonnegative sourceKh_lt_one
  · exact X.data.separation_zero_pos
  · rw [commonDlt, chordBase_eq_min X.data.model
        (configured_kstar_pos X.data.model)]
    exact half_pos (lt_min X.data.separation_zero_pos
      (div_pos Real.pi_pos
        (mul_pos (by norm_num) (configured_kstar_pos X.data.model))))
  · exact X.data.separation_zero_pos
  · exact X.data.separation_zero_pos
  · exact H.direction_norm
  · exact hbaseBounded
  · exact H.base_width
  · exact H.base_length
  · change TriangularMarkedPathSchemeVariableTerminal.rowC
        ActualStageProvider.paperP0 ActualStageProvider.paperP1
          ActualStageProvider.paperKhat ActualStageProvider.paperG1
          ActualStageProvider.paperCg 0 *
          (∑' k, publicError X 0 k) ≤ X.closing.radius 0
    rw [ActualStageProvider.paper_rowC, publicError_tsum_eq_radius]
    simp

end ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
