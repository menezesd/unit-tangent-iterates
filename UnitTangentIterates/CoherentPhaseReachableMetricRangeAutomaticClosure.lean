import UnitTangentIterates.CoherentPhaseReachableMetricRange
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone
import UnitTangentIterates.PhysicalRearLocalShiftedStageAutomaticClosure

/-!
# Automatic physical closure from a coherent reachable metric grid

This adapter separates the phase/range bookkeeping already present in
`CoherentPhaseReachableMetricRange.System` from the genuinely physical data
which must be retained by a finite-stage constructor.  For a fixed row `n`,
the rear sequence is `P n (k + 2)` and the unshifted front sequence is
`P (n + 1) (k + 1)`.  A normalized terminal phase supplies the actual front
used by the physical rear kinematics.

  The physical capstone package supplies the common ordinary rear tubes and
  rowwise perimeter bounds directly.  A rowwise intrinsic-curvature ceiling
  then gives the common normalized-steering Lipschitz bound automatically.
-/

noncomputable section

open Filter Function Set Topology MarkedSpace PathMetric

namespace CoherentPhaseReachableMetricRangeAutomaticClosure

open CoherentPhaseReachableMetricRange
    ConfiguredRecursiveEdgeRecostMultiplierClosing
    ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone
    ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  CurvatureFromMarkedDistance
  PhysicalRearLocalShiftedStageAutomaticClosure
  VariableMarkedTube

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {O : GaugeOutput J}

/-- The actual physical front in a coherently marked finite cell. -/
def physicalFront
    {modelBase : ℕ → Data} {error : ℕ → ℕ → ℝ}
    (F : System modelBase error)
    (phase : ℕ → ℕ → Set.Icc (0 : ℝ) 1) (n k : ℕ) : Data :=
  MarkedShift.shiftData (phase n k : ℝ) (F.P (n + 1) (k + 1))

/-- Data not implied by coherent metric/range reachability, synchronized with
  the physical capstone package carrying the actual finite rear tubes.

  The significant retained fields are `terminalPhase`, `kinematics`,
  `row_tendsto`, and `physicalFront_curvature`.  `grid_eq` is only structural:
  it identifies the coherent grid with the presented array already stored in
  `baseInput`, so no duplicate quantitative tube callbacks are needed.
  -/
structure Input
      (R : RecostClosingOutput J O)
      (baseInput : PhysicalBaseInput R)
      (F : System (base R) R.error) (X : ℕ → Data) where
    grid_eq : ∀ n k, F.P n k = baseInput.core.P n k
    row_tendsto : ∀ n, Tendsto (F.P n) atTop (nhds (X n))
    terminalPhase : ℕ → ℕ → Set.Icc (0 : ℝ) 1
    kinematics : ∀ n k, PhysicalRearLimitKinematics baseInput.kh0
      (F.P n (k + 2)) (physicalFront F terminalPhase n k)
    curvatureBound : ℕ → ℝ
    curvatureBound_nonneg : ∀ n, 0 ≤ curvatureBound n
    physicalFront_curvature : ∀ n k u,
      |dataCurv (physicalFront F terminalPhase n k) u| ≤ curvatureBound n

namespace Input

  variable {R : RecostClosingOutput J O}
    {baseInput : PhysicalBaseInput R}
    {F : System (base R) R.error} {X : ℕ → Data}

  /-- Every positive coherent-grid column is the corresponding physical rear,
  so its ordinary tube is projected from the retained physical package. -/
  theorem ordinaryTube (I : Input R baseInput F X) (n k : ℕ) :
      IsTubeMember
        baseInput.cb 0 baseInput.db (F.P n (k + 1)) := by
    rw [I.grid_eq n (k + 1)]
    simpa only [
      FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray.Array.physicalRear_succ]
      using baseInput.physical.physical.physical_tube n (k + 1)

  /-- The physical row package also supplies the exact perimeter ceiling used
  by the fixed-row steering estimate. -/
  theorem ordinary_perim_le (I : Input R baseInput F X) (n k : ℕ) :
      perim (F.P n (k + 1)) ≤ baseInput.physical.physical.Lmax n := by
    rw [I.grid_eq n (k + 1)]
    simpa only [
      FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray.Array.physicalRear_succ]
      using baseInput.physical.physical.physical_perim_upper n (k + 1)

/-- The normalized terminal phase transports the successor-row tube to the
actual physical front. -/
  theorem physicalFront_tube (I : Input R baseInput F X) (n k : ℕ) :
      IsTubeMember
        baseInput.cb 0 baseInput.db
        (physicalFront F I.terminalPhase n k) :=
  MarkedShift.isTubeMember_shiftData (I.ordinaryTube (n + 1) k)
    (I.terminalPhase n k : ℝ)

  /-- Phase shifting preserves the physical package's successor-row perimeter
  ceiling. -/
  theorem physicalFront_perim_le (I : Input R baseInput F X) (n k : ℕ) :
      perim (physicalFront F I.terminalPhase n k) ≤
        baseInput.physical.physical.Lmax (n + 1) := by
    rw [physicalFront,
      SelectedInverseShiftEquivariance.perim_shiftData
        (I.ordinaryTube (n + 1) k)]
    exact I.ordinary_perim_le (n + 1) k

/-- Tail convergence for the positive columns of a coherent row. -/
  theorem row_tail_tendsto (I : Input R baseInput F X) (n : ℕ) :
    Tendsto (fun k ↦ F.P n (k + 1)) atTop (nhds (X n)) := by
  exact (Filter.tendsto_add_atTop_iff_nat 1).2 (I.row_tendsto n)

/-- Tail convergence after dropping the first two columns of a coherent row. -/
  theorem row_two_tail_tendsto (I : Input R baseInput F X) (n : ℕ) :
    Tendsto (fun k ↦ F.P n (k + 2)) atTop (nhds (X n)) := by
  exact (Filter.tendsto_add_atTop_iff_nat 2).2 (I.row_tendsto n)

/-- Exact diagonal range transport remains available independently of the
physical closure sidecar. -/
  theorem rangeEdge (I : Input R baseInput F X) (n k : ℕ) :
    GeometricUnitTangentRangeEdge (F.P (n + 1) k) (F.P n (k + 1)) :=
  F.rangeEdge n k

/-- Assemble the automatic compactness input for one fixed row. -/
  def toFixedRowInput (I : Input R baseInput F X) (n : ℕ) :
      FixedRowInput baseInput.kh0 baseInput.cb baseInput.db
        (X n) (X (n + 1)) where
  rearN := fun k ↦ F.P n (k + 2)
  baseFrontN := fun k ↦ F.P (n + 1) (k + 1)
  physicalFrontN := fun k ↦ physicalFront F I.terminalPhase n k
  phaseSidecar :=
    { phase := I.terminalPhase n
      front_eq := fun _ ↦ rfl }
  kinematics := I.kinematics n
  rear_tube := fun k ↦ I.ordinaryTube n (k + 1)
  physicalFront_tube := I.physicalFront_tube n
  rear_tendsto := I.row_two_tail_tendsto n
  baseFront_tendsto := I.row_tail_tendsto (n + 1)
  steeringLip := exists_steeringLip_of_curvatureBounds
    (I.kinematics n) baseInput.cb_pos
    (I.physicalFront_tube n) (I.curvatureBound_nonneg n)
    (I.physicalFront_perim_le n) (I.physicalFront_curvature n)

/-- All coherent rows produce the automatic fixed-row inputs expected by the
smooth physical capstone. -/
  def fixedRowInputs (I : Input R baseInput F X) : ∀ n,
      FixedRowInput baseInput.kh0 baseInput.cb baseInput.db
        (X n) (X (n + 1)) :=
  I.toFixedRowInput

end Input

end CoherentPhaseReachableMetricRangeAutomaticClosure
