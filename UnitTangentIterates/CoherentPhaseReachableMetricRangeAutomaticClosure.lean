import UnitTangentIterates.CoherentPhaseReachableMetricRange
import UnitTangentIterates.PhysicalRearLocalShiftedStageAutomaticClosure

/-!
# Automatic physical closure from a coherent reachable metric grid

This adapter separates the phase/range bookkeeping already present in
`CoherentPhaseReachableMetricRange.System` from the genuinely physical data
which must be retained by a finite-stage constructor.  For a fixed row `n`,
the rear sequence is `P n (k + 1)` and the unshifted front sequence is
`P (n + 1) (k + 1)`.  A normalized terminal phase supplies the actual front
used by the physical rear kinematics.

The configured row budget proves the common variable-tube bounds.  Constant
speed upgrades those bounds to the ordinary arclength tube, and a rowwise
intrinsic-curvature ceiling gives the common normalized-steering Lipschitz
bound automatically.
-/

noncomputable section

open Filter Function Set Topology MarkedSpace PathMetric

namespace CoherentPhaseReachableMetricRangeAutomaticClosure

open CoherentPhaseReachableMetricRange
  ConfiguredRecursiveEdgeRecostMultiplierClosing
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

/-- Data not implied by coherent metric/range reachability, together with the
routine hypotheses needed to invoke the configured variable-tube theorem.

The significant retained fields are `terminalPhase`, `kinematics`,
`row_tendsto`, `speed_const`, and `physicalFront_curvature`.  The remaining
fields are the finite regularity and base estimates already consumed by
`System.variableTube_next`.
-/
structure Input
    (R : RecostClosingOutput J O)
    (F : System (base R) R.error) (X : ℕ → Data) (kh : ℝ) where
  budget : BudgetType R
  row_tendsto : ∀ n, Tendsto (F.P n) atTop (nhds (X n))
  model_tube : ∀ n, IsTubeMember
    (2 * R.data.Hs 0) 0
    (ConfiguredInductiveTubeBudget.chordBase R.data.model) (base R n)
  model_acc : ∀ n u, ‖(base R n).2.2 u‖ ≤
    ConfiguredInductiveTubeBudget.accBound R.data.model n
  curve_deriv : ∀ n k u, HasDerivAt (⇑(F.P n (k + 1)).1)
    ((F.P n (k + 1)).2.1 u) u
  vel_deriv : ∀ n k u, HasDerivAt (⇑(F.P n (k + 1)).2.1)
    ((F.P n (k + 1)).2.2 u) u
  periodic : ∀ n k, Periodic (⇑(F.P n (k + 1)).1) 1
  curvature_nonneg : ∀ n k u, 0 ≤
    ((starRingEnd ℂ) ((F.P n (k + 1)).2.1 u) *
      (F.P n (k + 1)).2.2 u).im
  speed_const : ∀ n k u v,
    ‖(F.P n (k + 1)).2.1 u‖ = ‖(F.P n (k + 1)).2.1 v‖
  terminalPhase : ℕ → ℕ → Set.Icc (0 : ℝ) 1
  kinematics : ∀ n k, PhysicalRearLimitKinematics kh
    (F.P n (k + 1)) (physicalFront F terminalPhase n k)
  curvatureBound : ℕ → ℝ
  curvatureBound_nonneg : ∀ n, 0 ≤ curvatureBound n
  physicalFront_curvature : ∀ n k u,
    |dataCurv (physicalFront F terminalPhase n k) u| ≤ curvatureBound n

namespace Input

variable {R : RecostClosingOutput J O}
  {F : System (base R) R.error} {X : ℕ → Data} {kh : ℝ}

/-- The coherent row budget supplies the variable tube at every positive
column. -/
theorem variableTube (I : Input R F X kh) (n k : ℕ) :
    IsVariableTubeMember
      (R.data.Hs 0) (upper R n) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (F.P n (k + 1)) :=
  F.variableTube_next R I.budget n k (I.model_tube n) (I.model_acc n)
    (I.curve_deriv n k) (I.vel_deriv n k) (I.periodic n k)
    (I.curvature_nonneg n k)

/-- Constant speed is the only extra field needed to upgrade the configured
variable tube to the arclength-marked tube used by physical rear closure. -/
def ordinaryTube (I : Input R F X kh) (n k : ℕ) :
    IsTubeMember
      (R.data.Hs 0) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (F.P n (k + 1)) := by
  let H := I.variableTube n k
  exact
    { hasDerivAt_curve := H.hasDerivAt_curve
      hasDerivAt_vel := H.hasDerivAt_vel
      periodic := H.periodic
      speed_const := I.speed_const n k
      speed_lb := H.speed_lb
      curv_lb := H.curv_lb
      chord := H.chord }

/-- The normalized terminal phase transports the successor-row tube to the
actual physical front. -/
theorem physicalFront_tube (I : Input R F X kh) (n k : ℕ) :
    IsTubeMember
      (R.data.Hs 0) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (physicalFront F I.terminalPhase n k) :=
  MarkedShift.isTubeMember_shiftData (I.ordinaryTube (n + 1) k)
    (I.terminalPhase n k : ℝ)

/-- The configured successor-row speed ceiling is also a perimeter ceiling
for the shifted physical front. -/
theorem physicalFront_perim_le (I : Input R F X kh) (n k : ℕ) :
    perim (physicalFront F I.terminalPhase n k) ≤ upper R (n + 1) := by
  rw [← norm_vel_eq_perim (I.physicalFront_tube n k) 0]
  simpa [physicalFront, MarkedShift.shiftData, MarkedShift.shiftMap] using
    (I.variableTube (n + 1) k).speed_ub (I.terminalPhase n k : ℝ)

/-- Tail convergence for the positive columns of a coherent row. -/
theorem row_tail_tendsto (I : Input R F X kh) (n : ℕ) :
    Tendsto (fun k ↦ F.P n (k + 1)) atTop (nhds (X n)) := by
  exact (Filter.tendsto_add_atTop_iff_nat 1).2 (I.row_tendsto n)

/-- Exact diagonal range transport remains available independently of the
physical closure sidecar. -/
theorem rangeEdge (I : Input R F X kh) (n k : ℕ) :
    GeometricUnitTangentRangeEdge (F.P (n + 1) k) (F.P n (k + 1)) :=
  F.rangeEdge n k

/-- Assemble the automatic compactness input for one fixed row. -/
def toFixedRowInput (I : Input R F X kh) (n : ℕ) :
    FixedRowInput kh (R.data.Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (X n) (X (n + 1)) where
  rearN := fun k ↦ F.P n (k + 1)
  baseFrontN := fun k ↦ F.P (n + 1) (k + 1)
  physicalFrontN := fun k ↦ physicalFront F I.terminalPhase n k
  phaseSidecar :=
    { phase := I.terminalPhase n
      front_eq := fun _ ↦ rfl }
  kinematics := I.kinematics n
  rear_tube := I.ordinaryTube n
  physicalFront_tube := I.physicalFront_tube n
  rear_tendsto := I.row_tail_tendsto n
  baseFront_tendsto := I.row_tail_tendsto (n + 1)
  steeringLip := exists_steeringLip_of_curvatureBounds
    (I.kinematics n) R.data.separation_zero_pos
    (I.physicalFront_tube n) (I.curvatureBound_nonneg n)
    (I.physicalFront_perim_le n) (I.physicalFront_curvature n)

/-- All coherent rows produce the automatic fixed-row inputs expected by the
smooth physical capstone. -/
def fixedRowInputs (I : Input R F X kh) : ∀ n,
    FixedRowInput kh (R.data.Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (X n) (X (n + 1)) :=
  I.toFixedRowInput

end Input

end CoherentPhaseReachableMetricRangeAutomaticClosure
