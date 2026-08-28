import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteCorrelatedScaledSuccessorTower
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray

/-!
# Presented arrays from the dependent depthwise successor tower

This file keeps the depthwise source-mass invariant inside the dependent
tower.  It does not erase that invariant into an over-strong successor
callback.  The displayed array is normalized by the exact phases carried by
the canonical dependent depths, and its public error may be any summable
majorant of the actual chosen-path budget plus terminal marking cap.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace ConfiguredRecursiveEdgeFiniteCorrelatedDepthwisePresentedArray

open ConfiguredRecursiveEdgeFiniteCorrelatedScaledSuccessorTower
  FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {baseMass : ℕ → ℝ} {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {kh Qmax : ℕ → ℝ}
  {hkh0 : ∀ n, 0 ≤ kh n} {hkh1 : ∀ n, kh n < 1}

abbrev TowerDepth
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (k : ℕ) :=
  depthwiseDepths B M k

/-- Forget only the mass field of one canonical dependent depth. -/
def erasedDepth
    (Z : DepthwiseDepth D baseMass Q e k P0 P1 khat G1 Cg C c dlt kh Qmax) :
    FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray.Depth
      Q e k P0 P1 khat G1 Cg C c dlt kh Qmax where
  current := Z.current
  column := Z.column
  ready := Z.ready
  bounds := Z.bounds

/-- The phase in the exact successor bundle at the canonical depth `k`. -/
def successorPhase
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : ℝ :=
  ((M.input k (depthwiseDepths B M k)).step.phaseBundles.bundle n).initialPhase

/-- Cumulative phase cancelling every canonical successor re-marking. -/
def coherentPhase
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => coherentPhase B M n k - successorPhase B M n k

/-- Exact intrinsic successor coherence along the dependent tower. -/
theorem row_p_succ_eq_shift_base
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) :
    ((depthwiseDepths B M (k + 1)).ready.row n).p =
      MarkedShift.shiftData (successorPhase B M n k)
        ((depthwiseDepths B M k).ready.row n).base := by
  rw [show depthwiseDepths B M (k + 1) =
    depthwiseNextDepth (M.input k (depthwiseDepths B M k)) from rfl]
  rw [ReadyColumn.row_p_eq_initial]
  exact ((M.input k (depthwiseDepths B M k)).step.phaseBundles.bundle n).initial_eq

/-- The normalized intrinsic initial grid. -/
def P
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : Data :=
  MarkedShift.shiftData (coherentPhase B M n k)
    ((depthwiseDepths B M k).ready.row n).p

/-- The normalized selected endpoint of one actual chosen row. -/
def selectedRear
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : Data :=
  MarkedShift.shiftData (coherentPhase B M n k)
    ((depthwiseDepths B M k).ready.row n).output.jets.rear

/-- The next displayed point is exactly the shifted physical terminal base. -/
theorem P_succ_eq_shift_base
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) :
    P B M n (k + 1) = MarkedShift.shiftData (coherentPhase B M n k)
      ((depthwiseDepths B M k).ready.row n).base := by
  unfold P
  rw [row_p_succ_eq_shift_base B M n k, MarkedShift.shiftData_add]
  congr 1
  simp only [coherentPhase]
  ring

/-- The actual chosen path, shifted by the coherent phase. -/
def rowPath
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : NormalPath (P B M n k) (selectedRear B M n k) :=
  MarkedShift.shiftPathOf (coherentPhase B M n k)
    ((depthwiseDepths B M k).ready.row n).output.chosen.Delta
    (fun _ => rfl) (fun _ => rfl)

@[simp] theorem rowPath_cost
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) :
    (rowPath B M n k).cost =
      ((depthwiseDepths B M k).ready.row n).output.chosen.Delta.cost :=
  MarkedShift.cost_shiftPathOf _ _ _ _

/-- Intrinsic endpoint marking cap at one dependent depth. -/
def endpointCap
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : ℝ :=
  intrinsicEndpointCap ((depthwiseDepths B M k).ready.row n).output

theorem endpointCap_nonnegative
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : 0 ≤ endpointCap B M n k :=
  dist_nonneg.trans ((depthwiseDepths B M k).ready.row n).output.endpoint_dist

/-- The endpoint and next displayed base differ by exactly the retained cap. -/
theorem selectedRear_dist_next
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) :
    dist (selectedRear B M n k) (P B M n (k + 1)) ≤ endpointCap B M n k := by
  rw [selectedRear, P_succ_eq_shift_base,
    FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray.dist_shiftData]
  exact ((depthwiseDepths B M k).ready.row n).output.endpoint_dist

/-- The raw diagonal unit-tangent edge at one dependent depth. -/
theorem raw_edge
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) :
    GeometricUnitTangentRangeEdge
      ((depthwiseDepths B M k).ready.row (n + 1)).p
      ((depthwiseDepths B M k).ready.row n).output.jets.rear :=
  FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray.raw_edge
    (erasedDepth (depthwiseDepths B M k)) hkh0 hkh1 n

/-- Exact diagonal range edge after coherent phase normalization. -/
theorem finiteEdge
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) :
    GeometricUnitTangentRangeEdge (P B M (n + 1) k) (P B M n (k + 1)) := by
  unfold GeometricUnitTangentRangeEdge
  rw [P_succ_eq_shift_base]
  unfold P
  rw [
    FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray.range_shiftData,
    FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray.range_geometricUnitTangent_shiftData]
  exact (raw_edge B M n k).trans
    (FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray.terminal_geometric_range
      (erasedDepth (depthwiseDepths B M k)) n).symm

/-- The front phase forced by the coherent rear phase. -/
def physicalFrontPhase
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : ℝ :=
  let R := (depthwiseDepths B M k).ready.row n
  R.output.frontKinematics.sf (perim R.base * coherentPhase B M n k) /
    perim R.terminalInput.frontData

def physicalFront
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : Data :=
  MarkedShift.shiftData (physicalFrontPhase B M n k)
    ((depthwiseDepths B M k).ready.row n).terminalInput.frontData

/-- The forced front phase preserves the row-local ordinary tube. -/
theorem physicalFront_tube
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) :
    IsTubeMember ((depthwiseDepths B M k).ready.row n).cFront 0
      ((depthwiseDepths B M k).ready.row n).dFront (physicalFront B M n k) := by
  have H := MarkedShift.isTubeMember_shiftData
    ((depthwiseDepths B M k).ready.row n).front_tube
    (physicalFrontPhase B M n k)
  rw [((depthwiseDepths B M k).ready.row_kFront_eq_zero n)] at H
  simpa [physicalFront] using H

/-- Exact physical rear/front kinematics after both forced phase changes. -/
noncomputable def physicalKinematics
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) :
    PhysicalRearLimitKinematics (kh n) (P B M n (k + 1))
      (physicalFront B M n k) := by
  let R := (depthwiseDepths B M k).ready.row n
  let K := R.output.frontKinematics
  let r := coherentPhase B M n k
  let b := physicalFrontPhase B M n k
  have hfrontPerim : perim R.terminalInput.frontData ≠ 0 :=
    (perim_pos R.cFront_pos R.front_tube).ne'
  have hphase : K.sf (perim R.base * r) =
      perim R.terminalInput.frontData * b := by
    simpa [b, physicalFrontPhase, r, K, R] using
      (mul_div_cancel₀ (K.sf (perim R.base * r)) hfrontPerim).symm
  have Ks := K.shift R.cFront_pos R.front_tube
    R.terminalInput.physical.cq_pos R.terminalInput.zero_floor_tube
    b r hphase
  rw [P_succ_eq_shift_base]
  simpa [physicalFront, b, r, R, K] using Ks

theorem physicalRear_speedConst
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : ∀ u v,
    ‖(P B M n (k + 1)).2.1 u‖ = ‖(P B M n (k + 1)).2.1 v‖ := by
  rw [P_succ_eq_shift_base]
  exact (MarkedShift.isTubeMember_shiftData
    ((depthwiseDepths B M k).ready.row n).terminalInput.zero_floor_tube
    (coherentPhase B M n k)).speed_const

/-- One exact cell of the canonical dependent tower. -/
def cell
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) : Cell (P B M) n k where
  state := (depthwiseDepths B M k).column.state n
  row := (depthwiseDepths B M k).ready.row n
  kh_nonnegative := hkh0 n
  kh_lt_one := hkh1 n
  selectedStart := P B M n k
  selectedEnd := selectedRear B M n k
  path := rowPath B M n k
  physicalFrontData := physicalFront B M n k
  physicalKinematics := ⟨physicalKinematics B M n k⟩
  physicalRearSpeedConst := physicalRear_speedConst B M n k
  range_edge := finiteEdge B M n k

@[simp] theorem cell_state_kh
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1) (n k : ℕ) :
    (cell B M n k).state.kh = kh n := rfl

/-- Monotone-error array constructor.  Only the genuine displayed-step
estimate is geometric; nonnegativity, summability, and tubes belong to the
chosen public majorant. -/
def toArray
    (B : DepthwiseDepth D baseMass Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : DepthwiseProvider D baseMass Q e P0 P1 khat G1 Cg C c dlt kh Qmax
      hkh0 hkh1)
    {w : ℕ → ℕ → ℝ} {C' : ℕ → ℝ} {c' dlt' : ℝ}
    (hw0 : ∀ n k, 0 ≤ w n k) (hws : ∀ n, Summable (w n))
    (htube : ∀ n k, IsVariableTubeMember c' (C' n) 0 dlt' (P B M n k))
    (hstep : ∀ n k, dist (P B M n k) (P B M n (k + 1)) ≤
      TriangularMarkedPathSchemeVariableTerminal.rowC P0 P1 khat G1 Cg n *
        w n k) :
    Array (fun n => ((depthwiseDepths B M 0).ready.row n).p)
      (P B M) w P0 P1 khat G1 Cg C' c' dlt' where
  cell := cell B M
  base := fun n => by simp [P, coherentPhase]
  error_nonnegative := hw0
  error_summable := hws
  tube := htube
  stepDistance := hstep

end ConfiguredRecursiveEdgeFiniteCorrelatedDepthwisePresentedArray
