import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
import UnitTangentIterates.PhysicalRearKinematicsShift
import UnitTangentIterates.VariableSpeedNormalPathPhaseTransport

/-!
# Infinite phase-coherent array from finite correlated successors

The finite row constructor produces intrinsic marked initials.  A successor
initial is generally a cyclic re-marking of the preceding selected rear, not
the same marked datum.  This module accumulates those explicitly supplied
phases, shifts each whole chosen path, and obtains an exact horizontal chain.
Only range equality is used in the vertical unit-tangent edge.
-/

noncomputable section

open Set MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray

open FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
open FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray

/-- One theorem-produced finite depth. -/
structure Depth
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ) (k : ℕ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (kh Qmax : ℕ → ℝ) where
  current : ℕ → Data
  column : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax
  ready : ReadyColumn column
  bounds : RowBounds ready

/-- A sound successor supplies the cyclic phase relating its intrinsic row
initial to the preceding row's terminal presented base. The selected rear is
not identified with this base; its endpoint defect is charged separately. -/
structure SuccessorProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (kh Qmax : ℕ → ℝ) where
  next : ∀ k, Depth Q e k P0 P1 khat G1 Cg C c dlt kh Qmax →
    Depth Q e (k + 1) P0 P1 khat G1 Cg C c dlt kh Qmax
  initialPhase : ∀ k
      (D : Depth Q e k P0 P1 khat G1 Cg C c dlt kh Qmax), ℕ → ℝ
  next_initial_eq : ∀ k
      (D : Depth Q e k P0 P1 khat G1 Cg C c dlt kh Qmax) n,
    ((next k D).ready.row n).p =
      MarkedShift.shiftData (initialPhase k D n)
        (D.ready.row n).base

/-- The dependent sequence of finite correlated depths. -/
def depths
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax) :
    ∀ k, Depth Q e k P0 P1 khat G1 Cg C c dlt kh Qmax
  | 0 => B
  | k + 1 => M.next k (depths B M k)

@[simp] theorem depths_zero
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax) :
    depths B M 0 = B := rfl

@[simp] theorem depths_succ
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax) (k : ℕ) :
    depths B M (k + 1) = M.next k (depths B M k) := rfl

/-- The cumulative phase which cancels all successor re-markings. -/
def coherentPhase
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => coherentPhase B M n k - M.initialPhase k (depths B M k) n

/-- The phase-normalized intrinsic initial grid. -/
def P
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : Data :=
  MarkedShift.shiftData (coherentPhase B M n k) ((depths B M k).ready.row n).p

/-- The shifted terminal base of a row is exactly the normalized next-depth
initial. -/
theorem P_succ_eq_shift_base
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) :
    P B M n (k + 1) =
      MarkedShift.shiftData (coherentPhase B M n k)
        ((depths B M k).ready.row n).base := by
  unfold P
  rw [depths_succ, M.next_initial_eq k (depths B M k) n,
    MarkedShift.shiftData_add]
  congr 1
  simp only [coherentPhase]
  ring

/-- The phase-normalized selected endpoint of row `(n,k)`. It is generally
only close to, not equal to, the displayed next-depth base. -/
def selectedRear
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : Data :=
  MarkedShift.shiftData (coherentPhase B M n k)
    ((depths B M k).ready.row n).output.jets.rear

/-- Shifting a datum does not change its curve range. -/
theorem range_shiftData (b : ℝ) (p : Data) :
    range (MarkedShift.shiftData b p).1 = range p.1 := by
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    exact ⟨u + b, rfl⟩
  · rintro z ⟨u, rfl⟩
    refine ⟨u - b, ?_⟩
    simp only [MarkedShift.shiftData_curve]
    congr 1
    ring

/-- Shifting a datum does not change the range of its normalized tangent. -/
theorem range_geometricUnitTangent_shiftData (b : ℝ) (p : Data) :
    range (geometricUnitTangent (MarkedShift.shiftData b p)) =
      range (geometricUnitTangent p) := by
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    exact ⟨u + b, rfl⟩
  · rintro z ⟨u, rfl⟩
    refine ⟨u - b, ?_⟩
    simp [geometricUnitTangent]

/-- The raw intrinsic rows already have the correct diagonal range edge. -/
theorem raw_edge
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ} {k : ℕ}
    (D : Depth Q e k P0 P1 khat G1 Cg C c dlt kh Qmax)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1) (n : ℕ) :
    GeometricUnitTangentRangeEdge (D.ready.row (n + 1)).p
      (D.ready.row n).output.jets.rear := by
  have H := ((D.ready.row n).canonicalTarget (hkh0 n) (hkh1 n)).endpoint_range_edge
  unfold GeometricUnitTangentRangeEdge at H ⊢
  exact (D.ready.row_p_range_current (n + 1)).trans H

/-- The phase-normalized diagonal range edge. -/
theorem coherent_selected_edge
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1) (n k : ℕ) :
    GeometricUnitTangentRangeEdge (P B M (n + 1) k) (selectedRear B M n k) := by
  unfold GeometricUnitTangentRangeEdge
  unfold P selectedRear
  rw [range_shiftData, range_geometricUnitTangent_shiftData]
  exact raw_edge (depths B M k) hkh0 hkh1 n

/-- The shifted chosen row path has exact normalized endpoints. -/
def rowPath
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : NormalPath (P B M n k) (selectedRear B M n k) :=
  MarkedShift.shiftPathOf (coherentPhase B M n k)
    ((depths B M k).ready.row n).output.chosen.Delta
    (fun _ => rfl)
    (fun _ => rfl)

/-- The front phase induced by shifting the ordinary terminal rear through
the cumulative coherent rear phase. -/
def physicalFrontPhase
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : ℝ :=
  let R := (depths B M k).ready.row n
  R.output.frontKinematics.sf
      (perim R.base * coherentPhase B M n k) /
    perim R.terminalInput.frontData

/-- The ordinary row front re-marked by the phase forced by the coherent rear
marking. -/
def physicalFront
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : Data :=
  MarkedShift.shiftData (physicalFrontPhase B M n k)
    ((depths B M k).ready.row n).terminalInput.frontData

/-- Exact physical kinematics after applying the coherent rear phase and its
forced front phase. -/
noncomputable def physicalKinematics
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) :
    PhysicalRearLimitKinematics (kh n) (P B M n (k + 1))
      (physicalFront B M n k) := by
  let R := (depths B M k).ready.row n
  let K := R.output.frontKinematics
  let r := coherentPhase B M n k
  let b := physicalFrontPhase B M n k
  have hfrontPerim : perim R.terminalInput.frontData ≠ 0 :=
    (perim_pos R.cFront_pos R.front_tube).ne'
  have hphase : K.sf (perim R.base * r) =
      perim R.terminalInput.frontData * b := by
    simpa [b, physicalFrontPhase, r, K, R] using
      (mul_div_cancel₀
        (K.sf (perim R.base * r)) hfrontPerim).symm
  have Ks := K.shift R.cFront_pos R.front_tube
    R.terminalInput.physical.cq_pos R.terminalInput.zero_floor_tube
    b r hphase
  rw [P_succ_eq_shift_base]
  simpa [physicalFront, b, r, R, K] using Ks

/-- The induced front re-marking preserves the row's certified ordinary
front tube. -/
theorem physicalFront_tube
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) :
    IsTubeMember ((depths B M k).ready.row n).cFront 0
      ((depths B M k).ready.row n).dFront (physicalFront B M n k) := by
  have H := MarkedShift.isTubeMember_shiftData
    ((depths B M k).ready.row n).front_tube (physicalFrontPhase B M n k)
  rw [((depths B M k).ready.row_kFront_eq_zero n)] at H
  simpa [physicalFront] using H

/-- A source-specific exact phase link to any common-tube presentation
transports that common tube to the coherently corrected physical front. -/
theorem physicalFront_tube_of_eq_shift
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    {cp dp q : ℝ} (n k : ℕ)
    (hfront : ((depths B M k).ready.row n).terminalInput.frontData =
      MarkedShift.shiftData q (P B M (n + 1) k))
    (htube : IsTubeMember cp 0 dp (P B M (n + 1) k)) :
    IsTubeMember cp 0 dp (physicalFront B M n k) := by
  rw [physicalFront, hfront, MarkedShift.shiftData_add]
  exact MarkedShift.isTubeMember_shiftData htube
    (physicalFrontPhase B M n k + q)

/-- The coherently re-marked terminal rear remains a constant-speed ordinary
arclength presentation. -/
theorem physicalRear_speedConst
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : ∀ u v,
    ‖(P B M n (k + 1)).2.1 u‖ = ‖(P B M n (k + 1)).2.1 v‖ := by
  rw [P_succ_eq_shift_base]
  exact (MarkedShift.isTubeMember_shiftData
    ((depths B M k).ready.row n).terminalInput.zero_floor_tube
    (coherentPhase B M n k)).speed_const

@[simp] theorem rowPath_cost
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) :
    (rowPath B M n k).cost =
      ((depths B M k).ready.row n).output.chosen.Delta.cost := by
  exact MarkedShift.cost_shiftPathOf _ _ _ _

/-- The exact phase-normalized cell at `(n,k)`. -/
def cell
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1)
    (hfiniteEdge : ∀ n k, GeometricUnitTangentRangeEdge
      (P B M (n + 1) k) (P B M n (k + 1)))
    (n k : ℕ) : Cell (P B M) n k :=
  { state := (depths B M k).column.state n
    row := (depths B M k).ready.row n
    kh_nonnegative := hkh0 n
    kh_lt_one := hkh1 n
    selectedStart := P B M n k
    selectedEnd := selectedRear B M n k
    path := rowPath B M n k
    physicalFrontData := physicalFront B M n k
    physicalKinematics := ⟨physicalKinematics B M n k⟩
    physicalRearSpeedConst := physicalRear_speedConst B M n k
    range_edge := hfiniteEdge n k }

/-- The error array naturally consumed by the rows: a depth-`k` constructed
row is bounded by the finite-column budget at depth `k+1`. -/
def tailError (e : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ := e n (k + 1)

open FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays

/-- A common cyclic change of marking preserves the ambient marked metric. -/
theorem dist_shiftData (b : ℝ) (p q : Data) :
    dist (MarkedShift.shiftData b p) (MarkedShift.shiftData b q) = dist p q := by
  simp only [Prod.dist_eq]
  congr 1
  · rw [BoundedContinuousFunction.dist_eq_iSup,
      BoundedContinuousFunction.dist_eq_iSup]
    exact (Equiv.addRight b).surjective.iSup_comp
      (fun u => dist (p.1 u) (q.1 u))
  · congr 1
    · rw [BoundedContinuousFunction.dist_eq_iSup,
        BoundedContinuousFunction.dist_eq_iSup]
      exact (Equiv.addRight b).surjective.iSup_comp
        (fun u => dist (p.2.1 u) (q.2.1 u))
    · rw [BoundedContinuousFunction.dist_eq_iSup,
        BoundedContinuousFunction.dist_eq_iSup]
      exact (Equiv.addRight b).surjective.iSup_comp
        (fun u => dist (p.2.2 u) (q.2.2 u))

/-- The displayed grid uses the actual terminal presentation. Depth zero is
the normalized intrinsic initial; depth `k+1` is the terminal base of row
`k`, shifted by exactly the same coherent phase as its selected rear. -/
def presentedP
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax) :
    ℕ → ℕ → Data
  | n, 0 => P B M n 0
  | n, k + 1 => MarkedShift.shiftData (coherentPhase B M n k)
      ((depths B M k).ready.row n).base

@[simp] theorem presentedP_eq_P
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : presentedP B M n k = P B M n k := by
  cases k with
  | zero => rfl
  | succ k => exact (P_succ_eq_shift_base B M n k).symm

/-- The intrinsic terminal marking cap of row `(n,k)`. -/
def endpointCap
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : ℝ :=
  intrinsicEndpointCap ((depths B M k).ready.row n).output

/-- The displayed point is the selected start itself, so there is no incoming
endpoint defect. This zero term is retained for the uniform triangle API. -/
def incomingCap
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (_n _k : ℕ) : ℝ := 0

/-- The summable displayed error consists of the chosen-path budget and the
single outgoing endpoint marking cap. -/
def presentedError
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : ℝ :=
  tailError e n k + incomingCap B M n k + endpointCap B M n k

theorem endpointCap_nonnegative
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : 0 ≤ endpointCap B M n k := by
  exact dist_nonneg.trans
    ((depths B M k).ready.row n).output.endpoint_dist

theorem incomingCap_nonnegative
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) : 0 ≤ incomingCap B M n k := by
  simp [incomingCap]

/-- The displayed terminal base is within the retained endpoint cap of the
selected endpoint, after their common phase shift. -/
theorem selectedEnd_dist_presented
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) :
    dist (selectedRear B M n k) (presentedP B M n (k + 1)) ≤
      endpointCap B M n k := by
  rw [selectedRear, presentedP, dist_shiftData]
  exact ((depths B M k).ready.row n).output.endpoint_dist

/-- At depth zero the displayed and selected starts coincide; at positive
depth their distance is the preceding row's endpoint cap. -/
theorem presented_dist_selectedStart
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) :
    dist (presentedP B M n k) (P B M n k) ≤ incomingCap B M n k := by
  rw [presentedP_eq_P]
  simp [incomingCap]

/-- A terminal oriented reparametrization preserves the underlying curve
range. -/
theorem terminal_curve_range
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ} {k : ℕ}
    (D : Depth Q e k P0 P1 khat G1 Cg C c dlt kh Qmax) (n : ℕ) :
    range ((D.ready.row n).base.1) =
      range ((D.ready.row n).output.jets.rear.1) := by
  let R := D.ready.row n
  have hcont : Continuous R.output.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (R.output.psi_deriv u).continuousAt
  have hmono : StrictMono R.output.marking.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(R.output.psi_deriv u).deriv]
    exact lt_of_lt_of_le R.terminalInput.lambda_pos
      (R.output.marking.lower u)
  have hsurj : Function.Surjective R.output.marking.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcont hmono R.output.marking.translate R.output.psi_zero
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    obtain ⟨u, hu⟩ := hsurj x
    exact ⟨u, by rw [R.output.marking.position u, hu]⟩
  · rintro z ⟨u, rfl⟩
    exact ⟨R.output.marking.psi u, (R.output.marking.position u).symm⟩

/-- The same terminal marking preserves the geometric unit-tangent range. -/
theorem terminal_geometric_range
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ} {k : ℕ}
    (D : Depth Q e k P0 P1 khat G1 Cg C c dlt kh Qmax) (n : ℕ) :
    range (geometricUnitTangent (D.ready.row n).base) =
      range (geometricUnitTangent (D.ready.row n).output.jets.rear) := by
  let R := D.ready.row n
  have hcont : Continuous R.output.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (R.output.psi_deriv u).continuousAt
  have hmono : StrictMono R.output.marking.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(R.output.psi_deriv u).deriv]
    exact lt_of_lt_of_le R.terminalInput.lambda_pos
      (R.output.marking.lower u)
  have hsurj : Function.Surjective R.output.marking.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcont hmono R.output.marking.translate R.output.psi_zero
  have hbase : geometricUnitTangent R.base = normalizedUnitTangent R.base := by
    funext u
    rw [geometricUnitTangent, normalizedUnitTangent,
      norm_vel_eq_perim R.terminalInput.zero_floor_tube u]
  rw [hbase]
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    obtain ⟨u, hu⟩ := hsurj x
    refine ⟨u, ?_⟩
    rw [GaugeRearFamilyVariableTerminal.geometricUnitTangent_eq_normalized_of_orientedReparametrization
      R.terminalInput.physical.cq_pos R.terminalInput.lambda_pos
      R.terminalInput.zero_floor_tube R.output.marking u, hu]
  · rintro z ⟨u, rfl⟩
    exact ⟨R.output.marking.psi u,
      (GaugeRearFamilyVariableTerminal.geometricUnitTangent_eq_normalized_of_orientedReparametrization
        R.terminalInput.physical.cq_pos R.terminalInput.lambda_pos
        R.terminalInput.zero_floor_tube R.output.marking u).symm⟩

/-- Each displayed terminal presentation has the same curve range as the
phase-normalized selected initial at that depth. -/
theorem presented_curve_range_selected
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) :
    range ((presentedP B M n k).1) = range ((P B M n k).1) := by
  rw [presentedP_eq_P]

/-- The selected rear and displayed terminal base have the same normalized
geometric unit-tangent range. -/
theorem selectedEnd_geometric_range_presented
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (n k : ℕ) :
    range (geometricUnitTangent (selectedRear B M n k)) =
      range (geometricUnitTangent (presentedP B M n (k + 1))) := by
  rw [selectedRear, presentedP,
    range_geometricUnitTangent_shiftData, range_geometricUnitTangent_shiftData]
  exact (terminal_geometric_range (depths B M k) n).symm

/-- The displayed diagonal edge is forced by the raw correlated edge,
terminal range preservation, and coherent phase invariance. -/
theorem presented_edge
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1) (n k : ℕ) :
    GeometricUnitTangentRangeEdge
      (presentedP B M (n + 1) k) (presentedP B M n (k + 1)) := by
  unfold GeometricUnitTangentRangeEdge
  exact (presented_curve_range_selected B M (n + 1) k).trans
    ((coherent_selected_edge B M hkh0 hkh1 n k).trans
      (selectedEnd_geometric_range_presented B M n k))

/-- A displayed cell retains the actual chosen selected path while its range
edge is stated for the phase-normalized terminal presentations. -/
def presentedCell
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1)
    (selectedPath : ∀ n k, NormalPath (P B M n k) (selectedRear B M n k))
    (n k : ℕ) : Cell (presentedP B M) n k :=
  { state := (depths B M k).column.state n
    row := (depths B M k).ready.row n
    kh_nonnegative := hkh0 n
    kh_lt_one := hkh1 n
    selectedStart := P B M n k
    selectedEnd := selectedRear B M n k
    path := selectedPath n k
    physicalFrontData := physicalFront B M n k
    physicalKinematics := by
      rw [presentedP_eq_P]
      exact ⟨physicalKinematics B M n k⟩
    physicalRearSpeedConst := by
      rw [presentedP_eq_P]
      exact physicalRear_speedConst B M n k
    range_edge := presented_edge B M hkh0 hkh1 n k }

/-- Assemble the geometric array once summability and tube sidecars are
available.  Geometry and cost are inherited through the common phase shift. -/
def toArray
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1)
    (he0 : ∀ n k, 0 ≤ tailError e n k)
    (hes : ∀ n, Summable (tailError e n))
    (htube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P B M n k))
    (hfiniteEdge : ∀ n k, GeometricUnitTangentRangeEdge
      (P B M (n + 1) k) (P B M n (k + 1)))
    (hstepDistance : ∀ n k, dist (P B M n k) (P B M n (k + 1)) ≤
      TriangularMarkedPathSchemeVariableTerminal.rowC P0 P1 khat G1 Cg n *
        tailError e n k) :
    Array (fun n => (B.ready.row n).p) (P B M) (tailError e)
      P0 P1 khat G1 Cg C c dlt where
  cell := cell B M hkh0 hkh1 hfiniteEdge
  base := fun n => by simp [P, coherentPhase]
  error_nonnegative := he0
  error_summable := hes
  tube := htube
  stepDistance := hstepDistance

/-- Assemble the terminal-presented array. The selected-path metric estimate
is kept separate from the theorem-produced outgoing endpoint cap; the final
step bound is their metric triangle inequality. -/
def toPresentedArray
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1)
    (he0 : ∀ n k, 0 ≤ tailError e n k)
    (hes : ∀ n, Summable (presentedError B M n))
    (htube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt
      (presentedP B M n k))
    (selectedPath : ∀ n k, NormalPath (P B M n k) (selectedRear B M n k))
    (hselectedDistance : ∀ n k,
      dist (P B M n k) (selectedRear B M n k) ≤
        TriangularMarkedPathSchemeVariableTerminal.rowC P0 P1 khat G1 Cg n *
          (selectedPath n k).cost)
    (hselectedCost : ∀ n k, (selectedPath n k).cost ≤ tailError e n k) :
    Array (fun n => (B.ready.row n).p) (presentedP B M)
      (presentedError B M) P0 P1 khat G1 Cg C c dlt where
  cell := presentedCell B M hkh0 hkh1 selectedPath
  base := fun n => by simp [presentedP, P, coherentPhase]
  error_nonnegative := fun n k =>
    add_nonneg (add_nonneg (he0 n k) (incomingCap_nonnegative B M n k))
      (endpointCap_nonnegative B M n k)
  error_summable := hes
  tube := htube
  stepDistance := by
    intro n k
    let K := TriangularMarkedPathSchemeVariableTerminal.rowC
      P0 P1 khat G1 Cg n
    have hK0 : 0 ≤ K := by
      simpa [K, TriangularMarkedPathSchemeVariableTerminal.rowC] using
        c2ConstVar_nonneg (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
    have hK1 : 1 ≤ K := by
      simpa [K, TriangularMarkedPathSchemeVariableTerminal.rowC] using
        one_le_c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
    have hcost' : K * (selectedPath n k).cost ≤
        K * tailError e n k :=
      mul_le_mul_of_nonneg_left (hselectedCost n k) hK0
    have hin := incomingCap_nonnegative B M n k
    have hout := endpointCap_nonnegative B M n k
    calc
      dist (presentedP B M n k) (presentedP B M n (k + 1)) ≤
          dist (presentedP B M n k) (P B M n k) +
            dist (P B M n k) (presentedP B M n (k + 1)) :=
        dist_triangle _ _ _
      _ ≤ dist (presentedP B M n k) (P B M n k) +
          (dist (P B M n k) (selectedRear B M n k) +
            dist (selectedRear B M n k) (presentedP B M n (k + 1))) :=
        by
          simpa only [add_assoc, add_comm, add_left_comm] using
            add_le_add_left
              (dist_triangle (P B M n k) (selectedRear B M n k)
                (presentedP B M n (k + 1)))
              (dist (presentedP B M n k) (P B M n k))
      _ ≤ incomingCap B M n k +
          (K * (selectedPath n k).cost +
            endpointCap B M n k) :=
        add_le_add (presented_dist_selectedStart B M n k)
          (add_le_add (hselectedDistance n k)
            (selectedEnd_dist_presented B M n k))
      _ ≤ incomingCap B M n k +
          (K * tailError e n k + endpointCap B M n k) :=
        by
          simpa only [add_assoc, add_comm, add_left_comm] using
            add_le_add_left
              (add_le_add_right hcost' (endpointCap B M n k))
              (incomingCap B M n k)
      _ ≤ K * presentedError B M n k := by
        dsimp [presentedError]
        nlinarith [mul_nonneg (sub_nonneg.mpr hK1) hin,
          mul_nonneg (sub_nonneg.mpr hK1) hout]

namespace PresentedPhysical

open FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray

/-- The genuinely external physical inputs for a constructed displayed
array. Phase normalization itself supplies the markings and zero defect. -/
structure Sidecars
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {err : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (A : Array Q P err P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (kh0 cb db cp dp : ℝ) where
  physical : RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
    (A.physicalRear B0) P cb db
  mixed : MixedFinitePhysicalRearKinematics kh0
    (A.physicalRear B0) (mixedFront A)
  frontTube : ∀ n k, IsTubeMember cp 0 dp (mixedFront A n k)

/-- One-call construction of the phase-normalized terminal-presented array
and its physical package. The selected paths may be the stable-component
recosted paths; only their exact endpoints, metric-cost estimate, and scalar
cost budget are used here. -/
def toArrayAndPackage
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {kh Qmax : ℕ → ℝ}
    (B : Depth Q e 0 P0 P1 khat G1 Cg C c dlt kh Qmax)
    (M : SuccessorProvider Q e P0 P1 khat G1 Cg C c dlt kh Qmax)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1)
    (he0 : ∀ n k, 0 ≤ tailError e n k)
    (hes : ∀ n, Summable (presentedError B M n))
    (htube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt
      (presentedP B M n k))
    (selectedPath : ∀ n k, NormalPath (P B M n k) (selectedRear B M n k))
    (hselectedDistance : ∀ n k,
      dist (P B M n k) (selectedRear B M n k) ≤
        TriangularMarkedPathSchemeVariableTerminal.rowC P0 P1 khat G1 Cg n *
          (selectedPath n k).cost)
    (hselectedCost : ∀ n k, (selectedPath n k).cost ≤ tailError e n k)
    {kh0 cb db cp dp : ℝ}
    (H : Sidecars
      (toPresentedArray B M hkh0 hkh1 he0 hes htube selectedPath
        hselectedDistance hselectedCost)
      (fun n => presentedP B M n 0) kh0 cb db cp dp) :
    Σ A : Array (fun n => (B.ready.row n).p) (presentedP B M)
        (presentedError B M) P0 P1 khat G1 Cg C c dlt,
      Package A (fun n => presentedP B M n 0) kh0 cb db cp dp := by
  let A := toPresentedArray B M hkh0 hkh1 he0 hes htube selectedPath
    hselectedDistance hselectedCost
  exact ⟨A, presentedPackage A (fun n => presentedP B M n 0)
    (fun _ => rfl) H.physical H.mixed H.frontTube⟩

end PresentedPhysical

end FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray
