import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
import UnitTangentIterates.GenericVariableTerminalDirectCapstoneExplicitFront

/-!
# A coherent array of theorem-produced presented rows

This is the two-dimensional geometric interface missing from the one-dimensional
`GeometricExactFiniteTower`.  It records only exact endpoint identifications.
In particular, it does not insert a path between two differently marked
representatives of the same curve.
-/

noncomputable section

open Set MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray

open FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower

/-- A presented row occupying the `(n,k)` cell of an actual marked array.
The analytic row is retained for its physical estimates, while `path` is its
phase-normalized chosen path.  The range edge is stored directly because the
ordinary terminal front and the normalized next-row datum need agree only up
to a cyclic marking change. -/
structure Cell (P : ℕ → ℕ → Data) (n k : ℕ) where
  state : State
  row : PresentedRow state.source
  kh_nonnegative : 0 ≤ state.kh
  kh_lt_one : state.kh < 1
  selectedStart : Data
  selectedEnd : Data
  path : NormalPath selectedStart selectedEnd
  physicalFrontData : Data
  physicalKinematics : Nonempty
    (PhysicalRearLimitKinematics state.kh (P n (k + 1)) physicalFrontData)
  physicalRearSpeedConst : ∀ u v,
    ‖(P n (k + 1)).2.1 u‖ = ‖(P n (k + 1)).2.1 v‖
  range_edge : GeometricUnitTangentRangeEdge (P (n + 1) k) (P n (k + 1))

/-- The actual chosen path, with its endpoints rewritten to the coherent array. -/
def Cell.stepPath {P : ℕ → ℕ → Data} {n k : ℕ} (R : Cell P n k) :
    NormalPath R.selectedStart R.selectedEnd :=
  R.path

/-- Physical rear retained before the terminal marking is applied. -/
def Cell.physicalRear {P : ℕ → ℕ → Data} {n k : ℕ} (R : Cell P n k) : Data :=
  P n (k + 1)

/-- Ordinary physical front used by the mixed finite-row kinematics. -/
def Cell.physicalFront {P : ℕ → ℕ → Data} {n k : ℕ} (R : Cell P n k) : Data :=
  R.physicalFrontData

/-- The physical edge retained by a cell already uses the same rear and front
markings as the displayed physical arrays. -/
def Cell.mixedKinematics {P : ℕ → ℕ → Data} {n k : ℕ} (R : Cell P n k) :
    Nonempty (PhysicalRearLimitKinematics R.state.kh R.physicalRear R.physicalFront) :=
  R.physicalKinematics

/-- The phase-normalized cell retains its diagonal unit-tangent range edge. -/
theorem Cell.finiteEdge {P : ℕ → ℕ → Data} {n k : ℕ} (R : Cell P n k) :
    GeometricUnitTangentRangeEdge (P (n + 1) k) (P n (k + 1)) :=
  R.range_edge

/-- A coherent infinite array of actual presented rows.  Quantitative path and
tube bounds remain explicit because they are supplied by the independent
stable-component and tube-budget arguments. -/
structure Array
    (Q : ℕ → Data) (P : ℕ → ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  cell : ∀ n k, Cell P n k
  base : ∀ n, P n 0 = Q n
  error_nonnegative : ∀ n k, 0 ≤ e n k
  error_summable : ∀ n, Summable (e n)
  tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k)
  stepDistance : ∀ n k, dist (P n k) (P n (k + 1)) ≤
    TriangularMarkedPathSchemeVariableTerminal.rowC P0 P1 khat G1 Cg n * e n k

/-- Forget analytic construction data and retain exactly the geometric scheme
consumed by the explicit-front direct capstone. -/
def Array.toGeometricScheme
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt) :
    GenericVariableTerminalDirectCapstoneExplicitFront.GeometricDistanceScheme
      Q P e P0 P1 khat G1 Cg C c dlt where
  base := A.base
  error_nonnegative := A.error_nonnegative
  error_summable := A.error_summable
  tube := A.tube
  stepDistance := A.stepDistance
  finiteEdge := fun n k => (A.cell n k).finiteEdge

/-- The retained rear array. Depth zero is external physical input; every
positive-depth rear is the phase-normalized presented datum of the array. -/
def Array.physicalRear
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) : ℕ → ℕ → Data
  | n, 0 => B0 n
  | n, k + 1 => (A.cell n k).physicalRear

/-- The ordinary front array is retained independently from the marked array. -/
def Array.physicalFront
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt) : ℕ → ℕ → Data :=
  fun n k => (A.cell n k).physicalFront

@[simp] theorem Array.physicalRear_succ
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (n k : ℕ) :
    A.physicalRear B0 n (k + 1) = P n (k + 1) := rfl

end FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
