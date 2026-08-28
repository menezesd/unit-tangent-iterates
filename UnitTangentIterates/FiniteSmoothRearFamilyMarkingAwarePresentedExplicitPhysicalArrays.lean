import UnitTangentIterates.GenericVariableTerminalDirectCapstoneExplicitFront
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminal
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
import UnitTangentIterates.RichFamilyPhysicalMarkingIntegration

/-!
# Explicit physical arrays from theorem-produced presented rows

Each presented output retains three distinct data: its constant-speed physical
terminal base, its selected marked rear, and its canonical ordinary physical
front.  This module packages those retained witnesses without identifying any
of the three arrays.  Uniform ordinary-tube and rowwise size bounds remain
explicit inputs because they are not consequences of range equality.
-/

noncomputable section

open Filter Topology MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  NormalizedTerminalMarkingComposition
  RichFamilyPhysicalMarkingIntegration

/-- The exact endpoint bound retained by a theorem-produced presented row. -/
def intrinsicEndpointCap
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base)
      (bound := bound) E}
    (O : PresentedOutputCore E B) : ℝ :=
  MarkingDeviationC2.markingC2Bound
    (2 * B.Lmax * rearKappa1 kh * O.chosen.Delta.cost)
    (MarkingFlowDefectC2.flowDefectC1Int (rearPeriod A 0)
      (rearKappa1 kh * O.chosen.Delta.cost))
    (MarkingFlowDefectC2.flowDefectC2Int (rearPeriod A 0)
      (rearKappa1 kh * O.chosen.Delta.cost)
      (rearKappa2 kh * O.chosen.Delta.cost))
    B.physical.L B.physical.kb B.physical.kL

/-- A dependency-free row witness extracted from `PresentedOutputCore`. -/
structure RowWitness (kh cap : ℝ) where
  base : Data
  rear : Data
  front : Data
  lambda : ℝ
  Lambda : ℝ
  marking : NormalizedC2Marking base rear lambda Lambda
  kinematics : PhysicalRearLimitKinematics kh base front
  endpoint_dist : dist base rear ≤ cap

namespace RowWitness

/-- Retain exactly the three physical/marked data and their certified links. -/
def ofPresentedOutput
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base)
      (bound := bound) E}
    (O : PresentedOutputCore E B) :
    RowWitness kh (intrinsicEndpointCap O) where
  base := base
  rear := O.jets.rear
  front := B.frontData
  lambda := B.lambda
  Lambda := B.Lambda
  marking :=
    { lambda_pos := B.lambda_pos
      marking := O.marking
      ddpsi := O.ddpsi
      psi_deriv := O.psi_deriv
      dpsi_deriv := O.dpsi_deriv
      ddpsi_cont := O.ddpsi_cont
      psi_zero := O.psi_zero }
  kinematics := O.frontKinematics
  endpoint_dist := by
    simpa [dist_comm, intrinsicEndpointCap] using O.endpoint_dist

end RowWitness

/-- A two-dimensional family of retained presented-row witnesses. -/
structure RowFamily (Q : ℕ → Data) (kh : ℝ) (cap : ℕ → ℕ → ℝ) where
  row : ∀ n k, RowWitness kh (cap n k)

namespace RowFamily

variable {Q : ℕ → Data} {kh : ℝ} {cap : ℕ → ℕ → ℝ}

/-- Intrinsic ordinary rear bases, with the configured datum at depth zero. -/
def bases (W : RowFamily Q kh cap) : ℕ → ℕ → Data
  | n, 0 => Q n
  | n, k + 1 => (W.row n k).base

/-- Actual selected marked terminals, with the configured datum at depth zero. -/
def presented (W : RowFamily Q kh cap) : ℕ → ℕ → Data
  | n, 0 => Q n
  | n, k + 1 => (W.row n k).rear

/-- Canonical ordinary fronts.  Row zero is unused by the mixed edge and is
filled by `Q 0`; row `n+1`, depth `k` is the front retained by row `n,k`. -/
def fronts (W : RowFamily Q kh cap) : ℕ → ℕ → Data
  | 0, _ => Q 0
  | n + 1, k => (W.row n k).front

/-- The endpoint cap displayed at the same depth as the physical/marked pair. -/
def displayedCap (_W : RowFamily Q kh cap) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | n, k + 1 => cap n k

@[simp] theorem bases_zero (W : RowFamily Q kh cap) (n : ℕ) :
    W.bases n 0 = Q n := rfl

@[simp] theorem presented_zero (W : RowFamily Q kh cap) (n : ℕ) :
    W.presented n 0 = Q n := rfl

/-- Exact direct markings from intrinsic physical bases to actual terminals. -/
def directMarkings (W : RowFamily Q kh cap) :
    DirectPhysicalTerminalMarkingFamily W.bases W.presented where
  lambda n k := match k with
    | 0 => 1
    | k + 1 => (W.row n k).lambda
  Lambda n k := match k with
    | 0 => 1
    | k + 1 => (W.row n k).Lambda
  marking n k := by
    cases k with
    | zero => exact NormalizedC2Marking.refl (Q n)
    | succ k => exact (W.row n k).marking

/-- Exact mixed rear/front kinematics, with no equality between the front and
the marked terminal. -/
def mixedKinematics (W : RowFamily Q kh cap) :
    MixedFinitePhysicalRearKinematics kh W.bases W.fronts where
  stage n k := ⟨(W.row n k).kinematics⟩

/-- The retained endpoint estimate at every displayed depth. -/
theorem endpoint_dist_le_displayedCap (W : RowFamily Q kh cap) :
    ∀ n k, dist (W.bases n k) (W.presented n k) ≤ W.displayedCap n k := by
  intro n k
  cases k with
  | zero => simp [bases, presented, displayedCap]
  | succ k => exact (W.row n k).endpoint_dist

/-- Assemble the row bounds.  The ordinary tube, perimeter, and acceleration
bounds are truthful explicit inputs; the physical-to-presented distance is
the retained endpoint cap. -/
def physicalRowBounds
    (W : RowFamily Q kh cap) {cb db : ℝ}
    (Lmin Lmax Ab r : ℕ → ℝ)
    (hLmin : ∀ n, 0 < Lmin n)
    (hAb : ∀ n, 0 ≤ Ab n) (hr : ∀ n, 0 ≤ r n)
    (hbaseTube : ∀ n k, IsTubeMember cb 0 db (W.bases n k))
    (hperimLower : ∀ n k, Lmin n ≤ perim (W.bases n k))
    (hperimUpper : ∀ n k, perim (W.bases n k) ≤ Lmax n)
    (hacc : ∀ n k u, ‖(W.bases n k).2.2 u‖ ≤ Ab n)
    (hcap : ∀ n k, W.displayedCap n k ≤ r n) :
    PhysicalRowBounds W.bases W.presented cb db where
  Lmin := Lmin
  Lmax := Lmax
  Ab := Ab
  r := r
  Lmin_pos := hLmin
  Ab_nonneg := hAb
  r_nonneg := hr
  physical_tube := hbaseTube
  physical_perim_lower := hperimLower
  physical_perim_upper := hperimUpper
  physical_acc := hacc
  endpoint_dist := fun n k =>
    (W.endpoint_dist_le_displayedCap n k).trans (hcap n k)

/-- Endpoint caps tending to zero give exactly the physical-defect convergence
required by the explicit-front direct capstone. -/
theorem physicalDefect_tendsto
    (W : RowFamily Q kh cap)
    (hcap : ∀ n, Tendsto (W.displayedCap n) atTop (nhds 0)) :
    ∀ n, Tendsto
      (fun k ↦ dist (W.bases n k) (W.presented n k)) atTop (nhds 0) := by
  intro n
  exact squeeze_zero (fun _ ↦ dist_nonneg)
    (W.endpoint_dist_le_displayedCap n) (hcap n)

/-- All explicit physical-array data consumed by
`GenericVariableTerminalDirectCapstoneExplicitFront`. -/
structure Package (W : RowFamily Q kh cap) (cb db cp dp : ℝ) where
  markings : DirectPhysicalTerminalMarkingFamily W.bases W.presented
  physical : PhysicalRowBounds W.bases W.presented cb db
  mixed : MixedFinitePhysicalRearKinematics kh W.bases W.fronts
  frontTube : ∀ n k, IsTubeMember cp 0 dp (W.fronts n k)
  physicalDefect : ∀ n, Tendsto
    (fun k ↦ dist (W.bases n k) (W.presented n k)) atTop (nhds 0)

/-- One-call package constructor from rowwise scalar/ordinary-tube bounds. -/
def package
    (W : RowFamily Q kh cap) {cb db cp dp : ℝ}
    (Lmin Lmax Ab r : ℕ → ℝ)
    (hLmin : ∀ n, 0 < Lmin n)
    (hAb : ∀ n, 0 ≤ Ab n) (hr : ∀ n, 0 ≤ r n)
    (hbaseTube : ∀ n k, IsTubeMember cb 0 db (W.bases n k))
    (hperimLower : ∀ n k, Lmin n ≤ perim (W.bases n k))
    (hperimUpper : ∀ n k, perim (W.bases n k) ≤ Lmax n)
    (hacc : ∀ n k u, ‖(W.bases n k).2.2 u‖ ≤ Ab n)
    (hcapBound : ∀ n k, W.displayedCap n k ≤ r n)
    (hfrontTube : ∀ n k, IsTubeMember cp 0 dp (W.fronts n k))
    (hcapLimit : ∀ n, Tendsto (W.displayedCap n) atTop (nhds 0)) :
    Package W cb db cp dp where
  markings := W.directMarkings
  physical := W.physicalRowBounds Lmin Lmax Ab r hLmin hAb hr hbaseTube
    hperimLower hperimUpper hacc hcapBound
  mixed := W.mixedKinematics
  frontTube := hfrontTube
  physicalDefect := W.physicalDefect_tendsto hcapLimit

end RowFamily

namespace GeometricArray

open FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray

variable {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}

/-- The front indexing required by mixed rear kinematics: cell `(n,k)` has
front row `n+1`.  This is only an index shift of `Array.physicalFront`. -/
def mixedFront
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt) : ℕ → ℕ → Data
  | 0, _ => Q 0
  | n + 1, k => A.physicalFront n k

/-- The endpoint cap displayed beside `A.physicalRear B0` and `P`. -/
def displayedEndpointCap
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | n, k + 1 => intrinsicEndpointCap (A.cell n k).row.output

/-- The concrete array's retained terminal markings, including the external
depth-zero physical identification. -/
def directMarkings
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data)
    (M : DirectPhysicalTerminalMarkingFamily (A.physicalRear B0) P) :
    DirectPhysicalTerminalMarkingFamily (A.physicalRear B0) P := M

/-- The concrete mixed physical-rear kinematics.  The cellwise curvature cap
is required to be the common cap used by the direct capstone. -/
def mixedKinematics
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) {kh0 : ℝ}
    (K : MixedFinitePhysicalRearKinematics kh0
      (A.physicalRear B0) (mixedFront A)) :
    MixedFinitePhysicalRearKinematics kh0 (A.physicalRear B0) (mixedFront A) := K

/-- Cellwise physical edges assemble directly once their stored curvature cap
is identified with the common cap used by the limit theorem. -/
def mixedKinematicsOfCells
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) {kh0 : ℝ}
    (hkh : ∀ n k, (A.cell n k).state.kh = kh0) :
    MixedFinitePhysicalRearKinematics kh0
      (A.physicalRear B0) (mixedFront A) where
  stage n k := by
    have H := (A.cell n k).mixedKinematics
    rw [hkh n k] at H
    simpa [mixedFront, Array.physicalFront, Cell.physicalFront,
      Cell.physicalRear] using H

/-- The actual array endpoint distance is bounded by its displayed retained
marking cap. -/
theorem endpoint_dist_le_displayedEndpointCap
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data)
    (H : ∀ n k, dist (A.physicalRear B0 n k) (P n k) ≤
      displayedEndpointCap A n k) :
    ∀ n k, dist (A.physicalRear B0 n k) (P n k) ≤
      displayedEndpointCap A n k := H

/-- Concrete `PhysicalRowBounds` for `Array.physicalRear B0` and the actual
presented array `P`. -/
def physicalRowBounds
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data)
    (hendpoint : ∀ n k, dist (A.physicalRear B0 n k) (P n k) ≤
      displayedEndpointCap A n k)
    {cb db : ℝ} (Lmin Lmax Ab r : ℕ → ℝ)
    (hLmin : ∀ n, 0 < Lmin n)
    (hAb : ∀ n, 0 ≤ Ab n) (hr : ∀ n, 0 ≤ r n)
    (hbaseTube : ∀ n k, IsTubeMember cb 0 db (A.physicalRear B0 n k))
    (hperimLower : ∀ n k, Lmin n ≤ perim (A.physicalRear B0 n k))
    (hperimUpper : ∀ n k, perim (A.physicalRear B0 n k) ≤ Lmax n)
    (hacc : ∀ n k u, ‖(A.physicalRear B0 n k).2.2 u‖ ≤ Ab n)
    (hcap : ∀ n k, displayedEndpointCap A n k ≤ r n) :
    PhysicalRowBounds (A.physicalRear B0) P cb db where
  Lmin := Lmin
  Lmax := Lmax
  Ab := Ab
  r := r
  Lmin_pos := hLmin
  Ab_nonneg := hAb
  r_nonneg := hr
  physical_tube := hbaseTube
  physical_perim_lower := hperimLower
  physical_perim_upper := hperimUpper
  physical_acc := hacc
  endpoint_dist := fun n k =>
    (hendpoint n k).trans (hcap n k)

/-- A paired endpoint major tending to zero gives the exact physical defect
convergence required downstream. -/
theorem physicalDefect_tendsto
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data)
    (hendpoint : ∀ n k, dist (A.physicalRear B0 n k) (P n k) ≤
      displayedEndpointCap A n k)
    (hcap : ∀ n, Tendsto (displayedEndpointCap A n) atTop (nhds 0)) :
    ∀ n, Tendsto (fun k ↦ dist (A.physicalRear B0 n k) (P n k))
      atTop (nhds 0) := by
  intro n
  exact squeeze_zero (fun _ ↦ dist_nonneg)
    (hendpoint n) (hcap n)

/-- The complete explicit physical-array package for the concrete presented
array.  Uniform ordinary rear/front tube constants remain explicit. -/
structure Package
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (kh0 cb db cp dp : ℝ) where
  markings : DirectPhysicalTerminalMarkingFamily (A.physicalRear B0) P
  physical : PhysicalRowBounds (A.physicalRear B0) P cb db
  mixed : MixedFinitePhysicalRearKinematics kh0
    (A.physicalRear B0) (mixedFront A)
  frontTube : ∀ n k, IsTubeMember cp 0 dp (mixedFront A n k)
  physicalDefect : ∀ n, Tendsto
    (fun k ↦ dist (A.physicalRear B0 n k) (P n k)) atTop (nhds 0)

/-- One-call construction of every physical-array input of the explicit-front
direct capstone. -/
def package
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data)
    {kh0 cb db cp dp : ℝ}
    (hmarkings : DirectPhysicalTerminalMarkingFamily (A.physicalRear B0) P)
    (hmixed : MixedFinitePhysicalRearKinematics kh0
      (A.physicalRear B0) (mixedFront A))
    (hendpoint : ∀ n k, dist (A.physicalRear B0 n k) (P n k) ≤
      displayedEndpointCap A n k)
    (Lmin Lmax Ab r : ℕ → ℝ)
    (hLmin : ∀ n, 0 < Lmin n)
    (hAb : ∀ n, 0 ≤ Ab n) (hr : ∀ n, 0 ≤ r n)
    (hbaseTube : ∀ n k, IsTubeMember cb 0 db (A.physicalRear B0 n k))
    (hperimLower : ∀ n k, Lmin n ≤ perim (A.physicalRear B0 n k))
    (hperimUpper : ∀ n k, perim (A.physicalRear B0 n k) ≤ Lmax n)
    (hacc : ∀ n k u, ‖(A.physicalRear B0 n k).2.2 u‖ ≤ Ab n)
    (hcapBound : ∀ n k, displayedEndpointCap A n k ≤ r n)
    (hfrontTube : ∀ n k, IsTubeMember cp 0 dp (mixedFront A n k))
    (hcapLimit : ∀ n, Tendsto (displayedEndpointCap A n) atTop (nhds 0)) :
    Package A B0 kh0 cb db cp dp where
  markings := directMarkings A B0 hmarkings
  physical := physicalRowBounds A B0 hendpoint Lmin Lmax Ab r hLmin hAb hr
    hbaseTube hperimLower hperimUpper hacc hcapBound
  mixed := mixedKinematics A B0 hmixed
  frontTube := hfrontTube
  physicalDefect := physicalDefect_tendsto A B0 hendpoint hcapLimit

/-- If the external depth-zero rear is the displayed base, the normalized
physical rear array is exactly the displayed array at every depth. -/
theorem physicalRear_eq_presented
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (hB0 : ∀ n, B0 n = P n 0) :
    ∀ n k, A.physicalRear B0 n k = P n k := by
  intro n k
  cases k with
  | zero => exact hB0 n
  | succ k => exact A.physicalRear_succ B0 n k

/-- The displayed physical rear is constant-speed at every depth: at depth
zero this is the configured ordinary tube, and at positive depth it is the
cell's coherently re-marked terminal rear. -/
theorem physicalRear_speedConst
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (hbase : ∀ n, IsTubeMember c 0 dlt (B0 n)) :
    ∀ n k u v,
      ‖(A.physicalRear B0 n k).2.1 u‖ =
        ‖(A.physicalRear B0 n k).2.1 v‖ := by
  intro n k
  cases k with
  | zero => exact (hbase n).speed_const
  | succ k => exact (A.cell n k).physicalRearSpeedConst

/-- The common variable tube becomes an ordinary tube on the physical rear
array because the terminal presentations are constant-speed. -/
def physicalRearTube
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (hB0 : ∀ n, B0 n = P n 0)
    (hbase : ∀ n, IsTubeMember c 0 dlt (B0 n)) (n k : ℕ) :
    IsTubeMember c 0 dlt (A.physicalRear B0 n k) := by
  have H := A.tube n k
  rw [physicalRear_eq_presented A B0 hB0 n k]
  exact
    { hasDerivAt_curve := H.hasDerivAt_curve
      hasDerivAt_vel := H.hasDerivAt_vel
      periodic := H.periodic
      speed_const := by
        simpa [physicalRear_eq_presented A B0 hB0] using
          physicalRear_speedConst A B0 hbase n k
      speed_lb := H.speed_lb
      curv_lb := H.curv_lb
      chord := H.chord }

/-- Common physical row bounds from the scalar column radius.  The only
quantitative input is the already-closed distance from the configured base;
all speed, chord, and endpoint fields are intrinsic to the array. -/
def physicalRowBoundsOfRadius
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (hB0 : ∀ n, B0 n = P n 0)
    (hbase : ∀ n, IsTubeMember c 0 dlt (B0 n))
    (hc : 0 < c) (A0 r : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A0 n) (hr : ∀ n, 0 ≤ r n)
    (hbaseAcc : ∀ n u, ‖(B0 n).2.2 u‖ ≤ A0 n)
    (hdist : ∀ n k, dist (B0 n) (A.physicalRear B0 n k) ≤ r n) :
    PhysicalRowBounds (A.physicalRear B0) P c dlt where
  Lmin := fun _ => c
  Lmax := C
  Ab := fun n => A0 n + r n
  r := fun _ => 0
  Lmin_pos := fun _ => hc
  Ab_nonneg := fun n => add_nonneg (hA0 n) (hr n)
  r_nonneg := fun _ => le_rfl
  physical_tube := physicalRearTube A B0 hB0 hbase
  physical_perim_lower := by
    intro n k
    let H := physicalRearTube A B0 hB0 hbase n k
    simpa [norm_vel_eq_perim H 0] using H.speed_lb 0
  physical_perim_upper := by
    intro n k
    have H := A.tube n k
    have H0 := physicalRearTube A B0 hB0 hbase n k
    rw [physicalRear_eq_presented A B0 hB0 n k]
    simpa [norm_vel_eq_perim H0 0,
      physicalRear_eq_presented A B0 hB0] using H.speed_ub 0
  physical_acc := by
    intro n k u
    have hdiff := VariableMarkedTubeLocalStability.dist_acc_apply_le
      (A.physicalRear B0 n k) (B0 n) u
    have hd : dist (A.physicalRear B0 n k) (B0 n) ≤ r n := by
      simpa [dist_comm] using hdist n k
    calc
      ‖(A.physicalRear B0 n k).2.2 u‖ ≤
          ‖(A.physicalRear B0 n k).2.2 u - (B0 n).2.2 u‖ +
            ‖(B0 n).2.2 u‖ := by
        conv_lhs => rw [← sub_add_cancel
          ((A.physicalRear B0 n k).2.2 u) ((B0 n).2.2 u)]
        exact norm_add_le _ _
      _ ≤ r n + A0 n := add_le_add (hdiff.trans hd) (hbaseAcc n u)
      _ = A0 n + r n := add_comm _ _
  endpoint_dist := by
    intro n k
    rw [physicalRear_eq_presented A B0 hB0]
    simp

/-- Total metric radius forced by the array's own summable row error. -/
def weightedErrorRadius
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt) (n : ℕ) : ℝ :=
  TriangularMarkedPathSchemeVariableTerminal.rowC P0 P1 khat G1 Cg n *
    ∑' k, e n k

theorem weightedErrorRadius_nonnegative
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt) (n : ℕ) :
    0 ≤ weightedErrorRadius A n := by
  exact mul_nonneg
    (NormalPathC2IncrementVariableSpeed.c2ConstVar_nonneg _ _ _ _ _)
    (tsum_nonneg fun k => A.error_nonnegative n k)

/-- Telescoping the genuine array steps bounds every displayed rear by the
row's total weighted error. -/
theorem dist_base_le_weightedErrorRadius
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt) :
    ∀ n k, dist (Q n) (P n k) ≤ weightedErrorRadius A n := by
  intro n k
  let K := TriangularMarkedPathSchemeVariableTerminal.rowC
    P0 P1 khat G1 Cg n
  have hK0 : 0 ≤ K := by
    simpa [K, TriangularMarkedPathSchemeVariableTerminal.rowC] using
      NormalPathC2IncrementVariableSpeed.c2ConstVar_nonneg
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
  have hs : Summable (fun j => K * e n j) :=
    (A.error_summable n).mul_left K
  calc
    dist (Q n) (P n k) = dist (P n 0) (P n k) := by rw [A.base n]
    _ ≤ ∑ j ∈ Finset.range k, dist (P n j) (P n (j + 1)) :=
      dist_le_range_sum_dist (P n) k
    _ ≤ ∑ j ∈ Finset.range k, K * e n j :=
      Finset.sum_le_sum fun j _ => A.stepDistance n j
    _ ≤ ∑' j, K * e n j :=
      hs.sum_le_tsum (Finset.range k)
        (fun j _ => mul_nonneg hK0 (A.error_nonnegative n j))
    _ = weightedErrorRadius A n := by
      rw [tsum_mul_left]
      rfl

/-- Physical row bounds with no independent radius callback: the radius is
the exact summable error mass already stored by the array. -/
def physicalRowBoundsOfError
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (hB0 : ∀ n, B0 n = P n 0)
    (hbase : ∀ n, IsTubeMember c 0 dlt (B0 n))
    (hc : 0 < c) (A0 : ℕ → ℝ) (hA0 : ∀ n, 0 ≤ A0 n)
    (hbaseAcc : ∀ n u, ‖(B0 n).2.2 u‖ ≤ A0 n) :
    PhysicalRowBounds (A.physicalRear B0) P c dlt :=
  physicalRowBoundsOfRadius A B0 hB0 hbase hc A0
    (weightedErrorRadius A) hA0 (weightedErrorRadius_nonnegative A)
    hbaseAcc (by
      intro n k
      rw [physicalRear_eq_presented A B0 hB0]
      calc
        dist (B0 n) (P n k) = dist (Q n) (P n k) := by
          rw [hB0 n, A.base n]
        _ ≤ weightedErrorRadius A n :=
          dist_base_le_weightedErrorRadius A n k)

/-- The acceleration ceiling already carried by a marked datum.  Using the
bounded-continuous-function norm removes an otherwise artificial external
acceleration callback from the physical package. -/
def intrinsicBaseAcceleration (B0 : ℕ → Data) (n : ℕ) : ℝ :=
  ‖(B0 n).2.2‖

theorem intrinsicBaseAcceleration_nonnegative
    (B0 : ℕ → Data) (n : ℕ) :
    0 ≤ intrinsicBaseAcceleration B0 n :=
  norm_nonneg _

theorem acceleration_le_intrinsicBaseAcceleration
    (B0 : ℕ → Data) (n : ℕ) (u : ℝ) :
    ‖(B0 n).2.2 u‖ ≤ intrinsicBaseAcceleration B0 n := by
  exact ((B0 n).2.2).norm_coe_le_norm u

/-- Callback-free physical row bounds.  The base acceleration cap is its
intrinsic sup norm and the row radius is the exact summable marked error
already retained by the array. -/
def physicalRowBoundsOfErrorIntrinsic
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (hB0 : ∀ n, B0 n = P n 0)
    (hbase : ∀ n, IsTubeMember c 0 dlt (B0 n))
    (hc : 0 < c) :
    PhysicalRowBounds (A.physicalRear B0) P c dlt :=
  physicalRowBoundsOfError A B0 hB0 hbase hc
    (intrinsicBaseAcceleration B0)
    (intrinsicBaseAcceleration_nonnegative B0)
    (acceleration_le_intrinsicBaseAcceleration B0)

/-- A common tube on the depth-zero front and on every retained cell front is
exactly a common tube on the mixed front array. -/
theorem mixedFront_tube_of_cells
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    {cp dp : ℝ}
    (hzero : IsTubeMember cp 0 dp (Q 0))
    (hcells : ∀ n k, IsTubeMember cp 0 dp (A.cell n k).physicalFront) :
    ∀ n k, IsTubeMember cp 0 dp (mixedFront A n k) := by
  intro n k
  cases n with
  | zero => exact hzero
  | succ n => exact hcells n k

/-- A variable tube becomes an ordinary tube as soon as its presentation is
known to have constant speed.  This is useful after scalar reindexing: the
final variable tube already has the final common constants, while constant
speed is phase-invariant. -/
def ordinaryTubeOfVariableSpeedConst
    {p : Data} {c C k dlt : ℝ}
    (H : VariableMarkedTube.IsVariableTubeMember c C k dlt p)
    (hspeed : ∀ u v, ‖p.2.1 u‖ = ‖p.2.1 v‖) :
    IsTubeMember c k dlt p where
  hasDerivAt_curve := H.hasDerivAt_curve
  hasDerivAt_vel := H.hasDerivAt_vel
  periodic := H.periodic
  speed_const := hspeed
  speed_lb := H.speed_lb
  curv_lb := H.curv_lb
  chord := H.chord

/-- The phase-normalized presented physical array has identity terminal
markings: no marking is reconstructed from endpoint range equality. -/
def presentedIdentityMarkings
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (hB0 : ∀ n, B0 n = P n 0) :
    DirectPhysicalTerminalMarkingFamily (A.physicalRear B0) P where
  lambda := fun _ _ => 1
  Lambda := fun _ _ => 1
  marking := fun n k => by
    rw [physicalRear_eq_presented A B0 hB0 n k]
    exact NormalizedC2Marking.refl (P n k)

/-- Exact identity of the normalized physical and presented grids makes the
physical marking defect identically zero. -/
theorem presentedPhysicalDefect_tendsto
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (hB0 : ∀ n, B0 n = P n 0) :
    ∀ n, Tendsto (fun k ↦ dist (A.physicalRear B0 n k) (P n k))
      atTop (nhds 0) := by
  intro n
  simpa only [physicalRear_eq_presented A B0 hB0, dist_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- Package the phase-normalized physical sidecars. Ordinary physical row
bounds, mixed rear/front kinematics, and the front tube remain explicit since
they are geometric data not implied by a cyclic phase normalization. -/
def presentedPackage
    (A : Array Q P e P0 P1 khat G1 Cg C c dlt)
    (B0 : ℕ → Data) (hB0 : ∀ n, B0 n = P n 0)
    {kh0 cb db cp dp : ℝ}
    (hphysical : PhysicalRowBounds (A.physicalRear B0) P cb db)
    (hmixed : MixedFinitePhysicalRearKinematics kh0
      (A.physicalRear B0) (mixedFront A))
    (hfrontTube : ∀ n k, IsTubeMember cp 0 dp (mixedFront A n k)) :
    Package A B0 kh0 cb db cp dp where
  markings := presentedIdentityMarkings A B0 hB0
  physical := hphysical
  mixed := hmixed
  frontTube := hfrontTube
  physicalDefect := presentedPhysicalDefect_tendsto A B0 hB0

end GeometricArray

end FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
