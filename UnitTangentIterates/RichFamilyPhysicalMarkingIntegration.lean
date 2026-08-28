import UnitTangentIterates.RowwiseNormalizedMarkingGeometryBounds
import UnitTangentIterates.ConfiguredFinitePullbackPhysicalRearKinematics
import UnitTangentIterates.VariableMarkedTubeLocalStability

/-!
# Physical-marking integration for rich recursive families

This module aligns a configured finite physical pullback family with the
variable terminal data retained by a rich recursive family.  Physical
perimeter and acceleration bounds are explicit because neither is stored by
the finite-kinematics interface.  Endpoint acceleration is recovered from a
rowwise marked-distance radius.
-/

noncomputable section

open Filter Topology MarkedSpace

namespace RichFamilyPhysicalMarkingIntegration

open VariableMarkedTube
open VariableMarkedTubeLocalStability
open NormalizedTerminalMarkingComposition
open RowwiseNormalizedMarkingGeometryBounds

/-- The genuinely geometric row bounds absent from finite physical
kinematics.  The physical family has one perimeter and one acceleration
ceiling per row, while its variable marked endpoints remain in a fixed marked
ball of radius `r`. -/
structure PhysicalRowBounds
    (B P : ℕ → ℕ → Data) (cb db : ℝ) where
  Lmin : ℕ → ℝ
  Lmax : ℕ → ℝ
  Ab : ℕ → ℝ
  r : ℕ → ℝ
  Lmin_pos : ∀ n, 0 < Lmin n
  Ab_nonneg : ∀ n, 0 ≤ Ab n
  r_nonneg : ∀ n, 0 ≤ r n
  physical_tube : ∀ n k, IsTubeMember cb 0 db (B n k)
  physical_perim_lower : ∀ n k, Lmin n ≤ perim (B n k)
  physical_perim_upper : ∀ n k, perim (B n k) ≤ Lmax n
  physical_acc : ∀ n k u, ‖(B n k).2.2 u‖ ≤ Ab n
  endpoint_dist : ∀ n k, dist (B n k) (P n k) ≤ r n

namespace PhysicalRowBounds

theorem endpoint_acc
    {B P : ℕ → ℕ → Data} {cb db : ℝ}
    (R : PhysicalRowBounds B P cb db) (n k : ℕ) (u : ℝ) :
    ‖(P n k).2.2 u‖ ≤ R.Ab n + R.r n := by
  have hdiff : ‖(P n k).2.2 u - (B n k).2.2 u‖ ≤ R.r n :=
    (dist_acc_apply_le (P n k) (B n k) u).trans (by
      simpa [dist_comm] using R.endpoint_dist n k)
  calc
    ‖(P n k).2.2 u‖ =
        ‖((P n k).2.2 u - (B n k).2.2 u) + (B n k).2.2 u‖ := by ring
    _ ≤ ‖(P n k).2.2 u - (B n k).2.2 u‖ + ‖(B n k).2.2 u‖ :=
      norm_add_le _ _
    _ ≤ R.r n + R.Ab n := add_le_add hdiff (R.physical_acc n k u)
    _ = R.Ab n + R.r n := add_comm _ _

end PhysicalRowBounds

/-- Direct normalized markings from a physical finite representative to the
actual variable terminal in the same row and depth. -/
structure DirectPhysicalTerminalMarkingFamily
    (B P : ℕ → ℕ → Data) where
  lambda : ℕ → ℕ → ℝ
  Lambda : ℕ → ℕ → ℝ
  marking : ∀ n k, NormalizedC2Marking (B n k) (P n k)
    (lambda n k) (Lambda n k)

/-- Assemble geometric row data from direct physical-to-terminal markings. -/
def geometricRowMarkingDataDirect
    {B P : ℕ → ℕ → Data} {C : ℕ → ℝ}
    {c dlt cb db : ℝ} (M : DirectPhysicalTerminalMarkingFamily B P)
    (R : PhysicalRowBounds B P cb db) (hc : 0 < c)
    (hendpointTube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k)) :
    GeometricRowMarkingData B P where
  cb := fun _ => cb
  db := fun _ => db
  dlt := fun _ => dlt
  Lmin := R.Lmin
  Lmax := R.Lmax
  c := fun _ => c
  C := C
  Ab := R.Ab
  Ap := fun n => R.Ab n + R.r n
  Lmin_pos := R.Lmin_pos
  c_pos := fun _ => hc
  Ab_nonneg := R.Ab_nonneg
  Ap_nonneg := fun n => add_nonneg (R.Ab_nonneg n) (R.r_nonneg n)
  base_tube := R.physical_tube
  base_perim_lower := R.physical_perim_lower
  base_perim_upper := R.physical_perim_upper
  base_acc := R.physical_acc
  endpoint_tube := hendpointTube
  endpoint_acc := R.endpoint_acc
  stageLambda := M.lambda
  stageUpper := M.Lambda
  stageMarking := M.marking

/-- Direct-marking form of the all-row oriented representative adapter. -/
def orientedRepresentativesDirect
    {B P : ℕ → ℕ → Data} {C : ℕ → ℝ}
    {c dlt cb db kh : ℝ} (M : DirectPhysicalTerminalMarkingFamily B P)
    (R : PhysicalRowBounds B P cb db)
    (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db)
    (hendpointTube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh B)
    {X Y : ℕ → Data}
    (hX : ∀ n, Tendsto (B n) atTop (nhds (X n)))
    (hY : ∀ n, Tendsto (P n) atTop (nhds (Y n))) :
    ∀ n, OrientedArclengthRepresentative (Y n) :=
  RowwiseNormalizedMarkingGeometryBounds.GeometricRowMarkingData.orientedRepresentatives_of_geometricRowMarkingData
    (geometricRowMarkingDataDirect M R hc hendpointTube) hkh0 hkh1 hcb hdb
      R.physical_tube finite hX hY

/-- Convert a finite physical marking stage to the aligned rich endpoint.
The equality is purely index bookkeeping: physical stage `k` ends at the
rich datum stored in column `k`. -/
def alignedStageMarking
    {B P : ℕ → ℕ → Data} (M : FinitePullbackMarkingFamily B)
    (halign : ∀ n k, B n (k + 1) = P n k) (n k : ℕ) :
    NormalizedC2Marking (B n k) (P n k)
      (M.lambda n k) (M.Lambda n k) := by
  simpa only [halign n k] using M.stage n k

/-- Assemble the geometric row data from a rich variable family, aligned
finite physical markings, and the three physical row bounds. -/
def geometricRowMarkingData
    {B P : ℕ → ℕ → Data} {C : ℕ → ℝ}
    {c dlt cb db : ℝ} (M : FinitePullbackMarkingFamily B)
    (halign : ∀ n k, B n (k + 1) = P n k)
    (R : PhysicalRowBounds B P cb db) (hc : 0 < c)
    (hendpointTube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k)) :
    GeometricRowMarkingData B P where
  cb := fun _ => cb
  db := fun _ => db
  dlt := fun _ => dlt
  Lmin := R.Lmin
  Lmax := R.Lmax
  c := fun _ => c
  C := C
  Ab := R.Ab
  Ap := fun n => R.Ab n + R.r n
  Lmin_pos := R.Lmin_pos
  c_pos := fun _ => hc
  Ab_nonneg := R.Ab_nonneg
  Ap_nonneg := fun n => add_nonneg (R.Ab_nonneg n) (R.r_nonneg n)
  base_tube := R.physical_tube
  base_perim_lower := R.physical_perim_lower
  base_perim_upper := R.physical_perim_upper
  base_acc := R.physical_acc
  endpoint_tube := hendpointTube
  endpoint_acc := R.endpoint_acc
  stageLambda := M.lambda
  stageUpper := M.Lambda
  stageMarking := alignedStageMarking M halign

/-- All-row oriented representatives from configured finite physical
kinematics and the aligned rich terminal markings. -/
def orientedRepresentatives
    {B P : ℕ → ℕ → Data} {C : ℕ → ℝ}
    {c dlt cb db kh : ℝ} (M : FinitePullbackMarkingFamily B)
    (halign : ∀ n k, B n (k + 1) = P n k)
    (R : PhysicalRowBounds B P cb db)
    (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db)
    (hendpointTube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh B)
    {X Y : ℕ → Data}
    (hX : ∀ n, Tendsto (B n) atTop (nhds (X n)))
    (hY : ∀ n, Tendsto (P n) atTop (nhds (Y n))) :
    ∀ n, OrientedArclengthRepresentative (Y n) :=
  RowwiseNormalizedMarkingGeometryBounds.GeometricRowMarkingData.orientedRepresentatives_of_geometricRowMarkingData
    (geometricRowMarkingData M halign R hc hendpointTube) hkh0 hkh1 hcb hdb
      R.physical_tube finite hX hY

end RichFamilyPhysicalMarkingIntegration
