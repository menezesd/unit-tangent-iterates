import UnitTangentIterates.NormalizedTerminalMarkingComposition
import UnitTangentIterates.TerminalMarkingCompactness

/-!
# Geometric rowwise bounds for normalized terminal markings

Uniform speed and acceleration bounds recover uniform marking jets directly
from curve geometry.  Thus recursive products of stage distortion constants
are unnecessary for terminal marking compactness.
-/

noncomputable section

open Function MarkedSpace

namespace RowwiseNormalizedMarkingGeometryBounds

open VariableMarkedTube GaugeRearFamilyVariableTerminal
  NormalizedTerminalMarkingComposition

namespace NormalizedC2Marking

theorem dpsi_eq_norm_vel_div
    {base rear : Data} {lambda Lambda cb db L : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hL : 0 < L) (hbase : IsTubeMember cb 0 db base)
    (hperim : perim base = L)
    (u : ℝ) : M.marking.dpsi u = ‖rear.2.1 u‖ / L := by
  have hd : 0 ≤ M.marking.dpsi u :=
    M.lambda_pos.le.trans (M.marking.lower u)
  have hv := congrArg norm (M.marking.velocity u)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd,
    norm_vel_eq_perim hbase, hperim] at hv
  exact (eq_div_iff hL.ne').2 hv.symm

theorem dpsi_lower_of_speed
    {base rear : Data} {lambda Lambda cb db c C dlt L : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hL : 0 < L) (hbase : IsTubeMember cb 0 db base)
    (hperim : perim base = L) (hrear : IsVariableTubeMember c C 0 dlt rear)
    (u : ℝ) : c / L ≤ M.marking.dpsi u := by
  rw [dpsi_eq_norm_vel_div M hL hbase hperim u]
  exact (div_le_div_iff_of_pos_right hL).2 (hrear.speed_lb u)

theorem dpsi_upper_of_speed
    {base rear : Data} {lambda Lambda cb db c C dlt L : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hL : 0 < L) (hbase : IsTubeMember cb 0 db base)
    (hperim : perim base = L) (hrear : IsVariableTubeMember c C 0 dlt rear)
    (u : ℝ) : M.marking.dpsi u ≤ C / L := by
  rw [dpsi_eq_norm_vel_div M hL hbase hperim u]
  exact (div_le_div_iff_of_pos_right hL).2 (hrear.speed_ub u)

theorem dpsi_lower_of_perim_bounds
    {base rear : Data} {lambda Lambda cb db c C dlt Lmin Lmax : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hLmin : 0 < Lmin) (hc : 0 < c)
    (hbase : IsTubeMember cb 0 db base)
    (hperimLower : Lmin ≤ perim base) (hperimUpper : perim base ≤ Lmax)
    (hrear : IsVariableTubeMember c C 0 dlt rear) (u : ℝ) :
    c / Lmax ≤ M.marking.dpsi u := by
  have hp : 0 < perim base := hLmin.trans_le hperimLower
  have hLmax : 0 < Lmax := hp.trans_le hperimUpper
  rw [dpsi_eq_norm_vel_div M hp hbase rfl u]
  apply (div_le_div_iff₀ hLmax hp).2
  calc
    c * perim base ≤ c * Lmax :=
      mul_le_mul_of_nonneg_left hperimUpper hc.le
    _ ≤ ‖rear.2.1 u‖ * Lmax :=
      mul_le_mul_of_nonneg_right (hrear.speed_lb u) hLmax.le

theorem dpsi_upper_of_perim_bounds
    {base rear : Data} {lambda Lambda cb db c C dlt Lmin Lmax : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hLmin : 0 < Lmin) (hc : 0 < c)
    (hbase : IsTubeMember cb 0 db base)
    (hperimLower : Lmin ≤ perim base) (hperimUpper : perim base ≤ Lmax)
    (hrear : IsVariableTubeMember c C 0 dlt rear) (u : ℝ) :
    M.marking.dpsi u ≤ C / Lmin := by
  have hp : 0 < perim base := hLmin.trans_le hperimLower
  have hC : 0 ≤ C := by
    have hlo := hrear.speed_lb 0
    have hup := hrear.speed_ub 0
    linarith
  rw [dpsi_eq_norm_vel_div M hp hbase rfl u]
  apply (div_le_div_iff₀ hp hLmin).2
  calc
    ‖rear.2.1 u‖ * Lmin ≤ C * Lmin :=
      mul_le_mul_of_nonneg_right (hrear.speed_ub u) hLmin.le
    _ ≤ C * perim base := mul_le_mul_of_nonneg_left hperimLower hC

/-- Acceleration chain rule for a normalized C2 marking. -/
theorem acceleration_identity
    {base rear : Data} {lambda Lambda cb db : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hbase : IsTubeMember cb 0 db base)
    (hrearVel : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u) (u : ℝ) :
    rear.2.2 u =
      (M.ddpsi u : ℂ) * base.2.1 (M.marking.psi u) +
        (M.marking.dpsi u : ℂ) ^ 2 * base.2.2 (M.marking.psi u) := by
  have hdC : HasDerivAt (fun x : ℝ => (M.marking.dpsi x : ℂ))
      (M.ddpsi u : ℂ) u := (M.dpsi_deriv u).ofReal_comp
  have hbcomp := (hbase.hasDerivAt_vel (M.marking.psi u)).scomp u
    (M.psi_deriv u)
  have hprod := hdC.mul hbcomp
  have heq : (fun x : ℝ => (M.marking.dpsi x : ℂ)) *
      (⇑base.2.1 ∘ M.marking.psi) = ⇑rear.2.1 :=
    funext fun x => (M.marking.velocity x).symm
  rw [heq] at hprod
  have hu := (hrearVel u).unique hprod
  simpa [smul_eq_mul, mul_assoc, pow_two] using hu

theorem abs_ddpsi_le_of_geometric_bounds
    {base rear : Data}
    {lambda Lambda cb db c C dlt L Ab Ap : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hL : 0 < L) (hAb : 0 ≤ Ab)
    (hbase : IsTubeMember cb 0 db base) (hperim : perim base = L)
    (hbaseAcc : ∀ u, ‖base.2.2 u‖ ≤ Ab)
    (hrear : IsVariableTubeMember c C 0 dlt rear)
    (hrearAcc : ∀ u, ‖rear.2.2 u‖ ≤ Ap) (u : ℝ) :
    |M.ddpsi u| ≤ (Ap + (C / L) ^ 2 * Ab) / L := by
  have hd : 0 ≤ M.marking.dpsi u :=
    M.lambda_pos.le.trans (M.marking.lower u)
  have hdC : M.marking.dpsi u ≤ C / L :=
    dpsi_upper_of_speed M hL hbase hperim hrear u
  have hid := acceleration_identity M hbase hrear.hasDerivAt_vel u
  have heq : (M.ddpsi u : ℂ) * base.2.1 (M.marking.psi u) =
      rear.2.2 u - (M.marking.dpsi u : ℂ) ^ 2 *
        base.2.2 (M.marking.psi u) := by
    rw [hid]
    ring
  apply (le_div_iff₀ hL).2
  calc
    |M.ddpsi u| * L =
        ‖(M.ddpsi u : ℂ) * base.2.1 (M.marking.psi u)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_vel_eq_perim hbase, hperim]
    _ = ‖rear.2.2 u - (M.marking.dpsi u : ℂ) ^ 2 *
          base.2.2 (M.marking.psi u)‖ := congrArg norm heq
    _ ≤ ‖rear.2.2 u‖ + ‖(M.marking.dpsi u : ℂ) ^ 2 *
          base.2.2 (M.marking.psi u)‖ := norm_sub_le _ _
    _ ≤ Ap + (C / L) ^ 2 * Ab := by
      apply add_le_add (hrearAcc u)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hd]
      exact mul_le_mul (pow_le_pow_left₀ hd hdC 2) (hbaseAcc _)
        (norm_nonneg _) (sq_nonneg (C / L))

theorem abs_ddpsi_le_of_row_bounds
    {base rear : Data}
    {lambda Lambda cb db c C dlt Lmin Lmax Ab Ap : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hLmin : 0 < Lmin) (hc : 0 < c) (hAb : 0 ≤ Ab)
    (hbase : IsTubeMember cb 0 db base)
    (hperimLower : Lmin ≤ perim base) (hperimUpper : perim base ≤ Lmax)
    (hbaseAcc : ∀ u, ‖base.2.2 u‖ ≤ Ab)
    (hrear : IsVariableTubeMember c C 0 dlt rear)
    (hrearAcc : ∀ u, ‖rear.2.2 u‖ ≤ Ap) (u : ℝ) :
    |M.ddpsi u| ≤ (Ap + (C / Lmin) ^ 2 * Ab) / Lmin := by
  have hp : 0 < perim base := hLmin.trans_le hperimLower
  have hd : 0 ≤ M.marking.dpsi u :=
    M.lambda_pos.le.trans (M.marking.lower u)
  have hdC : M.marking.dpsi u ≤ C / Lmin :=
    dpsi_upper_of_perim_bounds M hLmin hc hbase hperimLower hperimUpper hrear u
  have hid := acceleration_identity M hbase hrear.hasDerivAt_vel u
  have heq : (M.ddpsi u : ℂ) * base.2.1 (M.marking.psi u) =
      rear.2.2 u - (M.marking.dpsi u : ℂ) ^ 2 *
        base.2.2 (M.marking.psi u) := by
    rw [hid]
    ring
  apply (le_div_iff₀ hLmin).2
  calc
    |M.ddpsi u| * Lmin ≤ |M.ddpsi u| * perim base :=
      mul_le_mul_of_nonneg_left hperimLower (abs_nonneg _)
    _ = ‖(M.ddpsi u : ℂ) * base.2.1 (M.marking.psi u)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_vel_eq_perim hbase]
    _ = ‖rear.2.2 u - (M.marking.dpsi u : ℂ) ^ 2 *
          base.2.2 (M.marking.psi u)‖ := congrArg norm heq
    _ ≤ ‖rear.2.2 u‖ + ‖(M.marking.dpsi u : ℂ) ^ 2 *
          base.2.2 (M.marking.psi u)‖ := norm_sub_le _ _
    _ ≤ Ap + (C / Lmin) ^ 2 * Ab := by
      apply add_le_add (hrearAcc u)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hd]
      exact mul_le_mul (pow_le_pow_left₀ hd hdC 2) (hbaseAcc _)
        (norm_nonneg _) (sq_nonneg (C / Lmin))

/-- Replace construction-specific distortion constants by the sharper
geometric speed ratios. -/
def rebound
    {base rear : Data} {lambda Lambda cb db c C dlt L : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hL : 0 < L) (hc : 0 < c)
    (hbase : IsTubeMember cb 0 db base) (hperim : perim base = L)
    (hrear : IsVariableTubeMember c C 0 dlt rear) :
    NormalizedC2Marking base rear (c / L) (C / L) where
  lambda_pos := div_pos hc hL
  marking :=
    { psi := M.marking.psi
      dpsi := M.marking.dpsi
      position := M.marking.position
      velocity := M.marking.velocity
      translate := M.marking.translate
      lower := dpsi_lower_of_speed M hL hbase hperim hrear
      upper := dpsi_upper_of_speed M hL hbase hperim hrear }
  ddpsi := M.ddpsi
  psi_deriv := M.psi_deriv
  dpsi_deriv := M.dpsi_deriv
  ddpsi_cont := M.ddpsi_cont
  psi_zero := M.psi_zero

/-- Rebound a normalized marking using rowwise lower and upper perimeter
bounds rather than a false common row perimeter. -/
def reboundOfPerimBounds
    {base rear : Data} {lambda Lambda cb db c C dlt Lmin Lmax : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hLmin : 0 < Lmin) (hc : 0 < c)
    (hbase : IsTubeMember cb 0 db base)
    (hperimLower : Lmin ≤ perim base) (hperimUpper : perim base ≤ Lmax)
    (hrear : IsVariableTubeMember c C 0 dlt rear) :
    NormalizedC2Marking base rear (c / Lmax) (C / Lmin) where
  lambda_pos := div_pos hc (hLmin.trans_le hperimLower |>.trans_le hperimUpper)
  marking :=
    { psi := M.marking.psi
      dpsi := M.marking.dpsi
      position := M.marking.position
      velocity := M.marking.velocity
      translate := M.marking.translate
      lower := dpsi_lower_of_perim_bounds M hLmin hc hbase hperimLower
        hperimUpper hrear
      upper := dpsi_upper_of_perim_bounds M hLmin hc hbase hperimLower
        hperimUpper hrear }
  ddpsi := M.ddpsi
  psi_deriv := M.psi_deriv
  dpsi_deriv := M.dpsi_deriv
  ddpsi_cont := M.ddpsi_cont
  psi_zero := M.psi_zero

end NormalizedC2Marking

/-- Geometric hypotheses uniform in recursive depth and allowed to vary by
row.  The stage markings may carry arbitrary construction-specific constants;
`toRowwiseBounds` replaces them by geometric row constants. -/
structure GeometricRowMarkingData (Q P : ℕ → ℕ → Data) where
  cb : ℕ → ℝ
  db : ℕ → ℝ
  dlt : ℕ → ℝ
  Lmin : ℕ → ℝ
  Lmax : ℕ → ℝ
  c : ℕ → ℝ
  C : ℕ → ℝ
  Ab : ℕ → ℝ
  Ap : ℕ → ℝ
  Lmin_pos : ∀ n, 0 < Lmin n
  c_pos : ∀ n, 0 < c n
  Ab_nonneg : ∀ n, 0 ≤ Ab n
  Ap_nonneg : ∀ n, 0 ≤ Ap n
  base_tube : ∀ n k, IsTubeMember (cb n) 0 (db n) (Q n k)
  base_perim_lower : ∀ n k, Lmin n ≤ perim (Q n k)
  base_perim_upper : ∀ n k, perim (Q n k) ≤ Lmax n
  base_acc : ∀ n k u, ‖(Q n k).2.2 u‖ ≤ Ab n
  endpoint_tube : ∀ n k, IsVariableTubeMember (c n) (C n) 0 (dlt n) (P n k)
  endpoint_acc : ∀ n k u, ‖(P n k).2.2 u‖ ≤ Ap n
  stageLambda : ℕ → ℕ → ℝ
  stageUpper : ℕ → ℕ → ℝ
  stageMarking : ∀ n k, NormalizedC2Marking (Q n k) (P n k)
    (stageLambda n k) (stageUpper n k)

namespace GeometricRowMarkingData

def secondBound {Q P : ℕ → ℕ → Data}
    (G : GeometricRowMarkingData Q P) (n : ℕ) : ℝ :=
  (G.Ap n + (G.C n / G.Lmin n) ^ 2 * G.Ab n) / G.Lmin n

/-- Produce exactly the scalar compactness input expected by
`TerminalMarkingCompactness`, uniformly at all depths of each row. -/
def toRowwiseBounds {Q P : ℕ → ℕ → Data}
    (G : GeometricRowMarkingData Q P) :
    RowwiseNormalizedMarkingBounds Q P where
  lambda := fun n => G.c n / G.Lmax n
  Lambda := fun n => G.C n / G.Lmin n
  secondBound := G.secondBound
  lambda_pos := fun n => div_pos (G.c_pos n)
    ((G.Lmin_pos n).trans_le (G.base_perim_lower n 0) |>.trans_le
      (G.base_perim_upper n 0))
  secondBound_nonneg := by
    intro n
    exact div_nonneg
      (add_nonneg (G.Ap_nonneg n)
        (mul_nonneg (sq_nonneg _) (G.Ab_nonneg n))) (G.Lmin_pos n).le
  reparametrization := fun n k =>
    (NormalizedC2Marking.reboundOfPerimBounds (G.stageMarking n k)
      (G.Lmin_pos n) (G.c_pos n) (G.base_tube n k)
      (G.base_perim_lower n k) (G.base_perim_upper n k)
      (G.endpoint_tube n k)).marking
  basepoint := fun n k =>
    (NormalizedC2Marking.reboundOfPerimBounds (G.stageMarking n k)
      (G.Lmin_pos n) (G.c_pos n) (G.base_tube n k)
      (G.base_perim_lower n k) (G.base_perim_upper n k)
      (G.endpoint_tube n k)).psi_zero
  psi_hasDerivAt := fun n k =>
    (NormalizedC2Marking.reboundOfPerimBounds (G.stageMarking n k)
      (G.Lmin_pos n) (G.c_pos n) (G.base_tube n k)
      (G.base_perim_lower n k) (G.base_perim_upper n k)
      (G.endpoint_tube n k)).psi_deriv
  ddpsi := fun n k => (G.stageMarking n k).ddpsi
  dpsi_hasDerivAt := fun n k => (G.stageMarking n k).dpsi_deriv
  ddpsi_bound := fun n k u =>
    NormalizedC2Marking.abs_ddpsi_le_of_row_bounds
      (G.stageMarking n k) (G.Lmin_pos n) (G.c_pos n) (G.Ab_nonneg n)
      (G.base_tube n k) (G.base_perim_lower n k) (G.base_perim_upper n k)
      (G.base_acc n k)
      (G.endpoint_tube n k) (G.endpoint_acc n k) u

/-- Direct compactness output from geometric row bounds.  Finite physical
kinematics act on the ordinary constant-speed family `Q`; the recovered
rowwise marking bounds transport the resulting strict representatives to
the variable family `P`. -/
def orientedRepresentatives_of_geometricRowMarkingData
    {kh cb db : ℝ} {Q P : ℕ → ℕ → Data} {X Y : ℕ → Data}
    (G : GeometricRowMarkingData Q P)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (htube : ∀ n k, IsTubeMember cb 0 db (Q n k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh Q)
    (hX : ∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n)))
    (hY : ∀ n, Filter.Tendsto (P n) Filter.atTop (nhds (Y n))) :
    ∀ n, VariableMarkedTube.OrientedArclengthRepresentative (Y n) :=
  GaugeRearFamilyVariableTerminal.orientedRepresentatives_of_rowwise_marking_bounds
    hkh0 hkh1 hcb hdb htube finite hX hY G.toRowwiseBounds

end GeometricRowMarkingData

end RowwiseNormalizedMarkingGeometryBounds
