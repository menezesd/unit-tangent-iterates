import UnitTangentIterates.ConfiguredRecursiveEdgeGeometricPresentedDirectLimit
import UnitTangentIterates.ConfiguredRecursiveEdgePresentedCapstonePhysicalBounds

noncomputable section

open Function Set Filter MarkedSpace PathMetric
open VariableTerminalRowTubeAdapter ExponentialDiagonalLargeSeparation
  ConfiguredGaugeEndpointLinearRadius
open RichFamilyPhysicalMarkingIntegration

namespace ConfiguredRecursiveEdgeGeometricPresentedPhysicalBounds

open ConfiguredRecursiveEdgeGeometricPresentedCapstone
  ConfiguredRecursiveEdgeGeometricPresentedDirectLimit
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}

/-- The configured row budget closes all physical bounds on the actual
arclength-marked grid. -/
def physicalRowBounds_of_rowBudget_and_caps
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (w : ℕ → ℕ → ℝ)
    (hwnonnegative : ∀ n k, 0 ≤ w n k)
    (hwsummable : ∀ n, Summable (w n))
    (hstep : ∀ n k,
      dist (coherentGrid F n k) (coherentGrid F n (k + 1)) ≤ w n k)
    {c0 d0 A0 r rho upper : ℕ → ℝ}
    (B : RowBudget (fun n => F.markedGrid n 0) P0 P1 khat G1 Cg
      c0 d0 A0 r rho upper c dlt)
    (hweightedRadius : ∀ n, ∑' k, w n k ≤ r n)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (F.markedGrid n 0))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt (F.markedGrid n 0))
    (hbasePerim : ∀ n, c0 n ≤ perim (F.markedGrid n 0))
    (hbaseAcc : ∀ n u, ‖(F.markedGrid n 0).2.2 u‖ ≤ A0 n)
    (markedTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (F.markedGrid n k)) :
    PhysicalRowBounds (coherentGrid F) (coherentGrid F) c dlt := by
  have coherentTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (coherentGrid F n k) := fun n k =>
    isVariableTubeMember_shiftData (markedTube n k) (coherentPhase F n k)
  have hpartial : ∀ n k, (∑ j ∈ Finset.range k, w n j) ≤ r n := by
    intro n k
    exact ((hwsummable n).sum_le_tsum (Finset.range k)
      (fun j _ => hwnonnegative n j)).trans (hweightedRadius n)
  have hcolumn : ∀ n k,
      dist (coherentGrid F n 0) (coherentGrid F n k) ≤ r n := by
    intro n k
    calc
      dist (coherentGrid F n 0) (coherentGrid F n k) ≤
          ∑ j ∈ Finset.range k,
            dist (coherentGrid F n j) (coherentGrid F n (j + 1)) :=
        dist_le_range_sum_dist (coherentGrid F n) k
      _ ≤ ∑ j ∈ Finset.range k, w n j :=
        Finset.sum_le_sum fun j _ => hstep n j
      _ ≤ r n := hpartial n k
  refine
    { Lmin := fun n => c0 n - r n
      Lmax := upper
      Ab := fun n => A0 n + r n
      r := fun _ => 0
      Lmin_pos := B.local_speed_positive
      Ab_nonneg := fun n => add_nonneg (B.acceleration_nonnegative n)
        (B.radius_nonnegative n)
      r_nonneg := fun _ => le_rfl
      physical_tube := ?_
      physical_perim_lower := ?_
      physical_perim_upper := ?_
      physical_acc := ?_
      endpoint_dist := fun _ _ => by simp }
  · intro n k
    cases k with
    | zero => simpa [coherentGrid_zero] using hbaseCommon n
    | succ k =>
        let R := (F.rowFamilyAt k).row n
        let Z := coherentGrid F n (k + 1)
        have hzero : IsTubeMember R.terminalInput.physical.cq 0
            R.terminalInput.physical.dlt Z := by
          dsimp [Z]
          rw [coherentGrid_succ_eq_shift_presented]
          exact MarkedShift.isTubeMember_shiftData
            R.terminalInput.zero_floor_tube (coherentPhase F n k)
        have hvar := VariableMarkedTubeLocalStability.variableTube_of_dist_le
          (hbaseModel n) (coherentTube n (k + 1)).hasDerivAt_curve
          (coherentTube n (k + 1)).hasDerivAt_vel
          (coherentTube n (k + 1)).periodic
          (by simpa [coherentGrid_zero, Z] using hcolumn n (k + 1))
          (hbaseAcc n) (fun u => by simpa using hzero.curv_lb u)
          (B.radius_nonnegative n) (B.local_speed_positive n)
          (B.acceleration_nonnegative n) (B.rho_positive n)
          (B.rho_half n) (B.acceleration_radius n) B.chord_nonnegative
          (B.chord_speed n) (B.chord_margin n)
        exact
          { hasDerivAt_curve := hvar.hasDerivAt_curve
            hasDerivAt_vel := hvar.hasDerivAt_vel
            periodic := hvar.periodic
            speed_const := hzero.speed_const
            speed_lb := fun u => (B.target_speed n).trans (hvar.speed_lb u)
            curv_lb := hvar.curv_lb
            chord := hvar.chord }
  · intro n k
    have hp := abs_perim_sub_le_dist (coherentGrid F n 0) (coherentGrid F n k)
    have hone : perim (coherentGrid F n 0) - perim (coherentGrid F n k) ≤
        dist (coherentGrid F n 0) (coherentGrid F n k) := (le_abs_self _).trans hp
    have hbaseP : c0 n ≤ perim (coherentGrid F n 0) := by
      simpa [coherentGrid_zero] using hbasePerim n
    linarith [hone.trans (hcolumn n k), hbaseP]
  · intro n k
    have hp := abs_perim_sub_le_dist (coherentGrid F n k) (coherentGrid F n 0)
    have hone : perim (coherentGrid F n k) - perim (coherentGrid F n 0) ≤
        dist (coherentGrid F n k) (coherentGrid F n 0) := (le_abs_self _).trans hp
    have hd : dist (coherentGrid F n k) (coherentGrid F n 0) ≤ r n := by
      simpa [dist_comm] using hcolumn n k
    have hupper : perim (coherentGrid F n 0) + r n ≤ upper n := by
      simpa [coherentGrid_zero] using B.upper_speed n
    linarith [hone.trans hd, hupper]
  · intro n k u
    have hdiff := VariableMarkedTubeLocalStability.dist_acc_apply_le
      (coherentGrid F n k) (coherentGrid F n 0) u
    have hd : dist (coherentGrid F n k) (coherentGrid F n 0) ≤ r n := by
      simpa [dist_comm] using hcolumn n k
    calc
      ‖(coherentGrid F n k).2.2 u‖ ≤
          ‖(coherentGrid F n k).2.2 u - (coherentGrid F n 0).2.2 u‖ +
            ‖(coherentGrid F n 0).2.2 u‖ := by
        conv_lhs => rw [← sub_add_cancel
          ((coherentGrid F n k).2.2 u) ((coherentGrid F n 0).2.2 u)]
        exact norm_add_le _ _
      _ ≤ r n + A0 n := add_le_add (hdiff.trans hd) (by
        simpa [coherentGrid_zero] using hbaseAcc n u)
      _ = A0 n + r n := add_comm _ _

/-- Row-budget closure of the transition-free direct metric capstone.  The
exact normalization between consecutive source initials and terminal physical
rears is retained in `F`; this theorem makes no claim about how a concrete
provider discharges that construction-core obligation. -/
theorem exists_paperFacingOutput_of_rowBudget_and_caps
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (w : ℕ → ℕ → ℝ)
    (hwnonnegative : ∀ n k, 0 ≤ w n k)
    (hwsummable : ∀ n, Summable (w n))
    (hstep : ∀ n k,
      dist (coherentGrid F n k) (coherentGrid F n (k + 1)) ≤ w n k)
    {c0 d0 A0 r rho upper : ℕ → ℝ}
    (B : RowBudget (fun n => F.markedGrid n 0) P0 P1 khat G1 Cg
      c0 d0 A0 r rho upper c dlt)
    (hweightedRadius : ∀ n, ∑' k, w n k ≤ r n)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (F.markedGrid n 0))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt (F.markedGrid n 0))
    (hbasePerim : ∀ n, c0 n ≤ perim (F.markedGrid n 0))
    (hbaseAcc : ∀ n u, ‖(F.markedGrid n 0).2.2 u‖ ≤ A0 n)
    (markedTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (F.markedGrid n k))
    (hc : 0 < c) (hdlt : 0 < dlt)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range ⇑(coherentGrid F 0 0).1))
    (hQwidth : Width.width (range ⇑(coherentGrid F 0 0).1) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength fun u => (coherentGrid F 0 0).2.1 u)
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (fun n => coherentGrid F n 0) (coherentGrid F)
      w
      dummyP0 dummyZero dummyZero dummyZero dummyZero C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty ((O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (fun n => coherentGrid F n 0) (coherentGrid F)
      w
      dummyP0 dummyZero dummyZero dummyZero dummyZero C c dlt) ×
      PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  have coherentTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (coherentGrid F n k) := fun n k =>
    isVariableTubeMember_shiftData (markedTube n k) (coherentPhase F n k)
  let physical := physicalRowBounds_of_rowBudget_and_caps F w
    hwnonnegative hwsummable hstep B hweightedRadius hbaseModel
    hbaseCommon hbasePerim hbaseAcc markedTube
  exact ConfiguredRecursiveEdgeGeometricPresentedDirectLimit.exists_paperFacingOutput
    F w hwnonnegative hwsummable coherentTube hstep
    physical hc hdlt hc hdirection hQbounded hQwidth hQlength hgap

/-- Concrete dynamic-error specialization.  The row path and geometric row
cap discharge the metric step internally; only summability and the weighted
row-radius budget remain scalar obligations. -/
theorem exists_paperFacingOutput_of_effectiveError
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (endpoint diagonal : ℕ → ℝ)
    (hendpoint : ∀ j, 0 ≤ endpoint j) (hdiagonal : ∀ j, 0 ≤ diagonal j)
    (herror : ∀ n k, e n (k + 1) = diagonal (n + k + 1))
    (hwsummable : ∀ n, Summable
      (effectiveError (P0 := P0) (P1 := P1) (khat := khat)
        (G1 := G1) (Cg := Cg) endpoint diagonal n))
    {c0 d0 A0 r rho upper : ℕ → ℝ}
    (B : RowBudget (fun n => F.markedGrid n 0) P0 P1 khat G1 Cg
      c0 d0 A0 r rho upper c dlt)
    (hweightedRadius : ∀ n, ∑' k,
      effectiveError (P0 := P0) (P1 := P1) (khat := khat)
        (G1 := G1) (Cg := Cg) endpoint diagonal n k ≤ r n)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (F.markedGrid n 0))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt (F.markedGrid n 0))
    (hbasePerim : ∀ n, c0 n ≤ perim (F.markedGrid n 0))
    (hbaseAcc : ∀ n u, ‖(F.markedGrid n 0).2.2 u‖ ≤ A0 n)
    (markedTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (F.markedGrid n k))
    {M : ℝ} (hM : 0 ≤ M)
    (caps : ∀ n k, GeometricPresentedRowCap ((F.rowFamilyAt k).row n) M
      (endpoint n) (diagonal (n + k + 1)))
    (hc : 0 < c) (hdlt : 0 < dlt)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range ⇑(coherentGrid F 0 0).1))
    (hQwidth : Width.width (range ⇑(coherentGrid F 0 0).1) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength fun u => (coherentGrid F 0 0).2.1 u)
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (fun n => coherentGrid F n 0) (coherentGrid F)
      (effectiveError (P0 := P0) (P1 := P1) (khat := khat)
        (G1 := G1) (Cg := Cg) endpoint diagonal)
      dummyP0 dummyZero dummyZero dummyZero dummyZero C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty ((O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (fun n => coherentGrid F n 0) (coherentGrid F)
      (effectiveError (P0 := P0) (P1 := P1) (khat := khat)
        (G1 := G1) (Cg := Cg) endpoint diagonal)
      dummyP0 dummyZero dummyZero dummyZero dummyZero C c dlt) ×
      PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let w := effectiveError (P0 := P0) (P1 := P1) (khat := khat)
    (G1 := G1) (Cg := Cg) endpoint diagonal
  have hwnonnegative : ∀ n k, 0 ≤ w n k := by
    intro n k
    exact mul_nonneg
      (add_nonneg (NormalPathC2IncrementVariableSpeed.c2ConstVar_nonneg
        _ _ _ _ _) (hendpoint n)) (hdiagonal _)
  have coherentTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (coherentGrid F n k) := fun n k =>
    isVariableTubeMember_shiftData (markedTube n k) (coherentPhase F n k)
  have hstep : ∀ n k,
      dist (coherentGrid F n k) (coherentGrid F n (k + 1)) ≤ w n k :=
    step_dist_le_effectiveError F endpoint diagonal herror coherentTube hM caps
  exact exists_paperFacingOutput_of_rowBudget_and_caps F w
    hwnonnegative hwsummable hstep B hweightedRadius hbaseModel hbaseCommon
    hbasePerim hbaseAcc markedTube hc hdlt hdirection hQbounded hQwidth
    hQlength hgap

end ConfiguredRecursiveEdgeGeometricPresentedPhysicalBounds
