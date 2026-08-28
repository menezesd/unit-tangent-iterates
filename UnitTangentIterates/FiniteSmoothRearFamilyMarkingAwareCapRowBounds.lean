import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePhysicalCore
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCappedProvider
import UnitTangentIterates.ConfiguredEnrichedCommonTubeCertificate
import UnitTangentIterates.TerminalPhysicalRowBudgetTube

/-! # Physical row bounds for marking-aware correlated columns -/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePhysicalCore

open ConfiguredGaugeEndpointLinearRadius
  EnrichedPhysicalChosenRichFamily
  RichFamilyPhysicalMarkingIntegration
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  VariableMarkedTube VariableTerminalRowTubeAdapter

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

theorem CapFamily.retained_dist_le
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (R : CapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') (hdiag : ∀ j, 0 ≤ diagonal' j)
    (hbase : ∀ n, 0 ≤ baseConversion n)
    (hendpoint : ∀ n, 0 ≤ endpointConversion n)
    (hcolumn : ∀ n k, dist (Q n) (F.columns k n) ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        baseConversion diagonal' n) (n k : ℕ) :
    dist (Q n) (F.retainedRows n k) ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        (combinedConversion baseConversion endpointConversion) diagonal' n := by
  cases k with
  | zero =>
      change dist (Q n) (Q n) ≤ _
      rw [dist_self]
      exact mul_nonneg (add_nonneg (hbase n) (hendpoint n))
        (ShadowingTails.tail_nonneg (fun j ↦ hdiag (n + j)) 0)
  | succ k =>
      apply terminalBase_dist_le_combinedRadius hsum hdiag hendpoint
        (stageCost := fun n k ↦ diagonal' (n + k))
        (fun _ _ ↦ le_rfl) (n := n) (k := k)
        (hcolumn n (k + 1))
      simpa [ConstructionCore.columns_succ] using
        (R.columnCap k).endpoint_dist n

theorem CapFamily.endpoint_dist_le
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (R : CapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') (hdiag : ∀ j, 0 ≤ diagonal' j)
    (hbase : ∀ n, 0 ≤ baseConversion n)
    (hendpoint : ∀ n, 0 ≤ endpointConversion n) (n k : ℕ) :
    dist (F.retainedRows n k) (F.columns k n) ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        (combinedConversion baseConversion endpointConversion) diagonal' n := by
  cases k with
  | zero =>
      change dist (Q n) (Q n) ≤ _
      rw [dist_self]
      exact mul_nonneg (add_nonneg (hbase n) (hendpoint n))
        (ShadowingTails.tail_nonneg (fun j ↦ hdiag (n + j)) 0)
  | succ k =>
      rw [dist_comm]
      have hcap := (R.columnCap k).endpoint_dist n
      have hfit := columnRadius_add_endpoint_le_combinedRadius
        (C := baseConversion) hsum hdiag hendpoint
        (stageCost := fun n k ↦ diagonal' (n + k))
        (fun _ _ ↦ le_rfl) n k
      have hpath0 : 0 ≤ ExponentialDiagonalLargeSeparation.rowRadius
          baseConversion diagonal' n :=
        mul_nonneg (hbase n)
          (ShadowingTails.tail_nonneg (fun j ↦ hdiag (n + j)) 0)
      simpa [ConstructionCore.columns_succ] using
        hcap.trans (le_trans (le_add_of_nonneg_left hpath0) hfit)

/-- The selected cap family and configured row budget discharge every
physical-row quantitative field. -/
def CapFamily.physicalBounds_of_rowBudget
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (R : CapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') (hdiag : ∀ j, 0 ≤ diagonal' j)
    (hbaseConversion : ∀ n, 0 ≤ baseConversion n)
    (hendpoint : ∀ n, 0 ≤ endpointConversion n)
    {c0 d0 A0 r rho upper : ℕ → ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho upper c dlt)
    (hradius : ∀ n, r n =
      ExponentialDiagonalLargeSeparation.rowRadius
        (combinedConversion baseConversion endpointConversion) diagonal' n)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt (Q n))
    (hbasePerim : ∀ n, c0 n ≤ perim (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hcolumn : ∀ n k, dist (Q n) (F.columns k n) ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        baseConversion diagonal' n) :
    PhysicalRowBounds F.retainedRows (fun n k ↦ F.columns k n) c dlt := by
  let Lmin : ℕ → ℝ := fun n ↦ c0 n - r n
  let Ab : ℕ → ℝ := fun n ↦ A0 n + r n
  have hretained : ∀ n k, dist (Q n) (F.retainedRows n k) ≤ r n := by
    intro n k
    rw [hradius n]
    exact R.retained_dist_le hsum hdiag hbaseConversion hendpoint hcolumn n k
  refine
    { Lmin := Lmin
      Lmax := upper
      Ab := Ab
      r := r
      Lmin_pos := B.local_speed_positive
      Ab_nonneg := fun n ↦ add_nonneg (B.acceleration_nonnegative n)
        (B.radius_nonnegative n)
      r_nonneg := B.radius_nonnegative
      physical_tube := ?_
      physical_perim_lower := ?_
      physical_perim_upper := ?_
      physical_acc := ?_
      endpoint_dist := ?_ }
  · intro n k
    cases k with
    | zero => simpa [ConstructionCore.retainedRows] using hbaseCommon n
    | succ k =>
        apply TerminalPhysicalRowBudgetTube.mem_of_rowBudget B n
          (hbaseModel n) (hbaseAcc n)
          (Classical.choice
            ((F.chosenColumn k).column.gauge n).terminalPhysical_nonempty)
          ((R.columnCap k).terminal_curvature n)
        exact hretained n (k + 1)
  · intro n k
    have hp := abs_perim_sub_le_dist (Q n) (F.retainedRows n k)
    have hone : perim (Q n) - perim (F.retainedRows n k) ≤
        dist (Q n) (F.retainedRows n k) := (le_abs_self _).trans hp
    change c0 n - r n ≤ perim (F.retainedRows n k)
    linarith [hone.trans (hretained n k), hbasePerim n]
  · intro n k
    have hp := abs_perim_sub_le_dist (F.retainedRows n k) (Q n)
    have hone : perim (F.retainedRows n k) - perim (Q n) ≤
        dist (F.retainedRows n k) (Q n) := (le_abs_self _).trans hp
    have hd : dist (F.retainedRows n k) (Q n) ≤ r n := by
      simpa [dist_comm] using hretained n k
    change perim (F.retainedRows n k) ≤ upper n
    linarith [hone.trans hd, B.upper_speed n]
  · intro n k u
    have hdiff := VariableMarkedTubeLocalStability.dist_acc_apply_le
      (F.retainedRows n k) (Q n) u
    have hd : dist (F.retainedRows n k) (Q n) ≤ r n := by
      simpa [dist_comm] using hretained n k
    have htri : ‖(F.retainedRows n k).2.2 u‖ ≤
        ‖(F.retainedRows n k).2.2 u - (Q n).2.2 u‖ +
          ‖(Q n).2.2 u‖ := by
      conv_lhs => rw [← sub_add_cancel
        ((F.retainedRows n k).2.2 u) ((Q n).2.2 u)]
      exact norm_add_le _ _
    change ‖(F.retainedRows n k).2.2 u‖ ≤ A0 n + r n
    calc
      _ ≤ ‖(F.retainedRows n k).2.2 u - (Q n).2.2 u‖ +
          ‖(Q n).2.2 u‖ := htri
      _ ≤ r n + A0 n := add_le_add (hdiff.trans hd) (hbaseAcc n u)
      _ = A0 n + r n := add_comm _ _
  · intro n k
    rw [hradius n]
    exact R.endpoint_dist_le hsum hdiag hbaseConversion hendpoint n k

end FiniteSmoothRearFamilyMarkingAwarePhysicalCore

namespace FiniteSmoothRearFamilyMarkingAwareCappedProvider

open ConfiguredGaugeEndpointLinearRadius
  RichFamilyPhysicalMarkingIntegration
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  VariableMarkedTube VariableTerminalRowTubeAdapter

theorem SlicedCapFamily.retained_dist_le
    {F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (R : SlicedCapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') (hdiag : ∀ j, 0 ≤ diagonal' j)
    (hbase : ∀ n, 0 ≤ baseConversion n)
    (hendpoint : ∀ n, 0 ≤ endpointConversion n)
    (hcolumn : ∀ n k, dist (Q n) (F.columns k n) ≤
      ExponentialDiagonalLargeSeparation.rowRadius baseConversion diagonal' n)
    (n k : ℕ) :
    dist (Q n) (F.retainedRows n k) ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        (combinedConversion baseConversion endpointConversion) diagonal' n := by
  cases k with
  | zero =>
      change dist (Q n) (Q n) ≤ _
      rw [dist_self]
      exact mul_nonneg (add_nonneg (hbase n) (hendpoint n))
        (ShadowingTails.tail_nonneg (fun j ↦ hdiag (n + j)) 0)
  | succ k =>
      apply terminalBase_dist_le_combinedRadius hsum hdiag hendpoint
        (stageCost := fun n k ↦ diagonal' (n + k))
        (fun _ _ ↦ le_rfl) (n := n) (k := k)
        (hcolumn n (k + 1))
      simpa [SlicedConstructionCore.columns_succ] using
        (R.columnCap k).endpoint_dist n

theorem SlicedCapFamily.endpoint_dist_le
    {F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (R : SlicedCapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') (hdiag : ∀ j, 0 ≤ diagonal' j)
    (hbase : ∀ n, 0 ≤ baseConversion n)
    (hendpoint : ∀ n, 0 ≤ endpointConversion n) (n k : ℕ) :
    dist (F.retainedRows n k) (F.columns k n) ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        (combinedConversion baseConversion endpointConversion) diagonal' n := by
  cases k with
  | zero =>
      change dist (Q n) (Q n) ≤ _
      rw [dist_self]
      exact mul_nonneg (add_nonneg (hbase n) (hendpoint n))
        (ShadowingTails.tail_nonneg (fun j ↦ hdiag (n + j)) 0)
  | succ k =>
      rw [dist_comm]
      have hcap := (R.columnCap k).endpoint_dist n
      have hfit := columnRadius_add_endpoint_le_combinedRadius
        (C := baseConversion) hsum hdiag hendpoint
        (stageCost := fun n k ↦ diagonal' (n + k))
        (fun _ _ ↦ le_rfl) n k
      have hpath0 : 0 ≤ ExponentialDiagonalLargeSeparation.rowRadius
          baseConversion diagonal' n :=
        mul_nonneg (hbase n)
          (ShadowingTails.tail_nonneg (fun j ↦ hdiag (n + j)) 0)
      simpa [SlicedConstructionCore.columns_succ] using
        hcap.trans (le_trans (le_add_of_nonneg_left hpath0) hfit)

def SlicedCapFamily.physicalBounds_of_rowBudget
    {F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (R : SlicedCapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') (hdiag : ∀ j, 0 ≤ diagonal' j)
    (hbaseConversion : ∀ n, 0 ≤ baseConversion n)
    (hendpoint : ∀ n, 0 ≤ endpointConversion n)
    {c0 d0 A0 r rho upper : ℕ → ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho upper c dlt)
    (hradius : ∀ n, r n = ExponentialDiagonalLargeSeparation.rowRadius
      (combinedConversion baseConversion endpointConversion) diagonal' n)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt (Q n))
    (hbasePerim : ∀ n, c0 n ≤ perim (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hcolumn : ∀ n k, dist (Q n) (F.columns k n) ≤
      ExponentialDiagonalLargeSeparation.rowRadius baseConversion diagonal' n) :
    PhysicalRowBounds F.retainedRows (fun n k ↦ F.columns k n) c dlt := by
  let Lmin : ℕ → ℝ := fun n ↦ c0 n - r n
  let Ab : ℕ → ℝ := fun n ↦ A0 n + r n
  have hretained : ∀ n k, dist (Q n) (F.retainedRows n k) ≤ r n := by
    intro n k
    rw [hradius n]
    exact R.retained_dist_le hsum hdiag hbaseConversion hendpoint hcolumn n k
  refine
    { Lmin := Lmin
      Lmax := upper
      Ab := Ab
      r := r
      Lmin_pos := B.local_speed_positive
      Ab_nonneg := fun n ↦ add_nonneg (B.acceleration_nonnegative n)
        (B.radius_nonnegative n)
      r_nonneg := B.radius_nonnegative
      physical_tube := ?_
      physical_perim_lower := ?_
      physical_perim_upper := ?_
      physical_acc := ?_
      endpoint_dist := ?_ }
  · intro n k
    cases k with
    | zero => simpa [SlicedConstructionCore.retainedRows] using hbaseCommon n
    | succ k =>
        apply TerminalPhysicalRowBudgetTube.mem_of_rowBudget B n
          (hbaseModel n) (hbaseAcc n)
          (Classical.choice ((F.chosenColumn k).column.gauge n).terminalPhysical_nonempty)
          ((R.columnCap k).terminal_curvature n)
        exact hretained n (k + 1)
  · intro n k
    have hp := abs_perim_sub_le_dist (Q n) (F.retainedRows n k)
    have hone : perim (Q n) - perim (F.retainedRows n k) ≤
        dist (Q n) (F.retainedRows n k) := (le_abs_self _).trans hp
    change c0 n - r n ≤ perim (F.retainedRows n k)
    linarith [hone.trans (hretained n k), hbasePerim n]
  · intro n k
    have hp := abs_perim_sub_le_dist (F.retainedRows n k) (Q n)
    have hone : perim (F.retainedRows n k) - perim (Q n) ≤
        dist (F.retainedRows n k) (Q n) := (le_abs_self _).trans hp
    have hd : dist (F.retainedRows n k) (Q n) ≤ r n := by
      simpa [dist_comm] using hretained n k
    change perim (F.retainedRows n k) ≤ upper n
    linarith [hone.trans hd, B.upper_speed n]
  · intro n k u
    have hdiff := VariableMarkedTubeLocalStability.dist_acc_apply_le
      (F.retainedRows n k) (Q n) u
    have hd : dist (F.retainedRows n k) (Q n) ≤ r n := by
      simpa [dist_comm] using hretained n k
    have htri : ‖(F.retainedRows n k).2.2 u‖ ≤
        ‖(F.retainedRows n k).2.2 u - (Q n).2.2 u‖ + ‖(Q n).2.2 u‖ := by
      conv_lhs => rw [← sub_add_cancel
        ((F.retainedRows n k).2.2 u) ((Q n).2.2 u)]
      exact norm_add_le _ _
    change ‖(F.retainedRows n k).2.2 u‖ ≤ A0 n + r n
    calc
      _ ≤ ‖(F.retainedRows n k).2.2 u - (Q n).2.2 u‖ + ‖(Q n).2.2 u‖ := htri
      _ ≤ r n + A0 n := add_le_add (hdiff.trans hd) (hbaseAcc n u)
      _ = A0 n + r n := add_comm _ _
  · intro n k
    rw [hradius n]
    exact R.endpoint_dist_le hsum hdiag hbaseConversion hendpoint n k

end FiniteSmoothRearFamilyMarkingAwareCappedProvider
