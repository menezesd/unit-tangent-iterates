import UnitTangentIterates.ConfiguredRecursiveEdgePresentedCapstoneAdapter
import UnitTangentIterates.TerminalPhysicalRowBudgetTube
import UnitTangentIterates.VariableTerminalRowTubeStepAdapter

/-!
# Physical bounds from reachable presented row caps

This companion closes the two quantitative interfaces left explicit in the
capstone adapter.  It uses caps only on actually reachable rows: no total
provider on arbitrary correlated columns is introduced.
-/

noncomputable section

open Filter MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePresentedCapstonePhysicalBounds

open ConfiguredRecursiveEdgePresentedCapstoneAdapter
  ConfiguredRecursiveEdgePresentedCapstoneAdapter.RecursiveConstruction
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
  RichFamilyPhysicalMarkingIntegration

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- Reachable row caps and one rowwise scalar ceiling construct all physical
bounds.  The endpoint radius is the exact product of the retained endpoint
coefficient and the scalar ceiling. -/
def physicalRowBounds_of_rowCaps
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    {cb db M : ℝ}
    (baseTube : ∀ n, IsTubeMember cb 0 db (markedGrid F n 0))
    (basePerimLower : ∀ n, 1 ≤ perim (markedGrid F n 0))
    (basePerimUpper : ∀ n, perim (markedGrid F n 0) ≤ Qmax n)
    (baseAcc : ∀ n u, ‖(markedGrid F n 0).2.2 u‖ ≤ Qmax n ^ 2 * khat n)
    (hkhat : ∀ n, 0 ≤ khat n)
    (succCq : ∀ n k, cb ≤
      ((rowFamilyAt F k).row n).terminalInput.physical.cq)
    (succDlt : ∀ n k, db ≤
      ((rowFamilyAt F k).row n).terminalInput.physical.dlt)
    (succKb : ∀ n k,
      ((rowFamilyAt F k).row n).terminalInput.physical.kb ≤ khat n)
    (hM : 0 ≤ M) (endpoint defectMax : ℕ → ℝ)
    (hendpoint : ∀ n, 0 ≤ endpoint n)
    (hdefectMax : ∀ n, 0 ≤ defectMax n)
    (defect : ℕ → ℕ → ℝ)
    (caps : ∀ n k,
      PresentedRowCap ((rowFamilyAt F k).row n)
        M (endpoint n) (defect n k))
    (defect_le : ∀ n k, defect n k ≤ defectMax n) :
    PhysicalRowBounds (rearRows F) (markedGrid F) cb db := by
  apply physicalRowBounds_of_presented F baseTube basePerimLower
    basePerimUpper baseAcc hkhat succCq succDlt succKb
    (fun n => endpoint n * defectMax n)
    (fun n => mul_nonneg (hendpoint n) (hdefectMax n))
  intro n k
  cases k with
  | zero =>
      simpa [rearRows] using mul_nonneg (hendpoint n) (hdefectMax n)
  | succ k =>
      have H := PresentedRowCap.endpoint_dist_le hM (caps n k)
      have H' : dist (rearRows F n (k + 1)) (markedGrid F n (k + 1)) ≤
          endpoint n * defect n k := by
        simpa [rearRows, rearGrid, markedGrid, rowFamilyAt, successorAt,
          RecursivePresentedConstructionCore.state,
          RecursivePresentedSlicedState.next, dist_comm] using H
      exact H'.trans
        (mul_le_mul_of_nonneg_left (defect_le n k) (hendpoint n))

/-- Summability of the same scalar row error makes the physical/marked
endpoint defect vanish.  No second convergence sequence is postulated. -/
theorem physicalDefect_tendsto_of_summable_rowCaps
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    {M : ℝ} (hM : 0 ≤ M) (endpoint : ℕ → ℝ)
    (caps : ∀ n k,
      PresentedRowCap ((rowFamilyAt F k).row n)
        M (endpoint n) (e n (k + 1)))
    (hsummable : ∀ n, Summable (e n)) :
    ∀ n, Tendsto (fun k => dist (rearRows F n k) (markedGrid F n k))
      atTop (nhds 0) := by
  intro n
  apply physicalDefect_tendsto_of_rowCaps F hM endpoint
    (fun n k => e n (k + 1)) caps
  intro row
  have H : Summable (fun k => e row (k + 1)) := by
    simpa [Nat.add_comm] using
      ShadowingTails.summable_shift (hsummable row) 1
  exact H.tendsto_atTop_zero

end ConfiguredRecursiveEdgePresentedCapstonePhysicalBounds

namespace ConfiguredRecursiveEdgePresentedCapstonePhysicalBounds

open ConfiguredGaugeEndpointLinearRadius
  ConfiguredRecursiveEdgePresentedCapstoneAdapter
  ConfiguredRecursiveEdgePresentedCapstoneAdapter.RecursiveConstruction
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
  RichFamilyPhysicalMarkingIntegration
  VariableTerminalRowTubeAdapter
  VariableTerminalRowTubeStepAdapter

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- The configured row budget itself supplies the uniform positive speed and
chord constants for the ordinary presented rears.  Their private existential
chord constants are not compared across rows: common membership is rebuilt
from distance to the strict configured model. -/
def physicalRowBounds_of_rowBudget_and_caps
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (hsum : Summable diagonal') (hdiag : ∀ j, 0 ≤ diagonal' j)
    (hbaseConversion : ∀ n, 0 ≤ baseConversion n)
    (hpathConversion : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤ baseConversion n)
    (hendpoint : ∀ n, 0 ≤ endpointConversion n)
    (herror : ∀ n k, e n (k + 1) = diagonal' (n + (k + 1)))
    {c0 d0 A0 r rho upper : ℕ → ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho upper c dlt)
    (hradius : ∀ n, r n = rowRadius
      (combinedConversion baseConversion endpointConversion) diagonal' n)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt (Q n))
    (hbasePerim : ∀ n, c0 n ≤ perim (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (markedTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (markedGrid F n k))
    {M : ℝ} (hM : 0 ≤ M)
    (caps : ∀ n k, PresentedRowCap ((rowFamilyAt F k).row n) M
      (endpointConversion n) (diagonal' (n + (k + 1)))) :
    PhysicalRowBounds (rearRows F) (markedGrid F) c dlt := by
  let tail : ℕ → ℝ := fun n =>
    ShadowingTails.tail (fun j => diagonal' (n + j)) 0
  have htail0 : ∀ n, 0 ≤ tail n := fun n =>
    ShadowingTails.tail_nonneg (fun j => hdiag (n + j)) 0
  have hsrow : ∀ n, Summable (fun j => diagonal' (n + j)) := by
    intro n
    simpa [Nat.add_comm] using ShadowingTails.summable_shift hsum n
  have hterm : ∀ n k, diagonal' (n + (k + 1)) ≤ tail n := by
    intro n k
    dsimp [tail]
    unfold ShadowingTails.tail
    simpa only [Nat.zero_add] using
      (hsrow n).le_tsum (k + 1) (fun j _ => hdiag (n + j))
  let stepPath : ∀ n k, NormalPath (markedGrid F n k)
      (markedGrid F n (k + 1)) := fun n k => (stage F n k).stage.increment
  have hpartial : ∀ n k,
      (∑ j ∈ Finset.range k, diagonal' (n + (j + 1))) ≤ tail n := by
    intro n k
    have H := (hsrow n).sum_le_tsum (Finset.range (k + 1))
      (fun j _ => hdiag (n + j))
    have Hshift : (∑ j ∈ Finset.range k, diagonal' (n + (j + 1))) ≤
        ∑ j ∈ Finset.range (k + 1), diagonal' (n + j) := by
      rw [Finset.sum_range_succ']
      exact le_add_of_nonneg_right (hdiag n)
    exact Hshift.trans (by simpa [tail, ShadowingTails.tail] using H)
  have hpathRadius : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
          (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤
        rowRadius baseConversion diagonal' n := by
    intro n
    unfold rowRadius
    exact mul_le_mul_of_nonneg_right (hpathConversion n) (htail0 n)
  have hcolumn : ∀ n k, dist (Q n) (markedGrid F n k) ≤
      rowRadius baseConversion diagonal' n := by
    apply markedDist_le_rowRadius_of_steps F.base_eq stepPath
      (fun n k => (markedTube n k).hasDerivAt_curve)
      (fun n k => (markedTube n k).hasDerivAt_vel)
      (fun n k => (stage F n k).stage.increment_geometry)
      (fun n k => ?_) hpartial hpathRadius
    calc
      (stepPath n k).cost ≤ e n (k + 1) :=
        (stage F n k).stage.increment_cost
      _ = diagonal' (n + (k + 1)) := herror n k
  have hcap : ∀ n k,
      dist (markedGrid F n (k + 1)) (rearRows F n (k + 1)) ≤
        endpointConversion n * diagonal' (n + (k + 1)) := by
    intro n k
    have H := PresentedRowCap.endpoint_dist_le hM (caps n k)
    simpa [rearRows, rearGrid, markedGrid, rowFamilyAt, successorAt,
      RecursivePresentedConstructionCore.state,
      RecursivePresentedSlicedState.next] using H
  have hretained : ∀ n k, dist (Q n) (rearRows F n k) ≤ r n := by
    intro n k
    rw [hradius n]
    cases k with
    | zero =>
        rw [show rearRows F n 0 = Q n by
          simpa [rearRows, markedGrid] using F.base_eq n]
        simpa [rowRadius, combinedConversion, tail,
          ExponentialDiagonalLargeSeparation.rowError] using
          mul_nonneg (add_nonneg (hbaseConversion n) (hendpoint n))
            (htail0 n)
    | succ k =>
        calc
          dist (Q n) (rearRows F n (k + 1)) ≤
              dist (Q n) (markedGrid F n (k + 1)) +
                dist (markedGrid F n (k + 1)) (rearRows F n (k + 1)) :=
            dist_triangle _ _ _
          _ ≤ baseConversion n * tail n +
                endpointConversion n * diagonal' (n + (k + 1)) :=
            add_le_add (hcolumn n (k + 1)) (hcap n k)
          _ ≤ baseConversion n * tail n + endpointConversion n * tail n :=
            add_le_add le_rfl
              (mul_le_mul_of_nonneg_left (hterm n k) (hendpoint n))
          _ = rowRadius
              (combinedConversion baseConversion endpointConversion)
              diagonal' n := by
            change baseConversion n * tail n + endpointConversion n * tail n =
              (baseConversion n + endpointConversion n) * tail n
            ring
  refine
    { Lmin := fun n => c0 n - r n
      Lmax := upper
      Ab := fun n => A0 n + r n
      r := r
      Lmin_pos := B.local_speed_positive
      Ab_nonneg := fun n => add_nonneg (B.acceleration_nonnegative n)
        (B.radius_nonnegative n)
      r_nonneg := B.radius_nonnegative
      physical_tube := ?_
      physical_perim_lower := ?_
      physical_perim_upper := ?_
      physical_acc := ?_
      endpoint_dist := ?_ }
  · intro n k
    cases k with
    | zero =>
        rw [show rearRows F n 0 = Q n by
          simpa [rearRows, markedGrid] using F.base_eq n]
        exact hbaseCommon n
    | succ k =>
        let W := (rowFamilyAt F k).row n
        apply TerminalPhysicalRowBudgetTube.mem_of_rowBudget B n
          (hbaseModel n) (hbaseAcc n) W.terminalInput.physical
        · intro u
          simpa using W.terminalInput.zero_floor_tube.curv_lb u
        · simpa [W, rearRows] using hretained n (k + 1)
  · intro n k
    have hp := abs_perim_sub_le_dist (Q n) (rearRows F n k)
    have hone : perim (Q n) - perim (rearRows F n k) ≤
        dist (Q n) (rearRows F n k) := (le_abs_self _).trans hp
    linarith [hone.trans (hretained n k), hbasePerim n]
  · intro n k
    have hp := abs_perim_sub_le_dist (rearRows F n k) (Q n)
    have hone : perim (rearRows F n k) - perim (Q n) ≤
        dist (rearRows F n k) (Q n) := (le_abs_self _).trans hp
    have hd : dist (rearRows F n k) (Q n) ≤ r n := by
      simpa [dist_comm] using hretained n k
    linarith [hone.trans hd, B.upper_speed n]
  · intro n k u
    have hdiff := VariableMarkedTubeLocalStability.dist_acc_apply_le
      (rearRows F n k) (Q n) u
    have hd : dist (rearRows F n k) (Q n) ≤ r n := by
      simpa [dist_comm] using hretained n k
    calc
      ‖(rearRows F n k).2.2 u‖ ≤
          ‖(rearRows F n k).2.2 u - (Q n).2.2 u‖ + ‖(Q n).2.2 u‖ := by
        conv_lhs => rw [← sub_add_cancel
          ((rearRows F n k).2.2 u) ((Q n).2.2 u)]
        exact norm_add_le _ _
      _ ≤ r n + A0 n := add_le_add (hdiff.trans hd) (hbaseAcc n u)
      _ = A0 n + r n := add_comm _ _
  · intro n k
    cases k with
    | zero =>
        rw [hradius n]
        simpa [rearRows, markedGrid] using
          mul_nonneg (add_nonneg (hbaseConversion n) (hendpoint n))
            (htail0 n)
    | succ k =>
        rw [hradius n]
        have H := hcap n k
        calc
          dist (rearRows F n (k + 1)) (markedGrid F n (k + 1)) =
              dist (markedGrid F n (k + 1)) (rearRows F n (k + 1)) :=
            dist_comm _ _
          _ ≤ endpointConversion n * diagonal' (n + (k + 1)) := H
          _ ≤ endpointConversion n * tail n :=
            mul_le_mul_of_nonneg_left (hterm n k) (hendpoint n)
          _ ≤ (baseConversion n + endpointConversion n) * tail n := by
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left (hbaseConversion n)) (htail0 n)
          _ = rowRadius
              (combinedConversion baseConversion endpointConversion)
              diagonal' n := by rfl

end ConfiguredRecursiveEdgePresentedCapstonePhysicalBounds
