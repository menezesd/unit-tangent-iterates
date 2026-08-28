import UnitTangentIterates.VariableTerminalRowTubeAdapter

/-!
# Rowwise variable-tube control from consecutive recursive steps

The triangular limit theorem only retains consecutive stage paths.  Their
marked-distance bounds telescope, so no separately constructed path from the
row base to every finite depth is needed.
-/

noncomputable section

open Set Function MarkedSpace PathMetric PathMetric.NormalPath
  NormalPathC2IncrementVariableSpeed

namespace VariableTerminalRowTubeStepAdapter

open VariableMarkedTube VariableMarkedTubeLocalStability
  VariableTerminalRowTubeAdapter

/-- The marked distance from depth zero is bounded by the sum of the
consecutive variable-speed step costs. -/
theorem markedDist_le_rowRadius_of_steps
    {Q : ℕ → Data} {P : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg r tail : ℕ → ℝ}
    (hbase : ∀ n, P n 0 = Q n)
    (stepPath : ∀ n k, NormalPath (P n k) (P n (k + 1)))
    (hPcurve : ∀ n k u, HasDerivAt (⇑(P n k).1) ((P n k).2.1 u) u)
    (hPvel : ∀ n k u, HasDerivAt (⇑(P n k).2.1) ((P n k).2.2 u) u)
    (hgeometry : ∀ n k, IsVariableSpeedNormalPath
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) (stepPath n k))
    (hcost : ∀ n k, cost (stepPath n k) ≤ e n k)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n) :
    ∀ n k, dist (Q n) (P n k) ≤ r n := by
  intro n
  let A := c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact c2ConstVar_nonneg _ _ _ _ _
  have hstep : ∀ j, dist (P n j) (P n (j + 1)) ≤ A * e n j := by
    intro j
    exact (dist_le_cost_variableSpeed (stepPath n j)
      (hPcurve n j) (hPcurve n (j + 1))
      (hPvel n j) (hPvel n (j + 1)) (hgeometry n j)).trans
        (mul_le_mul_of_nonneg_left (hcost n j) hA)
  have hprefix : ∀ k,
      dist (P n 0) (P n k) ≤ A * ∑ j ∈ Finset.range k, e n j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          dist (P n 0) (P n (k + 1)) ≤
              dist (P n 0) (P n k) + dist (P n k) (P n (k + 1)) :=
            dist_triangle _ _ _
          _ ≤ A * (∑ j ∈ Finset.range k, e n j) + A * e n k :=
            add_le_add ih (hstep k)
          _ = A * ∑ j ∈ Finset.range (k + 1), e n j := by
            rw [Finset.sum_range_succ]
            ring
  intro k
  rw [← hbase n]
  exact (hprefix k).trans
    ((mul_le_mul_of_nonneg_left (hpartial n k) hA).trans (hradius n))

/-- Local tube stability applied after telescoping the consecutive recursive
steps.  This produces exactly the `tube` field of the variable-terminal
triangular scheme without a redundant family of accumulated paths. -/
theorem schemeTube_of_steps
    {Q : ℕ → Data} {P : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg : ℕ → ℝ}
    {c0 d0 A0 r rho C tail : ℕ → ℝ} {c dlt : ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbaseEq : ∀ n, P n 0 = Q n)
    (hbase : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbase_acc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (stepPath : ∀ n k, NormalPath (P n k) (P n (k + 1)))
    (hPcurve : ∀ n k u, HasDerivAt (⇑(P n k).1) ((P n k).2.1 u) u)
    (hPvel : ∀ n k u, HasDerivAt (⇑(P n k).2.1) ((P n k).2.2 u) u)
    (hPperiodic : ∀ n k, Periodic (⇑(P n k).1) 1)
    (horiented : ∀ n k u, 0 ≤
      ((starRingEnd ℂ) ((P n k).2.1 u) * (P n k).2.2 u).im)
    (hgeometry : ∀ n k, IsVariableSpeedNormalPath
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) (stepPath n k))
    (hcost : ∀ n k, cost (stepPath n k) ≤ e n k)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n) :
    ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k) := by
  have hdist : ∀ n k, dist (Q n) (P n k) ≤ r n :=
    markedDist_le_rowRadius_of_steps hbaseEq stepPath hPcurve hPvel
      hgeometry hcost hpartial hradius
  intro n k
  have hlocal := variableTube_of_dist_le (hbase n) (hPcurve n k)
    (hPvel n k) (hPperiodic n k) (hdist n k) (hbase_acc n)
    (horiented n k) (B.radius_nonnegative n) (B.local_speed_positive n)
    (B.acceleration_nonnegative n) (B.rho_positive n) (B.rho_half n)
    (B.acceleration_radius n) B.chord_nonnegative (B.chord_speed n)
    (B.chord_margin n)
  exact
    { hasDerivAt_curve := hlocal.hasDerivAt_curve
      hasDerivAt_vel := hlocal.hasDerivAt_vel
      periodic := hlocal.periodic
      speed_lb := fun u => (B.target_speed n).trans (hlocal.speed_lb u)
      speed_ub := fun u => (hlocal.speed_ub u).trans (B.upper_speed n)
      curv_lb := hlocal.curv_lb
      chord := hlocal.chord }

end VariableTerminalRowTubeStepAdapter
