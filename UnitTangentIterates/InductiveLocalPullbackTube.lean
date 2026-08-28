import UnitTangentIterates.LocalVariableSpeedApproximatePullback
import UnitTangentIterates.PullbackTubeTailBudget

/-!
# Simultaneous local pullback and tube induction

This module removes the apparent circularity in local selected-inverse
transport.  At depth `k`, local path transport uses positive tube membership
only through depth `k`.  The new endpoint at depth `k + 1` needs only the
closed zero-margin differential structure in order to estimate its marked
distance.  The accumulated finite-prefix estimate then lies below the
reserved summable tail and upgrades that endpoint to the positive tube.
-/

noncomputable section

open Set Function MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace PaperFaithfulLocalApproximatePullback

/-- Strict model margins and closed structural facts sufficient for the
simultaneous pullback induction.  No pullback with positive margins is assumed.
-/
structure InductiveTubeBudget
    (B : Data → Data) (Q : ℕ → Data) (C K : ℝ) (d : ℕ → ℝ)
    (c d0 dlt : ℝ) (A0 rho : ℕ → ℝ) : Prop where
  c_pos : 0 < c
  radius_nonneg : ∀ n, 0 ≤ PullbackTubeTailBudget.radius C K d n
  model_mem : ∀ n, IsTubeMember
    (c + PullbackTubeTailBudget.radius C K d n) 0 d0 (Q n)
  weak_mem : ∀ n k, IsTubeMember 0 0 0
    (TubePullbackLimit.pullback B Q n k)
  model_acc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n
  acc_nonneg : ∀ n, 0 ≤ A0 n
  rho_pos : ∀ n, 0 < rho n
  rho_half : ∀ n, rho n ≤ 1 / 2
  acc_radius : ∀ n,
    (A0 n + PullbackTubeTailBudget.radius C K d n) * rho n ≤ c / 2
  chord_nonneg : 0 ≤ dlt
  chord_speed : dlt ≤ c / 2
  chord_margin : ∀ n,
    2 * PullbackTubeTailBudget.radius C K d n ≤ (d0 - dlt) * rho n

private theorem dist_acc_apply_le (p q : Data) (u : ℝ) :
    ‖p.2.2 u - q.2.2 u‖ ≤ dist p q := by
  have h1 : dist (p.2.2 u) (q.2.2 u) ≤ dist p.2.2 q.2.2 :=
    BoundedContinuousFunction.dist_coe_le_dist u
  have h2 : dist p.2.2 q.2.2 ≤ dist p.2 q.2 := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have h3 : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  rw [← dist_eq_norm]
  exact h1.trans (h2.trans h3)

/-- Upgrade one closed diagonal pullback to the target tube once its distance
from the strict model is within the reserved row radius. -/
theorem InductiveTubeBudget.pullback_mem_of_dist
    {B : Data → Data} {Q : ℕ → Data} {C K c d0 dlt : ℝ}
    {d : ℕ → ℝ} {A0 rho : ℕ → ℝ}
    (R : InductiveTubeBudget B Q C K d c d0 dlt A0 rho)
    (n k : ℕ)
    (hdist : dist (Q n) (TubePullbackLimit.pullback B Q n k) ≤
      PullbackTubeTailBudget.radius C K d n) :
    IsTubeMember c 0 dlt (TubePullbackLimit.pullback B Q n k) := by
  let Z := TubePullbackLimit.pullback B Q n k
  let r := PullbackTubeTailBudget.radius C K d n
  have hQ := R.model_mem n
  have hZ := R.weak_mem n k
  have hspeed : ∀ u, c ≤ ‖Z.2.1 u‖ := by
    intro u
    have hv := MarkedSpace.dist_vel_apply_le (Q n) Z u
    have hvR : ‖(Q n).2.1 u - Z.2.1 u‖ ≤ r := hv.trans hdist
    have htri : ‖(Q n).2.1 u‖ ≤
        ‖(Q n).2.1 u - Z.2.1 u‖ + ‖Z.2.1 u‖ := by
      calc
        ‖(Q n).2.1 u‖ = ‖((Q n).2.1 u - Z.2.1 u) + Z.2.1 u‖ := by ring
        _ ≤ ‖(Q n).2.1 u - Z.2.1 u‖ + ‖Z.2.1 u‖ := norm_add_le _ _
    have hQspeed := hQ.speed_lb u
    dsimp [r] at hvR hQspeed ⊢
    linarith
  have hacc : ∀ u, ‖Z.2.2 u‖ ≤ A0 n + r := by
    intro u
    have ha := dist_acc_apply_le Z (Q n) u
    have haR : ‖Z.2.2 u - (Q n).2.2 u‖ ≤ r := by
      exact ha.trans (dist_comm Z (Q n) ▸ hdist)
    calc
      ‖Z.2.2 u‖ = ‖(Z.2.2 u - (Q n).2.2 u) + (Q n).2.2 u‖ := by ring
      _ ≤ ‖Z.2.2 u - (Q n).2.2 u‖ + ‖(Q n).2.2 u‖ := norm_add_le _ _
      _ ≤ r + A0 n := add_le_add haR (R.model_acc n u)
      _ = A0 n + r := add_comm _ _
  have hclose : ∀ u, ‖Z.1 u - (Q n).1 u‖ ≤ r := by
    intro u
    exact (MarkedSpace.dist_apply_le Z (Q n) u).trans
      (by simpa [dist_comm] using hdist)
  have hchord := ChordArc.chord_arc_stable_of_acc_bound
    hZ.hasDerivAt_curve hZ.hasDerivAt_vel (MarkedSpace.periodic_vel hZ)
    hZ.periodic hspeed hacc hQ.chord hclose
    (add_nonneg (R.acc_nonneg n) (R.radius_nonneg n))
    (R.rho_pos n) (R.rho_half n) (R.acc_radius n)
    R.chord_nonneg R.chord_speed (R.chord_margin n)
  exact
    { hasDerivAt_curve := hZ.hasDerivAt_curve
      hasDerivAt_vel := hZ.hasDerivAt_vel
      periodic := hZ.periodic
      speed_const := hZ.speed_const
      speed_lb := hspeed
      curv_lb := hZ.curv_lb
      chord := hchord }

private theorem dist_pullback_succ_le_of_previous
    {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat G1 Cg c dlt Mtotal : ℝ}
    (hK : 1 ≤ K)
    (hmap : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eps : ℝ, 0 < eps → ∃ Delta : NormalPath (B p) (B q),
        cost Delta ≤ K * cost Gamma + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Delta)
    (hdefect : ∀ n : ℕ, ∀ eps : ℝ, 0 < eps →
      ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
        cost Lambda ≤ d n + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Lambda)
    (hC : 0 ≤ c2ConstVar P0 P1 khat G1 Cg)
    (hweak : ∀ n k, IsTubeMember 0 0 0
      (TubePullbackLimit.pullback B Q n k))
    (n k : ℕ)
    (hprev : ∀ m j, j ≤ k → IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q m j))
    (hcap : K ^ k * d (n + k) < Mtotal) :
    dist (TubePullbackLimit.pullback B Q n k)
        (TubePullbackLimit.pullback B Q n (k + 1)) ≤
      c2ConstVar P0 P1 khat G1 Cg * (K ^ k * d (n + k)) := by
  let C := c2ConstVar P0 P1 khat G1 Cg
  let base := K ^ k * d (n + k)
  refine le_of_forall_pos_le_add (fun eps heps => ?_)
  have hCp : 0 < C + 1 := by dsimp [C]; linarith
  have hmargin : 0 < Mtotal - base := sub_pos.mpr hcap
  let eps' := min (eps / (C + 1)) ((Mtotal - base) / 2)
  have heps' : 0 < eps' := lt_min (div_pos heps hCp) (half_pos hmargin)
  have hcap' : base + eps' ≤ Mtotal := by
    have h := min_le_right (eps / (C + 1)) ((Mtotal - base) / 2)
    dsimp [eps', base] at h ⊢
    linarith
  obtain ⟨Gamma, hGammacost, hGammavs⟩ :=
    exists_step_path_local hK hmap hdefect n k hprev eps' heps'
      (by simpa [base] using hcap')
  have hdist := dist_le_cost_variableSpeed Gamma
    (hprev n k le_rfl).hasDerivAt_curve
    (hweak n (k + 1)).hasDerivAt_curve
    (hprev n k le_rfl).hasDerivAt_vel
    (hweak n (k + 1)).hasDerivAt_vel hGammavs
  have hfrac : C * eps' ≤ eps := by
    have hepsle := min_le_left (eps / (C + 1)) ((Mtotal - base) / 2)
    have hCle : C * eps' ≤ C * (eps / (C + 1)) :=
      mul_le_mul_of_nonneg_left hepsle (by simpa [C] using hC)
    have hlast : C * (eps / (C + 1)) ≤ eps := by
      rw [show C * (eps / (C + 1)) = C * eps / (C + 1) by ring]
      rw [div_le_iff₀ hCp]
      nlinarith [mul_nonneg (show 0 ≤ C by simpa [C] using hC) heps.le]
    exact hCle.trans hlast
  have hmul := mul_le_mul_of_nonneg_left hGammacost
    (show 0 ≤ C by simpa [C] using hC)
  calc
    dist (TubePullbackLimit.pullback B Q n k)
        (TubePullbackLimit.pullback B Q n (k + 1)) ≤ C * cost Gamma := hdist
    _ ≤ C * (base + eps') := by simpa [base] using hmul
    _ ≤ C * base + eps := by rw [mul_add]; linarith

/-- Simultaneously construct every positive diagonal tube membership and every
exact weighted increment bound.  Thus membership is an output, not a hidden
invariance callback. -/
theorem diagonal_membership_and_increment_of_inductive_budget
    {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat G1 Cg c d0 dlt Mtotal : ℝ}
    {A0 rho : ℕ → ℝ}
    (hK : 1 ≤ K)
    (hd : ∀ n, 0 ≤ d n)
    (hweighted : ∀ n, Summable (fun k => K ^ k * d (n + k)))
    (hmap : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eps : ℝ, 0 < eps → ∃ Delta : NormalPath (B p) (B q),
        cost Delta ≤ K * cost Gamma + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Delta)
    (hdefect : ∀ n : ℕ, ∀ eps : ℝ, 0 < eps →
      ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
        cost Lambda ≤ d n + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Lambda)
    (hC : 0 ≤ c2ConstVar P0 P1 khat G1 Cg)
    (hcap : ∀ n k, K ^ k * d (n + k) < Mtotal)
    (R : InductiveTubeBudget B Q
      (c2ConstVar P0 P1 khat G1 Cg) K d c d0 dlt A0 rho) :
    (∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k)) ∧
    (∀ n k, dist (TubePullbackLimit.pullback B Q n k)
        (TubePullbackLimit.pullback B Q n (k + 1)) ≤
      c2ConstVar P0 P1 khat G1 Cg * (K ^ k * d (n + k))) := by
  let C := c2ConstVar P0 P1 khat G1 Cg
  let e : ℕ → ℕ → ℝ := fun n k => C * (K ^ k * d (n + k))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have he0 : ∀ n k, 0 ≤ e n k := by
    intro n k
    exact mul_nonneg (by simpa [C] using hC)
      (mul_nonneg (pow_nonneg hK0 k) (hd (n + k)))
  have hesum : ∀ n, Summable (e n) := by
    intro n
    simpa [e] using (hweighted n).mul_left C
  have hprefix : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤
      PullbackTubeTailBudget.radius C K d n := by
    intro n k
    simpa [e, PullbackTubeTailBudget.radius, ShadowingTails.tail] using
      (hesum n).sum_le_tsum (Finset.range k) (fun j _ => he0 n j)
  have hstage : ∀ k,
      (∀ n j, j ≤ k → IsTubeMember c 0 dlt
        (TubePullbackLimit.pullback B Q n j)) ∧
      (∀ n j, j < k → dist (TubePullbackLimit.pullback B Q n j)
          (TubePullbackLimit.pullback B Q n (j + 1)) ≤ e n j) ∧
      (∀ n, dist (Q n) (TubePullbackLimit.pullback B Q n k) ≤
        ∑ j ∈ Finset.range k, e n j) := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · intro n j hj
          have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
          subst j
          apply R.pullback_mem_of_dist n 0
          simpa [TubePullbackLimit.pullback] using R.radius_nonneg n
        · intro n j hj
          omega
        · intro n
          simp [TubePullbackLimit.pullback]
    | succ k ih =>
        have hincr : ∀ n, dist (TubePullbackLimit.pullback B Q n k)
            (TubePullbackLimit.pullback B Q n (k + 1)) ≤ e n k := by
          intro n
          simpa [e, C] using dist_pullback_succ_le_of_previous
            hK hmap hdefect hC R.weak_mem n k ih.1 (hcap n k)
        have hdist : ∀ n, dist (Q n)
            (TubePullbackLimit.pullback B Q n (k + 1)) ≤
              ∑ j ∈ Finset.range (k + 1), e n j := by
          intro n
          calc
            dist (Q n) (TubePullbackLimit.pullback B Q n (k + 1)) ≤
                dist (Q n) (TubePullbackLimit.pullback B Q n k) +
                  dist (TubePullbackLimit.pullback B Q n k)
                    (TubePullbackLimit.pullback B Q n (k + 1)) := dist_triangle _ _ _
            _ ≤ (∑ j ∈ Finset.range k, e n j) + e n k :=
              add_le_add (ih.2.2 n) (hincr n)
            _ = ∑ j ∈ Finset.range (k + 1), e n j := by
              rw [Finset.sum_range_succ]
        have hmemnew : ∀ n, IsTubeMember c 0 dlt
            (TubePullbackLimit.pullback B Q n (k + 1)) := by
          intro n
          apply R.pullback_mem_of_dist n (k + 1)
          exact (hdist n).trans (hprefix n (k + 1))
        refine ⟨?_, ?_, hdist⟩
        · intro n j hj
          rcases Nat.lt_or_eq_of_le hj with hjlt | rfl
          · exact ih.1 n j (Nat.le_of_lt_succ hjlt)
          · exact hmemnew n
        · intro n j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjlt | rfl
          · exact ih.2.1 n j hjlt
          · exact hincr n
  refine ⟨?_, ?_⟩
  · intro n k
    exact (hstage k).1 n k le_rfl
  · intro n k
    simpa [e, C] using (hstage (k + 1)).2.1 n k (Nat.lt_succ_self k)

end PaperFaithfulLocalApproximatePullback
