import UnitTangentIterates.ApproximatePullbackClosedTube

/-!
# Local bounded approximate variable-speed pullbacks

The selected-rear gauge construction is local to the closed geometric tube and
its fixed derivative ceilings require a bound on the cost of the path being
transported.  This module threads both facts through the pullback induction.
It therefore avoids the unnecessarily global `hmap` interface.
-/

noncomputable section

open Function Filter Topology MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace PaperFaithfulLocalApproximatePullback

/-- Iterate a local approximate transport theorem while retaining an explicit
cost cap at every intermediate stage. -/
theorem exists_path_iterate_local
    {B : Data → Data} {K P0 P1 khat G1 Cg c dlt Mtotal : ℝ}
    (hK : 1 ≤ K)
    (hmap : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eps : ℝ, 0 < eps → ∃ Delta : NormalPath (B p) (B q),
        cost Delta ≤ K * cost Gamma + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Delta)
    {p q : Data}
    (k : ℕ)
    (hpmem : ∀ j, j < k → IsTubeMember c 0 dlt ((B^[j]) p))
    (hqmem : ∀ j, j < k → IsTubeMember c 0 dlt ((B^[j]) q))
    (Gamma : NormalPath p q)
    (hGamma : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma) :
    ∀ eps : ℝ, 0 < eps →
      K ^ k * cost Gamma + eps ≤ Mtotal →
      ∃ Delta : NormalPath ((B^[k]) p) ((B^[k]) q),
        cost Delta ≤ K ^ k * cost Gamma + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Delta := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  induction k with
  | zero =>
      intro eps heps _
      have hcost : cost Gamma ≤ cost Gamma + eps := le_add_of_nonneg_right heps.le
      exact ⟨Gamma, by simpa using hcost, hGamma⟩
  | succ k ih =>
      intro eps heps hcap
      have hKp : 0 < K + 1 := by linarith
      let e1 : ℝ := eps / (2 * (K + 1))
      have he1 : 0 < e1 := by dsimp [e1]; positivity
      have he1le : e1 ≤ eps := by
        dsimp [e1]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (K + 1))]
        nlinarith [heps.le, hK]
      have hpow : K ^ k ≤ K ^ (k + 1) := by
        rw [pow_succ]
        nlinarith [pow_nonneg hK0 k]
      have hprev : K ^ k * cost Gamma + e1 ≤ Mtotal := by
        apply le_trans _ hcap
        exact add_le_add
          (mul_le_mul_of_nonneg_right hpow Gamma.cost_nonneg) he1le
      obtain ⟨Delta, hDelta, hDeltavs⟩ := ih
        (fun j hj => hpmem j (Nat.lt.step hj))
        (fun j hj => hqmem j (Nat.lt.step hj)) e1 he1 hprev
      have hDeltaCap : cost Delta ≤ Mtotal := hDelta.trans hprev
      obtain ⟨Delta', hDelta', hDelta'vs⟩ :=
        hmap _ _ Delta (hpmem k (Nat.lt_succ_self k))
          (hqmem k (Nat.lt_succ_self k)) hDeltavs hDeltaCap
          (eps / 2) (by linarith)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨Delta', ?_, hDelta'vs⟩
      have hstep : K * cost Delta ≤ K * (K ^ k * cost Gamma + e1) :=
        mul_le_mul_of_nonneg_left hDelta hK0
      have hKe1 : K * e1 ≤ eps / 2 := by
        have hrw : K * e1 = (K * eps) / (2 * (K + 1)) := by
          dsimp [e1]
          ring
        rw [hrw, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
        nlinarith [heps.le, hK]
      calc
        cost Delta' ≤ K * cost Delta + eps / 2 := hDelta'
        _ ≤ K * (K ^ k * cost Gamma + e1) + eps / 2 := by linarith
        _ = K ^ (k + 1) * cost Gamma + (K * e1 + eps / 2) := by ring
        _ ≤ K ^ (k + 1) * cost Gamma + eps := by linarith

/-- The local bounded analogue of `exists_step_path_approx_vs`.  The caller
supplies exactly the cap needed for this finite pullback depth. -/
theorem exists_step_path_local
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
    (n k : ℕ)
    (hmem : ∀ m j, j ≤ k → IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q m j)) : ∀ eps : ℝ, 0 < eps →
      K ^ k * d (n + k) + eps ≤ Mtotal →
      ∃ Delta : NormalPath (TubePullbackLimit.pullback B Q n k)
          (TubePullbackLimit.pullback B Q n (k + 1)),
        cost Delta ≤ K ^ k * d (n + k) + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Delta := by
  intro eps heps hcap
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKk : 0 ≤ K ^ k := pow_nonneg hK0 k
  let e1 : ℝ := eps / (2 * (K ^ k + 1))
  have he1 : 0 < e1 := by dsimp [e1]; positivity
  obtain ⟨Lambda, hLambda, hLambdavs⟩ := hdefect (n + k) e1 he1
  have hitercap : K ^ k * cost Lambda + eps / 2 ≤ Mtotal := by
    apply le_trans _ hcap
    have hKe1 : K ^ k * e1 ≤ eps / 2 := by
      have hrw : K ^ k * e1 = (K ^ k * eps) / (2 * (K ^ k + 1)) := by
        dsimp [e1]
        ring
      rw [hrw, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      nlinarith [heps.le, hKk]
    have hmul : K ^ k * cost Lambda ≤ K ^ k * (d (n + k) + e1) :=
      mul_le_mul_of_nonneg_left hLambda hKk
    rw [mul_add] at hmul
    linarith
  have hleft : ∀ j, j < k →
      IsTubeMember c 0 dlt ((B^[j]) (Q (n + k))) := by
    intro j hj
    have hidx : n + k - j + j = n + k := by omega
    simpa [TubePullbackLimit.pullback, hidx] using
      hmem (n + k - j) j (Nat.le_of_lt hj)
  have hright : ∀ j, j < k →
      IsTubeMember c 0 dlt ((B^[j]) (B (Q (n + k + 1)))) := by
    intro j hj
    have hidx : n + k - j + (j + 1) = n + k + 1 := by omega
    simpa [TubePullbackLimit.pullback, hidx, Function.iterate_succ_apply] using
      hmem (n + k - j) (j + 1) (by omega)
  obtain ⟨Delta, hDelta, hDeltavs⟩ :=
    exists_path_iterate_local hK hmap k hleft hright Lambda hLambdavs
      (eps / 2) (by linarith) hitercap
  have hKe1 : K ^ k * e1 ≤ eps / 2 := by
    have hrw : K ^ k * e1 = (K ^ k * eps) / (2 * (K ^ k + 1)) := by
      dsimp [e1]
      ring
    rw [hrw, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [heps.le, hKk]
  have hmul : K ^ k * cost Lambda ≤ K ^ k * (d (n + k) + e1) :=
    mul_le_mul_of_nonneg_left hLambda hKk
  have hcostFinal : cost Delta ≤ K ^ k * d (n + k) + eps := calc
    cost Delta ≤ K ^ k * cost Lambda + eps / 2 := hDelta
    _ ≤ K ^ k * (d (n + k) + e1) + eps / 2 := by linarith
    _ = K ^ k * d (n + k) + (K ^ k * e1 + eps / 2) := by ring
    _ ≤ K ^ k * d (n + k) + eps := by linarith
  simpa [TubePullbackLimit.pullback, Function.iterate_succ_apply, Nat.add_assoc] using
    (show ∃ Delta' : NormalPath ((B^[k]) (Q (n + k)))
        ((B^[k]) (B (Q (n + k + 1)))),
        cost Delta' ≤ K ^ k * d (n + k) + eps ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Delta' from
      ⟨Delta, hcostFinal, hDeltavs⟩)

/-- Exact marked-distance increment from local bounded approximate transport.
The strict cap leaves room for the epsilon allocation used to remove path
slack. -/
theorem dist_pullback_succ_le_local
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
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hcap : ∀ n k, K ^ k * d (n + k) < Mtotal)
    (n k : ℕ) :
    dist (TubePullbackLimit.pullback B Q n k)
        (TubePullbackLimit.pullback B Q n (k + 1)) ≤
      c2ConstVar P0 P1 khat G1 Cg * (K ^ k * d (n + k)) := by
  let C := c2ConstVar P0 P1 khat G1 Cg
  let base := K ^ k * d (n + k)
  refine le_of_forall_pos_le_add (fun eps heps => ?_)
  have hCp : 0 < C + 1 := by dsimp [C]; linarith
  have hmargin : 0 < Mtotal - base := sub_pos.mpr (hcap n k)
  let eps' := min (eps / (C + 1)) ((Mtotal - base) / 2)
  have heps' : 0 < eps' := lt_min (div_pos heps hCp) (half_pos hmargin)
  have hcap' : base + eps' ≤ Mtotal := by
    have := min_le_right (eps / (C + 1)) ((Mtotal - base) / 2)
    dsimp [eps', base] at this ⊢
    linarith
  obtain ⟨Gamma, hGammacost, hGammavs⟩ :=
    exists_step_path_local hK hmap hdefect n k (fun m j _ => hmem m j) eps' heps'
      (by simpa [base] using hcap')
  have hdist := dist_le_cost_variableSpeed Gamma
    (hmem n k).hasDerivAt_curve (hmem n (k + 1)).hasDerivAt_curve
    (hmem n k).hasDerivAt_vel (hmem n (k + 1)).hasDerivAt_vel hGammavs
  have hfrac : C * eps' ≤ eps := by
    have hepsle := min_le_left (eps / (C + 1)) ((Mtotal - base) / 2)
    have hCle : C * eps' ≤ C * (eps / (C + 1)) :=
      mul_le_mul_of_nonneg_left hepsle (by simpa [C] using hC)
    have hlast : C * (eps / (C + 1)) ≤ eps := by
      rw [show C * (eps / (C + 1)) = C * eps / (C + 1) by ring]
      rw [div_le_iff₀ hCp]
      nlinarith [mul_nonneg (show 0 ≤ C by simpa [C] using hC) heps.le]
    exact hCle.trans hlast
  have hmul := mul_le_mul_of_nonneg_left hGammacost (show 0 ≤ C by simpa [C] using hC)
  calc
    dist (TubePullbackLimit.pullback B Q n k)
        (TubePullbackLimit.pullback B Q n (k + 1)) ≤ C * cost Gamma := hdist
    _ ≤ C * (base + eps') := by simpa [base] using hmul
    _ ≤ C * base + eps := by rw [mul_add]; linarith

/-- Completeness and the exact weighted tail using only local, capped map
transport.  This range-level form does not assume continuity of `B`: continuity
is needed only if one additionally wants to identify the limits by the literal
equation `X n = B (X (n+1))`. -/
theorem exists_markedLimit_of_local_transport_without_map_continuity
    {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat G1 Cg c dlt Mtotal : ℝ}
    (hK : 1 ≤ K)
    (hweighted : ∀ n, Summable fun k => K ^ k * d (n + k))
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
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hcap : ∀ n k, K ^ k * d (n + k) < Mtotal) :
    ∃ X : ℕ → Data,
      (∀ n, IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, dist (Q n) (X n) ≤ ShadowingTails.tail
        (fun k => c2ConstVar P0 P1 khat G1 Cg *
          (K ^ k * d (n + k))) 0) := by
  let C := c2ConstVar P0 P1 khat G1 Cg
  have hstep : ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤
        C * (K ^ k * d (n + k)) := by
    intro n k
    simpa [C] using dist_pullback_succ_le_local
      hK hmap hdefect hC hmem hcap n k
  have hlim : ∀ n, ∃ x : Data,
      Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 x) ∧
      ∀ k, dist (TubePullbackLimit.pullback B Q n k) x ≤
        ShadowingTails.tail (fun j => C * (K ^ j * d (n + j))) k := by
    intro n
    obtain ⟨x, hx, hxd⟩ := ShadowingTails.exists_limit_of_summable_increments
      (C := 1) ((hweighted n).mul_left C) (fun k => by simpa using hstep n k)
    exact ⟨x, hx, fun k => by simpa using hxd k⟩
  choose X hXlim hXdist using hlim
  have hXmem : ∀ n, IsTubeMember c 0 dlt (X n) := by
    intro n
    exact (MarkedSpace.isClosed_tube c 0 dlt).mem_of_tendsto (hXlim n)
      (Eventually.of_forall (hmem n))
  refine ⟨X, hXmem, hXlim, ?_⟩
  intro n
  simpa [C, TubePullbackLimit.pullback] using hXdist n 0

/-- Completeness, the exact weighted tail, and literal inverse-limit
identification when the pullback map is continuous. -/
theorem exists_markedLimit_of_local_transport
    {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat G1 Cg c dlt Mtotal : ℝ}
    (hK : 1 ≤ K)
    (hweighted : ∀ n, Summable fun k => K ^ k * d (n + k))
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
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hcap : ∀ n k, K ^ k * d (n + k) < Mtotal)
    (hBcont : Continuous B) :
    ∃ X : ℕ → Data,
      (∀ n, IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n, dist (Q n) (X n) ≤ ShadowingTails.tail
        (fun k => c2ConstVar P0 P1 khat G1 Cg *
          (K ^ k * d (n + k))) 0) := by
  let C := c2ConstVar P0 P1 khat G1 Cg
  have hstep : ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤
        C * (K ^ k * d (n + k)) := by
    intro n k
    simpa [C] using dist_pullback_succ_le_local
      hK hmap hdefect hC hmem hcap n k
  have hlim : ∀ n, ∃ x : Data,
      Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 x) ∧
      ∀ k, dist (TubePullbackLimit.pullback B Q n k) x ≤
        ShadowingTails.tail (fun j => C * (K ^ j * d (n + j))) k := by
    intro n
    obtain ⟨x, hx, hxd⟩ := ShadowingTails.exists_limit_of_summable_increments
      (C := 1) ((hweighted n).mul_left C) (fun k => by simpa using hstep n k)
    exact ⟨x, hx, fun k => by simpa using hxd k⟩
  choose X hXlim hXdist using hlim
  have hXmem : ∀ n, IsTubeMember c 0 dlt (X n) := by
    intro n
    exact (MarkedSpace.isClosed_tube c 0 dlt).mem_of_tendsto (hXlim n)
      (Eventually.of_forall (hmem n))
  have hinv : ∀ n, X n = B (X (n + 1)) := by
    intro n
    have hshift : Tendsto
        (fun k => TubePullbackLimit.pullback B Q n (k + 1)) atTop (𝓝 (X n)) :=
      (hXlim n).comp (tendsto_add_atTop_nat 1)
    have hBlim : Tendsto
        (fun k => B (TubePullbackLimit.pullback B Q (n + 1) k)) atTop
        (𝓝 (B (X (n + 1)))) :=
      (hBcont.tendsto _).comp (hXlim (n + 1))
    have heq : (fun k => TubePullbackLimit.pullback B Q n (k + 1)) =
        fun k => B (TubePullbackLimit.pullback B Q (n + 1) k) :=
      funext fun k => TubePullbackLimit.pullback_succ B Q n k
    rw [heq] at hshift
    exact tendsto_nhds_unique hshift hBlim
  refine ⟨X, hXmem, hXlim, hinv, ?_⟩
  intro n
  simpa [C, TubePullbackLimit.pullback] using hXdist n 0

end PaperFaithfulLocalApproximatePullback
