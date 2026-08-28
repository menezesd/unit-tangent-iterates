import UnitTangentIterates.VariableSpeedIteration
import UnitTangentIterates.UnconditionalAssemblyRemainder

/-!
# Approximate variable-speed pullbacks give exact metric bounds

The natural interpolation and gauge interfaces produce paths with cost at
most the desired bound plus an arbitrary positive error.  Since marked
distance is bounded by every such path, the error can be removed after
passing to the metric estimate.  This avoids assuming that the path-cost
infimum is attained and retains the genuine pullback factor `K ^ k`.
-/

noncomputable section

open Function Filter Topology MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace PaperFaithfulApproximatePullback

/-- Arbitrarily accurate variable-speed pullback paths imply the exact marked
distance estimate. -/
theorem dist_pullback_succ_le_of_approx_paths
    {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat G1 Cg c dlt : ℝ}
    (hK : 0 ≤ K)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ)
    (hdefect : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
        cost Λ ≤ d n + ε ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Λ)
    (hC : 0 ≤ c2ConstVar P0 P1 khat G1 Cg)
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k)) (n k : ℕ) :
    dist (TubePullbackLimit.pullback B Q n k)
        (TubePullbackLimit.pullback B Q n (k + 1)) ≤
      c2ConstVar P0 P1 khat G1 Cg * (K ^ k * d (n + k)) := by
  let C := c2ConstVar P0 P1 khat G1 Cg
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hCp : 0 < C + 1 := by dsimp [C]; linarith
  let ε' := ε / (C + 1)
  have hε' : 0 < ε' := div_pos hε hCp
  obtain ⟨Γ, hΓcost, hΓgeom⟩ :=
    TubePullbackLimit.exists_step_path_approx_vs hK hmap hdefect n k ε' hε'
  have hdist := dist_le_cost_variableSpeed Γ
    (hmem n k).hasDerivAt_curve (hmem n (k + 1)).hasDerivAt_curve
    (hmem n k).hasDerivAt_vel (hmem n (k + 1)).hasDerivAt_vel hΓgeom
  have hcost : C * cost Γ ≤ C * (K ^ k * d (n + k) + ε') :=
    mul_le_mul_of_nonneg_left hΓcost (by simpa [C] using hC)
  have hfrac : C * ε' ≤ ε := by
    rw [show C * ε' = C * ε / (C + 1) by simp [ε']; ring]
    rw [div_le_iff₀ hCp]
    nlinarith [mul_nonneg (show 0 ≤ C by simpa [C] using hC) hε.le]
  calc
    dist (TubePullbackLimit.pullback B Q n k)
        (TubePullbackLimit.pullback B Q n (k + 1)) ≤ C * cost Γ := hdist
    _ ≤ C * (K ^ k * d (n + k) + ε') := hcost
    _ ≤ C * (K ^ k * d (n + k)) + ε := by rw [mul_add]; linarith

/-- Completeness for approximate transported paths.  The conclusion retains
the exact inverse orbit and the sharp weighted tail; no minimizing path and no
assumption `K ≤ 1` are used. -/
theorem exists_markedLimit_of_approx_variableSpeed_transport
    {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat G1 Cg c dlt : ℝ}
    (hK : 0 ≤ K)
    (hweighted : ∀ n, Summable fun k => K ^ k * d (n + k))
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ)
    (hdefect : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
        cost Λ ≤ d n + ε ∧
        IsVariableSpeedNormalPath P0 P1 khat G1 Cg Λ)
    (hC : 0 ≤ c2ConstVar P0 P1 khat G1 Cg)
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
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
    simpa [C] using dist_pullback_succ_le_of_approx_paths
      hK hmap hdefect hC hmem n k
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

end PaperFaithfulApproximatePullback
