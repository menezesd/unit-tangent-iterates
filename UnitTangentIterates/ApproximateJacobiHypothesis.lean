import UnitTangentIterates.TubePullbackLimit

/-!
# The approximate form of the Jacobi hypothesis
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Filter Topology MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2Increment

namespace TubePullbackLimit

/-- **Approximate `hmap` iterates.**

`exists_path_iterate` asks that `B` send a constant-speed normal path to one of
cost at most `K` times as large.  What the Jacobi machinery actually delivers
(`SelectedInverseRearOwnPathDefect.exists_marked_rearOwn_pathDist_and_defect_floor_free`)
is a bound on `pathDist`, an *infimum*, which need not be attained.  So the
usable hypothesis is the approximate one: for every `ε > 0` there is an image
path of cost at most `K · cost Γ + ε`.

That is enough.  Iterating `k` times, the errors accumulate as
`K^{k-1}ε₁ + ⋯ + ε_k`, and choosing `ε_j` geometrically small keeps the total
below any prescribed `ε`.  This is the same move as the Harnack reformulation of
§77: the hypothesis that fails to be closed under limits is replaced by one that
is, at no cost to the conclusion. -/
theorem exists_path_iterate_approx {B : Data → Data} {K P0 P1 khat : ℝ} (hK : 0 ≤ K)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (k : ℕ) {p q : Data} (Γ : NormalPath p q)
    (hΓ : IsConstantSpeedNormalPath P0 P1 khat Γ) :
    ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B^[k] p) (B^[k] q),
      cost Δ ≤ K ^ k * cost Γ + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Δ := by
  induction k with
  | zero => intro ε hε; exact ⟨Γ, by simpa using by linarith, hΓ⟩
  | succ k ih =>
      intro ε hε
      -- split the budget: `K · ε' + ε'' ≤ ε` with `ε' = ε/(2(K+1))`, `ε'' = ε/2`
      have hKp : (0:ℝ) < K + 1 := by linarith
      set e1 : ℝ := ε / (2 * (K + 1)) with he1
      have he1pos : 0 < e1 := by positivity
      obtain ⟨Δ, hΔ, hΔgeom⟩ := ih e1 he1pos
      obtain ⟨Δ', hΔ', hΔ'geom⟩ := hmap _ _ Δ hΔgeom (ε / 2) (by linarith)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨Δ', ?_, hΔ'geom⟩
      have hstep : K * cost Δ ≤ K * (K ^ k * cost Γ + e1) :=
        mul_le_mul_of_nonneg_left hΔ hK
      have hKe1 : K * e1 ≤ ε / 2 := by
        have hrw : K * e1 = (K * ε) / (2 * (K + 1)) := by rw [he1]; ring
        rw [hrw, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
        nlinarith [hε.le, hK]
      calc cost Δ' ≤ K * cost Δ + ε / 2 := hΔ'
        _ ≤ K * (K ^ k * cost Γ + e1) + ε / 2 := by linarith
        _ = K ^ (k + 1) * cost Γ + (K * e1 + ε / 2) := by ring
        _ ≤ K ^ (k + 1) * cost Γ + ε := by linarith

/-- The step paths, from the approximate hypotheses. -/
theorem exists_step_path_approx {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat : ℝ} (hK : 0 ≤ K)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      cost Λ ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (n k : ℕ) : ∀ ε : ℝ, 0 < ε →
    ∃ Δ : NormalPath (pullback B Q n k) (pullback B Q n (k + 1)),
      cost Δ ≤ K ^ k * d (n + k) + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Δ := by
  intro ε hε
  obtain ⟨Λ, hΛ, hΛgeom⟩ := hdefect (n + k)
  obtain ⟨Δ, hΔ, hΔgeom⟩ := exists_path_iterate_approx hK hmap k Λ hΛgeom ε hε
  have hidx : n + (k + 1) = (n + k) + 1 := by omega
  have htarget : pullback B Q n (k + 1) = B^[k] (B (Q ((n + k) + 1))) := by
    simp [pullback, hidx, Function.iterate_succ_apply]
  rw [htarget]
  refine ⟨Δ, ?_, hΔgeom⟩
  have := mul_le_mul_of_nonneg_left hΛ (pow_nonneg hK k)
  linarith [hΔ]

end TubePullbackLimit
