import UnitTangentIterates.ConstantSpeedPathDist
import UnitTangentIterates.InverseStability

/-!
# The approximate form of the defect hypothesis
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Filter Topology MeasureTheory MarkedSpace PathMetric
  PathMetric.NormalPath
open NormalPathC2Increment

namespace TubePullbackLimit

/-- **Approximate `hdefect` also suffices.**

§94 weakened `hmap` from an attained image path to an `ε`-approximate one,
because `pathDist` is an infimum.  `hdefect` is consumed in exactly the same
place — `exists_step_path` calls it once and then iterates `hmap` — so the same
weakening applies, and for the same reason: the model defect estimate is a bound
on a path *distance*, not the exhibition of a minimizing path.

The budget split is `K^k * e1 + e2 <= eps` with `e1 = eps/(2(K^k+1))` and
`e2 = eps/2`. -/
theorem exists_step_path_approx_defect {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat : ℝ} (hK : 0 ≤ K)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
        cost Λ ≤ d n + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (n k : ℕ) : ∀ ε : ℝ, 0 < ε →
    ∃ Δ : NormalPath (pullback B Q n k) (pullback B Q n (k + 1)),
      cost Δ ≤ K ^ k * d (n + k) + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Δ := by
  intro ε hε
  have hKk : (0:ℝ) ≤ K ^ k := pow_nonneg hK k
  have hKk1 : (0:ℝ) < K ^ k + 1 := by linarith
  set e1 : ℝ := ε / (2 * (K ^ k + 1)) with he1
  have he1pos : 0 < e1 := by positivity
  obtain ⟨Λ, hΛ, hΛgeom⟩ := hdefect (n + k) e1 he1pos
  obtain ⟨Δ, hΔ, hΔgeom⟩ :=
    exists_path_iterate_approx hK hmap k Λ hΛgeom (ε / 2) (by linarith)
  have hidx : n + (k + 1) = (n + k) + 1 := by omega
  have htarget : pullback B Q n (k + 1) = B^[k] (B (Q ((n + k) + 1))) := by
    simp [pullback, hidx, Function.iterate_succ_apply]
  rw [htarget]
  refine ⟨Δ, ?_, hΔgeom⟩
  have hstep : K ^ k * cost Λ ≤ K ^ k * (d (n + k) + e1) :=
    mul_le_mul_of_nonneg_left hΛ hKk
  have hKe1 : K ^ k * e1 ≤ ε / 2 := by
    have hrw : K ^ k * e1 = (K ^ k * ε) / (2 * (K ^ k + 1)) := by rw [he1]; ring
    rw [hrw, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    nlinarith [hε.le, hKk]
  calc cost Δ ≤ K ^ k * cost Λ + ε / 2 := hΔ
    _ ≤ K ^ k * (d (n + k) + e1) + ε / 2 := by linarith
    _ = K ^ k * d (n + k) + (K ^ k * e1 + ε / 2) := by ring
    _ ≤ K ^ k * d (n + k) + ε := by linarith

/-- **The defect hypothesis from a constant-speed path-distance bound.**  The
exact analogue of `PathMetric.hmap_approx_of_pathDistCS_le`, so both hypotheses
of the pullback iteration are now consumable from bounds on infima. -/
theorem hdefect_approx_of_pathDistCS_le {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {P0 P1 khat : ℝ}
    (hne : ∀ n : ℕ, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      IsConstantSpeedNormalPath P0 P1 khat Λ)
    (hbound : ∀ n : ℕ, pathDistCS P0 P1 khat (Q n) (B (Q (n + 1))) ≤ d n) :
    ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
        cost Λ ≤ d n + ε ∧ IsConstantSpeedNormalPath P0 P1 khat Λ := by
  intro n ε hε
  obtain ⟨Λ, hΛcs, hΛ⟩ := exists_constantSpeed_near_minimizer (hne n) hε
  exact ⟨Λ, le_trans hΛ (by linarith [hbound n]), hΛcs⟩

end TubePullbackLimit
