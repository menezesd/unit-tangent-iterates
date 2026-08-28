import UnitTangentIterates.VariableSpeedPathDist
import UnitTangentIterates.UniformCeilings

/-!
# The pullback iteration in the variable-speed class
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Filter Topology MeasureTheory MarkedSpace PathMetric
  PathMetric.NormalPath
open NormalPathC2Increment NormalPathC2IncrementVariableSpeed

namespace TubePullbackLimit

/-- **The class is a fixed point once the ceilings are large enough.**

The rear map sends a path of *any* variable-speed class into the class whose
ceilings are `costP1 ell khat M` and `costG1 ell khat kappa2 M` — quantities
computed from that step's rear period and cost, not from the incoming ceilings
(§97).  So if `(G1, Cg)` dominates those, `IsVariableSpeedNormalPath.mono`
returns the image to the same class, and the class is preserved under iteration.

This lemma packages that step: a map landing in `(G1', Cg')` with
`G1' ≤ G1` and `Cg' ≤ Cg` is a map of the class `(G1, Cg)` into itself. -/
theorem hmap_vs_of_bounded_ceilings {B : Data → Data} {K P0 P1 khat G1 Cg G1' Cg' : ℝ}
    (hkhat : 0 ≤ khat) (hG1 : G1' ≤ G1) (hCg : Cg' ≤ Cg)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧ IsVariableSpeedNormalPath P0 P1 khat G1' Cg' Δ) :
    ∀ (p q : Data) (Γ : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧ IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ := by
  intro p q Γ hΓ ε hε
  obtain ⟨Δ, hΔ, hΔvs⟩ := hmap p q Γ hΓ ε hε
  exact ⟨Δ, hΔ, hΔvs.mono Δ hkhat (le_refl _) hG1 hCg⟩

/-- **The pullback iteration in the variable-speed class.**  The proof of §94
uses only `cost` arithmetic and treats the path class as an opaque predicate, so
it transports verbatim. -/
theorem exists_path_iterate_approx_vs {B : Data → Data} {K P0 P1 khat G1 Cg : ℝ}
    (hK : 0 ≤ K)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧ IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ)
    (k : ℕ) {p q : Data} (Γ : NormalPath p q)
    (hΓ : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ) :
    ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B^[k] p) (B^[k] q),
      cost Δ ≤ K ^ k * cost Γ + ε ∧ IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ := by
  induction k with
  | zero => intro ε hε; exact ⟨Γ, by simpa using by linarith, hΓ⟩
  | succ k ih =>
      intro ε hε
      have hKp : (0:ℝ) < K + 1 := by linarith
      set e1 : ℝ := ε / (2 * (K + 1)) with he1
      have he1pos : 0 < e1 := by positivity
      obtain ⟨Δ, hΔ, hΔvs⟩ := ih e1 he1pos
      obtain ⟨Δ', hΔ', hΔ'vs⟩ := hmap _ _ Δ hΔvs (ε / 2) (by linarith)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨Δ', ?_, hΔ'vs⟩
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

/-- The step paths, in the variable-speed class. -/
theorem exists_step_path_approx_vs {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat G1 Cg : ℝ} (hK : 0 ≤ K)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧ IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ)
    (hdefect : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
        cost Λ ≤ d n + ε ∧ IsVariableSpeedNormalPath P0 P1 khat G1 Cg Λ)
    (n k : ℕ) : ∀ ε : ℝ, 0 < ε →
    ∃ Δ : NormalPath (pullback B Q n k) (pullback B Q n (k + 1)),
      cost Δ ≤ K ^ k * d (n + k) + ε ∧ IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ := by
  intro ε hε
  have hKk : (0:ℝ) ≤ K ^ k := pow_nonneg hK k
  have hKk1 : (0:ℝ) < K ^ k + 1 := by linarith
  set e1 : ℝ := ε / (2 * (K ^ k + 1)) with he1
  have he1pos : 0 < e1 := by positivity
  obtain ⟨Λ, hΛ, hΛvs⟩ := hdefect (n + k) e1 he1pos
  obtain ⟨Δ, hΔ, hΔvs⟩ :=
    exists_path_iterate_approx_vs hK hmap k Λ hΛvs (ε / 2) (by linarith)
  have hidx : n + (k + 1) = (n + k) + 1 := by omega
  have htarget : pullback B Q n (k + 1) = B^[k] (B (Q ((n + k) + 1))) := by
    simp [pullback, hidx, Function.iterate_succ_apply]
  rw [htarget]
  refine ⟨Δ, ?_, hΔvs⟩
  have hKe1 : K ^ k * e1 ≤ ε / 2 := by
    have hrw : K ^ k * e1 = (K ^ k * ε) / (2 * (K ^ k + 1)) := by rw [he1]; ring
    rw [hrw, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    nlinarith [hε.le, hKk]
  have hstep : K ^ k * cost Λ ≤ K ^ k * (d (n + k) + e1) :=
    mul_le_mul_of_nonneg_left hΛ hKk
  calc cost Δ ≤ K ^ k * cost Λ + ε / 2 := hΔ
    _ ≤ K ^ k * (d (n + k) + e1) + ε / 2 := by linarith
    _ = K ^ k * d (n + k) + (K ^ k * e1 + ε / 2) := by ring
    _ ≤ K ^ k * d (n + k) + ε := by linarith

end TubePullbackLimit
