import UnitTangentIterates.InterpolationPathDist

/-!
# Uniform `P1` is impossible for unbounded separations

`costFac kstar L eps = 2*L*exp(rate1Bound kstar L eps)` with
`rate1Bound = 4*kstar*(3/2*L*eps) ≥ 0`.  Hence `costFac ≥ 2*L`.
If `Hs n → ∞` then `costFac → ∞` and no finite `P1` can dominate it
for all `n`.  This is the obstruction to
`ConfiguredApproximateDefectPath.Residual.P1_dom` for the unbounded
`eps`-constructed family.

The interface must be weakened to allow `P1` to depend on `n` or to grow
polynomially with `Hs n`.
-/

noncomputable section

open InterpolationFrame InterpolationPathDist

namespace UniformP1Obstruction

theorem costFac_lower_bound
    {kstar L eps : ℝ} (hL : 0 < L) (heps : 0 ≤ eps) (hk : 0 ≤ kstar) :
    2 * L ≤ costFac kstar L eps := by
  unfold costFac
  have h : 1 ≤ Real.exp (rate1Bound kstar L eps) := by
    rw [Real.one_le_exp_iff]
    exact rate1Bound_nonneg hk hL.le heps
  -- 2*L*1 ≤ 2*L*exp
  have h2 : 0 ≤ 2 * L := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h h2]

theorem costFac_unbounded_of_Hs_unbounded
    {kstar : ℝ} (hk : 0 ≤ kstar)
    {Hs : ℕ → ℝ} (hHs_unbounded : ∀ M, ∃ n, M ≤ Hs n)
    {eps : ℕ → ℝ} (heps : ∀ n, 0 ≤ eps n) :
    ¬ ∃ P1 : ℝ, ∀ n, costFac kstar (Hs n) (eps n) ≤ P1 := by
  intro ⟨P1, hP1⟩
  -- Choose M = P1/2 + 1, but ensure M > 0 so Hs n > 0
  let M : ℝ := max (P1 / 2 + 1) 1
  obtain ⟨n, hn⟩ := hHs_unbounded M
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hHpos : 0 < Hs n := lt_of_lt_of_le hMpos hn
  have h1 : 2 * Hs n ≤ costFac kstar (Hs n) (eps n) :=
    costFac_lower_bound hHpos (heps n) hk
  have h2 : costFac kstar (Hs n) (eps n) ≤ P1 := hP1 n
  have hMle : M ≤ Hs n := hn
  have hmax : P1 / 2 + 1 ≤ M := le_max_left _ _
  -- 2*M ≤ 2*Hs n ≤ P1 and P1+2 ≤ 2*M
  linarith

end UniformP1Obstruction
