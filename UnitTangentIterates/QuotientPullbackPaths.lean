import UnitTangentIterates.MarkedShiftPathFromInfimum
import UnitTangentIterates.TubePullbackLimit

/-!
# Pullback paths from a phase-quotient Lipschitz estimate

This is the paper-faithful recursion behind compatible markings.  A model
defect is propagated only as a bound in the path pseudodistance modulo phase.
No transported path density is reused as the source of a later analytic row.
After the scalar recursion is complete, an actual phase and normal path are
chosen independently at each finite pullback edge.
-/

noncomputable section

open MarkedSpace PathMetric PathMetric.NormalPath MarkedShift

namespace QuotientPullbackPaths

/-- The honest error at pullback depth `k`. -/
def pullbackError (K : ℝ) (d : ℕ → ℝ) (n k : ℕ) : ℝ :=
  K ^ k * d (n + k)

theorem pullbackError_nonnegative
    {K : ℝ} {d : ℕ → ℝ} (hK : 0 ≤ K) (hd : ∀ n, 0 ≤ d n) :
    ∀ n k, 0 ≤ pullbackError K d n k := by
  intro n k
  exact mul_nonneg (pow_nonneg hK k) (hd (n + k))

/-- Iterating a `K`-Lipschitz selected inverse in the phase quotient propagates
the model defect by exactly `K^k`. -/
theorem pathDistShift_pullback_succ_le
    {B : Data → Data} {Q : ℕ → Data} {K : ℝ} {d : ℕ → ℝ}
    (hK : 0 ≤ K)
    (hlip : ∀ p q,
      pathDistShift (B p) (B q) ≤ K * pathDistShift p q)
    (hdefect : ∀ n, pathDistShift (Q n) (B (Q (n + 1))) ≤ d n) :
    ∀ n k,
      pathDistShift (TubePullbackLimit.pullback B Q n k)
          (TubePullbackLimit.pullback B Q n (k + 1)) ≤
        pullbackError K d n k := by
  intro n k
  induction k generalizing n with
  | zero =>
      simpa [TubePullbackLimit.pullback, pullbackError] using hdefect n
  | succ k ih =>
      rw [TubePullbackLimit.pullback_succ,
        TubePullbackLimit.pullback_succ]
      calc
        pathDistShift
            (B (TubePullbackLimit.pullback B Q (n + 1) k))
            (B (TubePullbackLimit.pullback B Q (n + 1) (k + 1))) ≤
            K * pathDistShift
              (TubePullbackLimit.pullback B Q (n + 1) k)
              (TubePullbackLimit.pullback B Q (n + 1) (k + 1)) :=
          hlip _ _
        _ ≤ K * pullbackError K d (n + 1) k :=
          mul_le_mul_of_nonneg_left (ih (n + 1)) hK
        _ = pullbackError K d n (k + 1) := by
          simp [pullbackError, pow_succ]
          ring

/-- Choose the compatible marking and a concrete normal path at every finite
pullback edge.  The slack is external so callers may choose a summable
triangular sequence. -/
theorem exists_shift_pullback_step_path
    {B : Data → Data} {Q : ℕ → Data} {K : ℝ} {d : ℕ → ℝ}
    (hK : 0 ≤ K)
    (hlip : ∀ p q,
      pathDistShift (B p) (B q) ≤ K * pathDistShift p q)
    (hdefect : ∀ n, pathDistShift (Q n) (B (Q (n + 1))) ≤ d n)
    (hne : ∀ n k b, Nonempty (NormalPath
      (TubePullbackLimit.pullback B Q n k)
      (shiftData b (TubePullbackLimit.pullback B Q n (k + 1)))))
    {eps : ℕ → ℕ → ℝ} (heps : ∀ n k, 0 < eps n k) :
    ∀ n k, ∃ b : ℝ, ∃ Gamma : NormalPath
        (TubePullbackLimit.pullback B Q n k)
        (shiftData b (TubePullbackLimit.pullback B Q n (k + 1))),
      cost Gamma ≤ pullbackError K d n k + 2 * eps n k := by
  intro n k
  exact MarkedShift.exists_shift_path_of_pathDistShift_le
    (heps n k) (hne n k)
    (pathDistShift_pullback_succ_le hK hlip hdefect n k)

end QuotientPullbackPaths
