import UnitTangentIterates.JacobiEstimates
import UnitTangentIterates.JacobiPathGains

/-!
# The three slicewise gains, as one cost density

§70 reduced the per-path Jacobi bound to a slicewise statement: the pullback
path's cost density `Δ.m t` must dominate `C` times `∫₀¹|Γ.eta t u| du`.  But
the `NormalPath` structure asks a *single* `m t` to dominate the normal field
**and its first two derivatives** (`abs_eta_le`, `le_m_L1`, `le_m_sup` at
`j ≤ 2`).

`JacobiEstimates` supplies the three orders separately:

* `S0_gain` — `|η_R| ≤ (1−e^{−l₀})⁻¹ · ∫|η_F|`;
* `S1_gain` — `|η_{R,x}| ≤ (1/√(1−A²) + 1)·B`;
* `S2_gain` — the second-order constant `κ̂²/c₀³ + 1/c₀ + 1`.

`abs_iteratedDeriv_le_max` and `supNorm_iteratedDeriv_le_max` combine them: the
maximum of the three constants serves for all three orders, which is exactly
what a single cost density needs.

So the remaining content of the per-path Jacobi bound is the *construction* of
the pullback path — supplying a `NormalPath` whose `m` is that maximum times the
slice `L¹` norm — not any further estimate.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real


namespace JacobiEstimates

/-- **The three slicewise gains, combined into one cost density.**  The
`NormalPath` structure asks a single `m t` to dominate the normal field and its
first two derivatives.  `JacobiEstimates` supplies the three orders separately —
`S0_gain`, `S1_gain`, `S2_gain` — with constants `C₀, C₁, C₂`; their maximum
serves for all three. -/
theorem abs_iteratedDeriv_le_max {etaR : ℝ → ℝ} {C0 C1 C2 W : ℝ} (hW : 0 ≤ W)
    (h0 : ∀ x, |etaR x| ≤ C0 * W)
    (h1 : ∀ x, |deriv etaR x| ≤ C1 * W)
    (h2 : ∀ x, |deriv (deriv etaR) x| ≤ C2 * W) :
    ∀ j ≤ 2, ∀ x, |iteratedDeriv j etaR x| ≤ max (max C0 C1) C2 * W := by
  intro j hj x
  have hmax : ∀ C : ℝ, C ≤ max (max C0 C1) C2 → C * W ≤ max (max C0 C1) C2 * W :=
    fun C hC => mul_le_mul_of_nonneg_right hC hW
  interval_cases j
  · rw [iteratedDeriv_zero]
    exact le_trans (h0 x) (hmax C0 (le_trans (le_max_left _ _) (le_max_left _ _)))
  · rw [iteratedDeriv_one]
    exact le_trans (h1 x) (hmax C1 (le_trans (le_max_right _ _) (le_max_left _ _)))
  · rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact le_trans (h2 x) (hmax C2 (le_max_right _ _))

/-- The same conclusion in the `supNorm` form the path structure's `le_m_sup`
field takes. -/
theorem supNorm_iteratedDeriv_le_max {etaR : ℝ → ℝ} {C0 C1 C2 W : ℝ} (hW : 0 ≤ W)
    (h0 : ∀ x, |etaR x| ≤ C0 * W)
    (h1 : ∀ x, |deriv etaR x| ≤ C1 * W)
    (h2 : ∀ x, |deriv (deriv etaR) x| ≤ C2 * W) :
    ∀ j ≤ 2, MarkedTopology.supNorm (iteratedDeriv j etaR)
      ≤ max (max C0 C1) C2 * W := fun j hj =>
  JacobiPathGains.supNorm_le (abs_iteratedDeriv_le_max hW h0 h1 h2 j hj)

end JacobiEstimates
