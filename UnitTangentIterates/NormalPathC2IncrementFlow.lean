import Mathlib
import UnitTangentIterates.NormalPathC2Increment

/-!
# The geometric hypotheses of the increment bound, from the normal-flow
identities

`NormalPathC2Increment.IsConstantSpeedNormalPath` carries the three time
derivatives of the geometric data of a normal path as *bounds* against the cost
density.  Those bounds are not independent data: they are the normal-flow
identities of `NormalFlow.lean`,

```
  g_t = -η θ_u ,        τ_t = η_s ν ,        κ_t = η_ss + κ² η ,
```

together with the two facts that the cost density of a normal path dominates
the sup norms of `η`, `η_u` and `η_uu` (by definition of a normal path) and
that the arclength derivatives are the derivatives in the normalized parameter
divided by the speed: `η_s = η_u/P`, `η_ss = η_uu/P²`.

This file performs that reduction:

* `abs_iteratedDeriv_eta_le` — the cost density dominates `|∂_u^j η|` for
  `j ≤ 2`, which is the content of the fields `le_m_sup` of a normal path;
* `isConstantSpeedNormalPath_of_flow` — the hypothesis bundle of the increment
  bound follows from the normal-flow identities and the tube bounds;
* `dist_le_cost_of_flow` — hence the marked distance of the two ends of the
  path is at most `c2Const P₀ P₁ κ̂` times its cost.
-/

noncomputable section

open Set Function Complex MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
open NormalPathC2Increment

namespace NormalPathC2IncrementFlow

variable {p q : Data}

/-- **The cost density of a normal path dominates the derivatives of its normal
speed**, for `j ≤ 2`: this is the field `le_m_sup`, read pointwise.  The
boundedness hypothesis is what makes the supremum a supremum. -/
theorem abs_iteratedDeriv_eta_le (Γ : NormalPath p q) (t u : ℝ) {j : ℕ} (hj : j ≤ 2)
    (hbdd : BddAbove (range fun v => |iteratedDeriv j (Γ.eta t) v|)) :
    |iteratedDeriv j (Γ.eta t) u| ≤ Γ.m t :=
  le_trans (le_supNorm hbdd u) (Γ.le_m_sup t j hj)

/-- **The hypothesis bundle of the increment bound, from the normal-flow
identities.**  For a normal path whose slices are constant-speed closed curves
of arclength period `P`, tangent angle `θ` and curvature `κ`, the three time
derivatives are given by the normal-flow identities, and the resulting bounds
against the cost density are exactly the hypotheses of
`NormalPathC2Increment.IsConstantSpeedNormalPath`. -/
theorem isConstantSpeedNormalPath_of_flow (Γ : NormalPath p q)
    {P Pd : ℝ → ℝ} {theta kappa etau etauu : ℝ → ℝ → ℝ} {P0 P1 khat : ℝ}
    (hP0 : 0 < P0) (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hkap : ∀ t u, |kappa t u| ≤ khat)
    (hXu : ∀ t u, HasDerivAt (Γ.X t)
      ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hthetau : ∀ t u, HasDerivAt (theta t) (P t * kappa t u) u)
    (hPd : ∀ t, HasDerivAt P (Pd t) t) (hPdc : Continuous Pd)
    (hspeedeq : ∀ t u, Pd t = -(Γ.eta t u * (P t * kappa t u)))
    (hthetat : ∀ t u, HasDerivAt (fun r => theta r u) (etau t u / P t) t)
    (hetauc : ∀ u, Continuous fun t => etau t u / P t)
    (hetau : ∀ t u, |etau t u| ≤ Γ.m t)
    (hkappat : ∀ t u, HasDerivAt (fun r => kappa r u)
      (etauu t u / P t ^ 2 + kappa t u ^ 2 * Γ.eta t u) t)
    (hktc : ∀ u, Continuous fun t => etauu t u / P t ^ 2 + kappa t u ^ 2 * Γ.eta t u)
    (hetauu : ∀ t u, |etauu t u| ≤ Γ.m t) :
    IsConstantSpeedNormalPath P0 P1 khat Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  refine ⟨P, Pd, theta, kappa, fun t u => etau t u / P t,
    fun t u => etauu t u / P t ^ 2 + kappa t u ^ 2 * Γ.eta t u,
    fun t => (hPpos t).le, hPu, hkap, hXu, hthetau, hPd, hPdc, ?_, hthetat, hetauc, ?_,
    hkappat, hktc, ?_⟩
  · -- the speed equation
    intro t
    have hm := Γ.m_nonneg t
    have heta := Γ.abs_eta_le t 0
    have hP1 : P t ≤ P1 := hPu t
    rw [hspeedeq t 0, abs_neg, abs_mul, abs_mul, abs_of_pos (hPpos t)]
    have h1 : |Γ.eta t 0| * P t ≤ Γ.m t * P1 :=
      mul_le_mul heta hP1 (hPpos t).le hm
    have h2 : |Γ.eta t 0| * P t * |kappa t 0| ≤ Γ.m t * P1 * khat := by
      refine mul_le_mul h1 (hkap t 0) (abs_nonneg _) ?_
      exact mul_nonneg hm (le_trans (hPpos t).le hP1)
    calc |Γ.eta t 0| * (P t * |kappa t 0|)
        = |Γ.eta t 0| * P t * |kappa t 0| := by ring
      _ ≤ Γ.m t * P1 * khat := h2
      _ = khat * P1 * Γ.m t := by ring
  · -- the tangent equation
    intro t u
    have hm := Γ.m_nonneg t
    rw [abs_div, abs_of_pos (hPpos t), div_le_iff₀ (hPpos t)]
    have h1 : |etau t u| ≤ Γ.m t := hetau t u
    have h2 : (1 / P0) * Γ.m t * P0 ≤ (1 / P0) * Γ.m t * P t := by
      refine mul_le_mul_of_nonneg_left (hPl t) ?_
      positivity
    have h3 : (1 / P0) * Γ.m t * P0 = Γ.m t := by field_simp
    linarith
  · -- the curvature equation
    intro t u
    have hm := Γ.m_nonneg t
    have heta := Γ.abs_eta_le t u
    have hP0sq : 0 < P0 ^ 2 := by positivity
    have hPsq : 0 < P t ^ 2 := pow_pos (hPpos t) 2
    have h1 : |etauu t u / P t ^ 2| ≤ (1 / P0 ^ 2) * Γ.m t := by
      rw [abs_div, abs_of_pos hPsq, div_le_iff₀ hPsq]
      have hPle : P0 ^ 2 ≤ P t ^ 2 := by nlinarith [hPl t, hP0.le]
      have h2 : (1 / P0 ^ 2) * Γ.m t * P0 ^ 2 = Γ.m t := by field_simp
      have h3 : (1 / P0 ^ 2) * Γ.m t * P0 ^ 2 ≤ (1 / P0 ^ 2) * Γ.m t * P t ^ 2 := by
        refine mul_le_mul_of_nonneg_left hPle ?_
        positivity
      linarith [hetauu t u]
    have h4 : |kappa t u ^ 2 * Γ.eta t u| ≤ khat ^ 2 * Γ.m t := by
      rw [abs_mul, abs_pow]
      have h5 : |kappa t u| ^ 2 ≤ khat ^ 2 := by
        nlinarith [abs_nonneg (kappa t u), hkap t u]
      exact mul_le_mul h5 heta (abs_nonneg _) (by positivity)
    calc |etauu t u / P t ^ 2 + kappa t u ^ 2 * Γ.eta t u|
        ≤ |etauu t u / P t ^ 2| + |kappa t u ^ 2 * Γ.eta t u| := abs_add_le _ _
      _ ≤ (1 / P0 ^ 2) * Γ.m t + khat ^ 2 * Γ.m t := add_le_add h1 h4
      _ = (1 / P0 ^ 2 + khat ^ 2) * Γ.m t := by ring

/-- **The marked distance of the two ends of a normal path, from the
normal-flow identities.**  `NormalPathC2Increment.dist_le_cost` with its
hypothesis bundle produced by `isConstantSpeedNormalPath_of_flow`. -/
theorem dist_le_cost_of_flow {c kmin dlt cq kminq dltq : ℝ} (Γ : NormalPath p q)
    (hp : IsTubeMember c kmin dlt p) (hq : IsTubeMember cq kminq dltq q)
    {P Pd : ℝ → ℝ} {theta kappa etau etauu : ℝ → ℝ → ℝ} {P0 P1 khat : ℝ}
    (hP0 : 0 < P0) (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hkap : ∀ t u, |kappa t u| ≤ khat)
    (hXu : ∀ t u, HasDerivAt (Γ.X t)
      ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hthetau : ∀ t u, HasDerivAt (theta t) (P t * kappa t u) u)
    (hPd : ∀ t, HasDerivAt P (Pd t) t) (hPdc : Continuous Pd)
    (hspeedeq : ∀ t u, Pd t = -(Γ.eta t u * (P t * kappa t u)))
    (hthetat : ∀ t u, HasDerivAt (fun r => theta r u) (etau t u / P t) t)
    (hetauc : ∀ u, Continuous fun t => etau t u / P t)
    (hetau : ∀ t u, |etau t u| ≤ Γ.m t)
    (hkappat : ∀ t u, HasDerivAt (fun r => kappa r u)
      (etauu t u / P t ^ 2 + kappa t u ^ 2 * Γ.eta t u) t)
    (hktc : ∀ u, Continuous fun t => etauu t u / P t ^ 2 + kappa t u ^ 2 * Γ.eta t u)
    (hetauu : ∀ t u, |etauu t u| ≤ Γ.m t) :
    dist p q ≤ c2Const P0 P1 khat * cost Γ :=
  dist_le_cost Γ hp hq
    (isConstantSpeedNormalPath_of_flow Γ hP0 hPl hPu hkap hXu hthetau hPd hPdc hspeedeq
      hthetat hetauc hetau hkappat hktc hetauu)

end NormalPathC2IncrementFlow
