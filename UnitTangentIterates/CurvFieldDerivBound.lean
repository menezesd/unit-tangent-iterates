import UnitTangentIterates.HairpinLowerComparisonInterior

/-!
# The order-one relative bound for the hairpin curvature

The configured-model development needs the case `j = 1` of the paper's
`eq:relative-y-derivatives` **for the curvature** `K_* = G ∘ θ`, not for the
pulse:

```
  |K_*'(u)| ≤ D₁ K_*(u).
```

This is not an independent assumption.  Since `θ' = G(θ)`, the chain rule gives
`K_*' = G'(θ) · G(θ) = G'(θ) · K_*`, so the bound holds with `D₁` any bound for
`|G'|` on the interior.  And `G = sin t / f t`, so the paper's own barriers
`m ≤ f ≤ Am` together with a bound `|f'| ≤ F₁` on `(0, π)` give

```
  |G'| ≤ (Am + F₁)/m².
```

Main results:

* `HairpinRelative.abs_deriv_curvField_le` : `|G'(t)| ≤ (Am + F₁)/m²`;
* `HairpinRelative.abs_deriv_curv_along_theta_le` : the chain-rule step;
* `HairpinRelative.relK_of_profile_barriers` : the two combined.
-/

noncomputable section

open Set Real

open scoped ContDiff

namespace HairpinRelative

theorem abs_deriv_curvField_le {f : ℝ → ℝ} {m Am F1 t : ℝ}
    (hm : 0 < m) (hlow : m ≤ f t) (hupp : f t ≤ Am)
    (hdf : DifferentiableAt ℝ f t) (hF1 : |deriv f t| ≤ F1) :
    |deriv (curvField f) t| ≤ (Am + F1) / m ^ 2 := by
  have hft : 0 < f t := lt_of_lt_of_le hm hlow
  have hd : HasDerivAt (curvField f)
      ((Real.cos t * f t - Real.sin t * deriv f t) / f t ^ 2) t :=
    (Real.hasDerivAt_sin t).div hdf.hasDerivAt hft.ne'
  have hF0 : 0 ≤ F1 := le_trans (abs_nonneg _) hF1
  have hnum : |Real.cos t * f t - Real.sin t * deriv f t| ≤ Am + F1 := by
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul, abs_mul, abs_of_pos hft]
    have h1 : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
    have h2 : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
    nlinarith [abs_nonneg (deriv f t), abs_nonneg (Real.cos t),
      abs_nonneg (Real.sin t), hft.le]
  have hden : m ^ 2 ≤ f t ^ 2 := by nlinarith
  rw [hd.deriv, abs_div, abs_of_pos (by positivity : (0:ℝ) < f t ^ 2)]
  exact div_le_div₀ (by linarith) hnum (by positivity) hden

theorem abs_deriv_curv_along_theta_le
    {f theta : ℝ → ℝ} {D1 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hGb : ∀ t ∈ Ioo (0:ℝ) π, |deriv (curvField f) t| ≤ D1) :
    ∀ u, |deriv (fun r => curvField f (theta r)) u| ≤
      D1 * curvField f (theta u) := by
  intro u
  have hGon : ContDiffOn ℝ ∞ (curvField f) (Ioo 0 π) :=
    HairpinInteriorRegularity.contDiffOn_curvField hf hfpos
  have hdiff : DifferentiableAt ℝ (curvField f) (theta u) :=
    (hGon.contDiffAt (isOpen_Ioo.mem_nhds (hmem u))).differentiableAt (by norm_num)
  have hGd : HasDerivAt (curvField f) (deriv (curvField f) (theta u)) (theta u) :=
    hdiff.hasDerivAt
  have hcomp : HasDerivAt (fun r => curvField f (theta r))
      (deriv (curvField f) (theta u) * curvField f (theta u)) u :=
    hGd.comp u (hderiv u)
  rw [hcomp.deriv, abs_mul]
  have hK0 : 0 ≤ curvField f (theta u) := (curvField_pos_interior hfpos (hmem u)).le
  rw [abs_of_nonneg hK0]
  exact mul_le_mul_of_nonneg_right (hGb _ (hmem u)) hK0

/-- **The order-one relative curvature bound from the profile barriers.**

CAUTION.  The hypothesis `|f'| ≤ F₁` on `(0, π)` is *stronger* than what the
paper proves, and its satisfiability for the constructed profile is not
established anywhere in this development.  The paper's own route
(`eq:bounded-shift-Harnack` plus `eq:translator-curvature-identity`) bounds only
`sin t · f'`, never `f'` itself; see `PulseRelativeFromIdentity`.  This lemma is
sound, but do not read it as the paper's argument or assume its hypothesis is
dischargeable. -/
theorem relK_of_profile_barriers {f theta : ℝ → ℝ} {m Am F1 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am)
    (hF1 : ∀ t ∈ Ioo (0:ℝ) π, |deriv f t| ≤ F1)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) :
    ∀ u, |deriv (fun r => curvField f (theta r)) u| ≤
      ((Am + F1) / m ^ 2) * curvField f (theta u) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  refine abs_deriv_curv_along_theta_le hf hfpos hmem hderiv ?_
  intro t ht
  have hdf : DifferentiableAt ℝ f t :=
    (hf.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num)
  exact abs_deriv_curvField_le hm (hlow t ht) (hupp t ht) hdf (hF1 t ht)

/-- The constant is nonnegative. -/
theorem relK_const_nonneg {m Am F1 : ℝ} (hm : 0 < m) (hmA : 0 ≤ Am)
    (hF0 : 0 ≤ F1) : 0 ≤ (Am + F1) / m ^ 2 := by positivity

/-- **Bounded derivative of the isolated curvature, from interior data.**  This
is `MatchingHairpin.exists_curv_derivative_bounds` with the global profile
hypotheses replaced by the interior ones: the relative bound supplies the
derivative bound once the curvature itself is bounded. -/
theorem exists_curv_derivative_bounds_of_interior {f theta : ℝ → ℝ} {D1 Km : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hD1 : 0 ≤ D1)
    (hrelK : ∀ u, |deriv (fun r => curvField f (theta r)) u| ≤
      D1 * curvField f (theta u))
    (hbd : ∀ u, curvField f (theta u) ≤ Km) :
    ∃ Kstar' : ℝ → ℝ, ∃ Kd : ℝ,
      (∀ u, HasDerivAt (fun u => curvField f (theta u)) (Kstar' u) u) ∧
        ∀ u, |Kstar' u| ≤ Kd := by
  have hGon : ContDiffOn ℝ ∞ (curvField f) (Ioo 0 π) :=
    HairpinInteriorRegularity.contDiffOn_curvField hf hfpos
  have hdiff : Differentiable ℝ fun u => curvField f (theta u) := by
    intro u
    exact ((hGon.contDiffAt (isOpen_Ioo.mem_nhds (hmem u))).differentiableAt
      (by norm_num)).comp u (hderiv u).differentiableAt
  refine ⟨deriv fun u => curvField f (theta u), D1 * Km,
    fun u => (hdiff u).hasDerivAt, fun u => ?_⟩
  exact le_trans (hrelK u) (mul_le_mul_of_nonneg_left (hbd u) hD1)

end HairpinRelative
