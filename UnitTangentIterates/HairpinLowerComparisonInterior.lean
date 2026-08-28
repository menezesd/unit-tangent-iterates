import Mathlib
import UnitTangentIterates.HairpinLowerComparison
import UnitTangentIterates.HairpinTailsInterior
import UnitTangentIterates.HairpinInteriorRegularity

/-!
# The lower comparison `K_* ≥ b₀ y` from interior data

`HairpinRelative.hairpin_curv_ge_pulse` proves the last estimate of the paper's
lemma **Hairpin pulse estimates** from a profile that is smooth and positive on
*all* of `ℝ`, and it *constructs* the coordinates `θ, x` itself by compactness
on the closed interval `[0, π]`.

The paper assigns no endpoint values (`thm:hairpin`: "No endpoint values are
assigned"), so the profile is only `C^∞` on the open interval `(0, π)`, and in
the quantitative package the coordinates are *given*, not constructed.  This
file redoes the comparison in that setting:

* the compactness extraction of `min f` and `max f` over `[0, π]` is replaced by
  the paper's own barrier hypotheses on `(0, π)`;
* the constructed coordinates are replaced by the given ones;
* the relative bound `|K_*'| ≤ D₁ K_*` — case `j = 1` of the paper's
  `eq:relative-y-derivatives` — is taken as a hypothesis rather than re-derived.

The abstract engine `HairpinMass.Kstar_lower_bound` is reused verbatim: it was
already stated purely in terms of `K`, its logarithmic derivative, the bounded
shift and the exact identity `K(x(s)) = y(s)/c(s)`.

Main results:

* `HairpinTailsInterior.abs_frontArclength_sub_le_of_comp` : the bounded shift
  `|σ(u) − u| ≤ A²M/2` in difference form, from interior data;
* `HairpinRelative.hairpin_curv_ge_pulse_interior` : `K_*(s) ≥ b₀ y(s)`.
-/

noncomputable section

open Real Set

open scoped ContDiff

namespace HairpinTailsInterior

open HairpinRelative

variable {f theta : ℝ → ℝ} {A M : ℝ}

/-- **The bounded shift between the two arclengths, in difference form.**  This
is `HairpinRelative.abs_frontArclength_sub_le` with the global smoothness and
positivity of the profile replaced by continuity of the curvature along the
angle — the only consequence of them that the proof uses. -/
theorem abs_frontArclength_sub_le_of_comp
    (hkc : Continuous fun t => curvField f (theta t))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    (u : ℝ) : |frontArclength f theta u - u| ≤ A ^ 2 * M / 2 := by
  have hderiv := hasDerivAt_frontArclength_of_comp hkc
  have hge : ∀ t, (1:ℝ) ≤ Real.sqrt (1 + curvField f (theta t) ^ 2) := by
    intro t
    have h1 : (1:ℝ) ≤ 1 + curvField f (theta t) ^ 2 := by
      nlinarith [sq_nonneg (curvField f (theta t))]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt h1
  rcases le_or_gt 0 u with hu | hu
  · have h1 : u ≤ frontArclength f theta u := by
      have h := ArclengthInverse.le_of_deriv_ge (c := 1) hderiv hge hu
      rw [frontArclength_zero] at h
      linarith
    have h2 := frontArclength_le_of_comp hkc hnn hdecay hM hu
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ frontArclength f theta u - u)]
    linarith
  · have h1 : frontArclength f theta u ≤ u := by
      have h := ArclengthInverse.ge_of_deriv_ge (c := 1) hderiv hge hu.le
      rw [frontArclength_zero] at h
      linarith
    have h2 := le_frontArclength_of_comp hkc hnn hdecay hM hu.le
    rw [abs_of_nonpos (by linarith : frontArclength f theta u - u ≤ 0)]
    linarith

end HairpinTailsInterior

namespace HairpinRelative

variable {f : ℝ → ℝ}

/-- The hairpin curvature is positive at interior angles, from interior
positivity of the profile alone. -/
theorem curvField_pos_interior {t : ℝ}
    (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t) (ht : t ∈ Ioo (0:ℝ) π) :
    0 < curvField f t :=
  div_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2) (hfpos t ht)

/-- The steering pulse is nonnegative at interior angles. -/
theorem pulseField_nonneg_interior {t : ℝ}
    (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t) (ht : t ∈ Ioo (0:ℝ) π) :
    0 ≤ pulseField f t :=
  div_nonneg (curvField_pos_interior hfpos ht).le (Real.sqrt_nonneg _)

/-- **The lower comparison `K_* ≥ b₀ y`, from interior data.**

This is `hairpin_curv_ge_pulse` with every appeal to the closed interval
removed.  The profile is smooth and positive only on `(0, π)`; the coordinates
`θ` and `x` are given rather than constructed; and the order-one relative bound
is a hypothesis.  The constant is explicit: `b₀ = exp(−D₁A²M/2)`. -/
theorem hairpin_curv_ge_pulse_interior
    {theta x : ℝ → ℝ} {A M D1 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M) (hD1 : 0 ≤ D1)
    (hrel : ∀ u,
      |deriv (fun r => curvField f (theta r)) u| ≤ D1 * curvField f (theta u)) :
    ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ s, b₀ * pulseField f (theta (x s)) ≤ curvField f (theta s) := by
  have hGon : ContDiffOn ℝ ∞ (curvField f) (Ioo 0 π) :=
    HairpinInteriorRegularity.contDiffOn_curvField hf hfpos
  have hthetac : Continuous theta :=
    Differentiable.continuous fun u => (hderiv u).differentiableAt
  have hkc : Continuous fun t => curvField f (theta t) :=
    hGon.continuousOn.comp_continuous hthetac hmem
  set K : ℝ → ℝ := fun u => curvField f (theta u) with hKdef
  have hKpos : ∀ u, 0 < K u := fun u => curvField_pos_interior hfpos (hmem u)
  have hnn : ∀ u, 0 ≤ curvField f (theta u) := fun u => (hKpos u).le
  have hKdiff : ∀ u, DifferentiableAt ℝ K u := by
    intro u
    have h1 : DifferentiableAt ℝ (curvField f) (theta u) :=
      (hGon.contDiffAt (isOpen_Ioo.mem_nhds (hmem u))).differentiableAt (by norm_num)
    exact h1.comp u (hderiv u).differentiableAt
  have hlog : ∀ u, HasDerivAt (fun r => Real.log (K r)) (deriv K u / K u) u :=
    fun u => ((hKdiff u).hasDerivAt).log (hKpos u).ne'
  have hCbound : ∀ u, |deriv K u / K u| ≤ D1 := by
    intro u
    rw [abs_div, abs_of_pos (hKpos u), div_le_iff₀ (hKpos u)]
    exact hrel u
  have hshift : ∀ s, |s - x s| ≤ A ^ 2 * M / 2 := by
    intro s
    have h :=
      HairpinTailsInterior.abs_frontArclength_sub_le_of_comp hkc hnn hdecay hM (x s)
    rw [hxinv s] at h
    exact h
  set c : ℝ → ℝ := fun s => 1 / Real.sqrt (1 + curvField f (theta (x s)) ^ 2) with hc
  have hsqrtpos : ∀ s, 0 < Real.sqrt (1 + curvField f (theta (x s)) ^ 2) := fun s =>
    sqrt_one_add_sq_pos _
  have hc0 : ∀ s, 0 < c s := fun s => by rw [hc]; exact div_pos one_pos (hsqrtpos s)
  have hc1 : ∀ s, c s ≤ 1 := by
    intro s
    have h1 : (1:ℝ) ≤ Real.sqrt (1 + curvField f (theta (x s)) ^ 2) := by
      have h : (1:ℝ) ≤ 1 + curvField f (theta (x s)) ^ 2 := by
        nlinarith [sq_nonneg (curvField f (theta (x s)))]
      calc (1:ℝ) = Real.sqrt 1 := by simp
        _ ≤ _ := Real.sqrt_le_sqrt h
    rw [hc, div_le_one (hsqrtpos s)]
    exact h1
  have hid : ∀ s, K (x s) = pulseField f (theta (x s)) / c s := by
    intro s
    rw [hc, pulseField, hKdef]
    field_simp
  have hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)) := fun s =>
    pulseField_nonneg_interior hfpos (hmem _)
  refine ⟨Real.exp (-D1 * (A ^ 2 * M / 2)), Real.exp_pos _, fun s => ?_⟩
  exact HairpinMass.Kstar_lower_bound hKpos hlog hCbound hD1 hshift hy0 hc0 hc1 hid s

end HairpinRelative
