import Mathlib
import UnitTangentIterates.HairpinPulseDecay

/-!
# The total curvature of the hairpin is `π`

The lemma **Hairpin pulse estimates** of the paper *A Noncircular Oval with
Convex Unit-Tangent Iterates* records the exact mass identity

```
  ∫_ℝ y(s) ds = ∫_ℝ K_*(u) du = π,
```

"the rear tangent turns through `π`".  The change of variable between the two
integrals is `HairpinMass.mass_identity`; this file proves the value `π` of the
second one.

The proof is the fundamental theorem of calculus on the two half-lines: the
tangent angle `θ` is an increasing bijection of `ℝ` onto `(0, π)` with
`θ' = K_*`, so `θ → π` at `+∞` and `θ → 0` at `-∞`, and `K_*` is integrable
because it decays exponentially (`HairpinTails.lean`).

Main results:

* `HairpinRelative.tendsto_theta_atTop`, `HairpinRelative.tendsto_theta_atBot` :
  the limits of the tangent angle at the two ends;
* `HairpinRelative.integrableOn_curv_Ioi`,
  `HairpinRelative.integrableOn_curv_Iic` : integrability of the curvature;
* `HairpinRelative.integral_curv_eq_pi` : `∫_ℝ K_* = π`;
* `HairpinRelative.hairpin_total_curvature` : the same for the hairpin of
  `HairpinArclength.exists_angle`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

open scoped ContDiff

namespace HairpinRelative

variable {f : ℝ → ℝ} {A M : ℝ}

/-! ### The limits of the tangent angle -/

theorem tendsto_theta_atTop {theta : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hsm : StrictMono theta) (hsurj : ∀ x ∈ Ioo (0:ℝ) π, ∃ u, theta u = x) :
    Tendsto theta atTop (𝓝 π) := by
  have hbdd : BddAbove (Set.range theta) := ⟨π, by rintro _ ⟨u, rfl⟩; exact (hmem u).2.le⟩
  have htend := tendsto_atTop_ciSup hsm.monotone hbdd
  have hsup : (⨆ u, theta u) = π := by
    refine le_antisymm (ciSup_le fun u => (hmem u).2.le) ?_
    by_contra hcon
    push_neg at hcon
    set L : ℝ := ⨆ u, theta u with hL
    have hL0 : 0 < L := lt_of_lt_of_le (hmem 0).1 (le_ciSup hbdd 0)
    obtain ⟨u, hu⟩ := hsurj ((L + π) / 2) ⟨by linarith, by linarith⟩
    have : (L + π) / 2 ≤ L := hu ▸ le_ciSup hbdd u
    linarith
  rwa [hsup] at htend

theorem tendsto_theta_atBot {theta : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hsm : StrictMono theta) (hsurj : ∀ x ∈ Ioo (0:ℝ) π, ∃ u, theta u = x) :
    Tendsto theta atBot (𝓝 0) := by
  have hbdd : BddBelow (Set.range theta) := ⟨0, by rintro _ ⟨u, rfl⟩; exact (hmem u).1.le⟩
  have htend := tendsto_atBot_ciInf hsm.monotone hbdd
  have hinf : (⨅ u, theta u) = 0 := by
    refine le_antisymm ?_ (le_ciInf fun u => (hmem u).1.le)
    by_contra hcon
    push_neg at hcon
    set L : ℝ := ⨅ u, theta u with hL
    have hLpi : L < π := lt_of_le_of_lt (ciInf_le hbdd 0) (hmem 0).2
    obtain ⟨u, hu⟩ := hsurj (L / 2) ⟨by linarith, by linarith⟩
    have : L ≤ L / 2 := hu ▸ ciInf_le hbdd u
    linarith
  rwa [hinf] at htend

/-! ### Integrability of the curvature -/

theorem integrableOn_curv_Ioi (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hthetac : Continuous theta) (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M) :
    IntegrableOn (fun u => curvField f (theta u)) (Ioi 0) volume := by
  have hcont : Continuous fun u => curvField f (theta u) :=
    ((contDiff_curvField hf hfpos).continuous).comp hthetac
  have hg : IntegrableOn (fun x : ℝ => A * Real.exp (-(1 / M) * x)) (Ioi 0) volume :=
    (exp_neg_integrableOn_Ioi 0 (by positivity : (0:ℝ) < 1 / M)).const_mul A
  refine Integrable.mono' hg hcont.aestronglyMeasurable.restrict ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  have hx0 : (0:ℝ) ≤ x := le_of_lt hx
  have h1 : curvField f (theta x) ≤ A * Real.exp (-(1 / M) * x) := by
    have := hdecay x
    rwa [abs_of_nonneg hx0, show -x / M = -(1 / M) * x by ring] at this
  have h0 : 0 ≤ curvField f (theta x) := curvField_nonneg hfpos (hmem x)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

theorem integrableOn_curv_Iic (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hthetac : Continuous theta) (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M) :
    IntegrableOn (fun u => curvField f (theta u)) (Iic 0) volume := by
  have hcont : Continuous fun u => curvField f (theta u) :=
    ((contDiff_curvField hf hfpos).continuous).comp hthetac
  have hg : IntegrableOn (fun x : ℝ => A * Real.exp (1 / M * x)) (Iic 0) volume :=
    (integrableOn_exp_mul_Iic (by positivity : (0:ℝ) < 1 / M) 0).const_mul A
  refine Integrable.mono' hg hcont.aestronglyMeasurable.restrict ?_
  refine ae_restrict_of_forall_mem measurableSet_Iic fun x hx => ?_
  have hx0 : x ≤ 0 := hx
  have h1 : curvField f (theta x) ≤ A * Real.exp (1 / M * x) := by
    have := hdecay x
    rwa [abs_of_nonpos hx0, show - -x / M = 1 / M * x by ring] at this
  have h0 : 0 ≤ curvField f (theta x) := curvField_nonneg hfpos (hmem x)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-! ### The total curvature -/

/-- **The rear tangent turns through `π`.**  The total curvature of the hairpin
is `π`. -/
theorem integral_curv_eq_pi (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Ioo 0 π) (hsm : StrictMono theta)
    (hsurj : ∀ x ∈ Ioo (0:ℝ) π, ∃ u, theta u = x)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M) :
    ∫ u, curvField f (theta u) = π := by
  have hthetac : Continuous theta := Differentiable.continuous fun u => (hderiv u).differentiableAt
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hIoi := integrableOn_curv_Ioi hf hfpos hthetac hmem' hdecay hM
  have hIic := integrableOn_curv_Iic hf hfpos hthetac hmem' hdecay hM
  have h1 : (∫ u in Ioi (0:ℝ), curvField f (theta u)) = π - theta 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto hthetac.continuousWithinAt (fun x _ => hderiv x) hIoi
      (tendsto_theta_atTop hmem hsm hsurj)
  have h2 : (∫ u in Iic (0:ℝ), curvField f (theta u)) = theta 0 - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto hthetac.continuousWithinAt (fun x _ => hderiv x) hIic
      (tendsto_theta_atBot hmem hsm hsurj)
  have hsum := intervalIntegral.integral_Iic_add_Ioi hIic hIoi
  rw [h1, h2] at hsum
  linarith [hsum]

/-- **The total curvature of the hairpin of `HairpinArclength.exists_angle`.** -/
theorem hairpin_total_curvature (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ theta : ℝ → ℝ, (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π/2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      ∫ u, curvField f (theta u) = π := by
  have hcontf : Continuous f := hf.continuous
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  obtain ⟨t₁, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hM : 0 < f t₁ := hfpos t₁
  have hlow : ∀ t ∈ Ioo (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ⟨ht.1.le, ht.2.le⟩
  have hup : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ f t₁ := fun t ht => hmax ⟨ht.1.le, ht.2.le⟩
  obtain ⟨theta, hmem, hval, hleft, hsm, -, hderiv⟩ :=
    HairpinArclength.exists_angle hcontf.continuousOn hm hlow
  have hsurj : ∀ x ∈ Ioo (0:ℝ) π, ∃ u, theta u = x := fun x hx =>
    ⟨Hairpin.hairpinArclength f (π/2) x, hleft x hx⟩
  have hA : (0:ℝ) ≤ 2 / f t₀ := by positivity
  have hdecay : ∀ u, curvField f (theta u) ≤ (2 / f t₀) * Real.exp (-|u| / f t₁) := fun u =>
    HairpinArclength.curvature_decay_arclength hcontf.continuousOn hm hlow hup hmem hval u
  exact ⟨theta, hmem, hval, hderiv,
    integral_curv_eq_pi hf hfpos hmem hsm hsurj hderiv hdecay hM⟩

/-! ### A worked instance

The hypotheses are consistent: the constant profile `f ≡ 2` is smooth and
positive on the line. -/

example : ∃ theta : ℝ → ℝ, ∫ u, curvField (fun _ => (2:ℝ)) (theta u) = π := by
  obtain ⟨theta, -, -, -, h⟩ :=
    hairpin_total_curvature (f := fun _ => 2) contDiff_const (fun _ => two_pos)
  exact ⟨theta, h⟩

end HairpinRelative
