import Mathlib
import UnitTangentIterates.HairpinTotalMass
import UnitTangentIterates.HairpinDefect
import UnitTangentIterates.HairpinMass

/-!
# The steering mass of the hairpin is `π`

The mass identity of the lemma **Hairpin pulse estimates** of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates* reads

```
  ∫_ℝ y(s) ds = ∫_ℝ K_*(u) du = π.
```

`HairpinTotalMass.lean` proves the second equality; `HairpinMass.mass_identity`
proves the first one on a bounded interval, `∫_{σ(a)}^{σ(b)} y = ∫_a^b K_*`,
by the change of variables `s = σ(u)`.  This file lets `a → -∞`, `b → +∞`:
both integrands are integrable (they decay exponentially) and `σ(u) - u` is
bounded, so the two interval integrals converge to the two integrals over the
line, and the steering mass is `π` as well.

Main results:

* `HairpinRelative.integrable_of_exp_bound` : a continuous nonnegative function
  dominated by `A e^{-|s|/M}` is integrable;
* `HairpinRelative.hairpin_pulse_mass` : the same canonical pulse is
  integrable and satisfies `∫_ℝ y = π`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

open scoped ContDiff

namespace HairpinRelative

variable {f : ℝ → ℝ} {A M : ℝ}

/-- A continuous nonnegative function dominated by `A e^{-|s|/M}` is
integrable. -/
theorem integrable_of_exp_bound {g : ℝ → ℝ} (hcont : Continuous g) (hnn : ∀ s, 0 ≤ g s)
    (hb : ∀ s, g s ≤ A * Real.exp (-|s| / M)) (hM : 0 < M) : Integrable g := by
  have hg : Integrable (fun s : ℝ => A * Real.exp (-(1 / M) * |s|)) :=
    (integrable_exp_neg_mul_abs (by positivity : (0:ℝ) < 1 / M)).const_mul A
  refine Integrable.mono' hg hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn s)]
  have := hb s
  rwa [show -|s| / M = -(1 / M) * |s| by ring] at this

/-- **The steering mass of the hairpin is `π`.** -/
theorem hairpin_pulse_mass (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ theta x : ℝ → ℝ, (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π/2) (theta u) = u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      Integrable (fun s => pulseField f (theta (x s))) ∧
      ∫ s, pulseField f (theta (x s)) = π := by
  have hcontf : Continuous f := hf.continuous
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  obtain ⟨t₁, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hMpos : 0 < f t₁ := hfpos t₁
  have hlow : ∀ t ∈ Ioo (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ⟨ht.1.le, ht.2.le⟩
  have hup : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ f t₁ := fun t ht => hmax ⟨ht.1.le, ht.2.le⟩
  obtain ⟨theta, hmem, hval, hleft, hsm, hthetac, hderiv⟩ :=
    HairpinArclength.exists_angle hcontf.continuousOn hm hlow
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hderiv' : ∀ u, HasDerivAt theta (curvField f (theta u)) u := hderiv
  have hA : (0:ℝ) ≤ 2 / f t₀ := by positivity
  have hdecay : ∀ u, curvField f (theta u) ≤ (2 / f t₀) * Real.exp (-|u| / f t₁) := fun u =>
    HairpinArclength.curvature_decay_arclength hcontf.continuousOn hm hlow hup hmem hval u
  obtain ⟨x, hxinv, -, hxderiv⟩ := exists_pulseState hf hfpos hmem' hderiv'
  -- the two integrands
  set K : ℝ → ℝ := fun u => curvField f (theta u) with hK
  set y : ℝ → ℝ := fun s => pulseField f (theta (x s)) with hy
  have hKcont : Continuous K := ((contDiff_curvField hf hfpos).continuous).comp hthetac
  have hycont : Continuous y :=
    Differentiable.continuous fun s => by
      have := hxderiv s
      exact (((contDiff_pulseField hf hfpos).differentiable (by simp)).differentiableAt).comp s
        (this.differentiableAt)
  -- the front arclength and its inverse
  have hsigderiv : ∀ u, HasDerivAt (frontArclength f theta)
      (Real.sqrt (1 + K u ^ 2)) u := hasDerivAt_frontArclength hf hfpos hthetac
  have hge : ∀ u, (1:ℝ) ≤ Real.sqrt (1 + K u ^ 2) := by
    intro u
    have h1 : (1:ℝ) ≤ 1 + K u ^ 2 := by nlinarith [sq_nonneg (K u)]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have hsigmono : StrictMono (frontArclength f theta) :=
    ArclengthInverse.strictMono_of_deriv_ge (c := 1) one_pos hsigderiv hge
  have hxleft : ∀ u, x (frontArclength f theta u) = u := fun u =>
    ArclengthInverse.leftInverse_of_rightInverse hsigmono.injective hxinv u
  -- the mass identity on a bounded interval
  have hmass : ∀ a b : ℝ,
      (∫ s in (frontArclength f theta a)..(frontArclength f theta b), y s) = ∫ u in a..b, K u := by
    intro a b
    refine HairpinMass.mass_identity (fun u _ => hsigderiv u) hKcont hycont ?_
    intro u
    show pulseField f (theta (x (frontArclength f theta u))) = K u / Real.sqrt (1 + K u ^ 2)
    rw [hxleft u, pulseField]
  -- the two integrands are integrable
  have hKnn : ∀ u, 0 ≤ K u := fun u => curvField_nonneg hfpos (hmem' u)
  have hKint : Integrable K := integrable_of_exp_bound hKcont hKnn hdecay hMpos
  have hybound : ∀ s, y s
      ≤ (2 / f t₀) * Real.exp ((2 / f t₀) ^ 2 / 2) * Real.exp (-|s| / f t₁) :=
    fun s => pulse_decay hf hfpos hthetac hmem' hdecay hA hMpos hxinv s
  have hynn : ∀ s, 0 ≤ y s := fun s => pulseField_nonneg hfpos (hmem' _)
  have hyint : Integrable y := integrable_of_exp_bound hycont hynn hybound hMpos
  -- pass to the limit
  have hsigTop : Tendsto (fun t : ℝ => frontArclength f theta t) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℝ))
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    have := ArclengthInverse.le_of_deriv_ge (c := 1) hsigderiv hge hu
    rw [frontArclength_zero] at this
    simpa using this
  have hsigBot : Tendsto (fun t : ℝ => frontArclength f theta (-t)) atTop atBot := by
    have h : Tendsto (fun t : ℝ => frontArclength f theta t) atBot atBot := by
      refine tendsto_atBot_mono' atBot ?_ (tendsto_id (α := ℝ))
      filter_upwards [eventually_le_atBot (0:ℝ)] with u hu
      have := ArclengthInverse.ge_of_deriv_ge (c := 1) hsigderiv hge hu
      rw [frontArclength_zero] at this
      simpa using this
    exact h.comp tendsto_neg_atTop_atBot
  have h1 : Tendsto (fun t : ℝ =>
      ∫ s in (frontArclength f theta (-t))..(frontArclength f theta t), y s) atTop (𝓝 (∫ s, y s)) :=
    intervalIntegral_tendsto_integral hyint hsigBot hsigTop
  have h2 : Tendsto (fun t : ℝ => ∫ u in (-t)..t, K u) atTop (𝓝 (∫ u, K u)) :=
    intervalIntegral_tendsto_integral hKint tendsto_neg_atTop_atBot (tendsto_id (α := ℝ))
  have heq : (fun t : ℝ =>
      ∫ s in (frontArclength f theta (-t))..(frontArclength f theta t), y s)
      = fun t : ℝ => ∫ u in (-t)..t, K u := by
    funext t
    exact hmass (-t) t
  rw [heq] at h1
  have hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z := fun z hz =>
    ⟨Hairpin.hairpinArclength f (π/2) z, hleft z hz⟩
  have hpi : (∫ u, K u) = π :=
    integral_curv_eq_pi hf hfpos hmem hsm hsurj hderiv' hdecay hMpos
  have hyk : (∫ s, y s) = ∫ u, K u := tendsto_nhds_unique h1 h2
  refine ⟨theta, x, hmem, hval, hxinv, ?_, ?_⟩
  · simpa [hy] using hyint
  have hfin : (∫ s, y s) = π := by rw [hyk, hpi]
  simpa [hy] using hfin

/-! ### A worked instance

The hypotheses are consistent: the constant profile `f ≡ 2` is smooth and
positive on the line. -/

example : ∃ theta x : ℝ → ℝ, ∫ s, pulseField (fun _ => (2:ℝ)) (theta (x s)) = π := by
  obtain ⟨theta, x, -, -, -, -, h⟩ :=
    hairpin_pulse_mass (f := fun _ => 2) contDiff_const (fun _ => two_pos)
  exact ⟨theta, x, h⟩

end HairpinRelative
