import Mathlib
import UnitTangentIterates.HairpinPulseDecay

/-!
# The arclength defect of the hairpin is finite and positive

The lemma **Hairpin pulse estimates** of the paper *A Noncircular Oval with
Convex Unit-Tangent Iterates* records, besides the mass identity, the
*defect*

```
  Δ := ∫_ℝ (1 - c(s)) ds > 0,      c = cos δ = 1/√(1 + K_*²),
```

finite because `1 - c = O(y²)` and positive because `y ≢ 0`.

This file proves both statements for the hairpin: with the pulse field
`G₂ = sin ∘ arctan ∘ G` of `HairpinRelativeDerivatives.lean`, the defect field
is `1 - 1/√(1+G²)`, it is dominated by `G₂²` and hence integrable along the
pulse state (whose pulse decays exponentially, `HairpinPulseDecay.lean`), and
it is *strictly* positive at every point, because the curvature of the hairpin
never vanishes; so its integral is positive.

Main results:

* `HairpinRelative.defectField_le_pulseField_sq` : `1 - c ≤ y²`;
* `HairpinRelative.defectField_pos` : `1 - c > 0` at every interior angle;
* `HairpinRelative.integrable_defect` : the defect is integrable;
* `HairpinRelative.defect_pos` : `Δ > 0`;
* `HairpinRelative.hairpin_defect` : both statements for the hairpin of
  `HairpinArclength.exists_angle`.
-/

noncomputable section

open Real Set MeasureTheory Filter

open scoped ContDiff

namespace HairpinRelative

variable {f : ℝ → ℝ} {A M : ℝ}

/-- The **defect field** `1 - c = 1 - 1/√(1 + K_*²)`, as a function of the
tangent angle of the rear track. -/
def defectField (f : ℝ → ℝ) (t : ℝ) : ℝ := 1 - 1 / Real.sqrt (1 + curvField f t ^ 2)

theorem one_le_sqrt_one_add_curv_sq (t : ℝ) : (1:ℝ) ≤ Real.sqrt (1 + curvField f t ^ 2) := by
  have h : (1:ℝ) ≤ 1 + curvField f t ^ 2 := by nlinarith [sq_nonneg (curvField f t)]
  calc (1:ℝ) = Real.sqrt 1 := by simp
    _ ≤ _ := Real.sqrt_le_sqrt h

theorem defectField_nonneg (t : ℝ) : 0 ≤ defectField f t := by
  have h := one_le_sqrt_one_add_curv_sq (f := f) t
  have h0 : (0:ℝ) < Real.sqrt (1 + curvField f t ^ 2) := lt_of_lt_of_le one_pos h
  rw [defectField, sub_nonneg]
  rw [div_le_one h0]
  exact h

/-- `1 - c ≤ y²`. -/
theorem defectField_le_pulseField_sq (t : ℝ) : defectField f t ≤ pulseField f t ^ 2 := by
  have h1 : (1:ℝ) ≤ Real.sqrt (1 + curvField f t ^ 2) := one_le_sqrt_one_add_curv_sq t
  set r : ℝ := Real.sqrt (1 + curvField f t ^ 2) with hr
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le one_pos h1
  have hsq : r ^ 2 = 1 + curvField f t ^ 2 := Real.sq_sqrt (by positivity)
  have hk : curvField f t ^ 2 = r ^ 2 - 1 := by linarith
  have hp : pulseField f t ^ 2 = (r ^ 2 - 1) / r ^ 2 := by
    rw [pulseField, div_pow, ← hr, hk]
  have key : (r ^ 2 - 1) / r ^ 2 - (1 - 1 / r) = (r - 1) / r ^ 2 := by
    field_simp
    ring
  have hnn : 0 ≤ (r - 1) / r ^ 2 :=
    div_nonneg (by linarith) (by positivity)
  rw [defectField, ← hr, hp]
  linarith

/-- The defect is strictly positive wherever the curvature is. -/
theorem defectField_pos (hfpos : ∀ t, 0 < f t) {t : ℝ} (ht : t ∈ Ioo 0 π) :
    0 < defectField f t := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hk : 0 < curvField f t := div_pos hs (hfpos t)
  have h1 : (1:ℝ) < 1 + curvField f t ^ 2 := by nlinarith
  have h2 : (1:ℝ) < Real.sqrt (1 + curvField f t ^ 2) := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ < _ := by
          refine Real.sqrt_lt_sqrt (by norm_num) h1
  rw [defectField, sub_pos, div_lt_one (lt_trans one_pos h2)]
  exact h2

theorem continuous_defectField (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    Continuous (defectField f) := by
  have hG : Continuous (curvField f) := (contDiff_curvField hf hfpos).continuous
  have hs : Continuous fun t => Real.sqrt (1 + curvField f t ^ 2) :=
    (continuous_const.add (hG.pow 2)).sqrt
  refine continuous_const.sub (continuous_const.div hs fun t => ?_)
  exact ne_of_gt (lt_of_lt_of_le one_pos (one_le_sqrt_one_add_curv_sq t))

/-- `s ↦ e^{-b|s|}` is integrable on the line, for `b > 0`. -/
theorem integrable_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun s : ℝ => Real.exp (-b * |s|)) := by
  have h1 : IntegrableOn (fun s : ℝ => Real.exp (-b * |s|)) (Iic 0) volume := by
    refine IntegrableOn.congr_fun (integrableOn_exp_mul_Iic hb 0) ?_ measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := hx
    simp only []
    rw [abs_of_nonpos hx']; ring_nf
  have h2 : IntegrableOn (fun s : ℝ => Real.exp (-b * |s|)) (Ioi 0) volume := by
    refine IntegrableOn.congr_fun (exp_neg_integrableOn_Ioi 0 hb) ?_ measurableSet_Ioi
    intro x hx
    have hx' : (0:ℝ) ≤ x := le_of_lt hx
    simp only []
    rw [abs_of_nonneg hx']
  have := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-! ### The defect of the hairpin -/

/-- **The defect is integrable**, because it is dominated by the square of the
exponentially decaying pulse. -/
theorem integrable_defect (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {w : ℝ → ℝ} (hwc : Continuous w) (hmem : ∀ s, w s ∈ Icc 0 π)
    (hbound : ∀ s, pulseField f (w s) ≤ A * Real.exp (-|s| / M)) (hM : 0 < M) :
    Integrable (fun s => defectField f (w s)) := by
  have hcont : Continuous fun s => defectField f (w s) :=
    (continuous_defectField hf hfpos).comp hwc
  have hg : Integrable (fun s : ℝ => A ^ 2 * Real.exp (-(2 / M) * |s|)) :=
    (integrable_exp_neg_mul_abs (by positivity : (0:ℝ) < 2 / M)).const_mul (A ^ 2)
  refine Integrable.mono' hg hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  have h0 : 0 ≤ pulseField f (w s) := pulseField_nonneg hfpos (hmem s)
  have h1 : pulseField f (w s) ^ 2 ≤ (A * Real.exp (-|s| / M)) ^ 2 :=
    pow_le_pow_left₀ h0 (hbound s) 2
  have h2 : (A * Real.exp (-|s| / M)) ^ 2 = A ^ 2 * Real.exp (-(2 / M) * |s|) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have h3 : defectField f (w s) ≤ pulseField f (w s) ^ 2 := defectField_le_pulseField_sq _
  rw [Real.norm_eq_abs, abs_of_nonneg (defectField_nonneg _)]
  calc defectField f (w s) ≤ pulseField f (w s) ^ 2 := h3
    _ ≤ (A * Real.exp (-|s| / M)) ^ 2 := h1
    _ = A ^ 2 * Real.exp (-(2 / M) * |s|) := h2

/-- **The defect is positive.**  The curvature of the hairpin never vanishes, so
the defect field is positive at every point of the line. -/
theorem defect_pos (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {w : ℝ → ℝ} (hwc : Continuous w) (hmem : ∀ s, w s ∈ Ioo 0 π)
    (hbound : ∀ s, pulseField f (w s) ≤ A * Real.exp (-|s| / M)) (hM : 0 < M) :
    0 < ∫ s, defectField f (w s) := by
  have hmem' : ∀ s, w s ∈ Icc (0:ℝ) π := fun s => ⟨(hmem s).1.le, (hmem s).2.le⟩
  have hint := integrable_defect hf hfpos hwc hmem' hbound hM
  have hnn : 0 ≤ fun s => defectField f (w s) := fun s => defectField_nonneg _
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hsupp : Function.support (fun s => defectField f (w s)) = univ := by
    refine eq_univ_of_forall fun s => ?_
    exact ne_of_gt (defectField_pos hfpos (hmem s))
  rw [hsupp, Real.volume_univ]
  simp

/-- **The defect of the hairpin.**  For a profile smooth and positive on the
line, the hairpin has a front-arclength parametrization along which the defect
`1 - cos δ` is integrable with strictly positive integral. -/
theorem hairpin_defect (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ theta x : ℝ → ℝ, (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π/2) (theta u) = u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      Integrable (fun s => defectField f (theta (x s))) ∧
      0 < ∫ s, defectField f (theta (x s)) := by
  have hcontf : Continuous f := hf.continuous
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  obtain ⟨t₁, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hM : 0 < f t₁ := hfpos t₁
  have hlow : ∀ t ∈ Ioo (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ⟨ht.1.le, ht.2.le⟩
  have hup : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ f t₁ := fun t ht => hmax ⟨ht.1.le, ht.2.le⟩
  obtain ⟨theta, hmem, hval, -, -, hthetac, hderiv⟩ :=
    HairpinArclength.exists_angle hcontf.continuousOn hm hlow
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hderiv' : ∀ u, HasDerivAt theta (curvField f (theta u)) u := hderiv
  have hA : (0:ℝ) ≤ 2 / f t₀ := by positivity
  have hdecay : ∀ u, curvField f (theta u) ≤ (2 / f t₀) * Real.exp (-|u| / f t₁) := fun u =>
    HairpinArclength.curvature_decay_arclength hcontf.continuousOn hm hlow hup hmem hval u
  obtain ⟨x, hxinv, -, hxderiv⟩ := exists_pulseState hf hfpos hmem' hderiv'
  have hwc : Continuous fun s => theta (x s) :=
    Differentiable.continuous fun s => (hxderiv s).differentiableAt
  have hbound : ∀ s, pulseField f (theta (x s))
      ≤ (2 / f t₀) * Real.exp ((2 / f t₀) ^ 2 / 2) * Real.exp (-|s| / f t₁) :=
    fun s => pulse_decay hf hfpos hthetac hmem' hdecay hA hM hxinv s
  have hA' : (0:ℝ) ≤ (2 / f t₀) * Real.exp ((2 / f t₀) ^ 2 / 2) := by positivity
  exact ⟨theta, x, hmem, hval, hxinv,
    integrable_defect hf hfpos hwc (fun s => hmem' _) hbound hM,
    defect_pos hf hfpos hwc (fun s => hmem _) hbound hM⟩

/-! ### A worked instance

The hypotheses are consistent: the constant profile `f ≡ 2` is smooth and
positive on the line. -/

example : ∃ theta x : ℝ → ℝ, 0 < ∫ s, defectField (fun _ => (2:ℝ)) (theta (x s)) := by
  obtain ⟨theta, x, -, -, -, -, h⟩ :=
    hairpin_defect (f := fun _ => 2) contDiff_const (fun _ => two_pos)
  exact ⟨theta, x, h⟩

end HairpinRelative
