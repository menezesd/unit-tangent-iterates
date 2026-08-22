import Mathlib
import UnitTangentIterates.Hairpin
import UnitTangentIterates.HairpinPulse
import UnitTangentIterates.BarrierEstimates

/-!
# Exponential decay of the hairpin curvature in arclength

This file proves the *tail bounds* of the lemma **Hairpin pulse estimates** of
the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*: for a hairpin
profile with `0 < m ≤ f ≤ M` the curvature

`κ = sin θ / f(θ)`

decays exponentially in the arclength measured from the point `θ = π/2`.

The proof compares two integrals in the tangent angle, so that the arclength
parametrization never has to be inverted.  Writing

`S(θ) = ∫_{π/2}^θ f/sin`  (the arclength) and  `L(θ) = ∫_{π/2}^θ 1/sin`,

the half-angle equation of `HairpinPulse.lean` identifies `L(θ) = log tan(θ/2)`,
the bounds on `f` give `|S| ≤ M |L|`, and `sin θ = 2r/(1+r²) ≤ 2 e^{-|log r|}`
for `r = tan(θ/2)`.  Hence

`sin θ ≤ 2 e^{-|S(θ)|/M}`,  `κ(θ) ≤ (2/m) e^{-|S(θ)|/M}`.

Main results:

* `logHalf_eq_integral` : `∫_{π/2}^θ 1/sin = log tan(θ/2)`;
* `sin_le_two_exp` : `sin θ ≤ 2 e^{-|log tan(θ/2)|}`;
* `abs_arclength_le` : `|S(θ)| ≤ M |log tan(θ/2)|`;
* `curvature_decay` : `sin θ / f(θ) ≤ (2/m) e^{-|S(θ)|/M}`;
* `exists_hairpin_curvature_decay` : the same for the profile of the
  translating hairpin, with the explicit constants of the barriers;
* `integral_curvature_le` : `∫_0^π sin θ/f(θ) dθ ≤ 2/m`, which is the
  finiteness of the curvature energy `∫_ℝ κ² du`.
-/

noncomputable section

open Real Set MeasureTheory

namespace HairpinTails

variable {f : ℝ → ℝ} {m M : ℝ}

/-- The half-angle variable `log tan(θ/2)`: the arclength of the model in which
the tangent angle turns at rate `sin θ`. -/
def logHalf (θ : ℝ) : ℝ := Real.log (Real.tan (θ / 2))

theorem hasDerivAt_logHalf {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    HasDerivAt logHalf (1 / Real.sin θ) θ := by
  have := HairpinPulse.hasDerivAt_log_tan_half (theta := id) (tp := 1) (u := θ)
    (hasDerivAt_id θ) hθ.1 hθ.2
  simpa [logHalf, Function.comp] using this

theorem logHalf_pi_div_two : logHalf (π / 2) = 0 := by
  have h : (π / 2) / 2 = π / 4 := by ring
  simp [logHalf, h, Real.tan_pi_div_four]

theorem uIcc_subset_Ioo_pi {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) : uIcc (π/2) θ ⊆ Ioo (0:ℝ) π := by
  have hpi := Real.pi_pos
  exact (ordConnected_Ioo).uIcc_subset ⟨by linarith, by linarith⟩ hθ

theorem continuousOn_inv_sin : ContinuousOn (fun t : ℝ => 1 / Real.sin t) (Ioo 0 π) :=
  continuousOn_const.div Real.continuous_sin.continuousOn
    (fun _ ht => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))

theorem continuousOn_div_sin (hcont : ContinuousOn f (Ioo 0 π)) :
    ContinuousOn (fun t => f t / Real.sin t) (Ioo 0 π) :=
  hcont.div Real.continuous_sin.continuousOn
    (fun _ ht => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))

/-- `∫_{π/2}^θ dt/sin t = log tan(θ/2)`. -/
theorem logHalf_eq_integral {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    (∫ t in (π/2)..θ, 1 / Real.sin t) = logHalf θ := by
  have hsub := uIcc_subset_Ioo_pi hθ
  have hderiv : ∀ t ∈ uIcc (π/2) θ, HasDerivAt logHalf (1 / Real.sin t) t := fun t ht =>
    hasDerivAt_logHalf (hsub ht)
  have hint : IntervalIntegrable (fun t => 1 / Real.sin t) volume (π/2) θ :=
    (continuousOn_inv_sin.mono hsub).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, logHalf_pi_div_two, sub_zero]

/-! ### The elementary bound on the sine -/

theorem sin_eq_tan_half {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    Real.sin θ = 2 * Real.tan (θ/2) / (1 + Real.tan (θ/2)^2) := by
  have hpi := Real.pi_pos
  have h0 := hθ.1
  have h1 := hθ.2
  have hcos : Real.cos (θ/2) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  have hsin2 : Real.sin θ = 2 * Real.sin (θ/2) * Real.cos (θ/2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hpy : Real.sin (θ/2) ^ 2 + Real.cos (θ/2) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  rw [hsin2, Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination Real.sin (θ/2) * hpy

theorem tan_half_pos {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) : 0 < Real.tan (θ/2) := by
  have hpi := Real.pi_pos
  exact Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [hθ.1]) (by linarith [hθ.2])

/-- `sin θ ≤ 2 e^{-|log tan(θ/2)|}`: the sine decays exponentially in the
half-angle variable at both ends. -/
theorem sin_le_two_exp {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    Real.sin θ ≤ 2 * Real.exp (-|logHalf θ|) := by
  have hr0 : 0 < Real.tan (θ/2) := tan_half_pos hθ
  set r : ℝ := Real.tan (θ/2) with hr
  have hlog : logHalf θ = Real.log r := rfl
  rw [sin_eq_tan_half hθ, hlog]
  rcases le_total 1 r with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h), ← Real.log_inv, Real.exp_log (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    have he : 2 * r⁻¹ * (1 + r^2) = 2 * r⁻¹ + 2 * r := by field_simp
    rw [he]
    have h1 : 0 < r⁻¹ := by positivity
    nlinarith
  · rw [abs_of_nonpos (Real.log_nonpos hr0.le h), neg_neg, Real.exp_log hr0]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg r]

/-! ### Comparison of the two arclengths -/

/-- **The arclength is at most `M` times the model arclength.** -/
theorem abs_arclength_le (hcont : ContinuousOn f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hup : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ M)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    |Hairpin.hairpinArclength f (π/2) θ| ≤ M * |logHalf θ| := by
  have hpi := Real.pi_pos
  have hsub := uIcc_subset_Ioo_pi hθ
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / Real.sin t) volume (π/2) θ :=
    (continuousOn_inv_sin.mono hsub).intervalIntegrable
  have hintf : IntervalIntegrable (fun t => f t / Real.sin t) volume (π/2) θ :=
    ((continuousOn_div_sin hcont).mono hsub).intervalIntegrable
  have hL : (∫ t in (π/2)..θ, 1 / Real.sin t) = logHalf θ := logHalf_eq_integral hθ
  have harc : Hairpin.hairpinArclength f (π/2) θ = ∫ t in (π/2)..θ, f t / Real.sin t := rfl
  rw [harc, ← hL]
  rcases le_total (π/2) θ with hle | hle
  · have hIcc : Icc (π/2) θ ⊆ Ioo (0:ℝ) π := by rw [← uIcc_of_le hle]; exact hsub
    have hL0 : 0 ≤ ∫ t in (π/2)..θ, 1 / Real.sin t :=
      intervalIntegral.integral_nonneg hle (fun u hu => by
        have := Real.sin_pos_of_pos_of_lt_pi (hIcc hu).1 (hIcc hu).2; positivity)
    have hS0 : 0 ≤ ∫ t in (π/2)..θ, f t / Real.sin t :=
      intervalIntegral.integral_nonneg hle (fun u hu => by
        have hs := Real.sin_pos_of_pos_of_lt_pi (hIcc hu).1 (hIcc hu).2
        have hf := lt_of_lt_of_le hm (hlow u (hIcc hu))
        positivity)
    have hmono := intervalIntegral.integral_mono_on hle hintf (hint1.const_mul M)
      (fun u hu => by
        have hs := Real.sin_pos_of_pos_of_lt_pi (hIcc hu).1 (hIcc hu).2
        rw [div_le_iff₀ hs]
        have := hup u (hIcc hu)
        rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hs]
        nlinarith)
    rw [intervalIntegral.integral_const_mul] at hmono
    rw [abs_of_nonneg hS0, abs_of_nonneg hL0]
    exact hmono
  · have hIcc : Icc θ (π/2) ⊆ Ioo (0:ℝ) π := by
      rw [← uIcc_of_ge hle]; exact hsub
    have hL0 : 0 ≤ ∫ t in θ..(π/2), 1 / Real.sin t :=
      intervalIntegral.integral_nonneg hle (fun u hu => by
        have := Real.sin_pos_of_pos_of_lt_pi (hIcc hu).1 (hIcc hu).2; positivity)
    have hS0 : 0 ≤ ∫ t in θ..(π/2), f t / Real.sin t :=
      intervalIntegral.integral_nonneg hle (fun u hu => by
        have hs := Real.sin_pos_of_pos_of_lt_pi (hIcc hu).1 (hIcc hu).2
        have hf := lt_of_lt_of_le hm (hlow u (hIcc hu))
        positivity)
    have hmono := intervalIntegral.integral_mono_on hle hintf.symm (hint1.symm.const_mul M)
      (fun u hu => by
        have hs := Real.sin_pos_of_pos_of_lt_pi (hIcc hu).1 (hIcc hu).2
        rw [div_le_iff₀ hs]
        have := hup u (hIcc hu)
        rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hs]
        nlinarith)
    rw [intervalIntegral.integral_const_mul] at hmono
    rw [intervalIntegral.integral_symm θ (π/2), intervalIntegral.integral_symm θ (π/2),
      abs_neg, abs_neg, abs_of_nonneg hS0, abs_of_nonneg hL0]
    exact hmono

/-- The lower comparison to the right of `π/2`: `m L(θ) ≤ S(θ)`. -/
theorem m_mul_logHalf_le (hcont : ContinuousOn f (Ioo 0 π))
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) (hle : π/2 ≤ θ) :
    m * logHalf θ ≤ Hairpin.hairpinArclength f (π/2) θ := by
  have hsub := uIcc_subset_Ioo_pi hθ
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / Real.sin t) volume (π/2) θ :=
    (continuousOn_inv_sin.mono hsub).intervalIntegrable
  have hintf : IntervalIntegrable (fun t => f t / Real.sin t) volume (π/2) θ :=
    ((continuousOn_div_sin hcont).mono hsub).intervalIntegrable
  have hL : (∫ t in (π/2)..θ, 1 / Real.sin t) = logHalf θ := logHalf_eq_integral hθ
  have hIcc : Icc (π/2) θ ⊆ Ioo (0:ℝ) π := by rw [← uIcc_of_le hle]; exact hsub
  have hmono := intervalIntegral.integral_mono_on hle (hint1.const_mul m) hintf
    (fun u hu => by
      have hs := Real.sin_pos_of_pos_of_lt_pi (hIcc hu).1 (hIcc hu).2
      rw [le_div_iff₀ hs, mul_one_div, div_mul_eq_mul_div, div_le_iff₀ hs]
      nlinarith [hlow u (hIcc hu)])
  rw [intervalIntegral.integral_const_mul, hL] at hmono
  exact hmono

/-- The lower comparison to the left of `π/2`: `S(θ) ≤ m L(θ)`. -/
theorem le_m_mul_logHalf (hcont : ContinuousOn f (Ioo 0 π))
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) (hle : θ ≤ π/2) :
    Hairpin.hairpinArclength f (π/2) θ ≤ m * logHalf θ := by
  have hsub := uIcc_subset_Ioo_pi hθ
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / Real.sin t) volume (π/2) θ :=
    (continuousOn_inv_sin.mono hsub).intervalIntegrable
  have hintf : IntervalIntegrable (fun t => f t / Real.sin t) volume (π/2) θ :=
    ((continuousOn_div_sin hcont).mono hsub).intervalIntegrable
  have hL : (∫ t in (π/2)..θ, 1 / Real.sin t) = logHalf θ := logHalf_eq_integral hθ
  have hIcc : Icc θ (π/2) ⊆ Ioo (0:ℝ) π := by rw [← uIcc_of_ge hle]; exact hsub
  have hmono := intervalIntegral.integral_mono_on hle (hint1.symm.const_mul m) hintf.symm
    (fun u hu => by
      have hs := Real.sin_pos_of_pos_of_lt_pi (hIcc hu).1 (hIcc hu).2
      rw [le_div_iff₀ hs, mul_one_div, div_mul_eq_mul_div, div_le_iff₀ hs]
      nlinarith [hlow u (hIcc hu)])
  rw [intervalIntegral.integral_const_mul] at hmono
  have h1 : (∫ t in θ..(π/2), 1 / Real.sin t) = -logHalf θ := by
    rw [← hL, intervalIntegral.integral_symm θ (π/2), neg_neg]
  have h2 : Hairpin.hairpinArclength f (π/2) θ = -∫ t in θ..(π/2), f t / Real.sin t :=
    intervalIntegral.integral_symm θ (π/2)
  rw [h1] at hmono
  rw [h2]
  linarith

/-! ### The tail bound -/

/-- **Exponential decay of the curvature in arclength.**  For a hairpin profile
with `0 < m ≤ f ≤ M` the curvature at the point of arclength `S(θ)` is at most
`(2/m) e^{-|S(θ)|/M}`. -/
theorem curvature_decay (hcont : ContinuousOn f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hup : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ M)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    Real.sin θ / f θ
      ≤ (2 / m) * Real.exp (-|Hairpin.hairpinArclength f (π/2) θ| / M) := by
  have hM : 0 < M := lt_of_lt_of_le hm (le_trans (hlow θ hθ) (hup θ hθ))
  have hcomp := abs_arclength_le hcont hm hlow hup hθ
  have hexp : Real.exp (-|logHalf θ|)
      ≤ Real.exp (-|Hairpin.hairpinArclength f (π/2) θ| / M) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hM, mul_comm]
    exact hcomp
  have hstep : Real.sin θ ≤ 2 * Real.exp (-|Hairpin.hairpinArclength f (π/2) θ| / M) :=
    le_trans (sin_le_two_exp hθ) (by
      exact mul_le_mul_of_nonneg_left hexp (by norm_num))
  have hf : 0 < f θ := lt_of_lt_of_le hm (hlow θ hθ)
  have hmf : m ≤ f θ := hlow θ hθ
  have hE : 0 < Real.exp (-|Hairpin.hairpinArclength f (π/2) θ| / M) := Real.exp_pos _
  rw [div_le_iff₀ hf]
  have hkey : 2 * Real.exp (-|Hairpin.hairpinArclength f (π/2) θ| / M)
      ≤ 2 / m * Real.exp (-|Hairpin.hairpinArclength f (π/2) θ| / M) * f θ := by
    have hpos : (0:ℝ) ≤ 2 / m := by positivity
    have h1 : 2 / m * m ≤ 2 / m * f θ := by nlinarith
    have h2 : 2 / m * m = 2 := by field_simp
    have hcoef : (2:ℝ) ≤ 2 / m * f θ := by linarith
    nlinarith [hE, hcoef]
  linarith [hstep, hkey]

/-- The tail bound for the profile of the translating hairpin, with the
explicit constants of the barriers. -/
theorem exists_hairpin_curvature_decay {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    ∃ f : ℝ → ℝ, (∀ t, Barriers.fMinus ε t ≤ f t) ∧ (∀ t, f t ≤ Barriers.fPlus ε t) ∧
      ContinuousOn f (Ioo 0 π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π,
        (∫ t in θ..(θ + TranslatorOperator.shift f θ), f t) = Real.sin θ) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, Real.sin θ / f θ ≤ (2 / (ε⁻¹ - ε)) *
        Real.exp (-|Hairpin.hairpinArclength f (π/2) θ| / (ε⁻¹ + 4 / 3 + 3 * ε))) := by
  obtain ⟨f, -, hfl, hfu, hcont, -, hintEq, -, -⟩ :=
    BarrierEstimates.exists_hairpin_profile hε hε'
  have hm1 : 1 < ε⁻¹ - ε := BarrierEstimates.m_gt_one hε hε'
  have hm0 : (0:ℝ) < ε⁻¹ - ε := lt_trans zero_lt_one hm1
  have hlow : ∀ t, ε⁻¹ - ε ≤ f t := fun t =>
    le_trans ((Barriers.fMinus_min hε).1 t) (hfl t)
  have hup : ∀ t, f t ≤ ε⁻¹ + 4 / 3 + 3 * ε := fun t =>
    le_trans (hfu t) ((BarrierEstimates.profile_fPlus hε).upper t)
  exact ⟨f, hfl, hfu, hcont, hintEq, fun θ hθ =>
    curvature_decay hcont hm0 (fun t _ => hlow t) (fun t _ => hup t) hθ⟩

/-! ### Finiteness of the curvature energy -/

/-- `∫_ℝ κ² du = ∫_0^π sin θ/f(θ) dθ ≤ 2/m`: the curvature of the hairpin is
square integrable in arclength. -/
theorem integral_curvature_le (hm : 0 < m) (hlow : ∀ t, m ≤ f t)
    (hint : IntervalIntegrable (fun θ => Real.sin θ / f θ) volume 0 π) :
    (∫ θ in (0:ℝ)..π, Real.sin θ / f θ) ≤ 2 / m := by
  have hpi := Real.pi_pos
  have hint2 : IntervalIntegrable (fun t : ℝ => Real.sin t / m) volume 0 π :=
    (Real.continuous_sin.continuousOn.div_const m).intervalIntegrable
  have hmono : ∀ t ∈ Icc (0:ℝ) π, Real.sin t / f t ≤ Real.sin t / m := by
    intro t ht
    have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
    gcongr
    exact hlow t
  have h := intervalIntegral.integral_mono_on hpi.le hint hint2 hmono
  have hval : (∫ t in (0:ℝ)..π, Real.sin t / m) = 2 / m := by
    rw [intervalIntegral.integral_div, integral_sin]
    simp [Real.cos_pi]
    ring
  linarith [h, hval.le, hval.ge]

end HairpinTails
