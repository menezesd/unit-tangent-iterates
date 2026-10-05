module

public import UnitTangentIterates.HairpinOperator

/-!
# Barriers for the hairpin operator (Lemma 3.3)

We prove that for `0 < ε ≤ 1/10` the barrier profiles
`f_ε^- = ε⁻¹ + (2/3)(1 - cos θ) - ε cos θ` and `f_ε^+ = ε⁻¹ + (2/3)(1 - cos θ) + ε(2 + cos θ)`
satisfy `f_ε^- ≤ 𝒫 f_ε^- ≤ 𝒫 f_ε^+ ≤ f_ε^+` on `(0, π)`.

For a profile `A + B cos θ`, with `d = arctan (sin θ / f θ)`, we have the exact identity
`ℛ(f) · sin d = sin θ · N` with
`N = (d cos d - sin d) + B (cos d - 1) sin d + β (sin d - d) cos d`, `β = B cos θ / f θ`,
and the elementary Taylor bounds for `sin` and `cos` give
`|N - d³(-1/3 - B/2 - β/6)| ≤ d⁵/4`; this replaces the analytic-extension argument of the
paper by explicit inequalities.
-/

@[expose] public section

namespace Ovals

open Real Set MeasureTheory


theorem sin_ge_cubic {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have hmono : MonotoneOn (fun t => Real.sin t - t + t ^ 3 / 6) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro t _
      have hd : HasDerivAt (fun t => Real.sin t - t + t ^ 3 / 6)
          (Real.cos t - 1 + 3 * t ^ 2 / 6) t := by
        have := ((Real.hasDerivAt_sin t).sub (hasDerivAt_id t)).add
          ((hasDerivAt_pow 3 t).div_const 6)
        convert this using 1
      rw [hd.deriv]
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have := hmono (self_mem_Ici) (show x ∈ Ici (0:ℝ) from hx) hx
  simp at this
  linarith

theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hmono : MonotoneOn (fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro t ht
      rw [interior_Ici] at ht
      have hd : HasDerivAt (fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
          (-(2 * t / 2) + 4 * t ^ 3 / 24 + Real.sin t) t := by
        have := (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub (Real.hasDerivAt_cos t)
        convert this using 1; simp
      rw [hd.deriv]
      nlinarith [sin_ge_cubic (le_of_lt ht)]
  have := hmono (self_mem_Ici) (show x ∈ Ici (0:ℝ) from hx) hx
  simp at this
  linarith

theorem sin_le_quintic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hmono : MonotoneOn (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro t ht
      rw [interior_Ici] at ht
      have hd : HasDerivAt (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
          (1 - 3 * t ^ 2 / 6 + 5 * t ^ 4 / 120 - Real.cos t) t := by
        have := (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)
        convert this using 1
      rw [hd.deriv]
      nlinarith [cos_le_quartic (le_of_lt ht)]
  have := hmono (self_mem_Ici) (show x ∈ Ici (0:ℝ) from hx) hx
  simp at this
  linarith


/-- The quantity `N = (d cos d - sin d) + B (cos d - 1) sin d + β (sin d - d) cos d`. -/
noncomputable def barrierN (d B β : ℝ) : ℝ :=
  (d * Real.cos d - Real.sin d) + B * (Real.cos d - 1) * Real.sin d +
    β * (Real.sin d - d) * Real.cos d

theorem barrierN_bounds {d B β : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hB0 : -1 ≤ B) (hB1 : B ≤ 0)
    (hβ : |β| ≤ 1)
    (hs1 : d - d ^ 3 / 6 ≤ Real.sin d) (hs2 : Real.sin d ≤ d - d ^ 3 / 6 + d ^ 5 / 120)
    (hc1 : 1 - d ^ 2 / 2 ≤ Real.cos d) (hc2 : Real.cos d ≤ 1 - d ^ 2 / 2 + d ^ 4 / 24) :
    d ^ 3 * (-1 / 3 - B / 2 - β / 6) - d ^ 5 / 4 ≤ barrierN d B β ∧
      barrierN d B β ≤ d ^ 3 * (-1 / 3 - B / 2 - β / 6) + d ^ 5 / 4 := by
  set s := Real.sin d
  set c := Real.cos d
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  have hd3 : d ^ 3 ≤ d := by
    have := mul_le_mul_of_nonneg_left hd2 hd0; nlinarith
  have hd5 : 0 ≤ d ^ 5 := pow_nonneg hd0 5
  have hd53 : d ^ 5 ≤ d ^ 3 := by
    have := mul_le_mul_of_nonneg_left hd2 (pow_nonneg hd0 3); nlinarith
  have hd42 : d ^ 4 ≤ d ^ 2 := by
    have := mul_le_mul_of_nonneg_left hd2 (pow_nonneg hd0 2); nlinarith
  have hd75 : d ^ 7 ≤ d ^ 5 := by
    have := mul_le_mul_of_nonneg_left hd2 (pow_nonneg hd0 5); nlinarith
  have hd7 : 0 ≤ d ^ 7 := pow_nonneg hd0 7
  have hs0 : 0 ≤ s := by linarith
  have hsd : s ≤ d := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hc1' : c ≤ 1 := by linarith
  -- term 1
  have hdc1 := mul_le_mul_of_nonneg_left hc1 hd0
  have hdc2 := mul_le_mul_of_nonneg_left hc2 hd0
  have t1a : -d ^ 3 / 3 - d ^ 5 / 120 ≤ d * c - s := by
    have e : d * (1 - d ^ 2 / 2) = d - d ^ 3 / 2 := by ring
    linarith
  have t1b : d * c - s ≤ -d ^ 3 / 3 + d ^ 5 / 24 := by
    have e : d * (1 - d ^ 2 / 2 + d ^ 4 / 24) = d - d ^ 3 / 2 + d ^ 5 / 24 := by ring
    linarith
  -- term 2
  have t2a : -d ^ 3 / 2 ≤ (c - 1) * s := by
    have h1 : -(d ^ 2 / 2) * s ≤ (c - 1) * s := mul_le_mul_of_nonneg_right (by linarith) hs0
    have h2 : -(d ^ 2 / 2) * d ≤ -(d ^ 2 / 2) * s :=
      mul_le_mul_of_nonpos_left hsd (by nlinarith)
    have e : -(d ^ 2 / 2) * d = -d ^ 3 / 2 := by ring
    linarith
  have t2b : (c - 1) * s ≤ -d ^ 3 / 2 + d ^ 5 / 8 := by
    have hneg : -d ^ 2 / 2 + d ^ 4 / 24 ≤ 0 := by linarith
    have h1 : (c - 1) * s ≤ (-d ^ 2 / 2 + d ^ 4 / 24) * s :=
      mul_le_mul_of_nonneg_right (by linarith) hs0
    have h2 : (-d ^ 2 / 2 + d ^ 4 / 24) * s ≤ (-d ^ 2 / 2 + d ^ 4 / 24) * (d - d ^ 3 / 6) :=
      mul_le_mul_of_nonpos_left hs1 hneg
    have e : (-d ^ 2 / 2 + d ^ 4 / 24) * (d - d ^ 3 / 6) =
        -d ^ 3 / 2 + d ^ 5 / 12 + d ^ 5 / 24 - d ^ 7 / 144 := by ring
    linarith
  -- term 3
  have t3a : -d ^ 3 / 6 ≤ (s - d) * c := by
    have h1 : (s - d) * 1 ≤ (s - d) * c := mul_le_mul_of_nonpos_left hc1' (by linarith)
    linarith
  have t3b : (s - d) * c ≤ -d ^ 3 / 6 + d ^ 5 / 10 := by
    have hneg : -d ^ 3 / 6 + d ^ 5 / 120 ≤ 0 := by linarith
    have h1 : (s - d) * c ≤ (-d ^ 3 / 6 + d ^ 5 / 120) * c :=
      mul_le_mul_of_nonneg_right (by linarith) hc0
    have h2 : (-d ^ 3 / 6 + d ^ 5 / 120) * c ≤ (-d ^ 3 / 6 + d ^ 5 / 120) * (1 - d ^ 2 / 2) :=
      mul_le_mul_of_nonpos_left hc1 hneg
    have e : (-d ^ 3 / 6 + d ^ 5 / 120) * (1 - d ^ 2 / 2) =
        -d ^ 3 / 6 + d ^ 5 / 12 + d ^ 5 / 120 - d ^ 7 / 240 := by ring
    linarith
  -- combine
  have e2a : -B * d ^ 3 / 2 - d ^ 5 / 8 ≤ B * ((c - 1) * s) := by
    have h1 := mul_le_mul_of_nonpos_left t2b hB1
    have h2 := mul_le_mul_of_nonneg_right hB0 hd5
    have e : B * (-d ^ 3 / 2 + d ^ 5 / 8) = -B * d ^ 3 / 2 + B * d ^ 5 / 8 := by ring
    linarith
  have e2b : B * ((c - 1) * s) ≤ -B * d ^ 3 / 2 := by
    have h1 := mul_le_mul_of_nonpos_left t2a hB1
    have e : B * (-d ^ 3 / 2) = -B * d ^ 3 / 2 := by ring
    linarith
  have e3 : |β * ((s - d) * c) + β * d ^ 3 / 6| ≤ d ^ 5 / 10 := by
    rw [show β * ((s - d) * c) + β * d ^ 3 / 6 = β * ((s - d) * c + d ^ 3 / 6) by ring, abs_mul]
    have : |(s - d) * c + d ^ 3 / 6| ≤ d ^ 5 / 10 := abs_le.2 ⟨by linarith, by linarith⟩
    calc |β| * |(s - d) * c + d ^ 3 / 6| ≤ 1 * (d ^ 5 / 10) :=
          mul_le_mul hβ this (abs_nonneg _) zero_le_one
      _ = d ^ 5 / 10 := one_mul _
  have e3' := abs_le.1 e3
  have hN : barrierN d B β = (d * c - s) + B * ((c - 1) * s) + β * ((s - d) * c) := by
    unfold barrierN; ring
  rw [hN]
  constructor
  · have e : d ^ 3 * (-1 / 3 - B / 2 - β / 6) = -d ^ 3 / 3 - B * d ^ 3 / 2 - β * d ^ 3 / 6 := by
      ring
    linarith
  · have e : d ^ 3 * (-1 / 3 - B / 2 - β / 6) = -d ^ 3 / 3 - B * d ^ 3 / 2 - β * d ^ 3 / 6 := by
      ring
    linarith

theorem integral_cosProfile (A B a b : ℝ) :
    ∫ t in a..b, (A + B * Real.cos t) = A * (b - a) + B * (Real.sin b - Real.sin a) := by
  have h := intervalIntegral.integral_add (μ := volume) (a := a) (b := b) (f := fun _ => A)
    (g := fun t => B * Real.cos t) intervalIntegrable_const
    ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _)
  simp only at h
  rw [h, intervalIntegral.integral_const_mul, integral_cos]
  simp [mul_comm]

theorem profR_cosProfile_mul_sin (A B : ℝ) {θ : ℝ}
    (hf : 0 < A + B * Real.cos θ) :
    profR (fun t => A + B * Real.cos t) θ * Real.sin (hairpinD (fun t => A + B * Real.cos t) θ)
      = Real.sin θ * barrierN (hairpinD (fun t => A + B * Real.cos t) θ) B
          (B * Real.cos θ / (A + B * Real.cos θ)) := by
  set f : ℝ → ℝ := fun t => A + B * Real.cos t with hfdef
  set d := hairpinD f θ with hd
  have hcd : 0 < Real.cos d := Real.cos_arctan_pos _
  have htan : Real.tan d = Real.sin θ / f θ := Real.tan_arctan _
  have hfs : f θ * Real.sin d = Real.sin θ * Real.cos d := by
    rw [Real.tan_eq_sin_div_cos] at htan
    have hf' : f θ ≠ 0 := hf.ne'
    field_simp at htan
    linarith
  have hfθ : f θ = A + B * Real.cos θ := rfl
  unfold profR hairpinG
  rw [← hd, integral_cosProfile, Real.sin_add]
  unfold barrierN
  rw [hfθ] at hfs
  field_simp
  linear_combination (d * (A + B * Real.cos θ) + B * Real.cos θ * (Real.sin d - d)) * hfs

/-- The lower barrier `f_ε^-(θ) = ε⁻¹ + (2/3)(1 - cos θ) - ε cos θ`. -/
noncomputable def fMinus (ε : ℝ) (θ : ℝ) : ℝ :=
  ε⁻¹ + 2 / 3 * (1 - Real.cos θ) - ε * Real.cos θ

/-- The upper barrier `f_ε^+(θ) = ε⁻¹ + (2/3)(1 - cos θ) + ε (2 + cos θ)`. -/
noncomputable def fPlus (ε : ℝ) (θ : ℝ) : ℝ :=
  ε⁻¹ + 2 / 3 * (1 - Real.cos θ) + ε * (2 + Real.cos θ)

theorem fMinus_eq (ε : ℝ) :
    fMinus ε = fun t => (ε⁻¹ + 2 / 3) + (-2 / 3 - ε) * Real.cos t := by
  funext t; unfold fMinus; ring

theorem fPlus_eq (ε : ℝ) :
    fPlus ε = fun t => (ε⁻¹ + 2 / 3 + 2 * ε) + (-2 / 3 + ε) * Real.cos t := by
  funext t; unfold fPlus; ring

variable {ε : ℝ}

theorem fMinus_ge (hε0 : 0 < ε) (θ : ℝ) : ε⁻¹ - ε ≤ fMinus ε θ := by
  unfold fMinus
  nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]

theorem fPlus_ge (hε0 : 0 < ε) (θ : ℝ) : ε⁻¹ ≤ fPlus ε θ := by
  unfold fPlus
  nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]

theorem fMinus_le_fPlus (hε0 : 0 < ε) (θ : ℝ) : fMinus ε θ ≤ fPlus ε θ := by
  unfold fMinus fPlus
  nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]

theorem fPlus_le (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) (θ : ℝ) : fPlus ε θ ≤ ε⁻¹ + 2 := by
  unfold fPlus
  nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]

theorem one_lt_inv_sub (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) : 1 < ε⁻¹ - ε := by
  have : 10 ≤ ε⁻¹ := by rw [le_inv_comm₀ (by norm_num) hε0]; linarith
  linarith

theorem admissible_fMinus (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) :
    AdmissibleProfile (fMinus ε) (ε⁻¹ - ε) (ε⁻¹ + 2) where
  one_lt := one_lt_inv_sub hε0 hε
  lower := fun θ _ => fMinus_ge hε0 θ
  upper := fun θ _ => (fMinus_le_fPlus hε0 θ).trans (fPlus_le hε0 hε θ)
  integrable := by
    rw [fMinus_eq]
    exact (continuous_const.add (continuous_const.mul Real.continuous_cos)).intervalIntegrable _ _

theorem admissible_fPlus (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) :
    AdmissibleProfile (fPlus ε) (ε⁻¹ - ε) (ε⁻¹ + 2) where
  one_lt := one_lt_inv_sub hε0 hε
  lower := fun θ _ => by linarith [fPlus_ge hε0 θ]
  upper := fun θ _ => fPlus_le hε0 hε θ
  integrable := by
    rw [fPlus_eq]
    exact (continuous_const.add (continuous_const.mul Real.continuous_cos)).intervalIntegrable _ _

/-- Common estimates for the steering angle of a barrier. -/
theorem barrier_d_bounds {f : ℝ → ℝ} {θ c : ℝ} (hθ : θ ∈ Ioo 0 π) (hc : 0 < c)
    (hf : c⁻¹ ≤ f θ) :
    0 < hairpinD f θ ∧ hairpinD f θ ≤ c ∧ 0 < Real.sin (hairpinD f θ) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hf0 : 0 < f θ := lt_of_lt_of_le (inv_pos.2 hc) hf
  have hd0 : 0 < hairpinD f θ := Real.arctan_pos.2 (div_pos hs hf0)
  have hd1 : hairpinD f θ ≤ Real.sin θ / f θ := arctan_le_self_of_nonneg (div_pos hs hf0).le
  have h2 : Real.sin θ / f θ ≤ c := by
    rw [div_le_iff₀ hf0]
    have := Real.sin_le_one θ
    have : 1 ≤ c * f θ := by
      have := mul_le_mul_of_nonneg_left hf hc.le
      rwa [mul_inv_cancel₀ hc.ne'] at this
    linarith
  have hd2 : hairpinD f θ < π / 2 := Real.arctan_lt_pi_div_two _
  exact ⟨hd0, hd1.trans h2, Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith [Real.pi_pos])⟩

/-- The residual of the lower barrier is nonnegative. -/
theorem profR_fMinus_nonneg (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 ≤ profR (fMinus ε) θ := by
  have hfge := fMinus_ge hε0 θ
  have hinv : 10 ≤ ε⁻¹ := by rw [le_inv_comm₀ (by norm_num) hε0]; linarith
  have h2ε : (2 * ε)⁻¹ ≤ fMinus ε θ := by
    have : (2 * ε)⁻¹ = ε⁻¹ / 2 := by rw [mul_inv, mul_comm]; ring
    rw [this]; nlinarith
  obtain ⟨hd0, hd2, hsd⟩ := barrier_d_bounds hθ (by positivity) h2ε
  rw [fMinus_eq] at hd0 hd2 hsd ⊢
  have hfθ : 0 < (ε⁻¹ + 2 / 3) + (-2 / 3 - ε) * Real.cos θ := by
    have := fMinus_ge hε0 θ; unfold fMinus at this; nlinarith
  have key := profR_cosProfile_mul_sin (ε⁻¹ + 2 / 3) (-2 / 3 - ε) (θ := θ) hfθ
  set f : ℝ → ℝ := fun t => (ε⁻¹ + 2 / 3) + (-2 / 3 - ε) * Real.cos t
  set d := hairpinD f θ
  set β := (-2 / 3 - ε) * Real.cos θ / ((ε⁻¹ + 2 / 3) + (-2 / 3 - ε) * Real.cos θ) with hβdef
  have hβ : |β| ≤ ε := by
    rw [hβdef, abs_div, abs_of_pos hfθ, div_le_iff₀ hfθ, abs_mul]
    have hc := abs_cos_le_one θ
    have hB : |(-2 / 3 - ε : ℝ)| = 2 / 3 + ε := by rw [abs_of_neg (by linarith)]; ring
    rw [hB]
    have hf' : ε⁻¹ - ε ≤ (ε⁻¹ + 2 / 3) + (-2 / 3 - ε) * Real.cos θ := by
      have := fMinus_ge hε0 θ; unfold fMinus at this; linarith
    have h1 : ε * (ε⁻¹ - ε) = 1 - ε ^ 2 := by field_simp
    have h3 : (2 / 3 + ε) * |Real.cos θ| ≤ 2 / 3 + ε := by nlinarith [abs_nonneg (Real.cos θ)]
    nlinarith
  have hβ1 : |β| ≤ 1 := by linarith
  have hd1 : d ≤ 1 := by linarith
  obtain ⟨hN, -⟩ := barrierN_bounds hd0.le hd1 (B := -2 / 3 - ε) (β := β) (by linarith)
    (by linarith) hβ1 (sin_ge_cubic hd0.le) (sin_le_quintic hd0.le)
    Real.one_sub_sq_div_two_le_cos (cos_le_quartic hd0.le)
  have hN0 : 0 ≤ barrierN d (-2 / 3 - ε) β := by
    have hd3 : 0 ≤ d ^ 3 := pow_nonneg hd0.le 3
    have hd5 : d ^ 5 ≤ 4 * ε ^ 2 * d ^ 3 := by
      have : d ^ 2 ≤ 4 * ε ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left this hd3
      nlinarith
    have hb := (abs_le.1 hβ).2
    have : d ^ 3 * β ≤ d ^ 3 * ε := mul_le_mul_of_nonneg_left hb hd3
    have : 0 ≤ d ^ 3 * ε * (1 / 3 - ε) := by
      apply mul_nonneg (mul_nonneg hd3 hε0.le); linarith
    nlinarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have : 0 ≤ profR f θ * Real.sin d := by rw [key]; exact mul_nonneg hs.le hN0
  exact nonneg_of_mul_nonneg_left this hsd

/-- The residual of the upper barrier is nonpositive. -/
theorem profR_fPlus_nonpos (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    profR (fPlus ε) θ ≤ 0 := by
  have hfge := fPlus_ge hε0 θ
  have hε' : ε⁻¹ ≤ fPlus ε θ := hfge
  rw [← inv_inv ε] at hε'
  obtain ⟨hd0, hd2, hsd⟩ := barrier_d_bounds hθ (by positivity) (c := ε) (by simpa using hfge)
  rw [fPlus_eq] at hd0 hd2 hsd ⊢
  have hfθ : 0 < (ε⁻¹ + 2 / 3 + 2 * ε) + (-2 / 3 + ε) * Real.cos θ := by
    have := fPlus_ge hε0 θ; unfold fPlus at this
    have : 0 < ε⁻¹ := inv_pos.2 hε0
    nlinarith
  have key := profR_cosProfile_mul_sin (ε⁻¹ + 2 / 3 + 2 * ε) (-2 / 3 + ε) (θ := θ) hfθ
  set f : ℝ → ℝ := fun t => (ε⁻¹ + 2 / 3 + 2 * ε) + (-2 / 3 + ε) * Real.cos t
  set d := hairpinD f θ
  set β := (-2 / 3 + ε) * Real.cos θ / ((ε⁻¹ + 2 / 3 + 2 * ε) + (-2 / 3 + ε) * Real.cos θ)
    with hβdef
  have hβ : |β| ≤ ε := by
    rw [hβdef, abs_div, abs_of_pos hfθ, div_le_iff₀ hfθ, abs_mul]
    have hc := abs_cos_le_one θ
    have hB : |(-2 / 3 + ε : ℝ)| = 2 / 3 - ε := by rw [abs_of_neg (by linarith)]; ring
    rw [hB]
    have hf' : ε⁻¹ ≤ (ε⁻¹ + 2 / 3 + 2 * ε) + (-2 / 3 + ε) * Real.cos θ := by
      have := fPlus_ge hε0 θ; unfold fPlus at this; linarith
    have h1 : ε * ε⁻¹ = 1 := by field_simp
    have h3 : (2 / 3 - ε) * |Real.cos θ| ≤ 2 / 3 - ε := by
      nlinarith [abs_nonneg (Real.cos θ)]
    nlinarith
  have hβ1 : |β| ≤ 1 := by linarith
  have hd1 : d ≤ 1 := by linarith
  obtain ⟨-, hN⟩ := barrierN_bounds hd0.le hd1 (B := -2 / 3 + ε) (β := β) (by linarith)
    (by linarith) hβ1 (sin_ge_cubic hd0.le) (sin_le_quintic hd0.le)
    Real.one_sub_sq_div_two_le_cos (cos_le_quartic hd0.le)
  have hN0 : barrierN d (-2 / 3 + ε) β ≤ 0 := by
    have hd3 : 0 ≤ d ^ 3 := pow_nonneg hd0.le 3
    have hd5 : d ^ 5 ≤ ε ^ 2 * d ^ 3 := by
      have : d ^ 2 ≤ ε ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left this hd3
      nlinarith
    have hb := (abs_le.1 hβ).1
    have : -(d ^ 3 * ε) ≤ d ^ 3 * β := by nlinarith
    have : 0 ≤ d ^ 3 * ε * (1 / 3 - ε / 4) := by
      apply mul_nonneg (mul_nonneg hd3 hε0.le); linarith
    nlinarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have : profR f θ * Real.sin d ≤ 0 := by
    rw [key]; exact mul_nonpos_of_nonneg_of_nonpos hs.le hN0
  exact nonpos_of_mul_nonpos_left this hsd

/-- **Lemma 3.3 (barriers).** For `0 < ε ≤ 1/10` and `0 < θ < π`,
`f_ε^- ≤ 𝒫 f_ε^- ≤ 𝒫 f_ε^+ ≤ f_ε^+`. -/
theorem barrier_ineq (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    fMinus ε θ ≤ profP (fMinus ε) θ ∧ profP (fMinus ε) θ ≤ profP (fPlus ε) θ ∧
      profP (fPlus ε) θ ≤ fPlus ε θ :=
  ⟨(profR_nonneg_iff (admissible_fMinus hε0 hε) hθ).1 (profR_fMinus_nonneg hε0 hε hθ),
    profP_mono (admissible_fMinus hε0 hε) (admissible_fPlus hε0 hε)
      (fun θ _ => fMinus_le_fPlus hε0 θ) hθ,
    (profR_nonpos_iff (admissible_fPlus hε0 hε) hθ).1 (profR_fPlus_nonpos hε0 hε hθ)⟩

end Ovals

end
