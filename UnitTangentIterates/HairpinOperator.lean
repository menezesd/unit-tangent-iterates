module

public import UnitTangentIterates.Translator

/-!
# The monotone operator `𝒫` (Lemma 3.2)

For a profile `f` with `1 < m ≤ f ≤ M` on `(0, π)`, integrable on `[0, π]`, let
`D_f(θ)` be the unique `u > 0` with `∫_θ^{θ+u} f = sin θ` (i.e.
`D_f(θ) = A_f⁻¹(A_f(θ) + sin θ) - θ`), and `(𝒫 f)(θ) = sin θ · cot D_f(θ)`.

Lemma 3.2: `𝒫 f` is positive, `𝒫` is order preserving, and `f = 𝒫 f` iff `f` satisfies the
translator equation.  We also prove the sign criterion used in Lemma 3.3:
`ℛ(f) ≥ 0 ↔ 𝒫 f ≥ f` where `ℛ(f)(θ) = ∫_θ^{θ+d_f(θ)} f - sin θ`.
-/

@[expose] public section

namespace Ovals

open Real Set MeasureTheory

/-- Standing assumptions on a profile. -/
structure AdmissibleProfile (f : ℝ → ℝ) (m M : ℝ) : Prop where
  one_lt : 1 < m
  lower : ∀ θ ∈ Ioo 0 π, m ≤ f θ
  upper : ∀ θ ∈ Ioo 0 π, f θ ≤ M
  integrable : IntervalIntegrable f volume 0 π

/-- `D_f(θ)`: the first `u ≥ 0` with `∫_θ^{θ+u} f ≥ sin θ`. -/
noncomputable def profD (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  sInf {u : ℝ | 0 ≤ u ∧ Real.sin θ ≤ ∫ t in θ..θ + u, f t}

/-- The operator `(𝒫 f)(θ) = sin θ · cot D_f(θ)`. -/
noncomputable def profP (f : ℝ → ℝ) (θ : ℝ) : ℝ := Real.sin θ * Real.cot (profD f θ)

/-- The residual `ℛ(f)(θ) = ∫_θ^{θ + d_f(θ)} f - sin θ`. -/
noncomputable def profR (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (∫ t in θ..hairpinG f θ, f t) - Real.sin θ

variable {f h : ℝ → ℝ} {m M : ℝ}

theorem AdmissibleProfile.intervalIntegrable (hf : AdmissibleProfile f m M) {a b : ℝ}
    (ha : a ∈ Icc 0 π) (hb : b ∈ Icc 0 π) : IntervalIntegrable f volume a b := by
  apply hf.integrable.mono_set
  intro x hx
  rw [Set.mem_uIcc] at hx ⊢
  left
  rcases hx with hx | hx <;> constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hx.1, hx.2]

/-- Lower bound on increments: `∫_a^b f ≥ m (b - a)` for `0 ≤ a ≤ b ≤ π`. -/
theorem integral_ge_of_admissible (hf : AdmissibleProfile f m M) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) : m * (b - a) ≤ ∫ t in a..b, f t := by
  have := intervalIntegral.integral_mono_on_of_le_Ioo hab intervalIntegrable_const
    (hf.intervalIntegrable ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩) (f := fun _ => m)
    (fun x hx => hf.lower x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  simpa [mul_comm] using this

/-- Upper bound on increments: `∫_a^b f ≤ M (b - a)` for `0 ≤ a ≤ b ≤ π`. -/
theorem integral_le_of_admissible (hf : AdmissibleProfile f m M) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) : (∫ t in a..b, f t) ≤ M * (b - a) := by
  have := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (hf.intervalIntegrable ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩) intervalIntegrable_const
    (g := fun _ => M)
    (fun x hx => hf.upper x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  simpa [mul_comm] using this

/-- The increment `u ↦ ∫_θ^{θ+u} f` is strictly increasing on `[0, π - θ]`. -/
theorem integral_strictMonoOn (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    StrictMonoOn (fun u => ∫ t in θ..θ + u, f t) (Icc 0 (π - θ)) := by
  intro u hu v hv huv
  simp only
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (a := θ) (b := θ + u) ⟨hθ.1.le, hθ.2.le⟩
      ⟨by linarith [hu.1, hθ.1], by linarith [hu.2]⟩)
    (hf.intervalIntegrable (a := θ + u) (b := θ + v)
      ⟨by linarith [hu.1, hθ.1], by linarith [hu.2]⟩ ⟨by linarith [hv.1, hθ.1], by linarith [hv.2]⟩)
  have h2 := integral_ge_of_admissible hf (a := θ + u) (b := θ + v) (by linarith [hu.1, hθ.1])
    (by linarith) (by linarith [hv.2])
  have hm := hf.one_lt
  nlinarith

theorem continuousOn_increment (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ContinuousOn (fun u => ∫ t in θ..θ + u, f t) (Icc 0 (π - θ)) := by
  have hI : IntegrableOn f (uIcc θ π) volume := by
    rw [uIcc_of_le hθ.2.le]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hθ.2.le).1
      (hf.intervalIntegrable ⟨hθ.1.le, hθ.2.le⟩ ⟨Real.pi_pos.le, le_rfl⟩)
  have hG := intervalIntegral.continuousOn_primitive_interval (a := θ) (b := π) (μ := volume)
    (f := f) hI
  refine hG.comp (continuousOn_const.add continuousOn_id) ?_
  intro u hu
  rw [uIcc_of_le hθ.2.le]
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩


theorem sin_div_lt (hm : 1 < m) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < Real.sin θ / m ∧ Real.sin θ / m < π - θ ∧ Real.sin θ / m < π / 2 := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h1 : Real.sin θ ≤ π - θ := by
    rw [← Real.sin_pi_sub]; exact Real.sin_le (by linarith [hθ.2])
  have h2 : Real.sin θ / m < Real.sin θ := div_lt_self hs hm
  have h3 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  refine ⟨div_pos hs (by linarith), by linarith, ?_⟩
  linarith [Real.pi_gt_three]

theorem exists_increment_eq (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ∃ u ∈ Icc 0 (Real.sin θ / m), ∫ t in θ..θ + u, f t = Real.sin θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hm := hf.one_lt
  obtain ⟨hsm0, hsm, -⟩ := sin_div_lt hm hθ
  have hcont := (continuousOn_increment hf hθ).mono (Icc_subset_Icc le_rfl hsm.le)
  have h0 : ∫ t in θ..θ + 0, f t = 0 := by simp
  have h1 : Real.sin θ ≤ ∫ t in θ..θ + Real.sin θ / m, f t := by
    have := integral_ge_of_admissible hf (a := θ) (b := θ + Real.sin θ / m) hθ.1.le (by linarith)
      (by linarith)
    have e : m * (θ + Real.sin θ / m - θ) = Real.sin θ := by field_simp; ring
    linarith
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hsm0.le hcont ⟨by rw [h0]; exact hs.le, h1⟩
  exact ⟨u, hu, hfu⟩

theorem profD_eq (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) {u : ℝ}
    (hu : u ∈ Icc 0 (π - θ)) (hfu : ∫ t in θ..θ + u, f t = Real.sin θ) : profD f θ = u := by
  apply IsLeast.csInf_eq
  refine ⟨⟨hu.1, hfu.ge⟩, ?_⟩
  rintro v ⟨hv0, hv⟩
  by_contra hlt
  push_neg at hlt
  have hv' : v ∈ Icc 0 (π - θ) := ⟨hv0, by linarith [hu.2]⟩
  have := integral_strictMonoOn hf hθ hv' hu hlt
  simp only at this
  linarith

/-- Characterization of `D_f`: `0 < D_f(θ) ≤ sin θ / m` and `∫_θ^{θ+D_f(θ)} f = sin θ`. -/
theorem profD_spec (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < profD f θ ∧ profD f θ ≤ Real.sin θ / m ∧
      ∫ t in θ..θ + profD f θ, f t = Real.sin θ := by
  obtain ⟨u, hu, hfu⟩ := exists_increment_eq hf hθ
  obtain ⟨-, hsm, -⟩ := sin_div_lt hf.one_lt hθ
  have hD := profD_eq hf hθ ⟨hu.1, by linarith [hu.2]⟩ hfu
  rw [hD]
  refine ⟨?_, hu.2, hfu⟩
  rcases hu.1.eq_or_lt with h0 | h0
  · subst h0
    simp at hfu
    have := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    linarith
  · exact h0

theorem cot_pos_of_mem {x : ℝ} (h0 : 0 < x) (h1 : x < π / 2) : 0 < Real.cot x := by
  rw [Real.cot_eq_cos_div_sin]
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩)
    (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos]))

theorem cot_lt_cot {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < π / 2) :
    Real.cot v < Real.cot u := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  have hpi := Real.pi_pos
  have hsu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith)
  have hcv : 0 < Real.cos v := Real.cos_pos_of_mem_Ioo ⟨by linarith, hv⟩
  have hc : Real.cos v < Real.cos u :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hu.le hv.le huv
  have hs : Real.sin u < Real.sin v :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hv.le huv
  rw [div_lt_div_iff₀ (by linarith) hsu]
  nlinarith

theorem cot_arctan {x : ℝ} (hx : 0 < x) : Real.cot (Real.arctan x) = 1 / x := by
  rw [Real.cot_eq_cos_div_sin, Real.cos_arctan, Real.sin_arctan]
  have : 0 < √(1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  field_simp


theorem profD_lt (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    profD f θ < π - θ ∧ profD f θ < π / 2 := by
  obtain ⟨-, h2, -⟩ := profD_spec hf hθ
  obtain ⟨-, h3, h4⟩ := sin_div_lt hf.one_lt hθ
  exact ⟨by linarith, by linarith⟩

/-- **Lemma 3.2.** `𝒫 f` is positive on `(0, π)`. -/
theorem profP_pos (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < profP f θ :=
  mul_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
    (cot_pos_of_mem (profD_spec hf hθ).1 (profD_lt hf hθ).2)

/-- `D` is antitone in the profile. -/
theorem profD_anti (hf : AdmissibleProfile f m M) (hh : AdmissibleProfile h m M)
    (hfh : ∀ θ ∈ Ioo 0 π, f θ ≤ h θ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    profD h θ ≤ profD f θ := by
  obtain ⟨h0, -, hint⟩ := profD_spec hf hθ
  have hlt := (profD_lt hf hθ).1
  apply csInf_le ⟨0, fun u hu => hu.1⟩
  refine ⟨h0.le, ?_⟩
  rw [← hint]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by linarith)
    (hf.intervalIntegrable ⟨hθ.1.le, hθ.2.le⟩ ⟨by linarith [hθ.1], by linarith⟩)
    (hh.intervalIntegrable ⟨hθ.1.le, hθ.2.le⟩ ⟨by linarith [hθ.1], by linarith⟩)
  intro x hx
  exact hfh x ⟨by linarith [hx.1, hθ.1], by linarith [hx.2]⟩

/-- **Lemma 3.2 (monotonicity).** `𝒫` is order preserving. -/
theorem profP_mono (hf : AdmissibleProfile f m M) (hh : AdmissibleProfile h m M)
    (hfh : ∀ θ ∈ Ioo 0 π, f θ ≤ h θ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    profP f θ ≤ profP h θ := by
  unfold profP
  apply mul_le_mul_of_nonneg_left _ (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le
  have hle := profD_anti hf hh hfh hθ
  rcases hle.eq_or_lt with heq | hlt
  · rw [heq]
  · exact (cot_lt_cot (profD_spec hh hθ).1 hlt (profD_lt hf hθ).2).le

/-- `f θ = sin θ · cot d_f(θ)`. -/
theorem eq_sin_mul_cot_hairpinD (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    f θ = Real.sin θ * Real.cot (hairpinD f θ) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hf0 : 0 < f θ := by linarith [hf.lower θ hθ, hf.one_lt]
  unfold hairpinD
  rw [cot_arctan (div_pos hs hf0)]
  field_simp

theorem hairpinD_mem (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    hairpinD f θ ∈ Icc 0 (π - θ) ∧ 0 < hairpinD f θ ∧ hairpinD f θ < π / 2 := by
  obtain ⟨h1, h2, h3⟩ := hairpinD_bounds hf.one_lt hf.lower hθ
  obtain ⟨-, -, h4⟩ := sin_div_lt hf.one_lt hθ
  exact ⟨⟨h1.le, by linarith⟩, h1, by linarith⟩

/-- Sign criterion: `ℛ(f) ≥ 0 ↔ f ≤ 𝒫 f`. -/
theorem profR_nonneg_iff (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 ≤ profR f θ ↔ f θ ≤ profP f θ := by
  obtain ⟨hdmem, hd0, hd2⟩ := hairpinD_mem hf hθ
  obtain ⟨hD0, -, hDint⟩ := profD_spec hf hθ
  have hDmem : profD f θ ∈ Icc 0 (π - θ) := ⟨hD0.le, (profD_lt hf hθ).1.le⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hmono := integral_strictMonoOn hf hθ
  have key : 0 ≤ profR f θ ↔ profD f θ ≤ hairpinD f θ := by
    unfold profR hairpinG
    rw [sub_nonneg, ← hDint]
    exact hmono.le_iff_le hDmem hdmem
  rw [key, eq_sin_mul_cot_hairpinD hf hθ, profP]
  constructor
  · intro hle
    apply mul_le_mul_of_nonneg_left _ hs.le
    rcases hle.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (cot_lt_cot hD0 hlt hd2).le
  · intro hle
    have hle' : Real.cot (hairpinD f θ) ≤ Real.cot (profD f θ) := le_of_mul_le_mul_left hle hs
    by_contra hlt
    push_neg at hlt
    have := cot_lt_cot hd0 hlt (profD_lt hf hθ).2
    linarith

/-- Sign criterion: `ℛ(f) ≤ 0 ↔ 𝒫 f ≤ f`. -/
theorem profR_nonpos_iff (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    profR f θ ≤ 0 ↔ profP f θ ≤ f θ := by
  obtain ⟨hdmem, hd0, hd2⟩ := hairpinD_mem hf hθ
  obtain ⟨hD0, -, hDint⟩ := profD_spec hf hθ
  have hDmem : profD f θ ∈ Icc 0 (π - θ) := ⟨hD0.le, (profD_lt hf hθ).1.le⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hmono := integral_strictMonoOn hf hθ
  have key : profR f θ ≤ 0 ↔ hairpinD f θ ≤ profD f θ := by
    unfold profR hairpinG
    rw [sub_nonpos, ← hDint]
    exact hmono.le_iff_le hdmem hDmem
  rw [key, eq_sin_mul_cot_hairpinD hf hθ, profP]
  constructor
  · intro hle
    apply mul_le_mul_of_nonneg_left _ hs.le
    rcases hle.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (cot_lt_cot hd0 hlt (profD_lt hf hθ).2).le
  · intro hle
    have hle' : Real.cot (profD f θ) ≤ Real.cot (hairpinD f θ) := le_of_mul_le_mul_left hle hs
    by_contra hlt
    push_neg at hlt
    have := cot_lt_cot hD0 hlt hd2
    linarith

/-- **Lemma 3.2 (fixed points).** `f = 𝒫 f` on `(0, π)` iff `f` solves the translator
equation (3.3). -/
theorem profP_fixed_iff (hf : AdmissibleProfile f m M) :
    (∀ θ ∈ Ioo 0 π, profP f θ = f θ) ↔ TranslatorEq f := by
  constructor
  · intro hfix θ hθ
    have h1 := (profR_nonneg_iff hf hθ).2 (hfix θ hθ).ge
    have h2 := (profR_nonpos_iff hf hθ).2 (hfix θ hθ).le
    have : profR f θ = 0 := le_antisymm h2 h1
    unfold profR at this
    linarith
  · intro hT θ hθ
    have h0 : profR f θ = 0 := by unfold profR; rw [hT θ hθ]; ring
    exact le_antisymm ((profR_nonpos_iff hf hθ).1 h0.le) ((profR_nonneg_iff hf hθ).1 h0.ge)


theorem abs_integral_bounds (hf : AdmissibleProfile f m M) {a b : ℝ} (ha : a ∈ Icc 0 π)
    (hb : b ∈ Icc 0 π) :
    m * |b - a| ≤ |∫ t in a..b, f t| ∧ |∫ t in a..b, f t| ≤ M * |b - a| := by
  have hm := hf.one_lt
  rcases le_total a b with hab | hab
  · have h1 := integral_ge_of_admissible hf ha.1 hab hb.2
    have h2 := integral_le_of_admissible hf ha.1 hab hb.2
    have h0 : 0 ≤ ∫ t in a..b, f t := by nlinarith
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    exact ⟨h1, h2⟩
  · have h1 := integral_ge_of_admissible hf hb.1 hab ha.2
    have h2 := integral_le_of_admissible hf hb.1 hab ha.2
    rw [intervalIntegral.integral_symm]
    have h0 : 0 ≤ ∫ t in b..a, f t := by nlinarith
    rw [abs_neg, abs_of_nonneg h0, abs_of_nonpos (by linarith)]
    constructor <;> linarith

theorem profD_lipschitz (hf : AdmissibleProfile f m M) {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ Ioo 0 π)
    (h₂ : θ₂ ∈ Ioo 0 π) :
    |profD f θ₁ - profD f θ₂| ≤ ((M + 1) / m + 1) * |θ₁ - θ₂| := by
  have hm := hf.one_lt
  obtain ⟨hD1, -, hI1⟩ := profD_spec hf h₁
  obtain ⟨hD2, -, hI2⟩ := profD_spec hf h₂
  have hl1 := (profD_lt hf h₁).1
  have hl2 := (profD_lt hf h₂).1
  set x₁ := θ₁ + profD f θ₁ with hx₁
  set x₂ := θ₂ + profD f θ₂ with hx₂
  have m1 : θ₁ ∈ Icc 0 π := ⟨h₁.1.le, h₁.2.le⟩
  have m2 : θ₂ ∈ Icc 0 π := ⟨h₂.1.le, h₂.2.le⟩
  have mx1 : x₁ ∈ Icc 0 π := ⟨by linarith [h₁.1], by linarith⟩
  have mx2 : x₂ ∈ Icc 0 π := ⟨by linarith [h₂.1], by linarith⟩
  have hcomm := intervalIntegral.integral_interval_sub_interval_comm
    (hf.intervalIntegrable m1 mx1) (hf.intervalIntegrable m2 mx2)
    (hf.intervalIntegrable m1 m2)
  rw [hI1, hI2] at hcomm
  obtain ⟨hJ1, -⟩ := abs_integral_bounds hf mx1 mx2
  obtain ⟨-, hI⟩ := abs_integral_bounds hf m1 m2
  have hsin : |Real.sin θ₁ - Real.sin θ₂| ≤ |θ₁ - θ₂| := Real.abs_sin_sub_sin_le _ _
  have hJ : |∫ t in x₁..x₂, f t| ≤ M * |θ₂ - θ₁| + |θ₁ - θ₂| := by
    have : (∫ t in x₁..x₂, f t) = (∫ t in θ₁..θ₂, f t) - (Real.sin θ₁ - Real.sin θ₂) := by
      linarith
    rw [this]
    exact (abs_sub _ _).trans (add_le_add hI hsin)
  rw [abs_sub_comm θ₂ θ₁] at hJ
  have hx : |x₂ - x₁| ≤ (M + 1) / m * |θ₁ - θ₂| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  have : profD f θ₁ - profD f θ₂ = -(x₂ - x₁) + (θ₂ - θ₁) := by rw [hx₁, hx₂]; ring
  rw [this]
  calc |-(x₂ - x₁) + (θ₂ - θ₁)| ≤ |x₂ - x₁| + |θ₂ - θ₁| := by
        rw [← abs_neg (x₂ - x₁)]; exact abs_add_le _ _
    _ ≤ (M + 1) / m * |θ₁ - θ₂| + |θ₁ - θ₂| := by rw [abs_sub_comm θ₂ θ₁]; linarith
    _ = ((M + 1) / m + 1) * |θ₁ - θ₂| := by ring

theorem continuousOn_profD (hf : AdmissibleProfile f m M) :
    ContinuousOn (profD f) (Ioo 0 π) := by
  intro θ hθ
  rw [Metric.continuousWithinAt_iff]
  intro e he
  have hm := hf.one_lt
  have hM : 0 < (M + 1) / m + 1 := by
    have : m ≤ M := (hf.lower θ hθ).trans (hf.upper θ hθ)
    have : 0 < (M + 1) / m := div_pos (by linarith) (by linarith)
    linarith
  refine ⟨e / ((M + 1) / m + 1), div_pos he hM, fun y hy hyd => ?_⟩
  rw [Real.dist_eq] at hyd ⊢
  calc |profD f y - profD f θ| ≤ ((M + 1) / m + 1) * |y - θ| := profD_lipschitz hf hy hθ
    _ < ((M + 1) / m + 1) * (e / ((M + 1) / m + 1)) := mul_lt_mul_of_pos_left hyd hM
    _ = e := mul_div_cancel₀ _ hM.ne'

/-- **Lemma 3.2 (continuity).** `𝒫 f` is continuous on `(0, π)`. -/
theorem continuousOn_profP (hf : AdmissibleProfile f m M) :
    ContinuousOn (profP f) (Ioo 0 π) := by
  unfold profP
  apply Real.continuous_sin.continuousOn.mul
  have hcot : ContinuousOn Real.cot (Ioo 0 (π / 2)) := by
    have : Real.cot = fun x => Real.cos x / Real.sin x := funext Real.cot_eq_cos_div_sin
    rw [this]
    exact Real.continuous_cos.continuousOn.div Real.continuous_sin.continuousOn
      (fun x hx => (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])).ne')
  exact hcot.comp (continuousOn_profD hf) (fun θ hθ => ⟨(profD_spec hf hθ).1, (profD_lt hf hθ).2⟩)

end Ovals

end
