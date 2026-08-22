import Mathlib

/-!
# The hairpin defined by a translator profile

A *hairpin* is, in the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates*, a complete embedded strictly convex curve whose tangent turns
through `π` and whose two ends are asymptotic to parallel lines.  Section 3 of
the paper produces a hairpin from a profile `f` on `(0, π)` with
`1 < m ≤ f ≤ M`, via the coordinate equations

`X' = f cot θ`,  `Z' = f`,  `0 < θ < π`.

This file formalizes the geometric conclusion that these equations really do
define a hairpin.

Main results, for a continuous profile with `0 < m ≤ f ≤ M`:

* `hasDerivAt_hairpinZ`, `hasDerivAt_hairpinX` : the coordinate equations;
* `hasDerivAt_hairpinCurve` : in complex notation `C' = (f / sin θ) e^{iθ}`, so
  the curve is regular and its **tangent angle is the parameter `θ`**; as `θ`
  runs over `(0, π)` the tangent turns through `π`;
* `hairpin_injective` : the curve is **embedded** (`Z` is strictly increasing);
* `hairpin_curvature_pos` : the curvature `dθ/ds = sin θ / f` is **positive**,
  so the curve is strictly convex;
* `abs_hairpinZ_le`, `tendsto_hairpinX_atBot`, `tendsto_hairpinX_pi_atBot` :
  the vertical coordinate stays bounded, `|Z| ≤ M π`, while the horizontal one
  runs off to `-∞` at both ends: the two ends are asymptotic to two horizontal
  (hence **parallel**) lines, and the curve opens in one direction;
* `tendsto_hairpinArclength_atTop`, `tendsto_hairpinArclength_pi_atTop` : the
  arclength diverges at both ends `θ → 0⁺` and `θ → π⁻`, so the curve is
  **complete**.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral Filter Topology

namespace Hairpin

variable {f : ℝ → ℝ} {m M : ℝ}

/-- The vertical coordinate `Z(θ) = ∫_{π/2}^θ f`. -/
def hairpinZ (f : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ t in (π/2)..θ, f t

/-- The horizontal coordinate `X(θ) = ∫_{π/2}^θ f cot`. -/
def hairpinX (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ t in (π/2)..θ, f t * (Real.cos t / Real.sin t)

/-- The hairpin curve `C = X + iZ`, parametrized by its tangent angle. -/
def hairpinCurve (f : ℝ → ℝ) (θ : ℝ) : ℂ :=
  (hairpinX f θ : ℂ) + Complex.I * (hairpinZ f θ : ℂ)

/-- The arclength element is `f / sin θ`. -/
def hairpinArclength (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ t in a..b, f t / Real.sin t

@[simp] theorem hairpinCurve_im (θ : ℝ) : (hairpinCurve f θ).im = hairpinZ f θ := by
  simp [hairpinCurve]

/-! ### The coordinate equations -/

theorem hasDerivAt_hairpinZ (hf : Continuous f) (θ : ℝ) :
    HasDerivAt (hairpinZ f) (f θ) θ := by
  simpa [hairpinZ] using (hf.integral_hasStrictDerivAt (π/2) θ).hasDerivAt

theorem mem_Ioo_pi_div_two : (π/2 : ℝ) ∈ Ioo (0:ℝ) π := by
  constructor <;> linarith [Real.pi_pos]

theorem hasDerivAt_hairpinX (hf : Continuous f) {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    HasDerivAt (hairpinX f) (f θ * (Real.cos θ / Real.sin θ)) θ := by
  set g : ℝ → ℝ := fun t => f t * (Real.cos t / Real.sin t) with hg
  have hsub : uIcc (π/2) θ ⊆ Ioo (0:ℝ) π :=
    (Set.ordConnected_Ioo).uIcc_subset mem_Ioo_pi_div_two hθ
  have hgc : ContinuousOn g (uIcc (π/2) θ) := by
    refine hf.continuousOn.mul ((Real.continuous_cos.continuousOn).div
      (Real.continuous_sin.continuousOn) ?_)
    intro u hu
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (hsub hu).1 (hsub hu).2)
  have hint : IntervalIntegrable g volume (π/2) θ := hgc.intervalIntegrable
  have hsθ : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hcontAt : ContinuousAt g θ := by
    have h : ContinuousAt (fun t : ℝ => Real.cos t / Real.sin t) θ :=
      (Real.continuous_cos.continuousAt).div (Real.continuous_sin.continuousAt) hsθ
    exact (hf.continuousAt).mul h
  have hmeasg : AEStronglyMeasurable g volume :=
    (hf.measurable.mul
      (Real.continuous_cos.measurable.div Real.continuous_sin.measurable)).aestronglyMeasurable
  have hmeas : StronglyMeasurableAtFilter g (𝓝 θ) := ⟨univ, univ_mem, hmeasg.restrict⟩
  simpa [hairpinX, hg] using intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt

/-! ### Regularity: the tangent angle is the parameter -/

/-- **The velocity of the hairpin**: `C'(θ) = (f/sin θ) e^{iθ}`.  In particular
the unit tangent is `e^{iθ}`: the tangent angle is the parameter, and it turns
through `π` as `θ` runs over `(0, π)`. -/
theorem hasDerivAt_hairpinCurve (hf : Continuous f) {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    HasDerivAt (hairpinCurve f)
      ((f θ / Real.sin θ : ℝ) * Complex.exp (Complex.I * (θ : ℂ))) θ := by
  have hsθ : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hsC : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsθ
  have hX := (hasDerivAt_hairpinX hf hθ).ofReal_comp
  have hZ := (hasDerivAt_hairpinZ hf θ).ofReal_comp
  have h := hX.add (hZ.const_mul Complex.I)
  refine h.congr_deriv ?_
  have hEuler : Complex.exp (Complex.I * (θ : ℂ))
      = (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin, mul_comm]
  rw [hEuler]
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  field_simp

/-- The hairpin is regular: its speed `f / sin θ` is positive. -/
theorem hairpin_speed_pos (hfpos : ∀ t, 0 < f t) {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    0 < f θ / Real.sin θ :=
  div_pos (hfpos θ) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

/-! ### Embeddedness -/

theorem strictMono_hairpinZ (hf : Continuous f) (hfpos : ∀ t, 0 < f t) :
    StrictMono (hairpinZ f) := by
  refine strictMono_of_deriv_pos fun θ => ?_
  rw [(hasDerivAt_hairpinZ hf θ).deriv]
  exact hfpos θ

/-- **The hairpin is embedded**: the curve is injective, because its vertical
coordinate is strictly increasing. -/
theorem hairpin_injective (hf : Continuous f) (hfpos : ∀ t, 0 < f t) :
    Function.Injective (hairpinCurve f) := by
  intro a b hab
  have : hairpinZ f a = hairpinZ f b := by
    have := congrArg Complex.im hab
    simpa using this
  exact (strictMono_hairpinZ hf hfpos).injective this

/-! ### Strict convexity -/

/-- **The hairpin is strictly convex**: its curvature `dθ/ds = sin θ / f` is
positive on `(0, π)`. -/
theorem hairpin_curvature_pos (hfpos : ∀ t, 0 < f t) {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    0 < Real.sin θ / f θ :=
  div_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) (hfpos θ)

/-- The curvature is the reciprocal of the speed: `(dθ/ds)·(ds/dθ) = 1`. -/
theorem hairpin_curvature_mul_speed (hfpos : ∀ t, 0 < f t) {θ : ℝ}
    (hθ : θ ∈ Ioo (0:ℝ) π) :
    (Real.sin θ / f θ) * (f θ / Real.sin θ) = 1 := by
  have hs : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hfne : f θ ≠ 0 := ne_of_gt (hfpos θ)
  field_simp

/-! ### The ends: parallel asymptotes and completeness -/

/-- The vertical coordinate stays bounded by `M π`: the two ends of the hairpin
are asymptotic to two horizontal, hence parallel, lines. -/
theorem abs_hairpinZ_le (hM : ∀ t, |f t| ≤ M) {θ : ℝ}
    (hθ : θ ∈ Icc (0:ℝ) π) : |hairpinZ f θ| ≤ M * π := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := π/2) (b := θ) (C := M) (f := f) (fun t _ => by simpa using hM t)
  have hle : |θ - π/2| ≤ π := by
    rcases hθ with ⟨h0, h1⟩
    rw [abs_le]
    constructor <;> linarith [Real.pi_pos]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0)
  calc |hairpinZ f θ| ≤ M * |θ - π/2| := by simpa [hairpinZ, Real.norm_eq_abs] using hbound
    _ ≤ M * π := by exact mul_le_mul_of_nonneg_left hle hM0

/-- The arclength from a point `θ ∈ (0,1]` to `1` is at least `m log(1/θ)`. -/
theorem hairpinArclength_ge (hf : Continuous f) (hm : ∀ t, m ≤ f t) (hm0 : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    m * Real.log (1 / θ) ≤ hairpinArclength f θ 1 := by
  have hπ : (1:ℝ) < π := by linarith [Real.pi_gt_three]
  have hsub : ∀ t ∈ uIcc θ (1:ℝ), 0 < Real.sin t := by
    intro t ht
    rw [uIcc_of_le hθ1] at ht
    exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hθ0 ht.1) (lt_of_le_of_lt ht.2 hπ)
  have hlow : ∀ t ∈ Icc θ (1:ℝ), m * (1 / t) ≤ f t / Real.sin t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hθ0 ht.1
    have hsin : 0 < Real.sin t := hsub t (by rw [uIcc_of_le hθ1]; exact ht)
    have hst : Real.sin t ≤ t := Real.sin_le ht0.le
    have hmf : m ≤ f t := hm t
    rw [show m * (1/t) = m / t by ring, div_le_div_iff₀ ht0 hsin]
    nlinarith
  have hint1 : IntervalIntegrable (fun t => m * (1 / t)) volume θ 1 := by
    apply ContinuousOn.intervalIntegrable
    have h0 : ∀ t ∈ uIcc θ (1:ℝ), t ≠ 0 := by
      intro t ht
      rw [uIcc_of_le hθ1] at ht
      exact ne_of_gt (lt_of_lt_of_le hθ0 ht.1)
    exact continuousOn_const.mul (continuousOn_const.div continuousOn_id h0)
  have hint2 : IntervalIntegrable (fun t => f t / Real.sin t) volume θ 1 := by
    apply ContinuousOn.intervalIntegrable
    exact hf.continuousOn.div (Real.continuous_sin.continuousOn)
      (fun t ht => ne_of_gt (hsub t ht))
  have hmono := intervalIntegral.integral_mono_on hθ1 hint1 hint2 (fun t ht => hlow t ht)
  have hcalc : (∫ t in θ..(1:ℝ), m * (1 / t)) = m * Real.log (1 / θ) := by
    rw [intervalIntegral.integral_const_mul, integral_one_div (by
      rw [uIcc_of_le hθ1]
      intro h
      exact absurd h.1 (not_le.mpr hθ0))]
  rw [hcalc] at hmono
  exact hmono

/-- **Completeness at the end `θ → 0⁺`**: the arclength diverges. -/
theorem tendsto_hairpinArclength_atTop (hf : Continuous f) (hm : ∀ t, m ≤ f t) (hm0 : 0 < m) :
    Tendsto (fun θ => hairpinArclength f θ 1) (𝓝[>] (0:ℝ)) atTop := by
  have hlog : Tendsto (fun θ : ℝ => m * Real.log (1 / θ)) (𝓝[>] (0:ℝ)) atTop := by
    have h1 : Tendsto (fun θ : ℝ => Real.log (1 / θ)) (𝓝[>] (0:ℝ)) atTop := by
      have h2 : Tendsto (fun θ : ℝ => -Real.log θ) (𝓝[>] (0:ℝ)) atTop :=
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
      simpa [one_div, Real.log_inv] using h2
    exact Filter.Tendsto.const_mul_atTop hm0 h1
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with θ hθ
  exact hairpinArclength_ge hf hm hm0 hθ.1 hθ.2.le

/-- Reflecting the parameter, `θ ↦ π - θ`, exchanges the two ends. -/
theorem hairpinArclength_reflect (θ : ℝ) :
    hairpinArclength (fun u => f (π - u)) θ 1 = hairpinArclength f (π - 1) (π - θ) := by
  have h : ∀ x : ℝ, f (π - x) / Real.sin x = (fun y => f y / Real.sin y) (π - x) := by
    intro x
    simp [Real.sin_pi_sub]
  simp only [hairpinArclength]
  rw [intervalIntegral.integral_congr (g := fun x => (fun y => f y / Real.sin y) (π - x))
    (fun x _ => h x)]
  exact intervalIntegral.integral_comp_sub_left (fun y => f y / Real.sin y) π

/-- **Completeness at the end `θ → π⁻`**: the arclength diverges there too. -/
theorem tendsto_hairpinArclength_pi_atTop (hf : Continuous f) (hm : ∀ t, m ≤ f t)
    (hm0 : 0 < m) :
    Tendsto (fun θ => hairpinArclength f (π - 1) (π - θ)) (𝓝[>] (0:ℝ)) atTop := by
  have hfr : Continuous fun u => f (π - u) := hf.comp (continuous_const.sub continuous_id)
  have h := tendsto_hairpinArclength_atTop (f := fun u => f (π - u)) (m := m) hfr
    (fun t => hm _) hm0
  simpa [hairpinArclength_reflect] using h

/-- Integrability of `f cot` on a compact subinterval of `(0, π)`. -/
theorem cot_intervalIntegrable {a b : ℝ} (hf : Continuous f) (ha : 0 < a) (hb : b < π)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t => f t * (Real.cos t / Real.sin t)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hsub : ∀ t ∈ uIcc a b, 0 < Real.sin t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le ha ht.1) (lt_of_le_of_lt ht.2 hb)
  exact hf.continuousOn.mul (Real.continuous_cos.continuousOn.div
    Real.continuous_sin.continuousOn (fun t ht => ne_of_gt (hsub t ht)))

/-- Near the end `θ → 0⁺` the horizontal coordinate is at most
`-m cos 1 · log(1/θ)`. -/
theorem hairpinX_le (hf : Continuous f) (hm : ∀ t, m ≤ f t) (hm0 : 0 < m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    hairpinX f θ ≤ -(m * Real.cos 1 * Real.log (1 / θ)) := by
  have hπ2 : (1:ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  have hπ : (1:ℝ) < π := by linarith [Real.pi_gt_three]
  set g : ℝ → ℝ := fun t => f t * (Real.cos t / Real.sin t) with hg
  have hi1 : IntervalIntegrable g volume θ 1 := cot_intervalIntegrable hf hθ0 hπ hθ1
  have hi2 : IntervalIntegrable g volume 1 (π/2) :=
    cot_intervalIntegrable hf (by norm_num) (by linarith [Real.pi_pos]) hπ2.le
  have hadd : (∫ t in θ..1, g t) + (∫ t in (1:ℝ)..(π/2), g t) = ∫ t in θ..(π/2), g t :=
    intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hsym : hairpinX f θ = -∫ t in θ..(π/2), g t := by
    rw [hairpinX]
    exact intervalIntegral.integral_symm _ _
  have hpos2 : 0 ≤ ∫ t in (1:ℝ)..(π/2), g t := by
    apply intervalIntegral.integral_nonneg hπ2.le
    intro t ht
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by
      linarith [ht.2, Real.pi_pos])
    have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], by
      linarith [ht.2]⟩
    have hfpos : 0 < f t := lt_of_lt_of_le hm0 (hm t)
    have hdiv : 0 ≤ Real.cos t / Real.sin t := by positivity
    exact mul_nonneg hfpos.le hdiv
  have hlow : ∀ t ∈ Icc θ (1:ℝ), m * Real.cos 1 * (1 / t) ≤ g t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hθ0 ht.1
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [ht.2])
    have hst : Real.sin t ≤ t := Real.sin_le ht0.le
    have hcos : Real.cos 1 ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht0.le (by linarith [Real.pi_gt_three]) ht.2
    have hc1 : 0 < Real.cos 1 := Real.cos_one_pos
    have hfpos : 0 < f t := lt_of_lt_of_le hm0 (hm t)
    have hmf : m ≤ f t := hm t
    have h1 : m * Real.cos 1 ≤ f t * Real.cos t := by nlinarith
    have hts : 1 ≤ t / Real.sin t := (one_le_div hs).mpr hst
    have hcpos : 0 < Real.cos t := lt_of_lt_of_le hc1 hcos
    have h2 : f t * Real.cos t ≤ g t * t := by
      have hrw : g t * t = (f t * Real.cos t) * (t / Real.sin t) := by
        rw [hg]; field_simp
      rw [hrw]
      nlinarith [mul_pos hfpos hcpos]
    rw [show m * Real.cos 1 * (1/t) = (m * Real.cos 1) / t by ring, div_le_iff₀ ht0]
    linarith
  have hint1 : IntervalIntegrable (fun t => m * Real.cos 1 * (1 / t)) volume θ 1 := by
    apply ContinuousOn.intervalIntegrable
    have h0 : ∀ t ∈ uIcc θ (1:ℝ), t ≠ 0 := by
      intro t ht
      rw [uIcc_of_le hθ1] at ht
      exact ne_of_gt (lt_of_lt_of_le hθ0 ht.1)
    exact continuousOn_const.mul (continuousOn_const.div continuousOn_id h0)
  have hmono := intervalIntegral.integral_mono_on hθ1 hint1 hi1 hlow
  have hcalc : (∫ t in θ..(1:ℝ), m * Real.cos 1 * (1 / t))
      = m * Real.cos 1 * Real.log (1 / θ) := by
    rw [intervalIntegral.integral_const_mul, integral_one_div (by
      rw [uIcc_of_le hθ1]
      intro h
      exact absurd h.1 (not_le.mpr hθ0))]
  rw [hcalc] at hmono
  linarith [hsym, hadd, hpos2, hmono]

/-- **The end `θ → 0⁺` runs off to horizontal infinity**: `X → -∞`.  Together
with the bound `|Z| ≤ M π` this is the asymptotic-to-parallel-lines behaviour of
a hairpin. -/
theorem tendsto_hairpinX_atBot (hf : Continuous f) (hm : ∀ t, m ≤ f t) (hm0 : 0 < m) :
    Tendsto (hairpinX f) (𝓝[>] (0:ℝ)) atBot := by
  have hc1 : 0 < Real.cos 1 := Real.cos_one_pos
  have hlog : Tendsto (fun θ : ℝ => -(m * Real.cos 1 * Real.log (1 / θ)))
      (𝓝[>] (0:ℝ)) atBot := by
    have h1 : Tendsto (fun θ : ℝ => Real.log (1 / θ)) (𝓝[>] (0:ℝ)) atTop := by
      have h2 : Tendsto (fun θ : ℝ => -Real.log θ) (𝓝[>] (0:ℝ)) atTop :=
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
      simpa [one_div, Real.log_inv] using h2
    exact tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop (by positivity) h1)
  refine tendsto_atBot_mono' _ ?_ hlog
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with θ hθ
  exact hairpinX_le hf hm hm0 hθ.1 hθ.2.le

/-- Reflecting the parameter, `θ ↦ π - θ`, exchanges the two ends for the
horizontal coordinate as well. -/
theorem hairpinX_reflect (θ : ℝ) :
    hairpinX (fun u => f (π - u)) θ = hairpinX f (π - θ) := by
  have hH : ∀ u : ℝ, f (π - u) * (Real.cos u / Real.sin u)
      = (fun y => -(f y * (Real.cos y / Real.sin y))) (π - u) := by
    intro u
    have h1 : Real.cos (π - u) = -Real.cos u := Real.cos_pi_sub u
    have h2 : Real.sin (π - u) = Real.sin u := Real.sin_pi_sub u
    simp [h1, h2]
    ring
  simp only [hairpinX]
  rw [intervalIntegral.integral_congr
      (g := fun u => (fun y => -(f y * (Real.cos y / Real.sin y))) (π - u)) (fun u _ => hH u),
    intervalIntegral.integral_comp_sub_left (fun y => -(f y * (Real.cos y / Real.sin y))) π,
    intervalIntegral.integral_neg,
    show π - π/2 = π/2 by ring]
  rw [intervalIntegral.integral_symm (π/2) (π - θ)]
  ring

/-- **The end `θ → π⁻` also runs off to horizontal infinity**, on the same side:
`X → -∞` there too, so the hairpin opens in one direction. -/
theorem tendsto_hairpinX_pi_atBot (hf : Continuous f) (hm : ∀ t, m ≤ f t) (hm0 : 0 < m) :
    Tendsto (fun θ => hairpinX f (π - θ)) (𝓝[>] (0:ℝ)) atBot := by
  have hfr : Continuous fun u => f (π - u) := hf.comp (continuous_const.sub continuous_id)
  have h := tendsto_hairpinX_atBot (f := fun u => f (π - u)) (m := m) hfr (fun t => hm _) hm0
  rwa [show (hairpinX fun u => f (π - u)) = fun θ => hairpinX f (π - θ) from
    funext fun θ => hairpinX_reflect θ] at h

end Hairpin
