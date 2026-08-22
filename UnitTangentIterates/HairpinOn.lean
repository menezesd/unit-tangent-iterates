import Mathlib
import UnitTangentIterates.Hairpin
import UnitTangentIterates.LimitProfile

/-!
# The hairpin of a profile that is only continuous on the open interval

`UnitTangentIterates/Hairpin.lean` shows that the profile equations

`X' = f cot θ`,  `Z' = f`,  `0 < θ < π`

define a complete embedded strictly convex hairpin, for a profile `f` that is
continuous **on all of `ℝ`** and squeezed between two positive constants.  The
limit profile produced by the iteration of Section 3 of *A Noncircular Oval
with Convex Unit-Tangent Iterates*, however, is only known to be continuous on
the **open** interval `(0, π)` (`UnitTangentIterates/LimitProfile.lean`), and a
bounded function continuous on `(0, π)` need not extend continuously to `ℝ`.

This file removes that mismatch, and thereby joins the two halves of Section 3
into one statement.  The device is the *clamped profile*
`f_{a,b}(t) = f(max a (min b t))`, which agrees with `f` on `[a, b]` and is
continuous on `ℝ` as soon as `[a, b] ⊆ (0, π)`; every quantity appearing in the
hairpin equations only sees the values of `f` on a compact subinterval of
`(0, π)`, so each statement of `Hairpin.lean` transfers.

Main results, for `f` continuous on `(0, π)` with `0 < m ≤ f ≤ M` there:

* `hasDerivAt_hairpinZ'`, `hasDerivAt_hairpinX'`, `hasDerivAt_hairpinCurve'` :
  the coordinate equations and the velocity `C' = (f / sin θ) e^{iθ}`;
* `strictMonoOn_hairpinZ'`, `injOn_hairpinCurve'` : embeddedness;
* `abs_hairpinZ_le'` : `|Z| ≤ M π`;
* `tendsto_hairpinArclength_atTop'`, `tendsto_hairpinArclength_pi_atTop'` :
  completeness at the two ends;
* `tendsto_hairpinX_atBot'`, `tendsto_hairpinX_pi_atBot'` : the two ends run
  off to horizontal infinity on the same side;
* `isHairpin_of_continuousOn` : all of the above, assembled;
* `limit_profile_isHairpin` : the limit profile of the monotone iteration of
  Section 3 defines a hairpin.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral Filter Topology

namespace HairpinOn

open Hairpin

variable {f : ℝ → ℝ} {m M : ℝ}

/-! ### The clamped profile -/

/-- `clampTo a b t` is `t` clamped to the interval `[a, b]`. -/
def clampTo (a b t : ℝ) : ℝ := max a (min b t)

theorem continuous_clampTo (a b : ℝ) : Continuous (clampTo a b) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clampTo_mem_Icc {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clampTo a b t ∈ Icc a b := by
  constructor
  · exact le_max_left _ _
  · exact max_le hab (min_le_left _ _)

theorem clampTo_eq_self {a b t : ℝ} (ht : t ∈ Icc a b) : clampTo a b t = t := by
  simp [clampTo, min_eq_right ht.2, max_eq_right ht.1]

/-- The profile `f` clamped to the compact subinterval `[a, b] ⊆ (0, π)`. -/
def cprof (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ := fun t => f (clampTo a b t)

theorem cprof_continuous (hf : ContinuousOn f (Ioo 0 π)) {a b : ℝ}
    (ha : 0 < a) (hb : b < π) (hab : a ≤ b) : Continuous (cprof f a b) := by
  refine hf.comp_continuous (continuous_clampTo a b) ?_
  intro t
  obtain ⟨h1, h2⟩ := clampTo_mem_Icc hab t
  exact ⟨lt_of_lt_of_le ha h1, lt_of_le_of_lt h2 hb⟩

theorem cprof_eqOn {a b : ℝ} : EqOn (cprof f a b) f (Icc a b) := fun _ ht => by
  simp [cprof, clampTo_eq_self ht]

theorem cprof_mem_Ioo {a b : ℝ} (ha : 0 < a) (hb : b < π) (hab : a ≤ b) (t : ℝ) :
    clampTo a b t ∈ Ioo (0:ℝ) π := by
  obtain ⟨h1, h2⟩ := clampTo_mem_Icc hab t
  exact ⟨lt_of_lt_of_le ha h1, lt_of_le_of_lt h2 hb⟩

theorem cprof_lower {a b : ℝ} (ha : 0 < a) (hb : b < π) (hab : a ≤ b)
    (hm : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (t : ℝ) : m ≤ cprof f a b t :=
  hm _ (cprof_mem_Ioo ha hb hab t)

theorem cprof_upper {a b : ℝ} (ha : 0 < a) (hb : b < π) (hab : a ≤ b)
    (hM : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ M) (t : ℝ) : cprof f a b t ≤ M :=
  hM _ (cprof_mem_Ioo ha hb hab t)

/-! ### The clamped profile computes the same coordinates -/

theorem hairpinZ_cprof {a b θ : ℝ} (hsub : uIcc (π/2) θ ⊆ Icc a b) :
    hairpinZ (cprof f a b) θ = hairpinZ f θ :=
  intervalIntegral.integral_congr (fun _ ht => cprof_eqOn (hsub ht))

theorem hairpinX_cprof {a b θ : ℝ} (hsub : uIcc (π/2) θ ⊆ Icc a b) :
    hairpinX (cprof f a b) θ = hairpinX f θ :=
  intervalIntegral.integral_congr (fun _ ht => by rw [cprof_eqOn (hsub ht)])

theorem hairpinArclength_cprof {a b c d : ℝ} (hsub : uIcc c d ⊆ Icc a b) :
    hairpinArclength (cprof f a b) c d = hairpinArclength f c d :=
  intervalIntegral.integral_congr (fun _ ht => by rw [cprof_eqOn (hsub ht)])

/-- A compact interval `[a, b] ⊆ (0, π)` containing `π/2` and a neighbourhood
of a given `θ ∈ (0, π)`. -/
theorem exists_window {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    ∃ a b : ℝ, 0 < a ∧ b < π ∧ a ≤ b ∧ a < θ ∧ θ < b ∧ a < π/2 ∧ π/2 < b := by
  obtain ⟨h0, h1⟩ := hθ
  have hpi : 0 < π := Real.pi_pos
  have hmin1 : min θ (π/2) ≤ θ := min_le_left _ _
  have hmin2 : min θ (π/2) ≤ π/2 := min_le_right _ _
  have hmin0 : 0 < min θ (π/2) := lt_min h0 (by linarith)
  have hmax1 : θ ≤ max θ (π/2) := le_max_left _ _
  have hmax2 : π/2 ≤ max θ (π/2) := le_max_right _ _
  have hmax3 : max θ (π/2) < π := max_lt h1 (by linarith)
  exact ⟨min θ (π/2) / 2, (max θ (π/2) + π) / 2, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

theorem uIcc_subset_of_window {a b θ : ℝ} (ha : a ≤ θ) (hb : θ ≤ b)
    (ha' : a ≤ π/2) (hb' : π/2 ≤ b) : uIcc (π/2) θ ⊆ Icc a b :=
  uIcc_subset_Icc ⟨ha', hb'⟩ ⟨ha, hb⟩

/-! ### The coordinate equations -/

/-- **The vertical coordinate equation** `Z' = f`, for a profile continuous only
on the open interval `(0, π)`. -/
theorem hasDerivAt_hairpinZ' (hf : ContinuousOn f (Ioo 0 π)) {θ : ℝ}
    (hθ : θ ∈ Ioo (0:ℝ) π) : HasDerivAt (hairpinZ f) (f θ) θ := by
  obtain ⟨a, b, ha, hb, hab, haθ, hθb, ha2, hb2⟩ := exists_window hθ
  have hc : Continuous (cprof f a b) := cprof_continuous hf ha hb hab
  have hd := Hairpin.hasDerivAt_hairpinZ hc θ
  have hval : cprof f a b θ = f θ := cprof_eqOn ⟨haθ.le, hθb.le⟩
  rw [hval] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds haθ hθb] with x hx
  exact (hairpinZ_cprof (uIcc_subset_of_window hx.1.le hx.2.le ha2.le hb2.le)).symm

/-- **The horizontal coordinate equation** `X' = f cot θ`, for a profile
continuous only on `(0, π)`. -/
theorem hasDerivAt_hairpinX' (hf : ContinuousOn f (Ioo 0 π)) {θ : ℝ}
    (hθ : θ ∈ Ioo (0:ℝ) π) :
    HasDerivAt (hairpinX f) (f θ * (Real.cos θ / Real.sin θ)) θ := by
  obtain ⟨a, b, ha, hb, hab, haθ, hθb, ha2, hb2⟩ := exists_window hθ
  have hc : Continuous (cprof f a b) := cprof_continuous hf ha hb hab
  have hd := Hairpin.hasDerivAt_hairpinX hc hθ
  have hval : cprof f a b θ = f θ := cprof_eqOn ⟨haθ.le, hθb.le⟩
  rw [hval] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds haθ hθb] with x hx
  exact (hairpinX_cprof (uIcc_subset_of_window hx.1.le hx.2.le ha2.le hb2.le)).symm

/-- **The velocity of the hairpin**, `C'(θ) = (f/sin θ) e^{iθ}`: the tangent
angle is the parameter, so the tangent turns through `π` as `θ` runs over
`(0, π)`. -/
theorem hasDerivAt_hairpinCurve' (hf : ContinuousOn f (Ioo 0 π)) {θ : ℝ}
    (hθ : θ ∈ Ioo (0:ℝ) π) :
    HasDerivAt (hairpinCurve f)
      ((f θ / Real.sin θ : ℝ) * Complex.exp (Complex.I * (θ : ℂ))) θ := by
  have hX := (hasDerivAt_hairpinX' hf hθ).ofReal_comp
  have hZ := (hasDerivAt_hairpinZ' hf hθ).ofReal_comp
  have h := hX.add (hZ.const_mul Complex.I)
  refine h.congr_deriv ?_
  have hsθ : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hsC : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsθ
  have hEuler : Complex.exp (Complex.I * (θ : ℂ))
      = (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin, mul_comm]
  rw [hEuler]
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  field_simp

/-! ### Embeddedness -/

theorem continuousOn_hairpinZ' (hf : ContinuousOn f (Ioo 0 π)) :
    ContinuousOn (hairpinZ f) (Ioo 0 π) := fun _ hθ =>
  ((hasDerivAt_hairpinZ' hf hθ).continuousAt).continuousWithinAt

/-- **The vertical coordinate is strictly increasing** on `(0, π)`. -/
theorem strictMonoOn_hairpinZ' (hf : ContinuousOn f (Ioo 0 π))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t) : StrictMonoOn (hairpinZ f) (Ioo 0 π) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo (0:ℝ) π)
    (continuousOn_hairpinZ' hf) (f' := f) ?_ ?_
  · intro x hx
    rw [interior_Ioo] at hx
    exact ((hasDerivAt_hairpinZ' hf hx).hasDerivWithinAt)
  · intro x hx
    rw [interior_Ioo] at hx
    exact hfpos x hx

/-- **The hairpin is embedded**: the curve is injective on `(0, π)`. -/
theorem injOn_hairpinCurve' (hf : ContinuousOn f (Ioo 0 π))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t) : InjOn (hairpinCurve f) (Ioo 0 π) := by
  intro x hx y hy hxy
  have : hairpinZ f x = hairpinZ f y := by
    have := congrArg Complex.im hxy
    simpa using this
  exact (strictMonoOn_hairpinZ' hf hfpos).injOn hx hy this

/-! ### The ends -/

/-- The vertical coordinate stays bounded by `M π`. -/
theorem abs_hairpinZ_le' (hM : ∀ t ∈ Ioo (0:ℝ) π, |f t| ≤ M) {θ : ℝ}
    (hθ : θ ∈ Ioo (0:ℝ) π) : |hairpinZ f θ| ≤ M * π := by
  have hsub : uIcc (π/2) θ ⊆ Ioo (0:ℝ) π :=
    (Set.ordConnected_Ioo).uIcc_subset Hairpin.mem_Ioo_pi_div_two hθ
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := π/2) (b := θ) (C := M) (f := f) (fun t ht => by
      have ht' : t ∈ uIcc (π/2) θ := uIoc_subset_uIcc ht
      simpa using hM t (hsub ht'))
  have hle : |θ - π/2| ≤ π := by
    rcases hθ with ⟨h0, h1⟩
    rw [abs_le]
    constructor <;> linarith [Real.pi_pos]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f (π/2))) (hM _ Hairpin.mem_Ioo_pi_div_two)
  calc |hairpinZ f θ| ≤ M * |θ - π/2| := by simpa [hairpinZ, Real.norm_eq_abs] using hbound
    _ ≤ M * π := mul_le_mul_of_nonneg_left hle hM0

/-- A window `[θ/2, 3] ⊆ (0, π)` adapted to the end `θ → 0⁺`. -/
theorem end_window {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    0 < θ/2 ∧ (3:ℝ) < π ∧ θ/2 ≤ 3 ∧ uIcc θ (1:ℝ) ⊆ Icc (θ/2) 3 ∧
      uIcc (π/2) θ ⊆ Icc (θ/2) 3 := by
  have hpi : (3:ℝ) < π := Real.pi_gt_three
  have hpi' : π ≤ 4 := Real.pi_le_four
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_⟩
  · exact uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  · exact uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩

/-- **Completeness at the end `θ → 0⁺`**: the arclength diverges. -/
theorem tendsto_hairpinArclength_atTop' (hf : ContinuousOn f (Ioo 0 π))
    (hm : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hm0 : 0 < m) :
    Tendsto (fun θ => hairpinArclength f θ 1) (𝓝[>] (0:ℝ)) atTop := by
  have key : ∀ θ ∈ Ioo (0:ℝ) 1, m * Real.log (1/θ) ≤ hairpinArclength f θ 1 := by
    intro θ hθ
    obtain ⟨ha, hb, hab, hsub, -⟩ := end_window hθ.1 hθ.2.le
    have hc : Continuous (cprof f (θ/2) 3) := cprof_continuous hf ha hb hab
    have h := Hairpin.hairpinArclength_ge (f := cprof f (θ/2) 3) (m := m) hc
      (cprof_lower ha hb hab hm) hm0 hθ.1 hθ.2.le
    rwa [hairpinArclength_cprof hsub] at h
  have hlog : Tendsto (fun θ : ℝ => m * Real.log (1 / θ)) (𝓝[>] (0:ℝ)) atTop := by
    have h1 : Tendsto (fun θ : ℝ => Real.log (1 / θ)) (𝓝[>] (0:ℝ)) atTop := by
      have h2 : Tendsto (fun θ : ℝ => -Real.log θ) (𝓝[>] (0:ℝ)) atTop :=
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
      simpa [one_div, Real.log_inv] using h2
    exact Filter.Tendsto.const_mul_atTop hm0 h1
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with θ hθ
  exact key θ hθ

/-- **The end `θ → 0⁺` runs off to horizontal infinity**: `X → -∞`. -/
theorem tendsto_hairpinX_atBot' (hf : ContinuousOn f (Ioo 0 π))
    (hm : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hm0 : 0 < m) :
    Tendsto (hairpinX f) (𝓝[>] (0:ℝ)) atBot := by
  have key : ∀ θ ∈ Ioo (0:ℝ) 1, hairpinX f θ ≤ -(m * Real.cos 1 * Real.log (1/θ)) := by
    intro θ hθ
    obtain ⟨ha, hb, hab, -, hsub⟩ := end_window hθ.1 hθ.2.le
    have hc : Continuous (cprof f (θ/2) 3) := cprof_continuous hf ha hb hab
    have h := Hairpin.hairpinX_le (f := cprof f (θ/2) 3) (m := m) hc
      (cprof_lower ha hb hab hm) hm0 hθ.1 hθ.2.le
    rwa [hairpinX_cprof hsub] at h
  have hlog : Tendsto (fun θ : ℝ => -(m * Real.cos 1 * Real.log (1 / θ)))
      (𝓝[>] (0:ℝ)) atBot := by
    have h1 : Tendsto (fun θ : ℝ => Real.log (1 / θ)) (𝓝[>] (0:ℝ)) atTop := by
      have h2 : Tendsto (fun θ : ℝ => -Real.log θ) (𝓝[>] (0:ℝ)) atTop :=
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
      simpa [one_div, Real.log_inv] using h2
    have hc1 : 0 < Real.cos 1 := Real.cos_one_pos
    exact tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop (by positivity) h1)
  refine tendsto_atBot_mono' _ ?_ hlog
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with θ hθ
  exact key θ hθ

/-- The reflected profile `u ↦ f (π - u)` is again continuous on `(0, π)`. -/
theorem reflect_continuousOn (hf : ContinuousOn f (Ioo 0 π)) :
    ContinuousOn (fun u => f (π - u)) (Ioo 0 π) := by
  refine hf.comp (continuous_const.sub continuous_id).continuousOn ?_
  intro u hu
  exact ⟨by linarith [hu.2], by linarith [hu.1]⟩

theorem reflect_lower (hm : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) :
    ∀ t ∈ Ioo (0:ℝ) π, m ≤ f (π - t) := fun t ht =>
  hm _ ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- **Completeness at the end `θ → π⁻`**. -/
theorem tendsto_hairpinArclength_pi_atTop' (hf : ContinuousOn f (Ioo 0 π))
    (hm : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hm0 : 0 < m) :
    Tendsto (fun θ => hairpinArclength f (π - 1) (π - θ)) (𝓝[>] (0:ℝ)) atTop := by
  have h := tendsto_hairpinArclength_atTop' (f := fun u => f (π - u)) (m := m)
    (reflect_continuousOn hf) (reflect_lower hm) hm0
  simpa [Hairpin.hairpinArclength_reflect] using h

/-- **The end `θ → π⁻` also runs off to horizontal infinity**, on the same
side. -/
theorem tendsto_hairpinX_pi_atBot' (hf : ContinuousOn f (Ioo 0 π))
    (hm : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hm0 : 0 < m) :
    Tendsto (fun θ => hairpinX f (π - θ)) (𝓝[>] (0:ℝ)) atBot := by
  have h := tendsto_hairpinX_atBot' (f := fun u => f (π - u)) (m := m)
    (reflect_continuousOn hf) (reflect_lower hm) hm0
  rwa [show (hairpinX fun u => f (π - u)) = fun θ => hairpinX f (π - θ) from
    funext fun θ => Hairpin.hairpinX_reflect θ] at h

/-! ### The hairpin, assembled -/

/-- **A profile continuous on the open interval defines a hairpin.**  If
`f` is continuous on `(0, π)` with `0 < m ≤ f ≤ M` there, then the curve
`C = X + iZ` given by `X' = f cot θ`, `Z' = f`:

1. is regular, with velocity `(f/sin θ)e^{iθ}` — its tangent angle is the
   parameter, so the tangent turns through `π`;
2. is embedded (injective on `(0, π)`);
3. is strictly convex: its curvature `sin θ / f` is positive;
4. has bounded vertical coordinate `|Z| ≤ M π` while `X → -∞` at both ends,
   so the ends are asymptotic to parallel horizontal lines and the curve opens
   in one direction;
5. is complete: the arclength diverges at both ends.
-/
theorem isHairpin_of_continuousOn (hf : ContinuousOn f (Ioo 0 π))
    (hm0 : 0 < m) (hm : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hM : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ M) :
    (∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt (hairpinCurve f)
        ((f θ / Real.sin θ : ℝ) * Complex.exp (Complex.I * (θ : ℂ))) θ ∧
        0 < f θ / Real.sin θ) ∧
      InjOn (hairpinCurve f) (Ioo 0 π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, 0 < Real.sin θ / f θ) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, |hairpinZ f θ| ≤ M * π) ∧
      Tendsto (hairpinX f) (𝓝[>] (0:ℝ)) atBot ∧
      Tendsto (fun θ => hairpinX f (π - θ)) (𝓝[>] (0:ℝ)) atBot ∧
      Tendsto (fun θ => hairpinArclength f θ 1) (𝓝[>] (0:ℝ)) atTop ∧
      Tendsto (fun θ => hairpinArclength f (π - 1) (π - θ)) (𝓝[>] (0:ℝ)) atTop := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht => lt_of_lt_of_le hm0 (hm t ht)
  have habs : ∀ t ∈ Ioo (0:ℝ) π, |f t| ≤ M := by
    intro t ht
    rw [abs_of_pos (hfpos t ht)]
    exact hM t ht
  refine ⟨fun θ hθ => ⟨hasDerivAt_hairpinCurve' hf hθ,
      div_pos (hfpos θ hθ) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)⟩,
    injOn_hairpinCurve' hf hfpos,
    fun θ hθ => div_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) (hfpos θ hθ),
    fun θ hθ => abs_hairpinZ_le' habs hθ,
    tendsto_hairpinX_atBot' hf hm hm0,
    tendsto_hairpinX_pi_atBot' hf hm hm0,
    tendsto_hairpinArclength_atTop' hf hm hm0,
    tendsto_hairpinArclength_pi_atTop' hf hm hm0⟩

/-- **The limit profile of the iteration defines a hairpin.**  This joins the
two halves of Section 3: the monotone iteration of the translator operator
`𝒫`, trapped between the barriers `1 < m ≤ f_n ≤ M`, has a pointwise limit `F`
which — being a bounded fixed point — is continuous on `(0, π)`, and therefore
the profile equations `X' = F cot θ`, `Z' = F` define a complete embedded
strictly convex hairpin. -/
theorem limit_profile_isHairpin {fseq : ℕ → ℝ → ℝ} {F : ℝ → ℝ} (hm : 1 < m)
    (hlow : ∀ n θ, m ≤ fseq n θ) (hup : ∀ n θ, fseq n θ ≤ M)
    (hpt : ∀ θ, Tendsto (fun n => fseq n θ) atTop (𝓝 (F θ)))
    (hint : ∀ a b : ℝ, IntervalIntegrable F volume a b)
    {U : ℝ → ℝ} (hlt : ∀ θ ∈ Ioo 0 π, θ < U θ)
    (hU : ∀ θ ∈ Ioo 0 π, (∫ t in θ..U θ, F t) = Real.sin θ)
    (hfix : ∀ θ ∈ Ioo 0 π, F θ = Real.sin θ * (Real.cos (U θ - θ) / Real.sin (U θ - θ))) :
    (∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt (hairpinCurve F)
        ((F θ / Real.sin θ : ℝ) * Complex.exp (Complex.I * (θ : ℂ))) θ ∧
        0 < F θ / Real.sin θ) ∧
      InjOn (hairpinCurve F) (Ioo 0 π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, 0 < Real.sin θ / F θ) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, |hairpinZ F θ| ≤ M * π) ∧
      Tendsto (hairpinX F) (𝓝[>] (0:ℝ)) atBot ∧
      Tendsto (fun θ => hairpinX F (π - θ)) (𝓝[>] (0:ℝ)) atBot ∧
      Tendsto (fun θ => hairpinArclength F θ 1) (𝓝[>] (0:ℝ)) atTop ∧
      Tendsto (fun θ => hairpinArclength F (π - 1) (π - θ)) (𝓝[>] (0:ℝ)) atTop := by
  have hcont : ContinuousOn F (Ioo 0 π) :=
    LimitProfile.limit_profile_continuousOn hm hlow hup hpt hint hlt hU hfix
  have hbounds : ∀ θ, F θ ∈ Icc m M := fun θ =>
    LimitProfile.mem_Icc_of_tendsto (hpt θ) (fun n => hlow n θ) (fun n => hup n θ)
  exact isHairpin_of_continuousOn hcont (lt_trans zero_lt_one hm)
    (fun t _ => (hbounds t).1) (fun t _ => (hbounds t).2)

/-! ### The two ends are asymptotic to horizontal lines -/

/-- **The vertical coordinate has finite one-sided limits at the two ends.**
For an interval-integrable profile the primitive `Z(θ) = ∫_{π/2}^θ f` is
continuous on the whole line, so `Z(θ)` converges as `θ → 0⁺` and as
`θ → π⁻`.  Together with `X → -∞` at both ends this is the statement that the
two ends of the hairpin are asymptotic to parallel horizontal lines. -/
theorem tendsto_hairpinZ_ends (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    Tendsto (hairpinZ f) (𝓝[>] (0:ℝ)) (𝓝 (hairpinZ f 0)) ∧
      Tendsto (hairpinZ f) (𝓝[<] π) (𝓝 (hairpinZ f π)) := by
  have hc : Continuous (hairpinZ f) := intervalIntegral.continuous_primitive hint (π/2)
  exact ⟨(hc.tendsto _).mono_left nhdsWithin_le_nhds,
    (hc.tendsto _).mono_left nhdsWithin_le_nhds⟩

end HairpinOn
