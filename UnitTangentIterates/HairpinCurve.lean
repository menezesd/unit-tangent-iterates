module

public import UnitTangentIterates.HairpinExistence

/-!
# The translating hairpin (Theorem 3.4)

* A fixed point of `𝒫` is `C^∞` on `(0, π)` (bootstrap through the local inverse of the
  primitive `Z`).
* The hairpin `C = X + iZ` built from the profile is embedded, strictly convex (curvature
  `sin θ / f θ`), lies in a horizontal strip, both of its ends go to `X → -∞`, and
  `𝒯 C = C + (V, 0)` with `V > 0`.
-/

@[expose] public section

namespace Ovals

open Real Set MeasureTheory Filter Topology
open scoped ContDiff

variable {f : ℝ → ℝ} {m M : ℝ}

theorem contDiffOn_hairpinZ (hfc : ContinuousOn f (Ioo 0 π)) {n : ℕ}
    (hf : ContDiffOn ℝ n f (Ioo 0 π)) : ContDiffOn ℝ (n + 1) (hairpinZ f) (Ioo 0 π) := by
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun x hx => (hasDerivAt_hairpinZ hfc hx).differentiableAt.differentiableWithinAt,
    fun h => by exact absurd h (by simp), ?_⟩
  exact hf.congr fun x hx => (hasDerivAt_hairpinZ hfc hx).deriv

theorem contDiffAt_cot {x : ℝ} {n : WithTop ℕ∞} (hx : Real.sin x ≠ 0) :
    ContDiffAt ℝ n Real.cot x := by
  have : Real.cot = fun x => Real.cos x / Real.sin x := funext Real.cot_eq_cos_div_sin
  rw [this]
  exact Real.contDiff_cos.contDiffAt.div Real.contDiff_sin.contDiffAt hx

/-- Bootstrap step: a fixed point of `𝒫` which is `Cⁿ` on `(0, π)` is `C^{n+1}`. -/
theorem contDiffOn_succ_of_fixed (hf : AdmissibleProfile f m M)
    (hfix : ∀ θ ∈ Ioo 0 π, profP f θ = f θ) {n : ℕ}
    (hn : ContDiffOn ℝ n f (Ioo 0 π)) : ContDiffOn ℝ (n + 1) f (Ioo 0 π) := by
  have hfc : ContinuousOn f (Ioo 0 π) :=
    (continuousOn_profP hf).congr fun θ hθ => (hfix θ hθ).symm
  have hZ := contDiffOn_hairpinZ hfc hn
  intro θ₀ hθ₀
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨hD0, -, hDint⟩ := profD_spec hf hθ₀
  have hDlt := profD_lt hf hθ₀
  set x₀ := θ₀ + profD f θ₀ with hx₀
  have hx₀mem : x₀ ∈ Ioo 0 π := ⟨by linarith [hθ₀.1], by linarith [hDlt.1]⟩
  have hZx : ContDiffAt ℝ (n + 1) (hairpinZ f) x₀ := hZ.contDiffAt (isOpen_Ioo.mem_nhds hx₀mem)
  have hZθ : ContDiffAt ℝ (n + 1) (hairpinZ f) θ₀ := hZ.contDiffAt (isOpen_Ioo.mem_nhds hθ₀)
  have hf0 : f x₀ ≠ 0 := by linarith [hf.lower x₀ hx₀mem, hf.one_lt]
  have hZd := (hasDerivAt_hairpinZ hfc hx₀mem).hasFDerivAt_equiv hf0
  have hn0 : (n + 1 : WithTop ℕ∞) ≠ 0 := by simp
  have hψ := hZx.to_localInverse hZd hn0
  have hleft := (hZx.hasStrictFDerivAt' hZd hn0).eventually_left_inverse
  set ψ := hZx.localInverse hZd hn0 with hψdef
  -- the key value identity Z θ₀ + sin θ₀ = Z x₀
  have hval : ∀ θ ∈ Ioo 0 π, hairpinZ f θ + Real.sin θ = hairpinZ f (θ + profD f θ) := by
    intro θ hθ
    obtain ⟨-, -, hI⟩ := profD_spec hf hθ
    have hl := (profD_lt hf hθ).1
    have := integral_eq_hairpinZ_sub hfc (b := θ + profD f θ) hθ
      ⟨by linarith [hθ.1, (profD_spec hf hθ).1], by linarith⟩
    linarith
  -- continuity of θ ↦ θ + D θ at θ₀
  have hcont : ContinuousAt (fun θ => θ + profD f θ) θ₀ :=
    continuousAt_id.add ((continuousOn_profD hf).continuousAt (isOpen_Ioo.mem_nhds hθ₀))
  have hev : ∀ᶠ θ in 𝓝 θ₀, profD f θ = ψ (hairpinZ f θ + Real.sin θ) - θ := by
    have h1 : ∀ᶠ θ in 𝓝 θ₀, ψ (hairpinZ f (θ + profD f θ)) = θ + profD f θ :=
      hcont.eventually hleft
    filter_upwards [h1, isOpen_Ioo.mem_nhds hθ₀] with θ h1 hθ
    rw [hval θ hθ, h1]; ring
  have hDsmooth : ContDiffAt ℝ (n + 1) (profD f) θ₀ := by
    have hcomp : ContDiffAt ℝ (n + 1) (fun θ => ψ (hairpinZ f θ + Real.sin θ) - θ) θ₀ := by
      have h2 : ContDiffAt ℝ (n + 1) (fun θ => hairpinZ f θ + Real.sin θ) θ₀ :=
        hZθ.add Real.contDiff_sin.contDiffAt
      have h3 : ContDiffAt ℝ (n + 1) ψ (hairpinZ f θ₀ + Real.sin θ₀) := by
        rw [hval θ₀ hθ₀]; exact hψ
      exact (h3.comp θ₀ h2).sub contDiffAt_id
    exact hcomp.congr_of_eventuallyEq hev
  have hPsmooth : ContDiffAt ℝ (n + 1) (profP f) θ₀ := by
    unfold profP
    have hsin : Real.sin (profD f θ₀) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi hD0 (by linarith [hDlt.2, Real.pi_pos])).ne'
    exact Real.contDiff_sin.contDiffAt.mul ((contDiffAt_cot hsin).comp θ₀ hDsmooth)
  refine hPsmooth.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hθ₀] with θ hθ
  exact (hfix θ hθ).symm

/-- A fixed point of `𝒫` is `C^∞` on `(0, π)`. -/
theorem contDiffOn_of_fixed (hf : AdmissibleProfile f m M)
    (hfix : ∀ θ ∈ Ioo 0 π, profP f θ = f θ) : ContDiffOn ℝ ∞ f (Ioo 0 π) := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero =>
    simp only [Nat.cast_zero, contDiffOn_zero]
    exact (continuousOn_profP hf).congr fun θ hθ => (hfix θ hθ).symm
  | succ n ih =>
    exact_mod_cast contDiffOn_succ_of_fixed hf hfix ih


theorem curvature_hairpin (hfd : DifferentiableOn ℝ f (Ioo 0 π))
    (hpos : ∀ θ ∈ Ioo 0 π, 0 < f θ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    curvature (hairpin f) θ = Real.sin θ / f θ := by
  have hfc := hfd.continuousOn
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  set ρ : ℝ → ℝ := fun x => f x / Real.sin x with hρ
  have hρpos : 0 < ρ θ := div_pos (hpos θ hθ) hs
  have hev : deriv (hairpin f) =ᶠ[𝓝 θ] fun x => ((ρ x : ℝ) : ℂ) * tau x := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact (hasDerivAt_hairpin hfc hx).deriv
  have hρd : DifferentiableAt ℝ ρ θ :=
    (hfd.differentiableAt (isOpen_Ioo.mem_nhds hθ)).div (Real.differentiable_sin θ) hs.ne'
  have hd2 : HasDerivAt (fun x => ((ρ x : ℝ) : ℂ) * tau x)
      (((deriv ρ θ : ℝ) : ℂ) * tau θ + ((ρ θ : ℝ) : ℂ) * ((1 : ℝ) * Complex.I * tau θ)) θ := by
    have h1 := hρd.hasDerivAt.ofReal_comp
    have h2 := hasDerivAt_tau_comp (hasDerivAt_id θ)
    exact h1.mul h2
  unfold curvature
  rw [hev.deriv_eq, hd2.deriv, (hasDerivAt_hairpin hfc hθ).deriv]
  have hc := conj_tau_mul_tau θ
  have ht := norm_tau θ
  generalize tau θ = t at hc ht ⊢
  generalize deriv ρ θ = r'
  have hρθ : ρ θ = f θ / Real.sin θ := rfl
  rw [← hρθ]
  generalize hr : ρ θ = r at hρpos ⊢
  have key : (starRingEnd ℂ) ((r : ℂ) * t) * ((r' : ℂ) * t + (r : ℂ) * ((1 : ℝ) * Complex.I * t))
      = ((r * r' : ℝ) : ℂ) + ((r ^ 2 : ℝ) : ℂ) * Complex.I := by
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination ((r : ℂ) * r' + (r : ℂ) ^ 2 * Complex.I) * hc
  rw [key, norm_mul, ht, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  rw [← hr, hρθ]
  have := hpos θ hθ
  field_simp

theorem unitTangentTransform_hairpin_apply (hfc : ContinuousOn f (Ioo 0 π))
    (hpos : ∀ θ ∈ Ioo 0 π, 0 < f θ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    unitTangentTransform (hairpin f) θ = hairpin f θ + tau θ := by
  unfold unitTangentTransform
  rw [(hasDerivAt_hairpin hfc hθ).deriv]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hp : 0 < f θ / Real.sin θ := div_pos (hpos θ hθ) hs
  rw [norm_mul, norm_tau, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  have : ((f θ / Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

theorem hairpinZ_strictMonoOn (hfc : ContinuousOn f (Ioo 0 π))
    (hpos : ∀ θ ∈ Ioo 0 π, 0 < f θ) : StrictMonoOn (hairpinZ f) (Ioo 0 π) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 π)
  · exact fun x hx => (hasDerivAt_hairpinZ hfc hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_hairpinZ hfc hx).deriv]; exact hpos x hx

theorem hairpin_injOn (hfc : ContinuousOn f (Ioo 0 π))
    (hpos : ∀ θ ∈ Ioo 0 π, 0 < f θ) : InjOn (hairpin f) (Ioo 0 π) := by
  intro a ha b hb hab
  have := congrArg Complex.im hab
  simp [hairpin] at this
  exact (hairpinZ_strictMonoOn hfc hpos).injOn ha hb this

theorem hairpin_im_bound (hf : AdmissibleProfile f m M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    |(hairpin f θ).im| ≤ M * π := by
  simp only [hairpin, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
    zero_add]
  have hpi := Real.pi_pos
  obtain ⟨-, h⟩ := abs_integral_bounds hf (a := π / 2) (b := θ) ⟨by linarith, by linarith⟩
    ⟨hθ.1.le, hθ.2.le⟩
  have hM : 0 ≤ M := by linarith [hf.lower θ hθ, hf.upper θ hθ, hf.one_lt]
  have : |θ - π / 2| ≤ π := by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  unfold hairpinZ
  calc |∫ t in (π / 2)..θ, f t| ≤ M * |θ - π / 2| := h
    _ ≤ M * π := mul_le_mul_of_nonneg_left this hM

theorem hairpin_translation_pos (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfd : DifferentiableOn ℝ f (Ioo 0 π)) (hT : TranslatorEq f) :
    ∃ V : ℝ, 0 < V ∧ ∀ θ ∈ Ioo 0 π, hairpin f θ + tau θ = hairpin f (hairpinG f θ) + V := by
  obtain ⟨V, hV⟩ := hairpin_translation hm hf hfd hT
  refine ⟨V, ?_, hV⟩
  have hpi := Real.pi_pos
  have hθ : π / 2 ∈ Ioo 0 π := ⟨by linarith, by linarith⟩
  have h := congrArg Complex.re (hV (π / 2) hθ)
  simp [hairpin, tau_eq, -Complex.ofReal_cos, hairpinX] at h
  have hg := hairpinG_mem hm hf hθ
  have hneg : ∫ t in (π / 2)..hairpinG f (π / 2), f t * Real.cot t < 0 := by
    have hfc := hfd.continuousOn
    have hint : IntervalIntegrable (fun t => -(f t * Real.cot t)) MeasureTheory.volume (π / 2)
        (hairpinG f (π / 2)) :=
      (intervalIntegrable_of_Ioo (hfc.mul continuousOn_cot_Ioo) hθ
        ⟨by linarith [hg.1], hg.2⟩).neg
    have := intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun t ht => by
      have ht' : t ∈ Ioo 0 π := ⟨by linarith [ht.1], by linarith [ht.2, hg.2]⟩
      have hft : 0 < f t := by linarith [hf t ht']
      have hcot : Real.cot t < 0 := by
        rw [Real.cot_eq_cos_div_sin]
        exact div_neg_of_neg_of_pos (Real.cos_neg_of_pi_div_two_lt_of_lt ht.1 (by linarith [ht'.2]))
          (Real.sin_pos_of_pos_of_lt_pi ht'.1 ht'.2)
      nlinarith) hg.1
    rw [intervalIntegral.integral_neg] at this
    linarith
  linarith


theorem integral_cot_eq {a b : ℝ} (ha : a ∈ Ioo 0 π) (hb : b ∈ Ioo 0 π) :
    ∫ t in a..b, Real.cot t = Real.log (Real.sin b) - Real.log (Real.sin a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hx' : x ∈ Ioo 0 π := by
      rw [Set.mem_uIcc] at hx
      constructor <;> rcases hx with h | h <;> linarith [ha.1, ha.2, hb.1, hb.2, h.1, h.2]
    have := (Real.hasDerivAt_sin x).log (Real.sin_pos_of_pos_of_lt_pi hx'.1 hx'.2).ne'
    rwa [← Real.cot_eq_cos_div_sin] at this
  · exact intervalIntegrable_of_Ioo continuousOn_cot_Ioo ha hb

theorem hairpinX_le_log (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfc : ContinuousOn f (Ioo 0 π)) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    hairpinX f θ ≤ m * Real.log (Real.sin θ) := by
  have hpi := Real.pi_pos
  have hpi2 : π / 2 ∈ Ioo 0 π := ⟨by linarith, by linarith⟩
  have hlog := integral_cot_eq hpi2 hθ
  rw [Real.sin_pi_div_two, Real.log_one, sub_zero] at hlog
  have hint1 := intervalIntegrable_of_Ioo (h := fun t => f t * Real.cot t)
    (hfc.mul continuousOn_cot_Ioo) hpi2 hθ
  have hint2 := intervalIntegrable_of_Ioo continuousOn_cot_Ioo hpi2 hθ
  unfold hairpinX
  rcases le_total (π / 2) θ with h | h
  · have := intervalIntegral.integral_mono_on h hint1 (hint2.const_mul m) (fun t ht => by
      have ht' : t ∈ Ioo 0 π := ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hθ.2⟩
      have hcot : Real.cot t ≤ 0 := by
        rw [Real.cot_eq_cos_div_sin]
        exact div_nonpos_of_nonpos_of_nonneg
          (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1 (by linarith [ht'.2]))
          (Real.sin_pos_of_pos_of_lt_pi ht'.1 ht'.2).le
      nlinarith [hf t ht'])
    rw [intervalIntegral.integral_const_mul, hlog] at this
    exact this
  · rw [intervalIntegral.integral_symm] at hlog ⊢
    have := intervalIntegral.integral_mono_on h (hint2.symm.const_mul m) hint1.symm (fun t ht => by
      have ht' : t ∈ Ioo 0 π := ⟨lt_of_lt_of_le hθ.1 ht.1, by linarith [ht.2]⟩
      have hcot : 0 ≤ Real.cot t := by
        rw [Real.cot_eq_cos_div_sin]
        exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht'.1], ht.2⟩)
          (Real.sin_pos_of_pos_of_lt_pi ht'.1 ht'.2).le
      nlinarith [hf t ht'])
    rw [intervalIntegral.integral_const_mul] at this
    rw [← hlog]
    linarith

theorem tendsto_log_sin_left : Tendsto (fun θ => Real.log (Real.sin θ)) (𝓝[>] 0) atBot := by
  have h1 : Tendsto Real.sin (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (Real.continuous_sin.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with x hx
      exact Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  exact Real.tendsto_log_nhdsGT_zero.comp h1

theorem tendsto_log_sin_right : Tendsto (fun θ => Real.log (Real.sin θ)) (𝓝[<] π) atBot := by
  have h1 : Tendsto Real.sin (𝓝[<] π) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (Real.continuous_sin.tendsto π).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with x hx
      exact Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  exact Real.tendsto_log_nhdsGT_zero.comp h1

/-- Both ends of the hairpin go off to `X → -∞`. -/
theorem tendsto_hairpinX (hm : 0 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfc : ContinuousOn f (Ioo 0 π)) :
    Tendsto (hairpinX f) (𝓝[>] 0) atBot ∧ Tendsto (hairpinX f) (𝓝[<] π) atBot := by
  constructor
  · refine tendsto_atBot_mono' _ ?_ (tendsto_log_sin_left.const_mul_atBot hm)
    filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with x hx
    exact hairpinX_le_log hf hfc hx
  · refine tendsto_atBot_mono' _ ?_ (tendsto_log_sin_right.const_mul_atBot hm)
    filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with x hx
    exact hairpinX_le_log hf hfc hx


/-- **Theorem 3.4.** For every `0 < ε ≤ 1/10` the translator equation (3.3) has a solution
`f ∈ C^∞(0, π)` with `f_ε^- ≤ f ≤ f_ε^+`.  The corresponding hairpin `C` is embedded,
strictly convex, contained in a horizontal strip, both ends go to `X → -∞` (complete, asymptotic
to horizontal lines), and `𝒯 C = C + (V, 0)` with `V > 0`. -/
theorem hairpin_exists {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) :
    ∃ f : ℝ → ℝ, ContDiffOn ℝ ∞ f (Ioo 0 π) ∧
      (∀ θ ∈ Ioo 0 π, fMinus ε θ ≤ f θ ∧ f θ ≤ fPlus ε θ) ∧ TranslatorEq f ∧
      InjOn (hairpin f) (Ioo 0 π) ∧ (∀ θ ∈ Ioo 0 π, 0 < curvature (hairpin f) θ) ∧
      (∃ W : ℝ, ∀ θ ∈ Ioo 0 π, |(hairpin f θ).im| ≤ W) ∧
      Tendsto (hairpinX f) (𝓝[>] 0) atBot ∧ Tendsto (hairpinX f) (𝓝[<] π) atBot ∧
      ∃ V : ℝ, 0 < V ∧ ∀ θ ∈ Ioo 0 π,
        unitTangentTransform (hairpin f) θ = hairpin f (hairpinG f θ) + V := by
  have hadm := admissible_hairpinProfile hε0 hε
  have hfix : ∀ θ ∈ Ioo 0 π, profP (hairpinProfile ε) θ = hairpinProfile ε θ :=
    fun _ hθ => profP_hairpinProfile hε0 hε hθ
  have hsmooth := contDiffOn_of_fixed hadm hfix
  have hfd : DifferentiableOn ℝ (hairpinProfile ε) (Ioo 0 π) :=
    hsmooth.differentiableOn (by simp)
  have hfc := hfd.continuousOn
  have hm := hadm.one_lt
  have hpos : ∀ θ ∈ Ioo 0 π, 0 < hairpinProfile ε θ := fun θ hθ => by
    linarith [hadm.lower θ hθ]
  have hT := translatorEq_hairpinProfile hε0 hε
  obtain ⟨V, hV0, hV⟩ := hairpin_translation_pos hm hadm.lower hfd hT
  refine ⟨hairpinProfile ε, hsmooth, fun θ hθ => hairpinProfile_bounds hε0 hε hθ, hT,
    hairpin_injOn hfc hpos, fun θ hθ => ?_, ⟨_, fun θ hθ => hairpin_im_bound hadm hθ⟩,
    (tendsto_hairpinX (by linarith) hadm.lower hfc).1,
    (tendsto_hairpinX (by linarith) hadm.lower hfc).2, V, hV0,
    fun θ hθ => ?_⟩
  · rw [curvature_hairpin hfd hpos hθ]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) (hpos θ hθ)
  · rw [unitTangentTransform_hairpin_apply hfc hpos hθ, hV θ hθ]

end Ovals

end
