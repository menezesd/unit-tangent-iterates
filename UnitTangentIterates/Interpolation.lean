module

public import UnitTangentIterates.CurveFromCurvature

/-!
# Lemma 6.1: interpolating between two centrally symmetric ovals

Let `κ₀, κ₁` be continuous `L`-periodic curvature functions with `∫₀ᴸ κᵢ = π` and
`0 ≤ κᵢ ≤ κ_*`.  For `t ∈ [0, 1]` put `κ_t = (1 - t) κ₀ + t κ₁` and let `X_t` be the centered
curve of curvature `κ_t` with the common initial tangent angle `θ₀` (equation (6.2)).  Then
`θ_t = θ₀ + ∫₀ˢ κ₀ + t φ(s)` with `φ(s) = ∫₀ˢ (κ₁ - κ₀)`, and

* the velocity `∂ₜ X_t(s) = ∫₀ˢ i φ τ(θ_t) - ½ ∫₀ᴸ i φ τ(θ_t)` exists;
* its normal component `η = ⟨∂ₜ X_t, ν⟩`, `ν = i τ(θ_t)`, satisfies `η_s = φ - κ_t ξ`, where
  `ξ = ⟨∂ₜ X_t, τ(θ_t)⟩` (this is the identity `θ̇_t = η_s + κ_t ξ` of the paper);
* with `ε = ‖κ₁ - κ₀‖_{L¹(0,L)}`, for every `s`,
  `|η| ≤ (3/2) L ε` and `|η_s| ≤ (1 + (3/2) κ_* L) ε`.

Integrating over `t ∈ [0, 1]` and over the full perimeter `2L` gives the bound
`W + S₀ + S₁ ≤ C (1 + L)² ε` of Lemma 6.1.
-/

@[expose] public section

namespace Ovals

open Complex Real intervalIntegral MeasureTheory

/-- The interpolated curvature `κ_t = (1 - t) κ₀ + t κ₁`. -/
noncomputable def interpCurv (κ₀ κ₁ : ℝ → ℝ) (t r : ℝ) : ℝ := (1 - t) * κ₀ r + t * κ₁ r

/-- `φ(r) = ∫₀ʳ (κ₁ - κ₀)`, the `t`-derivative of the interpolated tangent angle. -/
noncomputable def angleVar (κ₀ κ₁ : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u in (0 : ℝ)..r, (κ₁ u - κ₀ u)

/-- The interpolating path of curves `X_t`. -/
noncomputable def interpCurve (θ₀ : ℝ) (κ₀ κ₁ : ℝ → ℝ) (L t : ℝ) : ℝ → ℂ :=
  curveOfCurvature θ₀ (interpCurv κ₀ κ₁ t) L

/-- The velocity `∂ₜ X_t(s)` of the interpolating path. -/
noncomputable def interpVelocity (θ₀ : ℝ) (κ₀ κ₁ : ℝ → ℝ) (L t s : ℝ) : ℂ :=
  (∫ r in (0 : ℝ)..s, (angleVar κ₀ κ₁ r : ℂ) * I *
      tau (angleOfCurvature θ₀ (interpCurv κ₀ κ₁ t) r)) -
    (1 / 2 : ℂ) * ∫ r in (0 : ℝ)..L, (angleVar κ₀ κ₁ r : ℂ) * I *
      tau (angleOfCurvature θ₀ (interpCurv κ₀ κ₁ t) r)

/-- The normal velocity `η = ⟨∂ₜ X_t, ν⟩` with inward normal `ν = i τ(θ_t)`. -/
noncomputable def interpNormal (θ₀ : ℝ) (κ₀ κ₁ : ℝ → ℝ) (L t s : ℝ) : ℝ :=
  (interpVelocity θ₀ κ₀ κ₁ L t s *
    (starRingEnd ℂ) (I * tau (angleOfCurvature θ₀ (interpCurv κ₀ κ₁ t) s))).re

/-- The tangential velocity `ξ = ⟨∂ₜ X_t, τ⟩`. -/
noncomputable def interpTangential (θ₀ : ℝ) (κ₀ κ₁ : ℝ → ℝ) (L t s : ℝ) : ℝ :=
  (interpVelocity θ₀ κ₀ κ₁ L t s *
    (starRingEnd ℂ) (tau (angleOfCurvature θ₀ (interpCurv κ₀ κ₁ t) s))).re

variable {θ₀ L : ℝ} {κ₀ κ₁ : ℝ → ℝ}

theorem continuous_interpCurv (h₀ : Continuous κ₀) (h₁ : Continuous κ₁) (t : ℝ) :
    Continuous (interpCurv κ₀ κ₁ t) := by
  unfold interpCurv; fun_prop

theorem continuous_angleVar (h₀ : Continuous κ₀) (h₁ : Continuous κ₁) :
    Continuous (angleVar κ₀ κ₁) :=
  continuous_iff_continuousAt.2 fun _ =>
    (intervalIntegral.integral_hasDerivAt_right ((h₁.sub h₀).intervalIntegrable _ _)
      ((h₁.sub h₀).stronglyMeasurableAtFilter _ _) (h₁.sub h₀).continuousAt).continuousAt

/-- Differentiation under the integral sign for `∫₀ᵇ τ(A + t φ)`. -/
lemma hasDerivAt_param_tau {A φ : ℝ → ℝ} (hA : Continuous A) (hφ : Continuous φ) (b t : ℝ) :
    HasDerivAt (fun t => ∫ r in (0 : ℝ)..b, tau (A r + t * φ r))
      (∫ r in (0 : ℝ)..b, (φ r : ℂ) * I * tau (A r + t * φ r)) t := by
  have hcF : ∀ x : ℝ, Continuous (fun r => tau (A r + x * φ r)) := fun x =>
    continuous_tau.comp (hA.add (continuous_const.mul hφ))
  have hcF' : ∀ x : ℝ, Continuous (fun r => (φ r : ℂ) * I * tau (A r + x * φ r)) := fun x =>
    ((Complex.continuous_ofReal.comp hφ).mul continuous_const).mul (hcF x)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x r => tau (A r + x * φ r)) (F' := fun x r => (φ r : ℂ) * I * tau (A r + x * φ r))
    (x₀ := t) (bound := fun r => |φ r|) Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (hcF x).aestronglyMeasurable)
    ((hcF t).intervalIntegrable _ _) (hcF' t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r _ x _ => ?_) (hφ.abs.intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun r _ x _ => ?_)).2
  · simp [norm_tau]
  · have h := hasDerivAt_tau_comp (((hasDerivAt_id x).mul_const (φ r)).const_add (A r))
    simpa using h

/-- The interpolated angle is affine in `t`. -/
theorem angle_interp (h₀ : Continuous κ₀) (h₁ : Continuous κ₁) (t r : ℝ) :
    angleOfCurvature θ₀ (interpCurv κ₀ κ₁ t) r =
      angleOfCurvature θ₀ κ₀ r + t * angleVar κ₀ κ₁ r := by
  unfold angleOfCurvature interpCurv angleVar
  have e : (fun u => (1 - t) * κ₀ u + t * κ₁ u) = fun u => κ₀ u + t * (κ₁ u - κ₀ u) := by
    ext u; ring
  have hc : Continuous fun u => t * (κ₁ u - κ₀ u) := by fun_prop
  rw [e, intervalIntegral.integral_add (f := κ₀) (g := fun u => t * (κ₁ u - κ₀ u))
    (h₀.intervalIntegrable _ _) (hc.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  ring

/-- **The velocity of the interpolating path.** -/
theorem hasDerivAt_interpCurve (h₀ : Continuous κ₀) (h₁ : Continuous κ₁) (t s : ℝ) :
    HasDerivAt (fun t => interpCurve θ₀ κ₀ κ₁ L t s) (interpVelocity θ₀ κ₀ κ₁ L t s) t := by
  have hA : Continuous (angleOfCurvature θ₀ κ₀) := continuous_angleOfCurvature h₀
  have hφ := continuous_angleVar (κ₀ := κ₀) (κ₁ := κ₁) h₀ h₁
  have e : (fun t => interpCurve θ₀ κ₀ κ₁ L t s) = fun t =>
      (∫ r in (0 : ℝ)..s, tau (angleOfCurvature θ₀ κ₀ r + t * angleVar κ₀ κ₁ r)) -
        (1 / 2 : ℂ) * ∫ r in (0 : ℝ)..L, tau (angleOfCurvature θ₀ κ₀ r + t * angleVar κ₀ κ₁ r) := by
    funext t; simp only [interpCurve, curveOfCurvature, angle_interp h₀ h₁]
  have eV : interpVelocity θ₀ κ₀ κ₁ L t s =
      (∫ r in (0 : ℝ)..s, (angleVar κ₀ κ₁ r : ℂ) * I *
        tau (angleOfCurvature θ₀ κ₀ r + t * angleVar κ₀ κ₁ r)) -
      (1 / 2 : ℂ) * ∫ r in (0 : ℝ)..L, (angleVar κ₀ κ₁ r : ℂ) * I *
        tau (angleOfCurvature θ₀ κ₀ r + t * angleVar κ₀ κ₁ r) := by
    simp only [interpVelocity, angle_interp h₀ h₁]
  rw [e, eV]
  exact (hasDerivAt_param_tau hA hφ s t).sub ((hasDerivAt_param_tau hA hφ L t).const_mul _)

/-- `|φ| ≤ ε` on `[0, L]`. -/
theorem abs_angleVar_le (h₀ : Continuous κ₀) (h₁ : Continuous κ₁) {r : ℝ}
    (hr0 : 0 ≤ r) (hrL : r ≤ L) :
    |angleVar κ₀ κ₁ r| ≤ ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u| := by
  unfold angleVar
  refine (intervalIntegral.abs_integral_le_integral_abs hr0).trans ?_
  exact intervalIntegral.integral_mono_interval le_rfl hr0 hrL
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) ((h₁.sub h₀).abs.intervalIntegrable _ _)

/-- `‖∂ₜ X_t(s)‖ ≤ (3/2) L ε` on `[0, L]`. -/
theorem norm_interpVelocity_le (h₀ : Continuous κ₀) (h₁ : Continuous κ₁) (hL : 0 ≤ L)
    (t : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hsL : s ≤ L) :
    ‖interpVelocity θ₀ κ₀ κ₁ L t s‖ ≤ 3 / 2 * L * ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u| := by
  set ε := ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u| with hε
  have hε0 : 0 ≤ ε := intervalIntegral.integral_nonneg hL fun _ _ => abs_nonneg _
  set g : ℝ → ℂ := fun r => (angleVar κ₀ κ₁ r : ℂ) * I *
    tau (angleOfCurvature θ₀ (interpCurv κ₀ κ₁ t) r) with hg
  have hgn : ∀ r, ‖g r‖ = |angleVar κ₀ κ₁ r| := fun r => by simp [hg, norm_tau]
  have hb : ∀ b, 0 ≤ b → b ≤ L → ‖∫ r in (0 : ℝ)..b, g r‖ ≤ ε * b := fun b hb0 hbL => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := b) (C := ε)
      (f := g) (fun r hr => by
        rw [Set.uIoc_of_le hb0] at hr
        rw [hgn]; exact abs_angleVar_le h₀ h₁ hr.1.le (hr.2.trans hbL))
    rwa [sub_zero, abs_of_nonneg hb0] at this
  show ‖(∫ r in (0 : ℝ)..s, g r) - (1 / 2 : ℂ) * ∫ r in (0 : ℝ)..L, g r‖ ≤ 3 / 2 * L * ε
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have h1 := hb s hs0 hsL
  have h2 := hb L hL le_rfl
  nlinarith

/-- **The identity `η_s = φ - κ_t ξ`** (equivalently `θ̇_t = η_s + κ_t ξ`). -/
theorem hasDerivAt_interpNormal (h₀ : Continuous κ₀) (h₁ : Continuous κ₁) (t s : ℝ) :
    HasDerivAt (interpNormal θ₀ κ₀ κ₁ L t)
      (angleVar κ₀ κ₁ s - interpCurv κ₀ κ₁ t s * interpTangential θ₀ κ₀ κ₁ L t s) s := by
  set θ := angleOfCurvature θ₀ (interpCurv κ₀ κ₁ t) with hθ
  have hκc := continuous_interpCurv h₀ h₁ t
  have hφ := continuous_angleVar (κ₀ := κ₀) (κ₁ := κ₁) h₀ h₁
  have hθd : ∀ s, HasDerivAt θ (interpCurv κ₀ κ₁ t s) s := fun s =>
    hasDerivAt_angleOfCurvature hκc s
  have hg : Continuous (fun r => (angleVar κ₀ κ₁ r : ℂ) * I * tau (θ r)) :=
    ((Complex.continuous_ofReal.comp hφ).mul continuous_const).mul
      (continuous_tau.comp (continuous_angleOfCurvature hκc))
  have hV : HasDerivAt (interpVelocity θ₀ κ₀ κ₁ L t)
      ((angleVar κ₀ κ₁ s : ℂ) * I * tau (θ s)) s :=
    (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt).sub_const _
  have hN : HasDerivAt (fun s => (starRingEnd ℂ) (I * tau (θ s)))
      ((starRingEnd ℂ) (I * ((interpCurv κ₀ κ₁ t s : ℂ) * I * tau (θ s)))) s :=
    ((hasDerivAt_tau_comp (hθd s)).const_mul I).star
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hV.mul hN)
  convert hR using 1
  simp only [Complex.reCLM_apply, interpTangential]
  rw [← hθ]
  have h := conj_tau_mul_tau (θ s)
  have e : (angleVar κ₀ κ₁ s : ℂ) * I * tau (θ s) * (starRingEnd ℂ) (I * tau (θ s)) +
      interpVelocity θ₀ κ₀ κ₁ L t s *
        (starRingEnd ℂ) (I * ((interpCurv κ₀ κ₁ t s : ℂ) * I * tau (θ s))) =
      (angleVar κ₀ κ₁ s : ℂ) - (interpCurv κ₀ κ₁ t s : ℂ) *
        (interpVelocity θ₀ κ₀ κ₁ L t s * (starRingEnd ℂ) (tau (θ s))) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    linear_combination (angleVar κ₀ κ₁ s : ℂ) * h +
      (-(angleVar κ₀ κ₁ s : ℂ) * tau (θ s) * (starRingEnd ℂ) (tau (θ s)) +
        (interpCurv κ₀ κ₁ t s : ℂ) * interpVelocity θ₀ κ₀ κ₁ L t s *
          (starRingEnd ℂ) (tau (θ s))) * Complex.I_sq
  rw [e, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul]

/-- The normal velocity is `L`-periodic in `s`. -/
theorem interpNormal_periodic (h₀ : Continuous κ₀) (h₁ : Continuous κ₁)
    (hp₀ : Function.Periodic κ₀ L) (hp₁ : Function.Periodic κ₁ L)
    (hi₀ : ∫ r in (0 : ℝ)..L, κ₀ r = π) (hi₁ : ∫ r in (0 : ℝ)..L, κ₁ r = π) (t : ℝ) :
    Function.Periodic (interpNormal θ₀ κ₀ κ₁ L t) L := by
  have hκc := continuous_interpCurv h₀ h₁
  have hκp : ∀ t', Function.Periodic (interpCurv κ₀ κ₁ t') L := fun t' r => by
    simp only [interpCurv, hp₀ r, hp₁ r]
  have hκi : ∀ t', ∫ r in (0 : ℝ)..L, interpCurv κ₀ κ₁ t' r = π := fun t' => by
    unfold interpCurv
    rw [intervalIntegral.integral_add (f := fun r => (1 - t') * κ₀ r) (g := fun r => t' * κ₁ r)
      ((continuous_const.mul h₀).intervalIntegrable _ _)
      ((continuous_const.mul h₁).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hi₀, hi₁]
    ring
  intro s
  -- the velocity is antiperiodic
  have hV : interpVelocity θ₀ κ₀ κ₁ L t (s + L) = -interpVelocity θ₀ κ₀ κ₁ L t s := by
    have h1 := hasDerivAt_interpCurve (θ₀ := θ₀) (L := L) h₀ h₁ t (s + L)
    have e : (fun t' => interpCurve θ₀ κ₀ κ₁ L t' (s + L)) =
        fun t' => -interpCurve θ₀ κ₀ κ₁ L t' s := funext fun t' =>
      curveOfCurvature_add_period (hκc t') (hκp t') (hκi t') s
    rw [e] at h1
    exact h1.unique (hasDerivAt_interpCurve (θ₀ := θ₀) (L := L) h₀ h₁ t s).neg
  have hθ := angleOfCurvature_add_period (θ₀ := θ₀) (hκc t) (hκp t) (hκi t) s
  simp only [interpNormal, hV, hθ, tau_add_pi]
  simp only [mul_neg, map_neg, neg_mul, neg_neg]

/-- **Lemma 6.1 (pointwise bounds).**  For `t ∈ [0, 1]` and every `s`, the normal velocity of
the interpolating path satisfies `|η| ≤ (3/2) L ε` and `|η_s| ≤ (1 + (3/2) κ_* L) ε`, where
`ε = ∫₀ᴸ |κ₁ - κ₀|`. -/
theorem interpolation_bounds (h₀ : Continuous κ₀) (h₁ : Continuous κ₁)
    (hp₀ : Function.Periodic κ₀ L) (hp₁ : Function.Periodic κ₁ L)
    (hi₀ : ∫ r in (0 : ℝ)..L, κ₀ r = π) (hi₁ : ∫ r in (0 : ℝ)..L, κ₁ r = π) (hL : 0 < L)
    {κs : ℝ} (hb₀ : ∀ r, 0 ≤ κ₀ r ∧ κ₀ r ≤ κs) (hb₁ : ∀ r, 0 ≤ κ₁ r ∧ κ₁ r ≤ κs)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : ℝ) :
    |interpNormal θ₀ κ₀ κ₁ L t s| ≤ 3 / 2 * L * ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u| ∧
      |deriv (interpNormal θ₀ κ₀ κ₁ L t) s| ≤
        (1 + 3 / 2 * κs * L) * ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u| := by
  set ε := ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u| with hε
  have hε0 : 0 ≤ ε := intervalIntegral.integral_nonneg hL.le fun _ _ => abs_nonneg _
  have hper := interpNormal_periodic (θ₀ := θ₀) h₀ h₁ hp₀ hp₁ hi₀ hi₁ t
  set k : ℤ := ⌊s / L⌋ with hk
  set r := s - k * L with hr
  have hr0 : 0 ≤ r := by
    have := Int.floor_le (s / L)
    rw [hr, sub_nonneg]
    calc (k : ℝ) * L ≤ s / L * L := mul_le_mul_of_nonneg_right this hL.le
      _ = s := by field_simp
  have hrL : r ≤ L := by
    have := Int.lt_floor_add_one (s / L)
    rw [hr]
    have h2 : s / L * L < ((k : ℝ) + 1) * L := mul_lt_mul_of_pos_right this hL
    rw [div_mul_cancel₀ _ hL.ne'] at h2
    linarith
  have hηs : interpNormal θ₀ κ₀ κ₁ L t s = interpNormal θ₀ κ₀ κ₁ L t r :=
    (hper.sub_int_mul_eq k).symm
  have hds : deriv (interpNormal θ₀ κ₀ κ₁ L t) s = deriv (interpNormal θ₀ κ₀ κ₁ L t) r := by
    have hfun : (fun u => interpNormal θ₀ κ₀ κ₁ L t (u - k * L)) =
        interpNormal θ₀ κ₀ κ₁ L t := funext fun u => hper.sub_int_mul_eq k
    conv_lhs => rw [← hfun]
    rw [deriv_comp_sub_const]
  have hVr := norm_interpVelocity_le (θ₀ := θ₀) h₀ h₁ hL.le t hr0 hrL
  have hunit : ∀ z : ℂ, ‖z‖ = 1 → ∀ w : ℂ, |(w * (starRingEnd ℂ) z).re| ≤ ‖w‖ := fun z hz w => by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_conj, hz, mul_one]
  have hIt : ∀ x : ℝ, ‖I * tau x‖ = 1 := fun x => by rw [norm_mul, Complex.norm_I, norm_tau, one_mul]
  refine ⟨?_, ?_⟩
  · rw [hηs]
    exact (hunit _ (hIt _) _).trans hVr
  · rw [hds, (hasDerivAt_interpNormal (θ₀ := θ₀) (L := L) h₀ h₁ t r).deriv]
    have hφ := abs_angleVar_le h₀ h₁ hr0 hrL
    have hξ : |interpTangential θ₀ κ₀ κ₁ L t r| ≤ 3 / 2 * L * ε :=
      (hunit _ (norm_tau _) _).trans hVr
    have hκ : |interpCurv κ₀ κ₁ t r| ≤ κs := by
      unfold interpCurv
      rw [abs_of_nonneg (by nlinarith [(hb₀ r).1, (hb₁ r).1])]
      nlinarith [(hb₀ r).2, (hb₁ r).2]
    have hκ0 : 0 ≤ κs := le_trans (hb₀ r).1 (hb₀ r).2
    calc |angleVar κ₀ κ₁ r - interpCurv κ₀ κ₁ t r * interpTangential θ₀ κ₀ κ₁ L t r|
        ≤ |angleVar κ₀ κ₁ r| + |interpCurv κ₀ κ₁ t r| * |interpTangential θ₀ κ₀ κ₁ L t r| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ ε + κs * (3 / 2 * L * ε) := by
          gcongr
      _ = (1 + 3 / 2 * κs * L) * ε := by ring

/-- **Lemma 6.1, `L¹` bound.**  Over the full perimeter `2L`,
`∫₀^{2L} |η| ≤ 3 L² ε`.  Together with the pointwise bounds of `interpolation_bounds`
(integrated over `t ∈ [0, 1]`) this gives `W + S₀ + S₁ ≤ (3 + 2κ_*)(1 + L)² ε`. -/
theorem interpolation_L1_bound (h₀ : Continuous κ₀) (h₁ : Continuous κ₁)
    (hp₀ : Function.Periodic κ₀ L) (hp₁ : Function.Periodic κ₁ L)
    (hi₀ : ∫ r in (0 : ℝ)..L, κ₀ r = π) (hi₁ : ∫ r in (0 : ℝ)..L, κ₁ r = π) (hL : 0 < L)
    {κs : ℝ} (hb₀ : ∀ r, 0 ≤ κ₀ r ∧ κ₀ r ≤ κs) (hb₁ : ∀ r, 0 ≤ κ₁ r ∧ κ₁ r ≤ κs)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ s in (0 : ℝ)..(2 * L), |interpNormal θ₀ κ₀ κ₁ L t s| ≤
      3 * L ^ 2 * ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * L)
    (C := 3 / 2 * L * ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u|)
    (f := fun s => |interpNormal θ₀ κ₀ κ₁ L t s|) (fun s _ => by
      rw [Real.norm_eq_abs, abs_abs]
      exact (interpolation_bounds h₀ h₁ hp₀ hp₁ hi₀ hi₁ hL hb₀ hb₁ ht0 ht1 s).1)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos (by linarith : (0 : ℝ) < 2 * L)] at h
  refine (le_abs_self _).trans (h.trans (le_of_eq ?_))
  ring

/-- The numerical form of Lemma 6.1:
`2L · (3/2) L ε + (3/2) L ε + (1 + (3/2) κ_* L) ε ≤ (3 + 2κ_*)(1 + L)² ε`. -/
theorem interpolation_constant_le {L κs ε : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κs) (hε : 0 ≤ ε) :
    2 * L * (3 / 2 * L * ε) + 3 / 2 * L * ε + (1 + 3 / 2 * κs * L) * ε ≤
      (3 + 2 * κs) * (1 + L) ^ 2 * ε := by
  have h1 : 0 ≤ κs * L := mul_nonneg hκ hL
  have h2 : 0 ≤ κs * L ^ 2 := mul_nonneg hκ (sq_nonneg L)
  have : 2 * L * (3 / 2 * L) + 3 / 2 * L + (1 + 3 / 2 * κs * L) ≤ (3 + 2 * κs) * (1 + L) ^ 2 := by
    nlinarith
  nlinarith

end Ovals

end
