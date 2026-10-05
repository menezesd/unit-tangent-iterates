module

public import UnitTangentIterates.ShadowEstimates
public import UnitTangentIterates.Interpolation

/-!
# The interpolation path (Lemma 6.1) in data form

For two `L`-periodic curvature functions `κ₀, κ₁` with integral `π` over a period, the
interpolating curves `X_σ` with curvature `(1 - σ) κ₀ + σ κ₁` (Lemma 6.1) form a path.  We run
the interpolation parameter through a smooth transition `σ(t)` (`0` for `t ≤ 0`, `1` for
`t ≥ 1`), so that the path is defined for all times and constant outside `[0, 1]`, and record
it in data form (`Ovals.interpPath`): it is valid (`Ovals.interpPath_valid`) and its normal
velocity is bounded by a multiple of `(1 + L)² ∫₀ᴸ |κ₁ - κ₀|` (`Ovals.interpPath_bounded`).
-/

@[expose] public section

namespace Ovals

open Real Filter Topology Complex

variable {θ₀ L : ℝ} {κ₀ κ₁ : ℝ → ℝ}

/-- **The identity `ξ_s = κ_t η`** for the interpolating path. -/
theorem hasDerivAt_interpTangential (h₀ : Continuous κ₀) (h₁ : Continuous κ₁) (t s : ℝ) :
    HasDerivAt (interpTangential θ₀ κ₀ κ₁ L t)
      (interpCurv κ₀ κ₁ t s * interpNormal θ₀ κ₀ κ₁ L t s) s := by
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
  have hN : HasDerivAt (fun s => (starRingEnd ℂ) (tau (θ s)))
      ((starRingEnd ℂ) ((interpCurv κ₀ κ₁ t s : ℂ) * I * tau (θ s))) s :=
    (hasDerivAt_tau_comp (hθd s)).star
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hV.mul hN)
  convert hR using 1
  simp only [Complex.reCLM_apply, interpNormal]
  rw [← hθ]
  have h := conj_tau_mul_tau (θ s)
  have e : (angleVar κ₀ κ₁ s : ℂ) * I * tau (θ s) * (starRingEnd ℂ) (tau (θ s)) +
      interpVelocity θ₀ κ₀ κ₁ L t s *
        (starRingEnd ℂ) ((interpCurv κ₀ κ₁ t s : ℂ) * I * tau (θ s)) =
      (angleVar κ₀ κ₁ s : ℂ) * I + (interpCurv κ₀ κ₁ t s : ℂ) *
        (interpVelocity θ₀ κ₀ κ₁ L t s * (starRingEnd ℂ) (I * tau (θ s))) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    linear_combination (angleVar κ₀ κ₁ s : ℂ) * I * h
  rw [e, Complex.add_re, Complex.re_ofReal_mul]
  simp; ring

lemma interpCurv_periodic (hp₀ : Function.Periodic κ₀ L) (hp₁ : Function.Periodic κ₁ L)
    (t : ℝ) : Function.Periodic (interpCurv κ₀ κ₁ t) L := fun r => by
  simp only [interpCurv, hp₀ r, hp₁ r]

lemma interpCurv_integral (h₀ : Continuous κ₀) (h₁ : Continuous κ₁)
    (hi₀ : ∫ r in (0 : ℝ)..L, κ₀ r = π) (hi₁ : ∫ r in (0 : ℝ)..L, κ₁ r = π) (t : ℝ) :
    ∫ r in (0 : ℝ)..L, interpCurv κ₀ κ₁ t r = π := by
  unfold interpCurv
  rw [intervalIntegral.integral_add (f := fun r => (1 - t) * κ₀ r) (g := fun r => t * κ₁ r)
    ((continuous_const.mul h₀).intervalIntegrable _ _)
    ((continuous_const.mul h₁).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hi₀, hi₁]
  ring

/-- The tangential velocity is `L`-periodic in `s`. -/
theorem interpTangential_periodic (h₀ : Continuous κ₀) (h₁ : Continuous κ₁)
    (hp₀ : Function.Periodic κ₀ L) (hp₁ : Function.Periodic κ₁ L)
    (hi₀ : ∫ r in (0 : ℝ)..L, κ₀ r = π) (hi₁ : ∫ r in (0 : ℝ)..L, κ₁ r = π) (t : ℝ) :
    Function.Periodic (interpTangential θ₀ κ₀ κ₁ L t) L := by
  have hκc := continuous_interpCurv h₀ h₁
  intro s
  have hV : interpVelocity θ₀ κ₀ κ₁ L t (s + L) = -interpVelocity θ₀ κ₀ κ₁ L t s := by
    have h1 := hasDerivAt_interpCurve (θ₀ := θ₀) (L := L) h₀ h₁ t (s + L)
    have e : (fun t' => interpCurve θ₀ κ₀ κ₁ L t' (s + L)) =
        fun t' => -interpCurve θ₀ κ₀ κ₁ L t' s := funext fun t' =>
      curveOfCurvature_add_period (hκc t') (interpCurv_periodic hp₀ hp₁ t')
        (interpCurv_integral h₀ h₁ hi₀ hi₁ t') s
    rw [e] at h1
    exact h1.unique (hasDerivAt_interpCurve (θ₀ := θ₀) (L := L) h₀ h₁ t s).neg
  have hθ := angleOfCurvature_add_period (θ₀ := θ₀) (hκc t) (interpCurv_periodic hp₀ hp₁ t)
    (interpCurv_integral h₀ h₁ hi₀ hi₁ t) s
  simp only [interpTangential, hV, hθ, tau_add_pi]
  simp only [map_neg, neg_mul, mul_neg, neg_neg]

lemma hasDerivAt_angleVar (h₀ : Continuous κ₀) (h₁ : Continuous κ₁) (s : ℝ) :
    HasDerivAt (angleVar κ₀ κ₁) (κ₁ s - κ₀ s) s :=
  intervalIntegral.integral_hasDerivAt_right ((h₁.sub h₀).intervalIntegrable _ _)
    ((h₁.sub h₀).stronglyMeasurableAtFilter _ _) (h₁.sub h₀).continuousAt

lemma angleVar_periodic (h₀ : Continuous κ₀) (h₁ : Continuous κ₁)
    (hp₀ : Function.Periodic κ₀ L) (hp₁ : Function.Periodic κ₁ L)
    (hi₀ : ∫ r in (0 : ℝ)..L, κ₀ r = π) (hi₁ : ∫ r in (0 : ℝ)..L, κ₁ r = π) :
    Function.Periodic (angleVar κ₀ κ₁) L := fun s => by
  unfold angleVar
  have hc := (h₁.sub h₀)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hper : Function.Periodic (fun u => κ₁ u - κ₀ u) L := fun u => by simp [hp₀ u, hp₁ u]
  have hL0 : ∫ u in (0 : ℝ)..L, (κ₁ u - κ₀ u) = 0 := by
    rw [intervalIntegral.integral_sub (h₁.intervalIntegrable _ _) (h₀.intervalIntegrable _ _),
      hi₀, hi₁, sub_self]
  rw [hper.intervalIntegral_add_eq s 0, zero_add, hL0, add_zero]

/-! ### The smooth transition -/

lemma exists_deriv_smoothTransition_le :
    ∃ C, 0 ≤ C ∧ ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨t₀, -, ht₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (Set.nonempty_Icc.2 zero_le_one) hc.abs.continuousOn
  refine ⟨|deriv Real.smoothTransition t₀|, abs_nonneg _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · exact ht₀ ht
  · rcases not_and_or.1 ht with h | h
    · have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds (not_le.1 h)] with x hx
        exact Real.smoothTransition.zero_of_nonpos hx.le
      rw [hev.deriv_eq, deriv_const, abs_zero]; exact abs_nonneg _
    · have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds (not_le.1 h)] with x hx
        exact Real.smoothTransition.one_of_one_le hx.le
      rw [hev.deriv_eq, deriv_const, abs_zero]; exact abs_nonneg _

/-- The bound on `σ'` used for the interpolation path. -/
noncomputable def Cσ : ℝ := exists_deriv_smoothTransition_le.choose

lemma Cσ_nonneg : 0 ≤ Cσ := exists_deriv_smoothTransition_le.choose_spec.1

lemma abs_deriv_smoothTransition_le (t : ℝ) : |deriv Real.smoothTransition t| ≤ Cσ :=
  exists_deriv_smoothTransition_le.choose_spec.2 t

lemma hasDerivAt_smoothTransition (t : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) t).hasDerivAt

/-! ### The path -/

/-- **The interpolation path from `κ₀` to `κ₁`** in data form, parametrized by arclength. -/
noncomputable def interpPath (κ₀ κ₁ : ℝ → ℝ) (L : ℝ) : PathData where
  p := L
  a t s := interpCurv κ₀ κ₁ (Real.smoothTransition t) s
  g _ _ := 1
  ξ t s := deriv Real.smoothTransition t *
    interpTangential 0 κ₀ κ₁ L (Real.smoothTransition t) s
  η t s := deriv Real.smoothTransition t * interpNormal 0 κ₀ κ₁ L (Real.smoothTransition t) s
  ω t s := deriv Real.smoothTransition t * angleVar κ₀ κ₁ s
  gd _ _ := 0

lemma interpPath_a_of_nonpos {t : ℝ} (ht : t ≤ 0) (s : ℝ) :
    (interpPath κ₀ κ₁ L).a t s = κ₀ s := by
  simp [interpPath, interpCurv, Real.smoothTransition.zero_of_nonpos ht]

lemma interpPath_a_of_one_le {t : ℝ} (ht : 1 ≤ t) (s : ℝ) :
    (interpPath κ₀ κ₁ L).a t s = κ₁ s := by
  simp [interpPath, interpCurv, Real.smoothTransition.one_of_one_le ht]

section valid

variable (h₀ : Continuous κ₀) (h₁ : Continuous κ₁)
    (hp₀ : Function.Periodic κ₀ L) (hp₁ : Function.Periodic κ₁ L)
    (hi₀ : ∫ r in (0 : ℝ)..L, κ₀ r = π) (hi₁ : ∫ r in (0 : ℝ)..L, κ₁ r = π) (hL : 0 < L)
    {κs : ℝ} (hb₀ : ∀ r, 0 ≤ κ₀ r ∧ κ₀ r ≤ κs) (hb₁ : ∀ r, 0 ≤ κ₁ r ∧ κ₁ r ≤ κs)
include h₀ h₁ hp₀ hp₁ hi₀ hi₁ hL hb₀ hb₁

/-- **The interpolation path is valid**, with curvature at most `κs` and unit speed. -/
theorem interpPath_valid : (interpPath κ₀ κ₁ L).Valid κs 1 := by
  have hT := fun t => hasDerivAt_interpTangential (θ₀ := 0) (L := L) h₀ h₁ t
  have hN := fun t => hasDerivAt_interpNormal (θ₀ := 0) (L := L) h₀ h₁ t
  have hTc : ∀ t, Continuous (interpTangential 0 κ₀ κ₁ L t) := fun t =>
    continuous_iff_continuousAt.2 fun s => (hT t s).continuousAt
  have hNc : ∀ t, Continuous (interpNormal 0 κ₀ κ₁ L t) := fun t =>
    continuous_iff_continuousAt.2 fun s => (hN t s).continuousAt
  have hφ := continuous_angleVar (κ₀ := κ₀) (κ₁ := κ₁) h₀ h₁
  have hσ0 := Real.smoothTransition.nonneg
  have hσ1 := Real.smoothTransition.le_one
  have hηd : ∀ t s, HasDerivAt ((interpPath κ₀ κ₁ L).η t)
      (deriv Real.smoothTransition t * (angleVar κ₀ κ₁ s - interpCurv κ₀ κ₁
        (Real.smoothTransition t) s * interpTangential 0 κ₀ κ₁ L (Real.smoothTransition t) s))
      s := fun t s => (hN _ s).const_mul _
  have hξd : ∀ t s, HasDerivAt ((interpPath κ₀ κ₁ L).ξ t)
      (deriv Real.smoothTransition t * (interpCurv κ₀ κ₁ (Real.smoothTransition t) s *
        interpNormal 0 κ₀ κ₁ L (Real.smoothTransition t) s)) s := fun t s =>
    (hT _ s).const_mul _
  have hωd : ∀ t s, HasDerivAt ((interpPath κ₀ κ₁ L).ω t)
      (deriv Real.smoothTransition t * (κ₁ s - κ₀ s)) s := fun t s =>
    (hasDerivAt_angleVar h₀ h₁ s).const_mul _
  obtain ⟨Bκ, hBκ⟩ := exists_abs_le_of_periodic hL (h₁.sub h₀)
    (fun s => by simp only [hp₀ s, hp₁ s])
  refine
  { p_pos := hL
    a_per := fun t => interpCurv_periodic hp₀ hp₁ _
    g_per := fun t s => rfl
    ξ_per := fun t s => by
      simp only [interpPath, interpTangential_periodic h₀ h₁ hp₀ hp₁ hi₀ hi₁ _ s]
    η_per := fun t s => by
      simp only [interpPath, interpNormal_periodic h₀ h₁ hp₀ hp₁ hi₀ hi₁ _ s]
    ω_per := fun t s => by
      simp only [interpPath, angleVar_periodic h₀ h₁ hp₀ hp₁ hi₀ hi₁ s]
    gd_per := fun t s => rfl
    a_cont := fun t => continuous_interpCurv h₀ h₁ _
    g_cont := fun t => continuous_const
    gd_cont := fun t => continuous_const
    ξ_diff := fun t s => (hξd t s).differentiableAt
    η_diff := fun t s => (hηd t s).differentiableAt
    η_deriv_cont := fun t => by
      rw [show deriv ((interpPath κ₀ κ₁ L).η t) = _ from funext fun s => (hηd t s).deriv]
      exact continuous_const.mul (hφ.sub ((continuous_interpCurv h₀ h₁ _).mul (hTc _)))
    ω_diff := fun t s => (hωd t s).differentiableAt
    ω_deriv_cont := fun t => by
      rw [show deriv ((interpPath κ₀ κ₁ L).ω t) = _ from funext fun s => (hωd t s).deriv]
      exact continuous_const.mul (h₁.sub h₀)
    m_pos := one_pos
    g_ge := fun t s => le_rfl
    a_nonneg := fun t s => by
      simp only [interpPath, interpCurv]
      have := hσ0 t; have := hσ1 t
      nlinarith [(hb₀ s).1, (hb₁ s).1]
    a_le := fun t s => by
      simp only [interpPath, interpCurv, mul_one]
      have := hσ0 t; have := hσ1 t
      nlinarith [(hb₀ s).2, (hb₁ s).2]
    turn := fun t => interpCurv_integral h₀ h₁ hi₀ hi₁ _
    rot := fun t s => by
      rw [(hηd t s).deriv]; simp only [interpPath]; ring
    stretch := fun t s => by
      rw [(hξd t s).deriv]; simp only [interpPath]; ring
    a_udiff := fun t₀ => by
      intro ε hε
      have hσd := hasDerivAt_smoothTransition t₀
      rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hσd
      filter_upwards [hσd (c := ε / (Bκ + 1)) (by
        have := (abs_nonneg _).trans (hBκ 0); positivity)] with t ht s
      rw [(hωd t₀ s).deriv]
      simp only [interpPath, interpCurv, Real.norm_eq_abs, smul_eq_mul] at ht ⊢
      have hB0 : 0 ≤ Bκ := (abs_nonneg _).trans (hBκ 0)
      have e : (1 - Real.smoothTransition t) * κ₀ s + Real.smoothTransition t * κ₁ s -
          ((1 - Real.smoothTransition t₀) * κ₀ s + Real.smoothTransition t₀ * κ₁ s) -
          (t - t₀) * (deriv Real.smoothTransition t₀ * (κ₁ s - κ₀ s)) =
          (Real.smoothTransition t - Real.smoothTransition t₀ -
            (t - t₀) * deriv Real.smoothTransition t₀) * (κ₁ s - κ₀ s) := by ring
      rw [e, abs_mul]
      calc _ ≤ ε / (Bκ + 1) * |t - t₀| * Bκ := by
            have ht' : |Real.smoothTransition t - Real.smoothTransition t₀ -
                (t - t₀) * deriv Real.smoothTransition t₀| ≤ ε / (Bκ + 1) * |t - t₀| := by
              exact ht
            exact mul_le_mul ht' (hBκ s) (abs_nonneg _) (by positivity)
        _ ≤ ε * |t - t₀| := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [abs_nonneg (t - t₀), mul_nonneg hε.le (abs_nonneg (t - t₀))]
    g_udiff := fun t₀ => UDiffAt.const (fun _ => 1) t₀ }

/-- **Lemma 6.1 in data form**: uniform bounds on the normal velocity of the interpolation path,
with `ε = ∫₀ᴸ |κ₁ - κ₀|`. -/
theorem interpPath_bounded :
    (interpPath κ₀ κ₁ L).Bounded (L * (Cσ * (3 / 2 * L * ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u|)))
      (Cσ * (3 / 2 * L * ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u|))
      (Cσ * ((1 + 3 / 2 * κs * L) * ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u|)) := by
  set ε := ∫ u in (0 : ℝ)..L, |κ₁ u - κ₀ u|
  have hε0 : 0 ≤ ε := intervalIntegral.integral_nonneg hL.le fun _ _ => abs_nonneg _
  have hb := fun t s => interpolation_bounds (θ₀ := 0) h₀ h₁ hp₀ hp₁ hi₀ hi₁ hL hb₀ hb₁
    (Real.smoothTransition.nonneg t) (Real.smoothTransition.le_one t) s
  have hη : ∀ t s, |(interpPath κ₀ κ₁ L).η t s| ≤ Cσ * (3 / 2 * L * ε) := fun t s => by
    simp only [interpPath, abs_mul]
    exact mul_le_mul (abs_deriv_smoothTransition_le t) (hb t s).1 (abs_nonneg _) Cσ_nonneg
  refine ⟨fun t => ?_, hη, fun t s => ?_⟩
  · have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (a := 0) (b := L) hL.le
      (f := fun s => (interpPath κ₀ κ₁ L).g t s * |(interpPath κ₀ κ₁ L).η t s|)
      (g := fun _ => Cσ * (3 / 2 * L * ε))
      ((interpPath_valid h₀ h₁ hp₀ hp₁ hi₀ hi₁ hL hb₀ hb₁).g_cont t |>.mul
        ((interpPath_valid h₀ h₁ hp₀ hp₁ hi₀ hi₁ hL hb₀ hb₁).η_diff t).continuous.abs
        |>.intervalIntegrable _ _)
      intervalIntegrable_const (fun s _ => by
        simp only [interpPath, one_mul] at hη ⊢; exact hη t s)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
    exact this
  · have e : deriv ((interpPath κ₀ κ₁ L).η t) s =
        deriv Real.smoothTransition t * deriv (interpNormal 0 κ₀ κ₁ L (Real.smoothTransition t)) s := by
      simp only [interpPath]
      exact deriv_const_mul _ ((hasDerivAt_interpNormal (θ₀ := 0) (L := L) h₀ h₁ _ s).differentiableAt)
    simp only [interpPath, div_one] at e ⊢
    rw [e, abs_mul]
    exact mul_le_mul (abs_deriv_smoothTransition_le t) (hb t s).2 (abs_nonneg _) Cσ_nonneg

end valid

end Ovals

end
