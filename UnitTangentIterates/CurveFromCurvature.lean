module

public import UnitTangentIterates.Circle

/-!
# Centrally symmetric closed curves with prescribed curvature

Proposition 4.3 and Lemma 6.1 build closed curves from a curvature function.  If `κ` is
continuous and `L`-periodic with `∫₀ᴸ κ = π`, then with
`θ(s) = θ₀ + ∫₀ˢ κ` the curve

`X(s) = ∫₀ˢ τ(θ(r)) dr - ½ ∫₀ᴸ τ(θ(r)) dr`                      (6.2)

is parametrized by arclength, has curvature `κ`, and satisfies `X(s + L) = -X(s)`: it is a
centered, centrally symmetric closed curve of perimeter `2L`.

We also prove the coordinate estimate of Lemma 6.1: two such curves with the same initial
tangent angle satisfy `|X₁(s) - X₀(s)| ≤ (3/2) L ‖κ₁ - κ₀‖_{L¹(0,L)}` on `[0, L]`.
-/

@[expose] public section

namespace Ovals

open Complex Real intervalIntegral MeasureTheory

/-- The tangent angle `θ(s) = θ₀ + ∫₀ˢ κ`. -/
noncomputable def angleOfCurvature (θ₀ : ℝ) (κ : ℝ → ℝ) (s : ℝ) : ℝ := θ₀ + ∫ r in (0 : ℝ)..s, κ r

/-- The centered curve `X(s) = ∫₀ˢ τ(θ) - ½ ∫₀ᴸ τ(θ)` with curvature `κ` (equation (6.2)). -/
noncomputable def curveOfCurvature (θ₀ : ℝ) (κ : ℝ → ℝ) (L : ℝ) (s : ℝ) : ℂ :=
  (∫ r in (0 : ℝ)..s, tau (angleOfCurvature θ₀ κ r)) -
    (1 / 2 : ℂ) * ∫ r in (0 : ℝ)..L, tau (angleOfCurvature θ₀ κ r)

variable {θ₀ L : ℝ} {κ : ℝ → ℝ}

theorem hasDerivAt_angleOfCurvature (hκ : Continuous κ) (s : ℝ) :
    HasDerivAt (angleOfCurvature θ₀ κ) (κ s) s := by
  unfold angleOfCurvature
  exact (intervalIntegral.integral_hasDerivAt_right (hκ.intervalIntegrable _ _)
    (hκ.stronglyMeasurableAtFilter _ _) hκ.continuousAt).const_add θ₀

theorem continuous_angleOfCurvature (hκ : Continuous κ) : Continuous (angleOfCurvature θ₀ κ) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_angleOfCurvature hκ s).continuousAt

theorem continuous_tau : Continuous tau := contDiff_tau.continuous

theorem continuous_tau_angle (hκ : Continuous κ) :
    Continuous (fun r => tau (angleOfCurvature θ₀ κ r)) :=
  continuous_tau.comp (continuous_angleOfCurvature hκ)

/-- The curve is parametrized by arclength with unit tangent `τ(θ)`. -/
theorem hasDerivAt_curveOfCurvature (hκ : Continuous κ) (s : ℝ) :
    HasDerivAt (curveOfCurvature θ₀ κ L) (tau (angleOfCurvature θ₀ κ s)) s := by
  unfold curveOfCurvature
  have hc := continuous_tau_angle (θ₀ := θ₀) hκ
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).sub_const _

theorem deriv_curveOfCurvature (hκ : Continuous κ) :
    deriv (curveOfCurvature θ₀ κ L) = fun s => tau (angleOfCurvature θ₀ κ s) :=
  funext fun s => (hasDerivAt_curveOfCurvature hκ s).deriv

theorem norm_deriv_curveOfCurvature (hκ : Continuous κ) (s : ℝ) :
    ‖deriv (curveOfCurvature θ₀ κ L) s‖ = 1 := by
  rw [deriv_curveOfCurvature hκ, norm_tau]

/-- The curve has curvature `κ`. -/
theorem curvature_curveOfCurvature (hκ : Continuous κ) (s : ℝ) :
    curvature (curveOfCurvature θ₀ κ L) s = κ s := by
  unfold curvature
  rw [norm_deriv_curveOfCurvature hκ, deriv_curveOfCurvature hκ,
    (hasDerivAt_tau_comp (hasDerivAt_angleOfCurvature (θ₀ := θ₀) hκ s)).deriv]
  have : (starRingEnd ℂ) (tau (angleOfCurvature θ₀ κ s)) *
      ((κ s : ℂ) * I * tau (angleOfCurvature θ₀ κ s)) = (κ s : ℂ) * I := by
    rw [mul_comm ((κ s : ℂ) * I), ← mul_assoc, conj_tau_mul_tau, one_mul]
  rw [this]; simp

/-- With `∫₀ᴸ κ = π`, the tangent reverses after one half-period. -/
theorem angleOfCurvature_add_period (hκ : Continuous κ) (hκp : Function.Periodic κ L)
    (hint : ∫ r in (0 : ℝ)..L, κ r = π) (s : ℝ) :
    angleOfCurvature θ₀ κ (s + L) = angleOfCurvature θ₀ κ s + π := by
  unfold angleOfCurvature
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s)
    (hκ.intervalIntegrable _ _) (hκ.intervalIntegrable _ _)]
  have : ∫ r in s..(s + L), κ r = π := by
    rw [hκp.intervalIntegral_add_eq s 0, zero_add, hint]
  rw [this]; ring

theorem tau_add_pi (x : ℝ) : tau (x + π) = -tau x := by
  rw [tau_add, tau_eq π]; simp

/-- **Central symmetry.**  `X(s + L) = -X(s)`; in particular `X` is `2L`-periodic. -/
theorem curveOfCurvature_add_period (hκ : Continuous κ) (hκp : Function.Periodic κ L)
    (hint : ∫ r in (0 : ℝ)..L, κ r = π) (s : ℝ) :
    curveOfCurvature θ₀ κ L (s + L) = -curveOfCurvature θ₀ κ L s := by
  have hc := continuous_tau_angle (θ₀ := θ₀) hκ
  unfold curveOfCurvature
  set c := ∫ r in (0 : ℝ)..L, tau (angleOfCurvature θ₀ κ r)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := L)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ r in L..(s + L), tau (angleOfCurvature θ₀ κ r) =
      -∫ r in (0 : ℝ)..s, tau (angleOfCurvature θ₀ κ r) := by
    have := intervalIntegral.integral_comp_add_right
      (fun r => tau (angleOfCurvature θ₀ κ r)) (a := 0) (b := s) L
    rw [zero_add] at this
    rw [← this, ← intervalIntegral.integral_neg]
    congr 1; ext r
    rw [angleOfCurvature_add_period hκ hκp hint, tau_add_pi]
  rw [h1]; ring

theorem curveOfCurvature_periodic (hκ : Continuous κ) (hκp : Function.Periodic κ L)
    (hint : ∫ r in (0 : ℝ)..L, κ r = π) :
    Function.Periodic (curveOfCurvature θ₀ κ L) (2 * L) := fun s => by
  rw [two_mul, ← add_assoc, curveOfCurvature_add_period hκ hκp hint,
    curveOfCurvature_add_period hκ hκp hint, neg_neg]

/-- `τ` is `1`-Lipschitz. -/
theorem norm_tau_sub_le (a b : ℝ) : ‖tau a - tau b‖ ≤ |a - b| := by
  have : tau a - tau b = tau b * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    unfold tau
    rw [mul_sub, mul_one, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul, norm_tau, one_mul]
  exact (norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq (Real.norm_eq_abs _))

/-- **Coordinate estimate of Lemma 6.1.**  Two curves built from continuous curvatures
`κ₀, κ₁` with the same initial angle satisfy, for `0 ≤ s ≤ L`,
`|X₁(s) - X₀(s)| ≤ (3/2) L ∫₀ᴸ |κ₁ - κ₀|`. -/
theorem norm_curveOfCurvature_sub_le {κ₀ κ₁ : ℝ → ℝ} (hκ₀ : Continuous κ₀)
    (hκ₁ : Continuous κ₁) (hL : 0 ≤ L) {s : ℝ} (hs0 : 0 ≤ s) (hsL : s ≤ L) :
    ‖curveOfCurvature θ₀ κ₁ L s - curveOfCurvature θ₀ κ₀ L s‖ ≤
      3 / 2 * L * ∫ r in (0 : ℝ)..L, |κ₁ r - κ₀ r| := by
  set ε := ∫ r in (0 : ℝ)..L, |κ₁ r - κ₀ r| with hε
  have hc₀ := continuous_tau_angle (θ₀ := θ₀) hκ₀
  have hc₁ := continuous_tau_angle (θ₀ := θ₀) hκ₁
  have hd : Continuous fun r => |κ₁ r - κ₀ r| := (hκ₁.sub hκ₀).abs
  -- the angles differ by at most `ε` on `[0, L]`
  have hang : ∀ r ∈ Set.Icc (0 : ℝ) L,
      ‖tau (angleOfCurvature θ₀ κ₁ r) - tau (angleOfCurvature θ₀ κ₀ r)‖ ≤ ε := by
    intro r hr
    refine (norm_tau_sub_le _ _).trans ?_
    unfold angleOfCurvature
    rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub (hκ₁.intervalIntegrable _ _)
      (hκ₀.intervalIntegrable _ _)]
    refine (intervalIntegral.abs_integral_le_integral_abs hr.1).trans ?_
    rw [hε]
    exact intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hd.intervalIntegrable _ _)
  have hint : ∀ b ∈ Set.Icc (0 : ℝ) L,
      ‖(∫ r in (0 : ℝ)..b, tau (angleOfCurvature θ₀ κ₁ r)) -
        ∫ r in (0 : ℝ)..b, tau (angleOfCurvature θ₀ κ₀ r)‖ ≤ ε * b := by
    intro b hb
    rw [← intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₀.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := b)
      (C := ε) (f := fun r => tau (angleOfCurvature θ₀ κ₁ r) - tau (angleOfCurvature θ₀ κ₀ r))
      (fun r hr => by
        rw [Set.uIoc_of_le hb.1] at hr
        exact hang r ⟨hr.1.le, hr.2.trans hb.2⟩)
    rw [sub_zero, abs_of_nonneg hb.1] at this
    exact this
  have hε0 : 0 ≤ ε := intervalIntegral.integral_nonneg hL fun _ _ => abs_nonneg _
  unfold curveOfCurvature
  have e : (∫ r in (0 : ℝ)..s, tau (angleOfCurvature θ₀ κ₁ r)) -
      (1 / 2 : ℂ) * (∫ r in (0 : ℝ)..L, tau (angleOfCurvature θ₀ κ₁ r)) -
      ((∫ r in (0 : ℝ)..s, tau (angleOfCurvature θ₀ κ₀ r)) -
      (1 / 2 : ℂ) * ∫ r in (0 : ℝ)..L, tau (angleOfCurvature θ₀ κ₀ r)) =
      ((∫ r in (0 : ℝ)..s, tau (angleOfCurvature θ₀ κ₁ r)) -
        ∫ r in (0 : ℝ)..s, tau (angleOfCurvature θ₀ κ₀ r)) -
      (1 / 2 : ℂ) * ((∫ r in (0 : ℝ)..L, tau (angleOfCurvature θ₀ κ₁ r)) -
        ∫ r in (0 : ℝ)..L, tau (angleOfCurvature θ₀ κ₀ r)) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have h1 := hint s ⟨hs0, hsL⟩
  have h2 := hint L ⟨hL, le_rfl⟩
  have h3 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h3]
  nlinarith

end Ovals

end
