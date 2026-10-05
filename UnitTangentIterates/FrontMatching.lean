module

public import UnitTangentIterates.FrontError
public import UnitTangentIterates.PerimeterAsymptotics

/-!
# The front half of the curvature matching (Theorem 5.1, estimate (5.6))

Integrating Lemma 4.2 over a period and using the mass identity `∫₀ᴸ Y_L = ∫_ℝ y` gives

`‖K_L - K̄_L‖_{L¹(ℝ/Lℤ)} ≤ C e^{-βL} ∫_ℝ y`,

where `K_L = frontCurv Y_L` is the front curvature of the periodized model and
`K̄_L(s) = ∑_m K_*(s - mL)` is the periodization of the isolated curvature `K_* = frontCurv y`.
In the paper `∫_ℝ y = π`.

We also record that the steering defect `Δ = ∫_ℝ (1 - √(1 - y²))` is positive
(Lemma 3.5, (3.13)).
-/

@[expose] public section

namespace Ovals

open Real MeasureTheory intervalIntegral

variable {y y' : ℝ → ℝ} {A a D b : ℝ}

/-- **Theorem 5.1, front estimate (5.6).**  For a `C¹` pulse with `0 ≤ y ≤ b < 1`,
`y ≤ A e^{-a|t|}` and `|y'| ≤ D y`, for all large `L`,
`∫₀ᴸ |K_L - K̄_L| ≤ C e^{-βL} ∫_ℝ y`. -/
theorem front_matching (hy : ∀ t, HasDerivAt y (y' t) t) (hy'c : Continuous y')
    (hy0 : ∀ t, 0 ≤ y t) (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a)
    (hyD : ∀ t, |y' t| ≤ D * y t) (hyb : ∀ t, y t ≤ b) (hb : b < 1) :
    ∃ C β L₀ : ℝ, 0 < β ∧ ∀ L ≥ L₀,
      ∫ s in (0 : ℝ)..L, |frontCurv (periodize y L) s - periodize (frontCurv y) L s| ≤
        C * exp (-(β * L)) * ∫ t, y t := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hb0 : 0 ≤ b := (hy0 0).trans (hyb 0)
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hy'A : ∀ t, |y' t| ≤ (|D| * A) * exp (-(a * |t|)) := fun t => by
    have h1 : D * y t ≤ |D| * y t := mul_le_mul_of_nonneg_right (le_abs_self D) (hy0 t)
    have h2 : |D| * y t ≤ |D| * (A * exp (-(a * |t|))) :=
      mul_le_mul_of_nonneg_left (hyA t) (abs_nonneg D)
    linarith [hyD t]
  obtain ⟨C, β, L₀, hβ, hfe⟩ := front_error hy hy0 hyA ha hyD hyb hb
  have hev : ∀ᶠ L in Filter.atTop, 8 * A * exp (-(a / 2 * L)) < (1 - b) / 2 := by
    have ht : Filter.Tendsto (fun L : ℝ => 8 * A * exp (-(a / 2 * L))) Filter.atTop
        (nhds (8 * A * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < a / 2))).const_mul _
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by linarith))
  obtain ⟨L₂, hL₂⟩ := Filter.eventually_atTop.1 hev
  refine ⟨C, β, max (max L₀ (2 / a)) L₂, hβ, fun L hL => ?_⟩
  have hL0' : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLa : 2 / a ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL2 := hL₂ L ((le_max_right _ _).trans hL)
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hLa
  -- continuity of the two curvatures
  set Y := periodize y L with hYdef
  have hYc : Continuous Y := continuous_periodize hyc hyA' ha hL0
  have hY'c : Continuous (periodize y' L) := continuous_periodize hy'c hy'A ha hL0
  have hYb : ∀ s, Y s < 1 := fun s => by
    have := periodize_le hyA' ha hyb hLa s; linarith
  have hY0 : ∀ s, 0 ≤ Y s := fun s => tsum_nonneg fun m => hy0 _
  have hsqY : ∀ s, 0 < √(1 - Y s ^ 2) := fun s =>
    Real.sqrt_pos.2 (by nlinarith [hY0 s, hYb s])
  have hKL : Continuous (frontCurv Y) := by
    have e : frontCurv Y = fun s => Y s + periodize y' L s / √(1 - Y s ^ 2) := by
      funext s; unfold frontCurv
      rw [(hasDerivAt_periodize hy hyA' hy'A ha hL0 s).deriv]
    rw [e]
    exact hYc.add (hY'c.div (Real.continuous_sqrt.comp (continuous_const.sub (hYc.pow 2)))
      fun s => (hsqY s).ne')
  have hsqy : ∀ t, √(1 - b ^ 2) ≤ √(1 - y t ^ 2) := fun t =>
    Real.sqrt_le_sqrt (by nlinarith [hy0 t, hyb t])
  have hc0 : 0 < √(1 - b ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hKstar : frontCurv y = fun t => y t + y' t / √(1 - y t ^ 2) := by
    funext t; unfold frontCurv; rw [(hy t).deriv]
  have hKc : Continuous (frontCurv y) := by
    rw [hKstar]
    exact hyc.add (hy'c.div (Real.continuous_sqrt.comp (continuous_const.sub (hyc.pow 2)))
      fun t => (hc0.trans_le (hsqy t)).ne')
  have hKA : ∀ t, |frontCurv y t| ≤ (A + |D| * A / √(1 - b ^ 2)) * exp (-(a * |t|)) := by
    intro t
    rw [hKstar]
    simp only
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos (hc0.trans_le (hsqy t))]
    have h1 : |y' t| / √(1 - y t ^ 2) ≤ (|D| * A * exp (-(a * |t|))) / √(1 - b ^ 2) :=
      div_le_div₀ (by positivity) (hy'A t) hc0 (hsqy t)
    have h2 := hyA' t
    have : (|D| * A * exp (-(a * |t|))) / √(1 - b ^ 2) =
        |D| * A / √(1 - b ^ 2) * exp (-(a * |t|)) := by ring
    nlinarith
  have hKbar : Continuous (periodize (frontCurv y) L) := continuous_periodize hKc hKA ha hL0
  -- integrate Lemma 4.2 over a period
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) L,
      |frontCurv Y s - periodize (frontCurv y) L s| ≤ C * exp (-(β * L)) * Y s := fun s _ =>
    (hfe L hL0' s).2
  calc ∫ s in (0 : ℝ)..L, |frontCurv Y s - periodize (frontCurv y) L s|
      ≤ ∫ s in (0 : ℝ)..L, C * exp (-(β * L)) * Y s :=
        intervalIntegral.integral_mono_on hL0.le ((hKL.sub hKbar).abs.intervalIntegrable _ _)
          ((continuous_const.mul hYc).intervalIntegrable _ _) hpt
    _ = C * exp (-(β * L)) * ∫ t, y t := by
        rw [intervalIntegral.integral_const_mul, hYdef, integral_periodize hyc hyA' ha hL0]

/-- **Positivity of the steering defect** (Lemma 3.5, (3.13)): if `y` is continuous,
`0 ≤ y ≤ b < 1`, `y` decays exponentially, and `y(t₀) > 0` for some `t₀`, then
`Δ = ∫_ℝ (1 - √(1 - y²)) > 0`. -/
theorem steeringDefect_pos (hyc : Continuous y) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a) (hyb : ∀ t, y t ≤ b) (hb : b < 1)
    {t₀ : ℝ} (ht₀ : 0 < y t₀) : 0 < steeringDefect y := by
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  set Φ : ℝ → ℝ := fun t => 1 - √(1 - y t ^ 2) with hΦ
  have hΦc : Continuous Φ :=
    continuous_const.sub (Real.continuous_sqrt.comp (continuous_const.sub (hyc.pow 2)))
  have hΦ0 : ∀ t, 0 ≤ Φ t := fun t => (one_sub_sqrt_bounds (by nlinarith [hy0 t, hyb t])).1
  have hΦint : Integrable Φ := by
    refine (integrable_of_exp_bound hyc hyA' ha).mono' hΦc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 t)]
    have := (one_sub_sqrt_bounds (z := y t) (by nlinarith [hy0 t, hyb t])).2
    nlinarith [hy0 t, hyb t]
  have hΦt₀ : 0 < Φ t₀ := by
    simp only [hΦ]
    have : √(1 - y t₀ ^ 2) < 1 := by
      rw [Real.sqrt_lt' one_pos]; nlinarith
    linarith
  exact (integral_pos_iff_support_of_nonneg hΦ0 hΦint).2
    (hΦc.isOpen_support.measure_pos _ ⟨t₀, hΦt₀.ne'⟩)

end Ovals

end
