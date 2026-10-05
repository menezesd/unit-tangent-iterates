module

public import UnitTangentIterates.PeriodizationIntegral

/-!
# The half-perimeter of the periodized rear (Proposition 4.3, first half of (4.5))

For the periodized steering profile `Y_H` (with `c_H = √(1 - Y_H²)`), the rear `R_H` has
half-perimeter `P(H) = ∫₀ᴴ c_H` (equation (4.4)).  With the steering defect
`Δ = ∫_ℝ (1 - c)`, `c = √(1 - y²)`, we prove

`P(H) = H - Δ + O(e^{-βH})`.

We also prove that the periodization of a continuous exponentially decaying pulse is
continuous.
-/

@[expose] public section

namespace Ovals

open Real MeasureTheory intervalIntegral

variable {y : ℝ → ℝ} {A a : ℝ}

/-- The periodization of a continuous exponentially decaying pulse is continuous. -/
theorem continuous_periodize (hyc : Continuous y) (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|)))
    (ha : 0 < a) {H : ℝ} (hH : 0 < H) : Continuous (periodize y H) := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hyA 0)) (exp_pos _)
  have hr1 : exp (-(a * H)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  obtain ⟨hgs, -⟩ := summable_geom_natAbs (exp_pos _).le hr1
  refine continuous_iff_continuousAt.2 fun s => ?_
  have hc : ContinuousOn (fun x => ∑' m : ℤ, y (x - m * H)) (Metric.ball s 1) := by
    refine continuousOn_tsum
      (u := fun m : ℤ => A * exp (a * (|s| + 1)) * exp (-(a * H)) ^ m.natAbs)
      (fun m => (hyc.comp (continuous_id.sub continuous_const)).continuousOn)
      (hgs.mul_left _) (fun m z hz => ?_)
    rw [Real.norm_eq_abs]
    refine (pulse_shift_le (y := fun t => |y t|) hyA hA ha hH z m).trans ?_
    have hz' : |z| ≤ |s| + 1 := by
      have := abs_sub_abs_le_abs_sub z s
      rw [Metric.mem_ball, Real.dist_eq] at hz
      linarith
    have h' : exp (a * |z|) ≤ exp (a * (|s| + 1)) := Real.exp_le_exp.2 (by nlinarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h' hA) (by positivity)
  exact hc.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

/-- `z ↦ √(1 - z²)` is Lipschitz on `[0, b]`, `b < 1`. -/
lemma sqrt_one_sub_sq_lipschitz {b u v : ℝ} (hb : b < 1) (hu0 : 0 ≤ u)
    (hub : u ≤ b) (hv0 : 0 ≤ v) (hvb : v ≤ b) :
    |√(1 - u ^ 2) - √(1 - v ^ 2)| ≤ |u - v| / √(1 - b ^ 2) := by
  have hb0 : 0 ≤ b := hu0.trans hub
  have hpos : 0 < 1 - b ^ 2 := by nlinarith
  set c0 := √(1 - b ^ 2)
  set cu := √(1 - u ^ 2)
  set cv := √(1 - v ^ 2)
  have hc0 : 0 < c0 := Real.sqrt_pos.2 hpos
  have hcu0 : c0 ≤ cu := Real.sqrt_le_sqrt (by nlinarith)
  have hcv0 : c0 ≤ cv := Real.sqrt_le_sqrt (by nlinarith)
  have hcu2 : cu ^ 2 = 1 - u ^ 2 := Real.sq_sqrt (by nlinarith)
  have hcv2 : cv ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by nlinarith)
  have h1 : |cu - cv| * (cu + cv) = |u - v| * (u + v) := by
    rw [← abs_of_pos (show 0 < cu + cv by linarith), ← abs_mul,
      ← abs_of_nonneg (show 0 ≤ u + v by linarith), ← abs_mul]
    rw [show (cu - cv) * (cu + cv) = cu ^ 2 - cv ^ 2 by ring, hcu2, hcv2,
      show (u - v) * (u + v) = u ^ 2 - v ^ 2 by ring, abs_sub_comm (u ^ 2)]
    congr 1; ring
  rw [le_div_iff₀ hc0]
  have : |cu - cv| * (2 * c0) ≤ |cu - cv| * (cu + cv) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have : |u - v| * (u + v) ≤ |u - v| * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  linarith

/-- `0 ≤ 1 - √(1 - z²) ≤ z²` for `|z| ≤ 1`. -/
lemma one_sub_sqrt_bounds {z : ℝ} (hz : z ^ 2 ≤ 1) :
    0 ≤ 1 - √(1 - z ^ 2) ∧ 1 - √(1 - z ^ 2) ≤ z ^ 2 := by
  have h0 : 0 ≤ 1 - z ^ 2 := by linarith
  have h1 : √(1 - z ^ 2) ≤ √1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg z])
  rw [Real.sqrt_one] at h1
  refine ⟨by linarith, ?_⟩
  have : 1 - z ^ 2 ≤ √(1 - z ^ 2) := by
    rw [Real.le_sqrt h0 h0]; nlinarith [sq_nonneg z]
  linarith

/-- The half-perimeter `P(H) = ∫₀ᴴ √(1 - Y_H²)` of the periodized rear (equation (4.4)). -/
noncomputable def halfPerimeter (y : ℝ → ℝ) (H : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..H, √(1 - periodize y H s ^ 2)

/-- The steering defect `Δ = ∫_ℝ (1 - √(1 - y²))` (equation (3.13)). -/
noncomputable def steeringDefect (y : ℝ → ℝ) : ℝ := ∫ t, (1 - √(1 - y t ^ 2))

/-- `H e^{-aH/2} ≤ (4/a) e^{-aH/4}`. -/
lemma mul_exp_neg_half_le (ha : 0 < a) (H : ℝ) :
    H * exp (-(a / 2 * H)) ≤ 4 / a * exp (-(a / 4 * H)) := by
  have h1 : a / 4 * H ≤ exp (a / 4 * H) := by linarith [Real.add_one_le_exp (a / 4 * H)]
  set E := exp (-(a / 4 * H)) with hE
  have hE0 : 0 < E := exp_pos _
  have h2 : exp (-(a / 2 * H)) = E * E := by
    rw [hE, ← Real.exp_add]; congr 1; ring
  have h3 : exp (a / 4 * H) * E = 1 := by
    rw [hE, ← Real.exp_add]; simp
  have h5 : H * E ≤ 4 / a := by
    rw [le_div_iff₀ ha]; nlinarith [mul_le_mul_of_nonneg_right h1 hE0.le]
  rw [h2]
  calc H * (E * E) = (H * E) * E := by ring
    _ ≤ 4 / a * E := mul_le_mul_of_nonneg_right h5 hE0.le

/-- **Proposition 4.3, asymptotics of the half-perimeter.**  For a continuous pulse with
`0 ≤ y ≤ b < 1` and `y ≤ A e^{-a|t|}`, `P(H) = H - Δ + O(e^{-βH})`. -/
theorem halfPerimeter_asymptotics (hyc : Continuous y) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a) {b : ℝ} (hyb : ∀ t, y t ≤ b)
    (hb : b < 1) :
    ∃ C β H₀ : ℝ, 0 < β ∧ ∀ H ≥ H₀,
      |H - halfPerimeter y H - steeringDefect y| ≤ C * exp (-(β * H)) := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hb0 : 0 ≤ b := (hy0 0).trans (hyb 0)
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  set b' : ℝ := (1 + b) / 2 with hb'
  have hb'1 : b' < 1 := by rw [hb']; linarith
  have hbb' : b ≤ b' := by rw [hb']; linarith
  set c0 : ℝ := √(1 - b' ^ 2) with hc0def
  have hc0 : 0 < c0 := Real.sqrt_pos.2 (by nlinarith)
  set I0 : ℝ := ∫ t, exp (-(a * |t|)) with hI0
  have hI0int := integrable_exp_neg_mul_abs ha
  have hI00 : 0 ≤ I0 := integral_nonneg fun t => (exp_pos _).le
  have hev : ∀ᶠ H in Filter.atTop, 8 * A * exp (-(a / 2 * H)) < (1 - b) / 2 := by
    have ht : Filter.Tendsto (fun H : ℝ => 8 * A * exp (-(a / 2 * H))) Filter.atTop
        (nhds (8 * A * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < a / 2))).const_mul _
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by linarith))
  obtain ⟨H2, hH2⟩ := Filter.eventually_atTop.1 hev
  refine ⟨8 * A / c0 * (4 / a) + A ^ 2 * I0, a / 4, max (2 / a) H2, by positivity,
    fun H hH => ?_⟩
  have hHa : 2 / a ≤ H := (le_max_left _ _).trans hH
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hHa
  have hH2' := hH2 H ((le_max_right _ _).trans hH)
  set Y := periodize y H with hYdef
  have hYc : Continuous Y := continuous_periodize hyc hyA' ha hH0
  have hYp : Function.Periodic Y H := fun s => by
    have := periodize_sub_int_mul y H s (-1)
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add] at this
    exact this
  have hY0 : ∀ s, 0 ≤ Y s := fun s => tsum_nonneg fun m => hy0 _
  have hYb : ∀ s, Y s ≤ b' := fun s => by
    have := periodize_le hyA' ha hyb hHa s
    rw [hb']; linarith
  set Φ : ℝ → ℝ := fun z => 1 - √(1 - z ^ 2) with hΦ
  have hΦc : Continuous Φ :=
    continuous_const.sub (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2)))
  -- step 1: `H - P(H)` is the integral of `Φ(Y)` over the centered cell
  have step1 : H - halfPerimeter y H = ∫ s in (-(H / 2))..(H / 2), Φ (Y s) := by
    have hsq : Continuous fun s => √(1 - Y s ^ 2) :=
      Real.continuous_sqrt.comp (continuous_const.sub (hYc.pow 2))
    have e1 : H - halfPerimeter y H = ∫ s in (0 : ℝ)..H, Φ (Y s) := by
      unfold halfPerimeter
      rw [← hYdef, intervalIntegral.integral_sub _root_.intervalIntegrable_const
        (hsq.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul, mul_one,
        sub_zero]
    have hp : Function.Periodic (fun s => Φ (Y s)) H := fun s => by simp only [hYp s]
    have := hp.intervalIntegral_add_eq (-(H / 2)) 0
    rw [zero_add, show -(H / 2) + H = H / 2 by ring] at this
    rw [e1, ← this]
  -- step 2: compare `Φ(Y)` and `Φ(y)` on the cell
  have step2 : |∫ s in (-(H / 2))..(H / 2), (Φ (Y s) - Φ (y s))| ≤
      H * (8 * A * exp (-(a / 2 * H)) / c0) := by
    rw [← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(H / 2)) (b := H / 2)
      (C := 8 * A * exp (-(a / 2 * H)) / c0) (f := fun s => Φ (Y s) - Φ (y s))
      (fun s hs => ?_)
    · rw [show H / 2 - -(H / 2) = H by ring, abs_of_pos hH0] at this
      linarith
    · rw [Set.uIoc_of_le (by linarith)] at hs
      have hs' : |s| ≤ H / 2 := abs_le.2 ⟨hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, hΦ]
      simp only
      rw [show 1 - √(1 - Y s ^ 2) - (1 - √(1 - y s ^ 2)) =
        √(1 - y s ^ 2) - √(1 - Y s ^ 2) by ring]
      refine (sqrt_one_sub_sq_lipschitz hb'1 (hy0 s) ((hyb s).trans hbb') (hY0 s)
        (hYb s)).trans ?_
      rw [abs_sub_comm]
      exact div_le_div_of_nonneg_right (periodize_sub_le_explicit hyA' ha hHa hs') hc0.le
  -- step 3: the tails of `Δ`
  have hΦy : ∀ t, 0 ≤ Φ (y t) ∧ Φ (y t) ≤ y t ^ 2 := fun t =>
    one_sub_sqrt_bounds (by nlinarith [hy0 t, hyb t])
  have hyint := integrable_of_exp_bound hyc hyA' ha
  have hΦint : Integrable fun t => Φ (y t) := by
    refine hyint.mono' (hΦc.comp hyc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦy t).1]
    nlinarith [hΦy t, hy0 t, hyb t]
  have step3 : |steeringDefect y - ∫ s in (-(H / 2))..(H / 2), Φ (y s)| ≤
      A ^ 2 * I0 * exp (-(a / 2 * H)) := by
    set S := Set.Ioc (-(H / 2)) (H / 2)
    have e : ∫ s in (-(H / 2))..(H / 2), Φ (y s) = ∫ t, S.indicator (fun t => Φ (y t)) t := by
      rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_indicator measurableSet_Ioc]
    have hind : Integrable (S.indicator fun t => Φ (y t)) := hΦint.indicator measurableSet_Ioc
    have e2 : steeringDefect y - ∫ s in (-(H / 2))..(H / 2), Φ (y s) =
        ∫ t, (Φ (y t) - S.indicator (fun t => Φ (y t)) t) := by
      rw [e, integral_sub hΦint hind]; rfl
    have hpt : ∀ t, 0 ≤ Φ (y t) - S.indicator (fun t => Φ (y t)) t ∧
        Φ (y t) - S.indicator (fun t => Φ (y t)) t ≤
          A ^ 2 * exp (-(a / 2 * H)) * exp (-(a * |t|)) := fun t => by
      by_cases ht : t ∈ S
      · rw [Set.indicator_of_mem ht, sub_self]
        exact ⟨le_rfl, by positivity⟩
      · rw [Set.indicator_of_notMem ht, sub_zero]
        refine ⟨(hΦy t).1, (hΦy t).2.trans ?_⟩
        have htH : H / 2 ≤ |t| := by
          simp only [S, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
          rcases ht with ht | ht
          · rw [abs_of_nonpos (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have h1 : y t ^ 2 ≤ (A * exp (-(a * |t|))) ^ 2 := pow_le_pow_left₀ (hy0 t) (hyA t) 2
        have h2 : exp (-(a * |t|)) ≤ exp (-(a / 2 * H)) := Real.exp_le_exp.2 (by nlinarith)
        have h3 : (A * exp (-(a * |t|))) ^ 2 ≤ A ^ 2 * exp (-(a / 2 * H)) * exp (-(a * |t|)) := by
          rw [mul_pow, sq (exp _)]
          have := mul_le_mul_of_nonneg_right h2 (exp_pos (-(a * |t|))).le
          nlinarith [sq_nonneg A]
        linarith
    rw [e2, abs_of_nonneg (integral_nonneg fun t => (hpt t).1)]
    calc ∫ t, (Φ (y t) - S.indicator (fun t => Φ (y t)) t)
        ≤ ∫ t, A ^ 2 * exp (-(a / 2 * H)) * exp (-(a * |t|)) :=
          integral_mono (hΦint.sub hind) (hI0int.const_mul _) fun t => (hpt t).2
      _ = A ^ 2 * I0 * exp (-(a / 2 * H)) := by rw [MeasureTheory.integral_const_mul]; ring
  -- combine
  have hsplit : H - halfPerimeter y H - steeringDefect y =
      (∫ s in (-(H / 2))..(H / 2), (Φ (Y s) - Φ (y s))) -
        (steeringDefect y - ∫ s in (-(H / 2))..(H / 2), Φ (y s)) := by
    rw [step1, intervalIntegral.integral_sub (f := fun s => Φ (Y s)) (g := fun s => Φ (y s))
      ((hΦc.comp hYc).intervalIntegrable _ _)
      ((hΦc.comp hyc).intervalIntegrable _ _)]
    ring
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  have habs := mul_exp_neg_half_le ha H
  have hq : exp (-(a / 2 * H)) ≤ exp (-(a / 4 * H)) := Real.exp_le_exp.2 (by nlinarith)
  have e3 : H * (8 * A * exp (-(a / 2 * H)) / c0) = 8 * A / c0 * (H * exp (-(a / 2 * H))) := by
    ring
  rw [e3] at step2
  have h4 : 8 * A / c0 * (H * exp (-(a / 2 * H))) ≤ 8 * A / c0 * (4 / a * exp (-(a / 4 * H))) :=
    mul_le_mul_of_nonneg_left habs (by positivity)
  have h5 : A ^ 2 * I0 * exp (-(a / 2 * H)) ≤ A ^ 2 * I0 * exp (-(a / 4 * H)) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  nlinarith

end Ovals

end
