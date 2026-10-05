module

public import UnitTangentIterates.RearMatching
public import UnitTangentIterates.FrontMatching

/-!
# Theorem 5.1: matching intrinsic curvatures

Combining the rear estimate (5.4) (`rear_matching`) with the front estimate (5.6)
(`front_matching`): for all large `H`, the curvature `k_H` of the closed rear `R_H`, as a
function of its arclength `u`, and the curvature `K_P` of the closed front `F_P`, `P = P(H)`,
satisfy

`∫_{J_H} |k_H(u) - K_P(u)| du ≤ C e^{-βH}`,

where `J_H = x_H([-H/2, H/2])` is an interval of length `P`, i.e. a fundamental domain of
`ℝ/Pℤ`.  Here the rear arclength is `x_H(s) = x₀ + ∫₀ˢ c_H`, and `k_H` is characterized by
`k_H(x_H(s)) = Y_H(s)/c_H(s)`.
-/

@[expose] public section

namespace Ovals

open Real MeasureTheory intervalIntegral

variable {y y' y'' : ℝ → ℝ} {A a D b : ℝ}

/-- The half-perimeter is at least `H - ∫ y`. -/
theorem halfPerimeter_ge (hyc : Continuous y) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a) {H : ℝ} (hH : 0 < H)
    (hY1 : ∀ s, periodize y H s ≤ 1) :
    H - ∫ t, y t ≤ halfPerimeter y H := by
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hYc : Continuous (periodize y H) := continuous_periodize hyc hyA' ha hH
  have hY0 : ∀ s, 0 ≤ periodize y H s := fun s => tsum_nonneg fun m => hy0 _
  have h1 : ∫ s in (0 : ℝ)..H, (1 - periodize y H s) ≤ halfPerimeter y H :=
    intervalIntegral.integral_mono_on hH.le ((continuous_const.sub hYc).intervalIntegrable _ _)
      ((Real.continuous_sqrt.comp (continuous_const.sub (hYc.pow 2))).intervalIntegrable _ _)
      fun s _ => (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [hY0 s, hY1 s]))
  rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const (hYc.intervalIntegrable _ _),
    integral_periodize hyc hyA' ha hH] at h1
  simpa using h1

/-- The front curvature of the periodization and the periodized isolated curvature are both
`L`-periodic. -/
theorem periodic_front_defect (hy : ∀ t, HasDerivAt y (y' t) t) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a) (hyD : ∀ t, |y' t| ≤ D * y t)
    {L : ℝ} (hL : 0 < L) :
    Function.Periodic (fun u => |frontCurv (periodize y L) u - periodize (frontCurv y) L u|) L := by
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hy'A : ∀ t, |y' t| ≤ (|D| * A) * exp (-(a * |t|)) := fun t => by
    have h1 : D * y t ≤ |D| * y t := mul_le_mul_of_nonneg_right (le_abs_self D) (hy0 t)
    have h2 : |D| * y t ≤ |D| * (A * exp (-(a * |t|))) :=
      mul_le_mul_of_nonneg_left (hyA t) (abs_nonneg D)
    linarith [hyD t]
  have hYd : ∀ t, HasDerivAt (periodize y L) (periodize y' L t) t :=
    hasDerivAt_periodize hy hyA' hy'A ha hL
  have hper : ∀ (g : ℝ → ℝ) (u : ℝ), periodize g L (u + L) = periodize g L u := fun g u => by
    have := periodize_sub_int_mul g L (u + L) 1
    simp only [Int.cast_one, one_mul, add_sub_cancel_right] at this
    exact this.symm
  intro u
  simp only
  rw [frontCurv, frontCurv, (hYd (u + L)).deriv, (hYd u).deriv, hper, hper, hper]

/-- **Theorem 5.1 (matching intrinsic curvatures).**  For all large `H`, with `P = P(H)` and
`x_H(s) = x₀ + ∫₀ˢ c_H`, the interval `J_H = [x_H(-H/2), x_H(H/2)]` has length `P`, and every
continuous `k` with `k(x_H(s)) = Y_H(s)/c_H(s)` (the curvature of the closed rear in its
arclength) satisfies `∫_{J_H} |k - K_P| ≤ C e^{-βH}`, where `K_P` is the curvature of the closed
front of half-perimeter `P`. -/
theorem curvature_matching (hy : ∀ t, HasDerivAt y (y' t) t)
    (hy' : ∀ t, HasDerivAt y' (y'' t) t) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a)
    (hyD : ∀ t, |y' t| ≤ D * y t) (hyD2 : ∀ t, |y'' t| ≤ D * y t)
    (hyb : ∀ t, y t ≤ b) (hb : b < 1) (x₀ : ℝ)
    (hKx : ∀ s, frontCurv y (x₀ + ∫ r in (0 : ℝ)..s, √(1 - y r ^ 2)) =
      y s / √(1 - y s ^ 2)) :
    ∃ C β H₀ : ℝ, 0 < β ∧ ∀ H ≥ H₀,
      (x₀ + ∫ r in (0 : ℝ)..(H / 2), √(1 - periodize y H r ^ 2)) -
          (x₀ + ∫ r in (0 : ℝ)..(-H / 2), √(1 - periodize y H r ^ 2)) = halfPerimeter y H ∧
      ∀ k : ℝ → ℝ, Continuous k →
        (∀ s, k (x₀ + ∫ r in (0 : ℝ)..s, √(1 - periodize y H r ^ 2)) =
          periodize y H s / √(1 - periodize y H s ^ 2)) →
        ∫ u in (x₀ + ∫ r in (0 : ℝ)..(-H / 2), √(1 - periodize y H r ^ 2))..
            (x₀ + ∫ r in (0 : ℝ)..(H / 2), √(1 - periodize y H r ^ 2)),
          |k u - frontCurv (periodize y (halfPerimeter y H)) u| ≤ C * exp (-(β * H)) := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hb0 : 0 ≤ b := (hy0 0).trans (hyb 0)
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hy'A : ∀ t, |y' t| ≤ (|D| * A) * exp (-(a * |t|)) := fun t => by
    have h1 : D * y t ≤ |D| * y t := mul_le_mul_of_nonneg_right (le_abs_self D) (hy0 t)
    have h2 : |D| * y t ≤ |D| * (A * exp (-(a * |t|))) :=
      mul_le_mul_of_nonneg_left (hyA t) (abs_nonneg D)
    linarith [hyD t]
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  have hy'c : Continuous y' := continuous_iff_continuousAt.2 fun t => (hy' t).continuousAt
  have hsq : ∀ t, 0 < 1 - y t ^ 2 := fun t =>
    sub_pos.2 (pow_lt_one₀ (hy0 t) (by linarith [hyb t]) two_ne_zero)
  have hKc : Continuous (frontCurv y) := by
    have e : frontCurv y = fun t => y t + y' t / √(1 - y t ^ 2) := funext fun t => by
      rw [frontCurv, (hy t).deriv]
    rw [e]
    exact hyc.add (hy'c.div (by fun_prop) fun t => (Real.sqrt_pos.2 (hsq t)).ne')
  have hKA := frontCurv_exp_bound hy hy0 hyA hyD hyb hb
  set Mt := ∫ t, y t with hMt
  have hMt0 : 0 ≤ Mt := integral_nonneg hy0
  obtain ⟨C₁, β₁, H₁, hβ₁, hrear⟩ := rear_matching hy hy' hy0 hyA ha hyD hyD2 hyb hb x₀ hKx
  obtain ⟨C₂, β₂, L₂, hβ₂, hfront⟩ := front_matching hy hy'c hy0 hyA ha hyD hyb hb
  have ha2 : (0 : ℝ) < a / 2 := by positivity
  have t2 : Filter.Tendsto (fun H : ℝ => 8 * A * exp (-(a / 2 * H))) Filter.atTop
      (nhds (8 * A * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop ha2)).const_mul _
  rw [mul_zero] at t2
  obtain ⟨H₃, hH₃⟩ := Filter.eventually_atTop.1
    (t2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 - b by linarith)))
  set β := min β₁ β₂ with hβ
  refine ⟨|C₁| + |C₂| * Mt * exp (β₂ * Mt), β, max (max H₁ (|L₂| + Mt + 1))
    (2 * Mt + max (2 / a) H₃), lt_min hβ₁ hβ₂, fun H hH => ?_⟩
  have hHH₁ : H₁ ≤ H := (le_max_left _ _).trans ((le_max_left _ _).trans hH)
  have hHL : |L₂| + Mt + 1 ≤ H := (le_max_right _ _).trans ((le_max_left _ _).trans hH)
  have hHa : 2 * Mt + max (2 / a) H₃ ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := by linarith [abs_nonneg L₂]
  -- the periodization stays below one
  have hYlt : ∀ L, Mt + max (2 / a) H₃ ≤ L → ∀ s, periodize y L s < 1 := fun L hL s => by
    have h1 := periodize_le hyA' ha hyb ((le_max_left _ _).trans (by linarith)) s (H := L)
    have h2 := hH₃ L ((le_max_right _ _).trans (by linarith))
    linarith
  have hY0 : ∀ L s, 0 ≤ periodize y L s := fun L s => tsum_nonneg fun m => hy0 _
  set P := halfPerimeter y H with hPdef
  have hPge : H - Mt ≤ P :=
    halfPerimeter_ge hyc hy0 hyA ha hH0 fun s => (hYlt H (by linarith) s).le
  have hP0 : 0 < P := by linarith [abs_nonneg L₂]
  have hPL : L₂ ≤ P := by linarith [le_abs_self L₂]
  set Y := periodize y H with hYdef
  set cH : ℝ → ℝ := fun s => √(1 - Y s ^ 2) with hcH
  have hYc : Continuous Y := continuous_periodize hyc hyA' ha hH0
  have hcHc : Continuous cH := by fun_prop
  have hcHpos : ∀ s, 0 < cH s := fun s => Real.sqrt_pos.2
    (sub_pos.2 (pow_lt_one₀ (hY0 H s) (hYlt H (by linarith) s) two_ne_zero))
  have hcHp : Function.Periodic cH H := fun s => by
    simp only [hcH, hYdef]
    have := periodize_sub_int_mul y H (s + H) 1
    simp only [Int.cast_one, one_mul, add_sub_cancel_right] at this
    rw [this]
  set xH : ℝ → ℝ := fun s => x₀ + ∫ r in (0 : ℝ)..s, cH r with hxH
  have hxHd : ∀ s, HasDerivAt xH (cH s) s := fun s =>
    (intervalIntegral.integral_hasDerivAt_right (hcHc.intervalIntegrable _ _)
      (hcHc.stronglyMeasurableAtFilter _ _) hcHc.continuousAt).const_add x₀
  have hlen : xH (H / 2) - xH (-H / 2) = P := by
    simp only [hxH]
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      (hcHc.intervalIntegrable _ _) (hcHc.intervalIntegrable _ _)]
    have := hcHp.intervalIntegral_add_eq (-H / 2) 0
    rw [show -H / 2 + H = H / 2 by ring, zero_add] at this
    rw [this, hPdef, halfPerimeter]
  refine ⟨hlen, fun k hkc hk => ?_⟩
  set Kbar := periodize (frontCurv y) P with hKbar
  set KP := frontCurv (periodize y P) with hKP
  have hKbarc : Continuous Kbar := continuous_periodize hKc hKA ha hP0
  have hKPc : Continuous KP := by
    have hYPd : ∀ t, HasDerivAt (periodize y P) (periodize y' P t) t :=
      hasDerivAt_periodize hy hyA' hy'A ha hP0
    have e : KP = fun u => periodize y P u + periodize y' P u /
        √(1 - periodize y P u ^ 2) := funext fun u => by
      rw [hKP, frontCurv, (hYPd u).deriv]
    rw [e]
    have hYPc : Continuous (periodize y P) := continuous_periodize hyc hyA' ha hP0
    exact hYPc.add ((continuous_periodize hy'c hy'A ha hP0).div (by fun_prop)
      fun u => (Real.sqrt_pos.2 (sub_pos.2 (pow_lt_one₀ (hY0 P u)
        (hYlt P (by linarith) u) two_ne_zero))).ne')
  have hle : xH (-H / 2) ≤ xH (H / 2) := by linarith
  -- triangle inequality
  have htri : ∫ u in xH (-H / 2)..xH (H / 2), |k u - KP u| ≤
      (∫ u in xH (-H / 2)..xH (H / 2), |k u - Kbar u|) +
        ∫ u in xH (-H / 2)..xH (H / 2), |KP u - Kbar u| := by
    rw [← intervalIntegral.integral_add ((hkc.sub hKbarc).abs.intervalIntegrable _ _)
      ((hKPc.sub hKbarc).abs.intervalIntegrable _ _)]
    refine intervalIntegral.integral_mono_on hle ((hkc.sub hKPc).abs.intervalIntegrable _ _)
      (((hkc.sub hKbarc).abs.add (hKPc.sub hKbarc).abs).intervalIntegrable _ _)
      fun u _ => ?_
    calc |k u - KP u| = |(k u - Kbar u) - (KP u - Kbar u)| := by ring_nf
      _ ≤ |k u - Kbar u| + |KP u - Kbar u| := abs_sub _ _
  -- the rear part, by change of variables
  have hrear' : ∫ u in xH (-H / 2)..xH (H / 2), |k u - Kbar u| ≤ C₁ * exp (-(β₁ * H)) := by
    have hcv := intervalIntegral.integral_comp_mul_deriv (a := -H / 2) (b := H / 2)
      (f := xH) (f' := cH) (g := fun u => |k u - Kbar u|) (fun s _ => hxHd s)
      hcHc.continuousOn (hkc.sub hKbarc).abs
    rw [← hcv]
    refine le_of_eq_of_le (intervalIntegral.integral_congr fun s _ => ?_) (hrear H hHH₁)
    simp only [Function.comp, hxH]
    rw [hk s, ← abs_of_pos (hcHpos s), ← abs_mul]
    congr 1
    show (Y s / cH s - Kbar (xH s)) * cH s = Y s - cH s * Kbar (xH s)
    rw [sub_mul, div_mul_cancel₀ _ (hcHpos s).ne']
    ring
  -- the front part, by periodicity
  have hfront' : ∫ u in xH (-H / 2)..xH (H / 2), |KP u - Kbar u| ≤
      C₂ * exp (-(β₂ * P)) * Mt := by
    have hper := periodic_front_defect hy hy0 hyA ha hyD hP0
    have e := hper.intervalIntegral_add_eq (xH (-H / 2)) 0
    rw [zero_add, show xH (-H / 2) + P = xH (H / 2) by linarith] at e
    rw [e]
    exact hfront P hPL
  -- constants
  have hb1 : C₁ * exp (-(β₁ * H)) ≤ |C₁| * exp (-(β * H)) :=
    mul_le_mul (le_abs_self _) (Real.exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_right (min_le_left β₁ β₂) hH0.le; linarith))
      (exp_pos _).le (abs_nonneg _)
  have hb2 : C₂ * exp (-(β₂ * P)) * Mt ≤ |C₂| * Mt * exp (β₂ * Mt) * exp (-(β * H)) := by
    have h1 : exp (-(β₂ * P)) ≤ exp (β₂ * Mt) * exp (-(β * H)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hPge hβ₂.le
      have := mul_le_mul_of_nonneg_right (min_le_right β₁ β₂) hH0.le
      linarith
    calc C₂ * exp (-(β₂ * P)) * Mt ≤ |C₂| * exp (-(β₂ * P)) * Mt :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
            (exp_pos _).le) hMt0
      _ ≤ |C₂| * (exp (β₂ * Mt) * exp (-(β * H))) * Mt :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) hMt0
      _ = |C₂| * Mt * exp (β₂ * Mt) * exp (-(β * H)) := by ring
  have hgoal := htri.trans (add_le_add (hrear'.trans hb1) (hfront'.trans hb2))
  simp only [hxH] at hgoal
  refine hgoal.trans (le_of_eq ?_)
  ring

end Ovals

end
