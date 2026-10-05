module

public import UnitTangentIterates.FrontError
public import UnitTangentIterates.PerimeterAsymptotics
public import UnitTangentIterates.PeriodizationIntegral

/-!
# The rear half of the curvature matching (Theorem 5.1, estimate (5.4))

Let `y` be the pulse, `c = √(1 - y²)`, and let `x(s) = x₀ + ∫₀ˢ c` be the isolated rear
arclength, so that the isolated rear curvature is `K_*(x(s)) = y(s)/c(s)`, where `K_*` is the
common intrinsic curvature of the isolated rear and front.  For the closed rear `R_H` put
`c_H = √(1 - Y_H²)` and `x_H(s) = x₀ + ∫₀ˢ c_H` (normalized by `x_H(0) = x(0)`); its curvature
is `k_H(x_H(s)) = Y_H(s)/c_H(s)`, and its half-perimeter is `P = P(H) = ∫₀ᴴ c_H`.

By the exact identity `k_H(x_H(s)) dx_H = Y_H(s) ds`, the rear comparison
`‖k_H - K̄_P‖_{L¹(J_H)}`, with `J_H = x_H([-H/2, H/2])` and `K̄_P(u) = ∑_j K_*(u - jP)`, equals

`∫_{-H/2}^{H/2} |Y_H(s) - c_H(s) K̄_P(x_H(s))| ds`,

and we prove that this is `O(e^{-βH})`.
-/

@[expose] public section

namespace Ovals

open Real MeasureTheory intervalIntegral

variable {f : ℝ → ℝ} {A a : ℝ}

/-- A wide cell estimate: for `|u| ≤ 3P/4` and `P ≥ 4/a`,
`|∑_m f(u - mP) - f(u)| ≤ 8 A e^{-aP/4}`. -/
theorem periodize_sub_le_wide (hfA : ∀ t, |f t| ≤ A * exp (-(a * |t|))) (ha : 0 < a)
    {P : ℝ} (hP : 4 / a ≤ P) {u : ℝ} (hu : |u| ≤ 3 * P / 4) :
    |periodize f P u - f u| ≤ 8 * A * exp (-(a / 4 * P)) := by
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  set q : ℝ := exp (-(a / 4 * P)) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q ≤ 1 / 2 := by
    have := exp_neg_half_le ha (H := P / 2) (by rw [div_le_iff₀ ha] at hP ⊢; linarith)
    rw [hq]; convert this using 2; ring
  have hsum := summable_periodize_abs hfA ha hP0 u
  obtain ⟨hgs, hgle⟩ := summable_offzero_geom hq0 hq1
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hfA 0)) (exp_pos _)
  have key : periodize f P u - f u =
      ∑' m : ℤ, (if m = 0 then 0 else f (u - m * P)) := by
    unfold periodize
    rw [hsum.tsum_eq_add_tsum_ite 0]
    simp
  have hshift : ∀ m : ℤ, m ≠ 0 → |f (u - m * P)| ≤ A * q ^ m.natAbs := fun m hm => by
    refine (hfA _).trans (mul_le_mul_of_nonneg_left ?_ hA)
    rw [hq, ← Real.exp_nat_mul, Real.exp_le_exp]
    have hmabs : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hmabs]
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
    have : |(m : ℝ)| * P - |u| ≤ |u - m * P| := by
      have := abs_sub_abs_le_abs_sub (m * P : ℝ) u
      rw [abs_mul, abs_of_pos hP0, abs_sub_comm] at this
      linarith
    have h2 : |(m : ℝ)| * P / 4 ≤ |u - m * P| := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 ha.le]
  have hb : ∀ m : ℤ, ‖(if m = 0 then 0 else f (u - m * P))‖ ≤
      A * (if m = 0 then 0 else q ^ m.natAbs) := fun m => by
    split_ifs with hm
    · simp
    · rw [Real.norm_eq_abs]; exact hshift m hm
  rw [key, ← Real.norm_eq_abs]
  refine (tsum_of_norm_bounded (hgs.mul_left A).hasSum hb).trans ?_
  rw [tsum_mul_left]
  nlinarith

variable {y y' y'' : ℝ → ℝ} {D b : ℝ}

/-- Exponential decay of the isolated curvature `K_* = y + y'/c`. -/
theorem frontCurv_exp_bound (hy : ∀ t, HasDerivAt y (y' t) t) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (hyD : ∀ t, |y' t| ≤ D * y t)
    (hyb : ∀ t, y t ≤ b) (hb : b < 1) :
    ∀ t, |frontCurv y t| ≤ (A + |D| * A / √(1 - b ^ 2)) * exp (-(a * |t|)) := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hb0 : 0 ≤ b := (hy0 0).trans (hyb 0)
  have hy'A : ∀ t, |y' t| ≤ (|D| * A) * exp (-(a * |t|)) := fun t => by
    have h1 : D * y t ≤ |D| * y t := mul_le_mul_of_nonneg_right (le_abs_self D) (hy0 t)
    have h2 : |D| * y t ≤ |D| * (A * exp (-(a * |t|))) :=
      mul_le_mul_of_nonneg_left (hyA t) (abs_nonneg D)
    linarith [hyD t]
  have hpos : 0 < 1 - b ^ 2 := by nlinarith
  have hc0 : 0 < √(1 - b ^ 2) := Real.sqrt_pos.2 hpos
  intro t
  rw [frontCurv, (hy t).deriv]
  have hct : √(1 - b ^ 2) ≤ √(1 - y t ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hyb t, hy0 t])
  have h1 : |y' t / √(1 - y t ^ 2)| ≤ |D| * A * exp (-(a * |t|)) / √(1 - b ^ 2) := by
    rw [abs_div, abs_of_pos (lt_of_lt_of_le hc0 hct)]
    exact div_le_div₀ (by positivity) (hy'A t) hc0 hct
  have h0 : |y t| ≤ A * exp (-(a * |t|)) := by rw [abs_of_nonneg (hy0 t)]; exact hyA t
  calc |y t + y' t / √(1 - y t ^ 2)| ≤ |y t| + |y' t / √(1 - y t ^ 2)| := abs_add_le _ _
    _ ≤ A * exp (-(a * |t|)) + |D| * A * exp (-(a * |t|)) / √(1 - b ^ 2) := add_le_add h0 h1
    _ = (A + |D| * A / √(1 - b ^ 2)) * exp (-(a * |t|)) := by ring

/-- The isolated curvature `K_*` is Lipschitz. -/
theorem frontCurv_lipschitz (hy : ∀ t, HasDerivAt y (y' t) t)
    (hy' : ∀ t, HasDerivAt y' (y'' t) t) (hy0 : ∀ t, 0 ≤ y t)
    (hyD : ∀ t, |y' t| ≤ D * y t) (hyD2 : ∀ t, |y'' t| ≤ D * y t)
    (hyb : ∀ t, y t ≤ b) (hb : b < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, |frontCurv y u - frontCurv y v| ≤ M * |u - v| := by
  have hb0 : 0 ≤ b := (hy0 0).trans (hyb 0)
  have hpos : 0 < 1 - b ^ 2 := by nlinarith
  set c0 := √(1 - b ^ 2) with hc0def
  have hc0 : 0 < c0 := Real.sqrt_pos.2 hpos
  have hsq : ∀ t, 0 < 1 - y t ^ 2 := fun t => by nlinarith [hy0 t, hyb t]
  have hct : ∀ t, c0 ≤ √(1 - y t ^ 2) := fun t =>
    Real.sqrt_le_sqrt (by nlinarith [hyb t, hy0 t])
  have hy1 : ∀ t, y t ≤ 1 := fun t => by linarith [hyb t]
  have hD1 : ∀ t, |y' t| ≤ |D| := fun t =>
    (hyD t).trans (by nlinarith [le_abs_self D, abs_nonneg D, hy0 t, hy1 t])
  have hD2 : ∀ t, |y'' t| ≤ |D| := fun t =>
    (hyD2 t).trans (by nlinarith [le_abs_self D, abs_nonneg D, hy0 t, hy1 t])
  set c : ℝ → ℝ := fun t => √(1 - y t ^ 2) with hcdef
  set g' : ℝ → ℝ := fun t =>
    y' t + (y'' t * c t - y' t * (-(2 * y t * y' t) / (2 * c t))) / c t ^ 2 with hg'
  have hK : frontCurv y = fun t => y t + y' t / c t := funext fun t => by
    rw [frontCurv, (hy t).deriv]
  have hd : ∀ t, HasDerivAt (frontCurv y) (g' t) t := by
    intro t
    rw [hK]
    have hc : HasDerivAt c (-(2 * y t * y' t) / (2 * c t)) t := by
      have h1 : HasDerivAt (fun t => 1 - y t ^ 2) (-(2 * y t * y' t)) t := by
        have := ((hy t).pow 2).const_sub 1
        convert this using 1; push_cast; ring
      exact h1.sqrt (hsq t).ne'
    exact (hy t).add ((hy' t).div hc (Real.sqrt_pos.2 (hsq t)).ne')
  set M := |D| + |D| / c0 + |D| ^ 2 / c0 ^ 3 with hM
  have hbound : ∀ t, |g' t| ≤ M := by
    intro t
    have hct0 : 0 < c t := lt_of_lt_of_le hc0 (hct t)
    have e : g' t = y' t + y'' t / c t + y t * y' t ^ 2 / c t ^ 3 := by
      simp only [hg']; field_simp; ring
    rw [e]
    have t1 : |y'' t / c t| ≤ |D| / c0 := by
      rw [abs_div, abs_of_pos hct0]; exact div_le_div₀ (abs_nonneg _) (hD2 t) hc0 (hct t)
    have t2 : |y t * y' t ^ 2 / c t ^ 3| ≤ |D| ^ 2 / c0 ^ 3 := by
      rw [abs_div, abs_mul, abs_pow, abs_of_pos (pow_pos hct0 3), abs_of_nonneg (hy0 t)]
      refine div_le_div₀ (by positivity) ?_ (pow_pos hc0 3)
        (pow_le_pow_left₀ hc0.le (hct t) 3)
      have := pow_le_pow_left₀ (abs_nonneg _) (hD1 t) 2
      calc y t * |y' t| ^ 2 ≤ 1 * |y' t| ^ 2 :=
            mul_le_mul_of_nonneg_right (hy1 t) (by positivity)
        _ ≤ |D| ^ 2 := by linarith
    calc |y' t + y'' t / c t + y t * y' t ^ 2 / c t ^ 3|
        ≤ |y' t| + |y'' t / c t| + |y t * y' t ^ 2 / c t ^ 3| := abs_add_three _ _ _
      _ ≤ M := by rw [hM]; linarith [hD1 t]
  refine ⟨M, by positivity, fun u v => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := frontCurv y)
    (s := Set.univ) (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hbound x) convex_univ
    (Set.mem_univ v) (Set.mem_univ u)
  simpa [Real.norm_eq_abs] using this

set_option maxHeartbeats 1000000 in
/-- **Theorem 5.1, rear estimate (5.4).**  If the isolated rear has curvature
`K_*(x(s)) = y(s)/c(s)` in its arclength `x(s) = x₀ + ∫₀ˢ c`, then for all large `H`,
with `x_H(s) = x₀ + ∫₀ˢ c_H` and `P = P(H)`,
`∫_{-H/2}^{H/2} |Y_H - c_H K̄_P(x_H)| ≤ C e^{-βH}`. -/
theorem rear_matching (hy : ∀ t, HasDerivAt y (y' t) t)
    (hy' : ∀ t, HasDerivAt y' (y'' t) t) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a)
    (hyD : ∀ t, |y' t| ≤ D * y t) (hyD2 : ∀ t, |y'' t| ≤ D * y t)
    (hyb : ∀ t, y t ≤ b) (hb : b < 1) (x₀ : ℝ)
    (hKx : ∀ s, frontCurv y (x₀ + ∫ r in (0 : ℝ)..s, √(1 - y r ^ 2)) =
      y s / √(1 - y s ^ 2)) :
    ∃ C β H₀ : ℝ, 0 < β ∧ ∀ H ≥ H₀,
      ∫ s in (-H / 2)..(H / 2), |periodize y H s - √(1 - periodize y H s ^ 2) *
          periodize (frontCurv y) (halfPerimeter y H)
            (x₀ + ∫ r in (0 : ℝ)..s, √(1 - periodize y H r ^ 2))| ≤
        C * exp (-(β * H)) := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hb0 : 0 ≤ b := (hy0 0).trans (hyb 0)
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  set A' := A + |D| * A / √(1 - b ^ 2) with hA'def
  have hKA := frontCurv_exp_bound hy hy0 hyA hyD hyb hb
  rw [← hA'def] at hKA
  have hA' : 0 ≤ A' := by rw [hA'def]; positivity
  obtain ⟨M₁, hM₁, hLip⟩ := frontCurv_lipschitz hy hy' hy0 hyD hyD2 hyb hb
  set b' := (1 + b) / 2 with hb'def
  have hb' : b' < 1 := by rw [hb'def]; linarith
  have hb'0 : 0 ≤ b' := by rw [hb'def]; linarith
  set c0 := √(1 - b' ^ 2) with hc0def
  have hc0 : 0 < c0 := Real.sqrt_pos.2 (by nlinarith)
  set Mt := ∫ t, y t with hMt
  have hMt0 : 0 ≤ Mt := integral_nonneg hy0
  have hexp : ∀ {r : ℝ}, 0 < r → Filter.Tendsto (fun H : ℝ => exp (-(r * H))) Filter.atTop
      (nhds 0) :=
    fun hr => Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop hr)
  have ha2 : (0 : ℝ) < a / 2 := by positivity
  have t2 : Filter.Tendsto (fun H : ℝ => 8 * A * exp (-(a / 2 * H))) Filter.atTop
      (nhds (8 * A * 0)) := (hexp ha2).const_mul _
  rw [mul_zero] at t2
  obtain ⟨H₁, hH₁⟩ := Filter.eventually_atTop.1
    (t2.eventually (gt_mem_nhds (show (0 : ℝ) < (1 - b) / 2 by linarith)))
  set C : ℝ := (8 * A + 8 * A * A' / c0) * (8 / a) + (4 * A * M₁ / c0) * (8 / a) ^ 2 +
    8 * A' * exp (a / 4 * Mt) * (8 / a) with hC
  refine ⟨C, a / 8, max (max (2 / a) H₁) (max (4 / a + Mt) (4 * |x₀| + 3 * Mt)),
    by positivity, fun H hH => ?_⟩
  have hHa : 2 / a ≤ H := (le_max_left _ _).trans ((le_max_left _ _).trans hH)
  have hH1 : H₁ ≤ H := (le_max_right _ _).trans ((le_max_left _ _).trans hH)
  have hH2 : 4 / a + Mt ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hH3 : 4 * |x₀| + 3 * Mt ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hHa
  set E := 8 * A * exp (-(a / 2 * H)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hEb : E < (1 - b) / 2 := hH₁ H hH1
  set Y := periodize y H with hYdef
  set P := halfPerimeter y H with hPdef
  set K := frontCurv y with hKdef
  have hYc : Continuous Y := continuous_periodize hyc hyA' ha hH0
  have hY0 : ∀ s, 0 ≤ Y s := fun s => tsum_nonneg fun m => hy0 _
  have hYb' : ∀ s, Y s ≤ b' := fun s => by
    have := periodize_le hyA' ha hyb hHa s
    rw [hb'def]; linarith
  have hcH1 : ∀ s, √(1 - Y s ^ 2) ≤ 1 := fun s => by
    rw [Real.sqrt_le_one]; nlinarith [hY0 s]
  have hcHc : Continuous (fun s => √(1 - Y s ^ 2)) := by fun_prop
  have hcc : Continuous (fun s => √(1 - y s ^ 2)) := by fun_prop
  -- lower bound on the half-perimeter
  have hPlow : H - Mt ≤ P := by
    have h1 : ∫ s in (0 : ℝ)..H, (1 - Y s) ≤ P :=
      intervalIntegral.integral_mono_on hH0.le ((continuous_const.sub hYc).intervalIntegrable _ _)
        (hcHc.intervalIntegrable _ _) fun s _ => by
          have hYs1 : Y s ≤ 1 := (hYb' s).trans hb'.le
          exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [hY0 s]))
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const (hYc.intervalIntegrable _ _),
      hYdef, integral_periodize hyc hyA' ha hH0] at h1
    simpa using h1
  have hP4 : 4 / a ≤ P := by linarith
  -- pointwise estimate on the cell
  have hpt : ∀ s, |s| ≤ H / 2 →
      |Y s - √(1 - Y s ^ 2) * periodize K P (x₀ + ∫ r in (0 : ℝ)..s, √(1 - Y r ^ 2))| ≤
        E + E * A' / c0 + M₁ * (E / c0 * (H / 2)) + 8 * A' * exp (a / 4 * Mt) *
          exp (-(a / 4 * H)) := by
    intro s hs
    set xH := x₀ + ∫ r in (0 : ℝ)..s, √(1 - Y r ^ 2) with hxH
    set x := x₀ + ∫ r in (0 : ℝ)..s, √(1 - y r ^ 2) with hx
    have hsub : ∀ t ∈ Set.uIoc (0 : ℝ) s, |t| ≤ H / 2 := fun t ht => by
      rcases Set.mem_uIoc.1 ht with h | h
      · rw [abs_le] at hs ⊢; constructor <;> linarith [h.1, h.2]
      · rw [abs_le] at hs ⊢; constructor <;> linarith [h.1, h.2]
    have hcdiff : ∀ t, |t| ≤ H / 2 → |√(1 - y t ^ 2) - √(1 - Y t ^ 2)| ≤ E / c0 := fun t ht => by
      have h1 := sqrt_one_sub_sq_lipschitz hb' (hy0 t)
        (by rw [hb'def]; linarith [hyb t]) (hY0 t) (hYb' t)
      have h2 := periodize_sub_le_explicit hyA' ha hHa ht
      rw [abs_sub_comm] at h2
      exact h1.trans (div_le_div_of_nonneg_right h2 hc0.le)
    -- `x` and `x_H` are close
    have hxx : |x - xH| ≤ E / c0 * (H / 2) := by
      have e : x - xH = ∫ r in (0 : ℝ)..s, (√(1 - y r ^ 2) - √(1 - Y r ^ 2)) := by
        rw [hx, hxH, intervalIntegral.integral_sub (hcc.intervalIntegrable _ _)
          (hcHc.intervalIntegrable _ _)]; ring
      rw [e, ← Real.norm_eq_abs]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := E / c0) fun t ht => ?_).trans ?_
      · rw [Real.norm_eq_abs]; exact hcdiff t (hsub t ht)
      · rw [sub_zero]; exact mul_le_mul_of_nonneg_left hs (by positivity)
    -- `x_H` lies in the wide cell
    have hxHb : |xH| ≤ 3 * P / 4 := by
      have h1 : ‖∫ r in (0 : ℝ)..s, √(1 - Y r ^ 2)‖ ≤ 1 * |s - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; exact hcH1 t
      rw [Real.norm_eq_abs, one_mul, sub_zero] at h1
      calc |xH| ≤ |x₀| + |∫ r in (0 : ℝ)..s, √(1 - Y r ^ 2)| := abs_add_le _ _
        _ ≤ 3 * P / 4 := by linarith
    have hwide := periodize_sub_le_wide hKA ha hP4 hxHb
    have hwide' : 8 * A' * exp (-(a / 4 * P)) ≤
        8 * A' * exp (a / 4 * Mt) * exp (-(a / 4 * H)) := by
      have h1 : exp (-(a / 4 * P)) ≤ exp (a / 4 * Mt) * exp (-(a / 4 * H)) := by
        rw [← Real.exp_add]
        have := mul_le_mul_of_nonneg_left hPlow (show 0 ≤ a / 4 by positivity)
        exact Real.exp_le_exp.2 (by linarith)
      calc 8 * A' * exp (-(a / 4 * P)) ≤ 8 * A' * (exp (a / 4 * Mt) * exp (-(a / 4 * H))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by ring
    -- the isolated identity `y = c K(x)`
    have hcpos : 0 < √(1 - y s ^ 2) := Real.sqrt_pos.2 (sub_pos.2
      (pow_lt_one₀ (hy0 s) (by linarith [hyb s]) two_ne_zero))
    have hyx : y s = √(1 - y s ^ 2) * K x := by
      have h1 := hKx s
      rw [← hx] at h1
      rw [h1, mul_div_cancel₀ _ hcpos.ne']
    have hKx1 : |K x| ≤ A' := (hKA x).trans (mul_le_of_le_one_right hA'
      (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha.le (abs_nonneg x)))))
    have hYy := periodize_sub_le_explicit hyA' ha hHa hs
    have hcd := hcdiff s hs
    have hcH0 : 0 ≤ √(1 - Y s ^ 2) := Real.sqrt_nonneg _
    have key : Y s - √(1 - Y s ^ 2) * periodize K P xH =
        (Y s - y s) + (√(1 - y s ^ 2) - √(1 - Y s ^ 2)) * K x +
          √(1 - Y s ^ 2) * (K x - K xH) - √(1 - Y s ^ 2) * (periodize K P xH - K xH) := by
      linear_combination hyx
    rw [key]
    have i1 : |(√(1 - y s ^ 2) - √(1 - Y s ^ 2)) * K x| ≤ E * A' / c0 := by
      rw [abs_mul, mul_div_right_comm]
      exact mul_le_mul hcd hKx1 (abs_nonneg _) (by positivity)
    have i2 : |√(1 - Y s ^ 2) * (K x - K xH)| ≤ M₁ * (E / c0 * (H / 2)) := by
      rw [abs_mul, abs_of_nonneg hcH0]
      calc √(1 - Y s ^ 2) * |K x - K xH| ≤ 1 * |K x - K xH| :=
            mul_le_mul_of_nonneg_right (hcH1 s) (abs_nonneg _)
        _ ≤ M₁ * |x - xH| := by rw [one_mul]; exact hLip x xH
        _ ≤ M₁ * (E / c0 * (H / 2)) := mul_le_mul_of_nonneg_left hxx hM₁
    have i3 : |√(1 - Y s ^ 2) * (periodize K P xH - K xH)| ≤
        8 * A' * exp (a / 4 * Mt) * exp (-(a / 4 * H)) := by
      rw [abs_mul, abs_of_nonneg hcH0]
      calc √(1 - Y s ^ 2) * |periodize K P xH - K xH| ≤ 1 * |periodize K P xH - K xH| :=
            mul_le_mul_of_nonneg_right (hcH1 s) (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hwide.trans hwide'
    calc |(Y s - y s) + (√(1 - y s ^ 2) - √(1 - Y s ^ 2)) * K x +
          √(1 - Y s ^ 2) * (K x - K xH) - √(1 - Y s ^ 2) * (periodize K P xH - K xH)|
        ≤ |Y s - y s| + |(√(1 - y s ^ 2) - √(1 - Y s ^ 2)) * K x| +
          |√(1 - Y s ^ 2) * (K x - K xH)| +
          |√(1 - Y s ^ 2) * (periodize K P xH - K xH)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_three _ _ _
      _ ≤ _ := by linarith
  set Bp := E + E * A' / c0 + M₁ * (E / c0 * (H / 2)) + 8 * A' * exp (a / 4 * Mt) *
    exp (-(a / 4 * H)) with hBp
  have hint : ∫ s in (-H / 2)..(H / 2), |Y s - √(1 - Y s ^ 2) *
      periodize K P (x₀ + ∫ r in (0 : ℝ)..s, √(1 - Y r ^ 2))| ≤ Bp * H := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -H / 2) (b := H / 2)
      (C := Bp) (f := fun s => |Y s - √(1 - Y s ^ 2) *
        periodize K P (x₀ + ∫ r in (0 : ℝ)..s, √(1 - Y r ^ 2))|) (fun s hs => by
          rw [Real.norm_eq_abs, abs_abs]
          rw [Set.uIoc_of_le (by linarith)] at hs
          exact hpt s (abs_le.2 ⟨by linarith [hs.1], hs.2⟩))
    rw [show H / 2 - -H / 2 = H by ring, abs_of_pos hH0, Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1
  refine hint.trans ?_
  set e2 := exp (-(a / 2 * H)) with he2
  set e4 := exp (-(a / 4 * H)) with he4
  set e8 := exp (-(a / 8 * H)) with he8
  have he8_1 : e8 ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
  have he8_0 : 0 ≤ e8 := (exp_pos _).le
  have hHe4 : H * e4 ≤ 8 / a * e8 := by
    have h := mul_exp_neg_half_le ha2 H
    have e1 : a / 2 / 2 * H = a / 4 * H := by ring
    have e2' : a / 2 / 4 * H = a / 8 * H := by ring
    have e3 : 4 / (a / 2) = 8 / a := by field_simp; norm_num
    rw [e1, e2', e3] at h
    exact h
  have hHe2 : H * e2 ≤ H * e4 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by have := mul_pos ha hH0; linarith)) hH0.le
  have hH2e2 : H ^ 2 * e2 ≤ (8 / a) ^ 2 * e8 := by
    have e : H ^ 2 * e2 = (H * e4) ^ 2 := by
      rw [he2, he4, mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [e]
    have h0 : 0 ≤ H * e4 := by positivity
    calc (H * e4) ^ 2 ≤ (8 / a * e8) ^ 2 := pow_le_pow_left₀ h0 hHe4 2
      _ = (8 / a) ^ 2 * (e8 * e8) := by ring
      _ ≤ (8 / a) ^ 2 * (e8 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he8_1 he8_0) (by positivity)
      _ = (8 / a) ^ 2 * e8 := by ring
  have hexpand : Bp * H = (8 * A + 8 * A * A' / c0) * (H * e2) +
      (4 * A * M₁ / c0) * (H ^ 2 * e2) + 8 * A' * exp (a / 4 * Mt) * (H * e4) := by
    rw [hBp, hE]; field_simp; ring
  rw [hexpand, hC]
  have k1 : (8 * A + 8 * A * A' / c0) * (H * e2) ≤ (8 * A + 8 * A * A' / c0) * (8 / a * e8) :=
    mul_le_mul_of_nonneg_left (hHe2.trans hHe4) (by positivity)
  have k2 : (4 * A * M₁ / c0) * (H ^ 2 * e2) ≤ (4 * A * M₁ / c0) * ((8 / a) ^ 2 * e8) :=
    mul_le_mul_of_nonneg_left hH2e2 (by positivity)
  have k3 : 8 * A' * exp (a / 4 * Mt) * (H * e4) ≤ 8 * A' * exp (a / 4 * Mt) * (8 / a * e8) :=
    mul_le_mul_of_nonneg_left hHe4 (by positivity)
  have : ((8 * A + 8 * A * A' / c0) * (8 / a) + 4 * A * M₁ / c0 * (8 / a) ^ 2 +
      8 * A' * exp (a / 4 * Mt) * (8 / a)) * e8 =
      (8 * A + 8 * A * A' / c0) * (8 / a * e8) + (4 * A * M₁ / c0) * ((8 / a) ^ 2 * e8) +
        8 * A' * exp (a / 4 * Mt) * (8 / a * e8) := by ring
  linarith

end Ovals

end
