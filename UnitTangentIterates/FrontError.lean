module

public import UnitTangentIterates.PeriodizationEstimates

/-!
# The front-curvature error of the periodized pulse (Lemma 4.2)

For a steering profile `y = sin δ` (with `c = √(1 - y²)`), the front curvature is
`K = y + y'/c` (equation (3.10)/(4.3) of the paper).  We write `frontCurv Y` for this
expression built from a function `Y`.  For the periodization `Y_L` of a pulse `y`,
Lemma 4.2 compares `K_L = frontCurv Y_L` with the periodization of the isolated curvature
`K_* = frontCurv y`:

`|K_L(s) - ∑_m K_*(s - mL)| ≤ C e^{-βL} Y_L(s)`.

The pulse is abstract: we assume `0 ≤ y ≤ b < 1`, `y ≤ A e^{-a|t|}`, and the relative
derivative bound `|y'| ≤ D y` (these are the properties of Lemma 3.5 used in the proof).
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- The front curvature `K = Y + Y' / √(1 - Y²)` determined by a steering profile
`Y = sin δ`. -/
noncomputable def frontCurv (Y : ℝ → ℝ) (s : ℝ) : ℝ := Y s + deriv Y s / √(1 - Y s ^ 2)

/-- `G(z) = (1 - z²)^{-1/2}` is Lipschitz on `[0, b]`, `b < 1`. -/
lemma inv_sqrt_one_sub_sq_lipschitz {b u v : ℝ} (hb : b < 1) (hu0 : 0 ≤ u)
    (hub : u ≤ b) (hv0 : 0 ≤ v) (hvb : v ≤ b) :
    |1 / √(1 - u ^ 2) - 1 / √(1 - v ^ 2)| ≤ |u - v| / √(1 - b ^ 2) ^ 3 := by
  have hb0 : 0 ≤ b := hu0.trans hub
  have hpos : 0 < 1 - b ^ 2 := by nlinarith
  set c0 := √(1 - b ^ 2) with hc0def
  set cu := √(1 - u ^ 2) with hcudef
  set cv := √(1 - v ^ 2) with hcvdef
  have hc0 : 0 < c0 := Real.sqrt_pos.2 hpos
  have hcu0 : c0 ≤ cu := Real.sqrt_le_sqrt (by nlinarith)
  have hcv0 : c0 ≤ cv := Real.sqrt_le_sqrt (by nlinarith)
  have hcu : 0 < cu := hc0.trans_le hcu0
  have hcv : 0 < cv := hc0.trans_le hcv0
  have hcu2 : cu ^ 2 = 1 - u ^ 2 := Real.sq_sqrt (by nlinarith)
  have hcv2 : cv ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by nlinarith)
  have h1 : |cv - cu| * (cu + cv) = |u - v| * (u + v) := by
    rw [← abs_of_pos (show 0 < cu + cv by linarith), ← abs_mul,
      ← abs_of_nonneg (show 0 ≤ u + v by linarith), ← abs_mul]
    congr 1; nlinarith
  have h2 : |cv - cu| ≤ |u - v| / c0 := by
    rw [le_div_iff₀ hc0]
    have : |cv - cu| * (2 * c0) ≤ |cv - cu| * (cu + cv) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have : |u - v| * (u + v) ≤ |u - v| * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith
  have h3 : 1 / cu - 1 / cv = (cv - cu) / (cu * cv) := by field_simp
  rw [h3, abs_div, abs_of_pos (mul_pos hcu hcv)]
  calc |cv - cu| / (cu * cv) ≤ (|u - v| / c0) / (c0 * c0) :=
        div_le_div₀ (by positivity) h2 (by positivity) (mul_le_mul hcu0 hcv0 hc0.le hcu.le)
    _ = |u - v| / c0 ^ 3 := by field_simp

section

variable {y y' : ℝ → ℝ} {A a D b : ℝ}

/-- The cross-term identity: `∑_m y_m (Y - y_m) = ∑_{m ≠ n} y_m y_n` for a nonnegative
summable family `y_m` with sum `Y`. -/
lemma tsum_mul_sub_eq_offdiag {w : ℤ → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w)
    (hoff : Summable (fun p : ℤ × ℤ => if p.1 ≠ p.2 then |w p.1| * |w p.2| else 0)) :
    ∑' m, w m * (∑' n, w n - w m) =
      ∑' p : ℤ × ℤ, (if p.1 ≠ p.2 then |w p.1| * |w p.2| else 0) := by
  rw [hoff.tsum_prod]
  congr 1; ext m
  rw [hw.tsum_eq_add_tsum_ite m, add_sub_cancel_left, ← tsum_mul_left]
  congr 1; ext n
  simp only [abs_of_nonneg (hw0 _)]
  by_cases h : n = m
  · simp [h]
  · simp [h, Ne.symm h]

/-- **Lemma 4.2 (front error).**  Let `y` be a differentiable pulse with `0 ≤ y ≤ b < 1`,
exponential decay `y(t) ≤ A e^{-a|t|}` and relative derivative bound `|y'| ≤ D y`.
Then for all sufficiently large `L` and all `s`, the series `∑_m K_*(s - mL)` converges and
`|K_L(s) - ∑_m K_*(s - mL)| ≤ C e^{-βL} Y_L(s)`, where `K_* = frontCurv y` and
`K_L = frontCurv Y_L` with `Y_L = periodize y L`. -/
theorem front_error (hy : ∀ t, HasDerivAt y (y' t) t) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a) (hyD : ∀ t, |y' t| ≤ D * y t)
    (hyb : ∀ t, y t ≤ b) (hb : b < 1) :
    ∃ C β L₀ : ℝ, 0 < β ∧ ∀ L ≥ L₀, ∀ s : ℝ,
      Summable (fun m : ℤ => frontCurv y (s - m * L)) ∧
      |frontCurv (periodize y L) s - ∑' m : ℤ, frontCurv y (s - m * L)| ≤
        C * exp (-(β * L)) * periodize y L s := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hb0 : 0 ≤ b := (hy0 0).trans (hyb 0)
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hy'A : ∀ t, |y' t| ≤ (|D| * A) * exp (-(a * |t|)) := fun t => by
    have h1 : D * y t ≤ |D| * y t := mul_le_mul_of_nonneg_right (le_abs_self D) (hy0 t)
    have h2 : |D| * y t ≤ |D| * (A * exp (-(a * |t|))) :=
      mul_le_mul_of_nonneg_left (hyA t) (abs_nonneg D)
    linarith [hyD t]
  have hderiv_y : deriv y = y' := funext fun t => (hy t).deriv
  set b' : ℝ := (1 + b) / 2 with hb'
  have hb'1 : b' < 1 := by rw [hb']; linarith
  have hbb' : b ≤ b' := by rw [hb']; linarith
  set c0 : ℝ := √(1 - b' ^ 2) with hc0def
  have hc0 : 0 < c0 := Real.sqrt_pos.2 (by nlinarith)
  obtain ⟨C1, β1, H1, hβ1, hov⟩ := overlap_estimate (u := y) (v := y) (D := 1) hy0 hyA ha
    (fun t => by rw [one_mul, abs_of_nonneg (hy0 t)]) (fun t => by
      rw [one_mul, abs_of_nonneg (hy0 t)])
  -- eventually the periodization stays below `b'`
  have hev : ∀ᶠ L in atTop, 8 * A * exp (-(a / 2 * L)) < (1 - b) / 2 := by
    have ht : Tendsto (fun L : ℝ => 8 * A * exp (-(a / 2 * L))) atTop (𝓝 (8 * A * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < a / 2))).const_mul _
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by linarith))
  obtain ⟨H2, hH2⟩ := eventually_atTop.1 hev
  refine ⟨|D| * C1 / c0 ^ 3, β1, max (max H1 (2 / a)) H2, hβ1, fun L hL s => ?_⟩
  have hL1 : H1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLa : 2 / a ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : H2 ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hLa
  set w : ℤ → ℝ := fun m => y (s - m * L) with hw
  set d : ℤ → ℝ := fun m => y' (s - m * L) with hd
  have hw0 : ∀ m, 0 ≤ w m := fun m => hy0 _
  have hws : Summable w := summable_periodize hy0 hyA ha hL0 s
  have hds : Summable d := summable_periodize_abs hy'A ha hL0 s
  set Y : ℝ := periodize y L s with hYdef
  have hYw : Y = ∑' m, w m := rfl
  have hYb : Y ≤ b' := by
    have := periodize_le hyA' ha hyb hLa s
    have := hH2 L hL2
    rw [hb']; linarith
  have hwb : ∀ m, w m ≤ b' := fun m => (hyb _).trans hbb'
  have hwY : ∀ m, w m ≤ Y := fun m => hws.le_tsum m (fun j _ => hw0 j)
  have hY0 : 0 ≤ Y := (hw0 0).trans (hwY 0)
  have hdY : deriv (periodize y L) s = ∑' m, d m := by
    rw [deriv_periodize hy hyA' hy'A ha hL0]; rfl
  -- the curvature quotient terms
  set g : ℤ → ℝ := fun m => d m / √(1 - w m ^ 2) with hg
  have hcw : ∀ m, c0 ≤ √(1 - w m ^ 2) := fun m =>
    Real.sqrt_le_sqrt (by nlinarith [hw0 m, hwb m])
  have hgb : ∀ m, ‖g m‖ ≤ (|D| / c0) * w m := fun m => by
    rw [Real.norm_eq_abs, hg, abs_div, abs_of_pos (hc0.trans_le (hcw m))]
    have h1 : |d m| ≤ |D| * w m := (hyD _).trans
      (mul_le_mul_of_nonneg_right (le_abs_self D) (hw0 m))
    calc |d m| / √(1 - w m ^ 2) ≤ (|D| * w m) / c0 :=
          div_le_div₀ (mul_nonneg (abs_nonneg _) (hw0 m)) h1 hc0 (hcw m)
      _ = |D| / c0 * w m := by ring
  have hgs : Summable g := Summable.of_norm_bounded (hws.mul_left _) hgb
  have hK : ∀ m : ℤ, frontCurv y (s - m * L) = w m + g m := fun m => by
    simp only [frontCurv, hderiv_y, hg, hw, hd]
  have hKs : Summable (fun m : ℤ => frontCurv y (s - m * L)) := by
    simp_rw [hK]; exact hws.add hgs
  refine ⟨hKs, ?_⟩
  -- the main identity
  set T : ℤ → ℝ := fun m => d m / √(1 - Y ^ 2) - g m with hT
  have hTs : Summable T := (hds.div_const _).sub hgs
  have hid : frontCurv (periodize y L) s - ∑' m : ℤ, frontCurv y (s - m * L) = ∑' m, T m := by
    simp_rw [hK]
    rw [hws.tsum_add hgs, hT, (hds.div_const _).tsum_sub hgs, tsum_div_const]
    simp only [frontCurv, hdY, ← hYdef, hYw]
    ring
  -- pointwise bound of the summand
  set B : ℤ → ℝ := fun m => (|D| / c0 ^ 3) * (w m * (Y - w m)) with hB
  have hTB : ∀ m, ‖T m‖ ≤ B m := fun m => by
    have e : T m = d m * (1 / √(1 - Y ^ 2) - 1 / √(1 - w m ^ 2)) := by
      simp only [hT, hg]; ring
    rw [Real.norm_eq_abs, e, abs_mul]
    have hlip := inv_sqrt_one_sub_sq_lipschitz hb'1 hY0 hYb (hw0 m) (hwb m)
    rw [abs_of_nonneg (sub_nonneg.2 (hwY m))] at hlip
    have h1 : |d m| ≤ |D| * w m := (hyD _).trans
      (mul_le_mul_of_nonneg_right (le_abs_self D) (hw0 m))
    calc |d m| * |1 / √(1 - Y ^ 2) - 1 / √(1 - w m ^ 2)|
        ≤ (|D| * w m) * ((Y - w m) / c0 ^ 3) :=
          mul_le_mul h1 hlip (abs_nonneg _) (mul_nonneg (abs_nonneg _) (hw0 m))
      _ = B m := by rw [hB]; ring
  have hBs : Summable B := by
    refine Summable.mul_left _ (Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      (hws.mul_right Y))
    · exact mul_nonneg (hw0 m) (sub_nonneg.2 (hwY m))
    · nlinarith [hw0 m, hwY m]
  obtain ⟨hoffs, hoff⟩ := hov L hL1 s
  have hBsum : ∑' m, B m ≤ |D| * C1 / c0 ^ 3 * exp (-(β1 * L)) * Y := by
    rw [hB, tsum_mul_left]
    have := tsum_mul_sub_eq_offdiag hw0 hws hoffs
    rw [← hYw] at this
    rw [this]
    calc |D| / c0 ^ 3 * ∑' p : ℤ × ℤ, (if p.1 ≠ p.2 then |w p.1| * |w p.2| else 0)
        ≤ |D| / c0 ^ 3 * (C1 * exp (-(β1 * L)) * periodize y L s) :=
          mul_le_mul_of_nonneg_left hoff (by positivity)
      _ = _ := by rw [← hYdef]; ring
  rw [hid, ← Real.norm_eq_abs]
  exact (tsum_of_norm_bounded hBs.hasSum hTB).trans hBsum

end

end Ovals

end
