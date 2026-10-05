module

public import UnitTangentIterates.PulseFront
public import UnitTangentIterates.PeriodizationIntegral
public import UnitTangentIterates.FrontError

/-!
# Lemma 3.5, step 3: the pulse from an intrinsic translator

We isolate the analytic content of Lemma 3.5.  Let `K > 0` be the curvature of a curve in its
arclength `x`, and suppose the curve and its unit-tangent image are translates, in the
following intrinsic sense: the front arclength is `σ(x)` with `σ' = √(1 + K²)`, and the
front curvature at front arclength `σ(x)` is `K(σ(x)) = K(x) G(x) / √(1 + K(x)²)` where
`K' = (1 + K²)(G - 1) K`.  (For the hairpin, `G = g'` is the derivative of the translator
angle map.)  If `K` decays exponentially and satisfies the shift comparison (3.9), then the
pulse `y(s) = sin δ(s)`, `tan δ(s) = K(x(s))`, `x = σ⁻¹`, has all the properties (3.6)–(3.8)
used in Sections 4–7, with derivative bounds up to second order.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology MeasureTheory

/-- `σ(x) - x` is bounded when `1 ≤ σ' ≤ 1 + A₀ e^{-a|x|}`. -/
theorem sub_bounded_of_deriv {σ σ' : ℝ → ℝ} {A₀ a : ℝ} (ha : 0 < a)
    (hσ : ∀ x, HasDerivAt σ (σ' x) x) (h1 : ∀ x, 1 ≤ σ' x)
    (h2 : ∀ x, σ' x ≤ 1 + A₀ * Real.exp (-(a * |x|))) (hA₀ : 0 ≤ A₀) :
    ∀ x, |σ x - x| ≤ |σ 0| + A₀ / a := by
  have hmono : Monotone (fun x => σ x - x) :=
    monotone_of_hasDerivAt_nonneg (f' := fun x => σ' x - 1)
      (fun x => ((hσ x).sub (hasDerivAt_id x)))
      (fun x => by show 0 ≤ σ' x - 1; linarith [h1 x])
  have hanti1 : Antitone (fun x => σ x - x + A₀ / a * Real.exp (-(a * x))) := by
    refine antitone_of_hasDerivAt_nonpos (f' := fun x => σ' x - 1 + A₀ / a *
      (Real.exp (-(a * x)) * (-a))) (fun x => ?_) (fun x => ?_)
    · exact ((hσ x).sub (hasDerivAt_id x)).add
        ((((hasDerivAt_id x).const_mul a).neg.exp).const_mul (A₀ / a) |>.congr_deriv (by simp))
    · show σ' x - 1 + A₀ / a * (Real.exp (-(a * x)) * (-a)) ≤ 0
      have : Real.exp (-(a * |x|)) ≤ Real.exp (-(a * x)) :=
        Real.exp_le_exp.2 (by nlinarith [le_abs_self x])
      have e : A₀ / a * (Real.exp (-(a * x)) * (-a)) = -(A₀ * Real.exp (-(a * x))) := by
        field_simp
      rw [e]; nlinarith [h2 x]
  have hanti2 : Antitone (fun x => σ x - x - A₀ / a * Real.exp (a * x)) := by
    refine antitone_of_hasDerivAt_nonpos (f' := fun x => σ' x - 1 - A₀ / a *
      (Real.exp (a * x) * a)) (fun x => ?_) (fun x => ?_)
    · exact ((hσ x).sub (hasDerivAt_id x)).sub
        ((((hasDerivAt_id x).const_mul a).exp).const_mul (A₀ / a) |>.congr_deriv (by simp))
    · show σ' x - 1 - A₀ / a * (Real.exp (a * x) * a) ≤ 0
      have : Real.exp (-(a * |x|)) ≤ Real.exp (a * x) :=
        Real.exp_le_exp.2 (by nlinarith [neg_abs_le x])
      have e : A₀ / a * (Real.exp (a * x) * a) = A₀ * Real.exp (a * x) := by
        field_simp
      rw [e]; nlinarith [h2 x]
  intro x
  have hAa : 0 ≤ A₀ / a := by positivity
  rcases le_total 0 x with hx | hx
  · have e1 := hmono hx
    have e2 := hanti1 hx
    simp only [sub_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at e1 e2
    have := Real.exp_pos (-(a * x))
    rw [abs_le]; constructor <;> nlinarith [abs_nonneg (σ 0), le_abs_self (σ 0),
      neg_abs_le (σ 0)]
  · have e1 := hmono hx
    have e2 := hanti2 hx
    simp only [sub_zero, mul_zero, Real.exp_zero, mul_one] at e1 e2
    have := Real.exp_pos (a * x)
    rw [abs_le]; constructor <;> nlinarith [abs_nonneg (σ 0), le_abs_self (σ 0),
      neg_abs_le (σ 0)]

/-- **Lemma 3.5, analytic core.**  See the module docstring for the hypotheses. -/
theorem pulse_of_shift {K K' G σ X Φ : ℝ → ℝ} {κ Gm Cs r A₀ a : ℝ}
    (hK : ∀ x, HasDerivAt K (K' x) x) (hK' : ∀ x, K' x = (1 + K x ^ 2) * (G x - 1) * K x)
    (hKpos : ∀ x, 0 < K x) (hKle : ∀ x, K x ≤ κ) (hκ : κ < 1)
    (hG : ∀ x, 0 < G x ∧ G x ≤ Gm)
    (hσ : ∀ x, HasDerivAt σ (√(1 + K x ^ 2)) x) (hσX : ∀ s, σ (X s) = s)
    (hX : ∀ s, HasDerivAt X (√(1 + K (X s) ^ 2))⁻¹ s)
    (hshift : ∀ x, K (σ x) = K x * G x / √(1 + K x ^ 2))
    (hcomp : ∀ x h, K (x + h) ≤ Cs * Real.exp (r * |h|) * K x) (hr : 0 ≤ r)
    (hdecay : ∀ x, K x ≤ A₀ * Real.exp (-(a * |x|))) (ha : 0 < a)
    (hΦ : ∀ x, HasDerivAt Φ (K x) x) (hΦbot : Tendsto Φ atBot (𝓝 0))
    (hΦtop : Tendsto Φ atTop (𝓝 π)) :
    ∃ (y y' y'' : ℝ → ℝ) (A D b b₀ x₀ : ℝ),
      (∀ t, HasDerivAt y (y' t) t) ∧ (∀ t, HasDerivAt y' (y'' t) t) ∧ (∀ t, 0 < y t) ∧
      (∀ t, y t ≤ A * Real.exp (-(a * |t|))) ∧ (∀ t, |y' t| ≤ D * y t) ∧
      (∀ t, |y'' t| ≤ D * y t) ∧ (∀ t, y t ≤ b) ∧ b < 1 ∧ ∫ t, y t = π ∧ 0 < b₀ ∧
      (∀ t, b₀ * y t ≤ frontCurv y t) ∧
      (∀ s, frontCurv y (x₀ + ∫ r in (0 : ℝ)..s, √(1 - y r ^ 2)) = y s / √(1 - y s ^ 2)) ∧
      (∀ t, frontCurv y t ≤ κ) ∧ (∀ t, y t / √(1 - y t ^ 2) ≤ κ) := by
  -- basic facts
  have hKc : Continuous K := continuous_iff_continuousAt.2 fun x => (hK x).continuousAt
  have hCs : 1 ≤ Cs := by
    have h := hcomp 0 0
    simp only [add_zero, abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    by_contra hc
    push_neg at hc
    nlinarith [hKpos 0]
  have hA₀ : 0 ≤ A₀ := by
    have h := hdecay 0
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    linarith [hKpos 0]
  have hκ0 : 0 < κ := (hKpos 0).trans_le (hKle 0)
  have hσ1 : ∀ x, 1 ≤ √(1 + K x ^ 2) := fun x =>
    Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (K x)])
  have hσ2 : ∀ x, √(1 + K x ^ 2) ≤ 1 + A₀ * Real.exp (-(a * |x|)) := fun x => by
    calc √(1 + K x ^ 2) ≤ √((1 + K x) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hKpos x])
      _ = 1 + K x := Real.sqrt_sq (by linarith [hKpos x])
      _ ≤ 1 + A₀ * Real.exp (-(a * |x|)) := by linarith [hdecay x]
  set B : ℝ := |σ 0| + A₀ / a with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ s, |X s - s| ≤ B := fun s => by
    have h := sub_bounded_of_deriv ha hσ hσ1 hσ2 hA₀ (X s)
    rw [hσX] at h
    rw [abs_sub_comm]; exact h
  -- the pulse
  set w : ℝ → ℝ := fun s => K (X s) with hwdef
  set q : ℝ → ℝ := fun s => √(1 + w s ^ 2) with hqdef
  have hq2 : ∀ s, q s ^ 2 = 1 + w s ^ 2 := fun s => Real.sq_sqrt (by positivity)
  have hq1 : ∀ s, 1 ≤ q s := fun s => Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (w s)])
  have hq0 : ∀ s, 0 < q s := fun s => lt_of_lt_of_le one_pos (hq1 s)
  have hwpos : ∀ s, 0 < w s := fun s => hKpos _
  have hwle : ∀ s, w s ≤ κ := fun s => hKle _
  have hq2le : ∀ s, q s ≤ 2 := fun s => by
    nlinarith [hq2 s, hwle s, hwpos s, hq0 s]
  have hKs : ∀ s, K s = w s * G (X s) / q s := fun s => by
    have h := hshift (X s); rwa [hσX] at h
  set y : ℝ → ℝ := fun s => w s / q s with hydef
  set y' : ℝ → ℝ := fun s => 1 / q s * (K s - y s) with hy'def
  set c' : ℝ → ℝ := fun s => -(w s) ^ 2 * (G (X s) - 1) / q s ^ 2 with hc'def
  set y'' : ℝ → ℝ := fun s => c' s * (K s - y s) + 1 / q s * (K' s - y' s) with hy''def
  have hw : ∀ s, HasDerivAt w (K' (X s) * (q s)⁻¹) s := fun s => (hK (X s)).comp s (hX s)
  have hq : ∀ s, HasDerivAt q (w s ^ 2 * (G (X s) - 1)) s := by
    intro s
    have h1 : HasDerivAt (fun t => 1 + w t ^ 2) (2 * w s * (K' (X s) * (q s)⁻¹)) s := by
      have := ((hw s).pow 2).const_add 1
      convert this using 1
      simp
    have h2 := h1.sqrt (ne_of_gt (by positivity : (0:ℝ) < 1 + w s ^ 2))
    have h3 : HasDerivAt q (2 * w s * (K' (X s) * (q s)⁻¹) / (2 * q s)) s := h2
    convert h3 using 1
    have hqne := (hq0 s).ne'
    rw [hK' (X s)]
    field_simp
    rw [show K (X s) = w s from rfl, ← hq2 s]
    ring
  have hy : ∀ s, HasDerivAt y (y' s) s := by
    intro s
    have h := (hw s).div (hq s) (hq0 s).ne'
    convert h using 1
    simp only [hy'def, hydef]
    have hqne := (hq0 s).ne'
    rw [hK' (X s), hKs s, show K (X s) = w s from rfl]
    field_simp
    ring
  have hc : ∀ s, HasDerivAt (fun s => 1 / q s) (c' s) s := by
    intro s
    have h := (hasDerivAt_const s (1 : ℝ)).div (hq s) (hq0 s).ne'
    convert h using 1
    have hqne := (hq0 s).ne'
    simp only [hc'def]
    field_simp
    ring
  have hy' : ∀ s, HasDerivAt y' (y'' s) s := fun s => (hc s).mul ((hK s).sub (hy s))
  -- comparison of the front curvature `K s` with `w s = K (X s)`
  set E : ℝ := Cs * Real.exp (r * B) with hEdef
  have hE1 : 1 ≤ E := by
    have := Real.one_le_exp (by positivity : 0 ≤ r * B); nlinarith
  have hE0 : 0 < E := by linarith
  have hKs_le : ∀ s, K s ≤ E * w s := fun s => by
    have h := hcomp (X s) (s - X s)
    rw [add_sub_cancel] at h
    have hb : Real.exp (r * |s - X s|) ≤ Real.exp (r * B) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hB s) hr)
    calc K s ≤ Cs * Real.exp (r * |s - X s|) * K (X s) := h
      _ ≤ Cs * Real.exp (r * B) * K (X s) := by
          gcongr; exact (hKpos _).le
      _ = E * w s := rfl
  have hw_le : ∀ s, w s ≤ E * K s := fun s => by
    have h := hcomp s (X s - s)
    rw [add_sub_cancel] at h
    have hb : Real.exp (r * |X s - s|) ≤ Real.exp (r * B) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hB s) hr)
    calc w s = K (X s) := rfl
      _ ≤ Cs * Real.exp (r * |X s - s|) * K s := h
      _ ≤ Cs * Real.exp (r * B) * K s := by
          gcongr; exact (hKpos _).le
  have hypos : ∀ s, 0 < y s := fun s => div_pos (hwpos s) (hq0 s)
  have hy_le : ∀ s, y s ≤ w s := fun s => div_le_self (hwpos s).le (hq1 s)
  have hy_ge : ∀ s, w s ≤ 2 * y s := fun s => by
    show w s ≤ 2 * (w s / q s)
    rw [mul_div_assoc', le_div_iff₀ (hq0 s)]; nlinarith [hq2le s, hwpos s]
  set G1 : ℝ := Gm + 1 with hG1def
  have hG1 : ∀ x, |G x - 1| ≤ G1 := fun x =>
    abs_le.2 ⟨by linarith [(hG x).1, (hG x).2], by linarith [(hG x).2]⟩
  have hG10 : 1 ≤ G1 := by linarith [(hG 0).1, (hG 0).2]
  have hiq : ∀ s, 0 < 1 / q s ∧ 1 / q s ≤ 1 := fun s =>
    ⟨one_div_pos.2 (hq0 s), (div_le_one (hq0 s)).2 (hq1 s)⟩
  have hKy : ∀ s, |K s - y s| ≤ (2 * E + 1) * y s := fun s => by
    rw [abs_le]; constructor <;> nlinarith [hKs_le s, hy_ge s, hKpos s, hypos s]
  have hy'b : ∀ s, |y' s| ≤ (2 * E + 1) * y s := fun s => by
    simp only [hy'def]
    rw [abs_mul, abs_of_pos (hiq s).1]
    calc 1 / q s * |K s - y s| ≤ 1 * |K s - y s| :=
          mul_le_mul_of_nonneg_right (hiq s).2 (abs_nonneg _)
      _ ≤ (2 * E + 1) * y s := by rw [one_mul]; exact hKy s
  have hc'b : ∀ s, |c' s| ≤ G1 := fun s => by
    simp only [hc'def]
    have hw1 : w s ^ 2 ≤ 1 := by nlinarith [hwle s, hwpos s]
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _), abs_of_pos (pow_pos (hq0 s) 2),
      div_le_iff₀ (pow_pos (hq0 s) 2)]
    have := hG1 (X s)
    nlinarith [hq2 s, sq_nonneg (w s), abs_nonneg (G (X s) - 1)]
  have hK's : ∀ s, |K' s| ≤ 4 * G1 * E * y s := fun s => by
    rw [hK' s, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 + K s ^ 2),
      abs_of_pos (hKpos s)]
    have hK1 : 1 + K s ^ 2 ≤ 2 := by nlinarith [hKle s, hKpos s]
    have := hG1 s
    calc (1 + K s ^ 2) * |G s - 1| * K s ≤ 2 * G1 * K s :=
          mul_le_mul (mul_le_mul hK1 this (abs_nonneg _) (by norm_num)) le_rfl (hKpos s).le
            (by linarith)
      _ ≤ 2 * G1 * (E * w s) := by gcongr; exact hKs_le s
      _ ≤ 2 * G1 * (E * (2 * y s)) := by gcongr; exact hy_ge s
      _ = 4 * G1 * E * y s := by ring
  set D : ℝ := (G1 + 1) * (2 * E + 1) + 4 * G1 * E with hDdef
  have hy''b : ∀ s, |y'' s| ≤ D * y s := fun s => by
    simp only [hy''def]
    have h1 : |c' s * (K s - y s)| ≤ G1 * ((2 * E + 1) * y s) := by
      rw [abs_mul]; exact mul_le_mul (hc'b s) (hKy s) (abs_nonneg _) (by linarith)
    have h2 : |1 / q s * (K' s - y' s)| ≤ 4 * G1 * E * y s + (2 * E + 1) * y s := by
      rw [abs_mul, abs_of_pos (hiq s).1]
      calc 1 / q s * |K' s - y' s| ≤ 1 * |K' s - y' s| :=
            mul_le_mul_of_nonneg_right (hiq s).2 (abs_nonneg _)
        _ ≤ |K' s| + |y' s| := by rw [one_mul]; exact abs_sub _ _
        _ ≤ _ := add_le_add (hK's s) (hy'b s)
    calc |c' s * (K s - y s) + 1 / q s * (K' s - y' s)|
        ≤ |c' s * (K s - y s)| + |1 / q s * (K' s - y' s)| := abs_add_le _ _
      _ ≤ G1 * ((2 * E + 1) * y s) + (4 * G1 * E * y s + (2 * E + 1) * y s) :=
          add_le_add h1 h2
      _ = D * y s := by rw [hDdef]; ring
  have hDy' : ∀ s, |y' s| ≤ D * y s := fun s => by
    refine (hy'b s).trans (mul_le_mul_of_nonneg_right ?_ (hypos s).le)
    rw [hDdef]; nlinarith
  -- exponential decay
  have hdec : ∀ s, y s ≤ A₀ * Real.exp (a * B) * Real.exp (-(a * |s|)) := fun s => by
    have h1 : |s| ≤ |X s| + B := by
      have := abs_sub_abs_le_abs_sub s (X s)
      rw [abs_sub_comm] at this; linarith [hB s]
    have h2 : Real.exp (-(a * |X s|)) ≤ Real.exp (a * B) * Real.exp (-(a * |s|)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    calc y s ≤ w s := hy_le s
      _ ≤ A₀ * Real.exp (-(a * |X s|)) := hdecay _
      _ ≤ A₀ * (Real.exp (a * B) * Real.exp (-(a * |s|))) := by gcongr
      _ = A₀ * Real.exp (a * B) * Real.exp (-(a * |s|)) := by ring
  -- `c = √(1 - y²) = 1/q` and the front curvature
  have hsq : ∀ s, √(1 - y s ^ 2) = 1 / q s := fun s => by
    have hqne := (hq0 s).ne'
    have e : 1 - y s ^ 2 = (1 / q s) ^ 2 := by
      simp only [hydef]
      field_simp
      linear_combination hq2 s
    rw [e, Real.sqrt_sq (hiq s).1.le]
  have hfront : ∀ s, frontCurv y s = K s := fun s => by
    have hqne := (hq0 s).ne'
    rw [frontCurv, (hy s).deriv, hsq]
    simp only [hy'def]
    field_simp
    ring
  -- the rear arclength
  have hqc : Continuous q := continuous_iff_continuousAt.2 fun s => (hq s).continuousAt
  have hint : ∀ s, ∫ r in (0 : ℝ)..s, √(1 - y r ^ 2) = X s - X 0 := fun s => by
    have hcont : Continuous (fun r => (q r)⁻¹) := hqc.inv₀ fun r => (hq0 r).ne'
    simp_rw [hsq, one_div]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hX r)
      (hcont.intervalIntegrable _ _)
  -- the mass
  have hΦX : ∀ s, HasDerivAt (fun s => Φ (X s)) (y s) s := fun s => by
    have h := (hΦ (X s)).comp s (hX s)
    convert h using 1
  have hXtop : Tendsto X atTop atTop :=
    tendsto_atTop_mono (fun s => by show s + -B ≤ X s; linarith [(abs_le.1 (hB s)).1])
      (tendsto_atTop_add_const_right _ (-B) tendsto_id)
  have hXbot : Tendsto X atBot atBot :=
    tendsto_atBot_mono (fun s => by show X s ≤ s + B; linarith [(abs_le.1 (hB s)).2])
      (tendsto_atBot_add_const_right _ B tendsto_id)
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun s => (hy s).continuousAt
  have hyint : Integrable y := integrable_of_exp_bound hyc
    (fun t => by rw [abs_of_pos (hypos t)]; exact hdec t) ha
  have hmass : ∫ t, y t = π := by
    have := integral_of_hasDerivAt_of_tendsto hΦX hyint (hΦbot.comp hXbot) (hΦtop.comp hXtop)
    rw [this, sub_zero]
  refine ⟨y, y', y'', A₀ * Real.exp (a * B), D, κ, 1 / E, X 0, hy, hy', hypos, hdec, hDy',
    hy''b, fun t => (hy_le t).trans (hwle t), hκ, hmass, by positivity, fun t => ?_,
    fun s => ?_, fun t => by rw [hfront]; exact hKle t, fun t => ?_⟩
  · rw [hfront, one_div_mul_eq_div, div_le_iff₀ hE0]
    nlinarith [hy_le t, hw_le t]
  · have hqne := (hq0 s).ne'
    rw [hint, add_sub_cancel, hfront, hsq]
    simp only [hydef]
    field_simp
    rfl
  · have hqne := (hq0 t).ne'
    rw [hsq]
    simp only [hydef]
    rw [div_div_div_cancel_right₀ hqne]
    simpa using hwle t

end Ovals

end
