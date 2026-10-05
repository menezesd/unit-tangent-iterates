module

public import UnitTangentIterates.Width
public import UnitTangentIterates.PeriodizedPairs
public import UnitTangentIterates.PerimeterAsymptotics

/-!
# Lemma 4.4: the closed fronts have bounded width

For the periodized pulse, the closed front `F_H` of Proposition 4.3 has width
`0 < W_H ≤ C` for all sufficiently large `H`, with `C` independent of `H`.  Together with
`curveOfCurvature_strip`, this says that `F_H` lies in a strip of bounded width.
-/

@[expose] public section

namespace Ovals

open Real intervalIntegral MeasureTheory

/-- `arcsin x ≤ (π/2) x` on `[0, 1]` (Jordan's inequality). -/
lemma arcsin_le_pi_div_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.arcsin x ≤ π / 2 * x := by
  have h := Real.mul_le_sin (Real.arcsin_nonneg.2 h0) (Real.arcsin_le_pi_div_two x)
  rw [Real.sin_arcsin (by linarith) h1] at h
  have hp := Real.pi_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ hp] at h
  nlinarith

/-- Integral of a function bounded by `A e^{a t} + E` on `[-h, s]`. -/
lemma integral_le_exp_left {f : ℝ → ℝ} {A a E h s : ℝ} (hf : Continuous f) (ha : 0 < a)
    (hA : 0 ≤ A) (hs : -h ≤ s) (hb : ∀ t ∈ Set.Icc (-h) s, f t ≤ A * exp (a * t) + E) :
    ∫ t in (-h)..s, f t ≤ A / a * exp (a * s) + (s + h) * E := by
  have hd : ∀ t, HasDerivAt (fun t => A / a * exp (a * t) + E * t) (A * exp (a * t) + E) t := by
    intro t
    have := (((hasDerivAt_id t).const_mul a).exp.const_mul (A / a)).add
      ((hasDerivAt_id t).const_mul E)
    convert this using 1
    field_simp; simp
  have hc : Continuous (fun t => A * exp (a * t) + E) := by fun_prop
  calc ∫ t in (-h)..s, f t ≤ ∫ t in (-h)..s, (A * exp (a * t) + E) :=
        intervalIntegral.integral_mono_on hs (hf.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _) hb
    _ = (A / a * exp (a * s) + E * s) - (A / a * exp (a * -h) + E * -h) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
          (hc.intervalIntegrable _ _)
    _ ≤ A / a * exp (a * s) + (s + h) * E := by
        have : 0 ≤ A / a * exp (a * -h) := by positivity
        nlinarith

/-- Integral of a function bounded by `A e^{-a t} + E` on `[s, h]`. -/
lemma integral_le_exp_right {f : ℝ → ℝ} {A a E h s : ℝ} (hf : Continuous f) (ha : 0 < a)
    (hA : 0 ≤ A) (hs : s ≤ h) (hb : ∀ t ∈ Set.Icc s h, f t ≤ A * exp (-(a * t)) + E) :
    ∫ t in s..h, f t ≤ A / a * exp (-(a * s)) + (h - s) * E := by
  have hd : ∀ t, HasDerivAt (fun t => -(A / a) * exp (-(a * t)) + E * t)
      (A * exp (-(a * t)) + E) t := by
    intro t
    have := (((hasDerivAt_id t).const_mul a).neg.exp.const_mul (-(A / a))).add
      ((hasDerivAt_id t).const_mul E)
    convert this using 1
    field_simp; simp
  have hc : Continuous (fun t => A * exp (-(a * t)) + E) := by fun_prop
  calc ∫ t in s..h, f t ≤ ∫ t in s..h, (A * exp (-(a * t)) + E) :=
        intervalIntegral.integral_mono_on hs (hf.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _) hb
    _ = (-(A / a) * exp (-(a * h)) + E * h) - (-(A / a) * exp (-(a * s)) + E * s) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
          (hc.intervalIntegrable _ _)
    _ ≤ A / a * exp (-(a * s)) + (h - s) * E := by
        have : 0 ≤ A / a * exp (-(a * h)) := by positivity
        nlinarith

/-- **Lemma 4.4.**  For all sufficiently large `H`, the closed front `F_H` built from the
periodized pulse has width `0 < W_H ≤ C`, with `C` independent of `H`. -/
theorem periodized_width_bounded {y y' y'' : ℝ → ℝ} {A a D b b₀ : ℝ} (θ₀ : ℝ)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hy' : ∀ t, HasDerivAt y' (y'' t) t)
    (hypos : ∀ t, 0 < y t) (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a)
    (hyD : ∀ t, |y' t| ≤ D * y t) (hyD2 : ∀ t, |y'' t| ≤ D * y t)
    (hyb : ∀ t, y t ≤ b) (hb : b < 1) (hmass : ∫ t, y t = π)
    (hb₀ : 0 < b₀) (hK : ∀ t, b₀ * y t ≤ frontCurv y t) :
    ∃ C H₀ : ℝ, ∀ H ≥ H₀,
      0 < curveWidth θ₀ (pairCurvature (periodizedAngle y H) (periodizedAngleDeriv y y' H)) H ∧
      curveWidth θ₀ (pairCurvature (periodizedAngle y H) (periodizedAngleDeriv y y' H)) H ≤ C := by
  have hy0 : ∀ t, 0 ≤ y t := fun t => (hypos t).le
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hexp : ∀ {u : ℝ → ℝ}, (∀ t, |u t| ≤ D * y t) →
      ∀ t, |u t| ≤ (|D| * A) * exp (-(a * |t|)) := fun {u} hu t => by
    have h1 : D * y t ≤ |D| * y t := mul_le_mul_of_nonneg_right (le_abs_self D) (hy0 t)
    have h2 : |D| * y t ≤ |D| * (A * exp (-(a * |t|))) :=
      mul_le_mul_of_nonneg_left (hyA t) (abs_nonneg D)
    linarith [hu t]
  have hy'A := hexp hyD
  obtain ⟨H₁, hpair⟩ := periodized_closed_pair θ₀ hy hy' hypos hyA ha hyD hyD2 hyb hb hmass hb₀ hK
  set c : ℝ := π / 2 * A + A / a with hc
  refine ⟨2 * c / a + 17 * π / 2 * A * (4 / a) + 8 * A * (8 / a) ^ 2, max H₁ (2 / a),
    fun H hH => ?_⟩
  have hHa : 2 / a ≤ H := (le_max_right _ _).trans hH
  have hH1 : H₁ ≤ H := (le_max_left _ _).trans hH
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hHa
  obtain ⟨hY01, -, -, -, hF, -⟩ := hpair H hH1
  set Y := periodize y H with hYdef
  set δ := periodizedAngle y H with hδdef
  set δ' := periodizedAngleDeriv y y' H with hδ'def
  set κ := pairCurvature δ δ' with hκdef
  have hYd : ∀ s, HasDerivAt Y (periodize y' H s) s :=
    hasDerivAt_periodize hy hyA' hy'A ha hH0
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun s => (hYd s).continuousAt
  have hY'c : Continuous (periodize y' H) := by
    have hy''A := hexp hyD2
    have hY'd : ∀ s, HasDerivAt (periodize y' H) (periodize y'' H s) s :=
      hasDerivAt_periodize hy' hy'A hy''A ha hH0
    exact continuous_iff_continuousAt.2 fun s => (hY'd s).continuousAt
  have hsq : ∀ s, 0 < 1 - Y s ^ 2 := fun s => by nlinarith [(hY01 s).1, (hY01 s).2]
  have hYp : Function.Periodic Y H := fun s => by
    have := periodize_sub_int_mul y H s (-1)
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add] at this
    exact this
  have hδ : ∀ s, HasDerivAt δ (δ' s) s := by
    intro s
    have h := (Real.hasDerivAt_arcsin (by linarith [(hY01 s).1]) (hY01 s).2.ne).comp s (hYd s)
    simp only [hδdef, hδ'def, periodizedAngleDeriv]
    convert h using 1
    rw [← hYdef]; ring
  have hδ'c : Continuous δ' := by
    simp only [hδ'def]
    exact hY'c.div (Real.continuous_sqrt.comp (continuous_const.sub (hYc.pow 2)))
      (fun s => (Real.sqrt_pos.2 (hsq s)).ne')
  have hδp : Function.Periodic δ H := fun s => by
    simp only [hδdef, periodizedAngle]; rw [← hYdef, hYp s]
  have hsin : ∀ s, Real.sin (δ s) = Y s := fun s =>
    Real.sin_arcsin (by linarith [(hY01 s).1]) (hY01 s).2.le
  have hint : ∫ s in (0 : ℝ)..H, Real.sin (δ s) = π := by
    simp_rw [hsin]
    rw [hYdef, integral_periodize (hyc := continuous_iff_continuousAt.2 fun t =>
      (hy t).continuousAt) hyA' ha hH0, hmass]
  have hκc : Continuous κ := continuous_pairCurvature hδ hδ'c
  have hκp : Function.Periodic κ H := fun s => by
    simp only [hκdef, pairCurvature]; rw [periodic_of_hasDerivAt hδ hδp s, hδp s]
  have hκint : ∫ s in (0 : ℝ)..H, κ s = π := by
    rw [integral_pairCurvature hδ hδ'c hδp, hint]
  have hκpos : ∀ s, 0 < κ s := fun s => by
    have h1 := (hF s).2.2
    rw [pairFront, curvature_curveOfCurvature hκc] at h1
    exact h1
  have hκY : ∀ u v, ∫ r in u..v, κ r = δ v - δ u + ∫ r in u..v, Y r := fun u v => by
    simp only [hκdef, pairCurvature]
    rw [intervalIntegral.integral_add (f := δ') (g := fun s => Real.sin (δ s))
      (hδ'c.intervalIntegrable _ _)
      ((Real.continuous_sin.comp (continuous_iff_continuousAt.2 fun s =>
        (hδ s).continuousAt)).intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hδ s)
        (hδ'c.intervalIntegrable _ _)]
    simp_rw [hsin]
  have hδ0 : ∀ s, 0 ≤ δ s := fun s => Real.arcsin_nonneg.2 (hY01 s).1.le
  have hδY : ∀ s, δ s ≤ π / 2 * Y s := fun s =>
    arcsin_le_pi_div_two_mul (hY01 s).1.le (hY01 s).2.le
  -- pointwise bound on the cell
  set e : ℝ := exp (-(a / 2 * H)) with he
  set E : ℝ := 8 * A * e with hE
  have he0 : 0 ≤ e := (exp_pos _).le
  have hE0 : 0 ≤ E := by positivity
  have hYcell : ∀ t, |t| ≤ H / 2 → Y t ≤ A * exp (-(a * |t|)) + E := fun t ht => by
    have h1 := periodize_sub_le_explicit hyA' ha hHa ht
    have h2 := (abs_le.1 h1).2
    linarith [hyA t]
  set E₂ : ℝ := π / 2 * E + H * E + π / 2 * (A * e + E) with hE₂
  have hpi := Real.pi_pos
  have hE₂0 : 0 ≤ E₂ := by positivity
  have hc0 : 0 ≤ c := by positivity
  refine ⟨curveWidth_pos hκc hκpos hκp hκint hH0, ?_⟩
  have hb1 : ∀ s ∈ Set.Icc (-H / 2) 0, ∫ r in (-H / 2)..s, κ r ≤ c * exp (a * s) + E₂ := by
    intro s hs
    rw [hκY]
    have hYb : ∀ t ∈ Set.Icc (-(H / 2)) s, Y t ≤ A * exp (a * t) + E := fun t ht => by
      have ht0 : t ≤ 0 := ht.2.trans hs.2
      have h1 := hYcell t (by rw [abs_of_nonpos ht0]; linarith [ht.1])
      rwa [abs_of_nonpos ht0, show -(a * -t) = a * t by ring] at h1
    have hI := integral_le_exp_left (h := H / 2) hYc ha hA (by linarith [hs.1]) hYb
    rw [show -(H / 2) = -H / 2 by ring] at hI
    have hYs := hYb s ⟨by linarith [hs.1], le_rfl⟩
    have h1 : δ s ≤ π / 2 * (A * exp (a * s) + E) :=
      (hδY s).trans (mul_le_mul_of_nonneg_left hYs (by positivity))
    have h2 : (s + H / 2) * E ≤ H * E := mul_le_mul_of_nonneg_right (by linarith [hs.2]) hE0
    have h3 : 0 ≤ π / 2 * (A * e + E) := by positivity
    have h4 := hδ0 (-H / 2)
    rw [hc, hE₂]
    linarith
  have hb2 : ∀ s ∈ Set.Icc 0 (H / 2), ∫ r in s..(H / 2), κ r ≤ c * exp (-(a * s)) + E₂ := by
    intro s hs
    rw [hκY]
    have hYb : ∀ t ∈ Set.Icc s (H / 2), Y t ≤ A * exp (-(a * t)) + E := fun t ht => by
      have ht0 : 0 ≤ t := hs.1.trans ht.1
      have h1 := hYcell t (by rw [abs_of_nonneg ht0]; exact ht.2)
      rwa [abs_of_nonneg ht0] at h1
    have hI := integral_le_exp_right (h := H / 2) hYc ha hA hs.2 hYb
    have hYh := hYb (H / 2) ⟨hs.2, le_rfl⟩
    rw [show a * (H / 2) = a / 2 * H by ring, ← he] at hYh
    have h1 : δ (H / 2) ≤ π / 2 * (A * e + E) :=
      (hδY _).trans (mul_le_mul_of_nonneg_left hYh (by positivity))
    have h2 : (H / 2 - s) * E ≤ H * E := mul_le_mul_of_nonneg_right (by linarith [hs.1]) hE0
    have h3 : 0 ≤ π / 2 * E := by positivity
    have h4 := hδ0 s
    have h5 : 0 ≤ π / 2 * A * exp (-(a * s)) := by positivity
    rw [hc, hE₂]
    linarith
  have hg₁ : Continuous (fun s => c * exp (a * s) + E₂) := by fun_prop
  have hg₂ : Continuous (fun s => c * exp (-(a * s)) + E₂) := by fun_prop
  have hW := curveWidth_le (θ₀ := θ₀) hκc (fun s => (hκpos s).le) hκp hκint hH0 hg₁ hg₂ hb1 hb2
  have hI1 := integral_le_exp_left (h := H / 2) (s := 0) hg₁ ha hc0 (by linarith)
    (fun t _ => le_rfl)
  rw [show -(H / 2) = -H / 2 by ring] at hI1
  have hI2 := integral_le_exp_right (h := H / 2) (s := 0) hg₂ ha hc0 (by linarith)
    (fun t _ => le_rfl)
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, zero_add, sub_zero] at hI1 hI2
  -- the error terms are bounded
  have hHe : H * e ≤ 4 / a := by
    have h1 := mul_exp_neg_half_le ha H
    have h2 : exp (-(a / 4 * H)) ≤ 1 := Real.exp_le_one_iff.2
      (by have : 0 ≤ a / 4 * H := by positivity
          linarith)
    have h3 : 4 / a * exp (-(a / 4 * H)) ≤ 4 / a := by
      have : 0 ≤ 4 / a := by positivity
      nlinarith
    linarith
  have hHe2 : H ^ 2 * e ≤ (8 / a) ^ 2 := by
    have ha2 : (0 : ℝ) < a / 2 := by positivity
    have h1 := mul_exp_neg_half_le ha2 H
    have h2 : exp (-(a / 2 / 4 * H)) ≤ 1 := Real.exp_le_one_iff.2
      (by have : 0 ≤ a / 2 / 4 * H := by positivity
          linarith)
    have h3 : H * exp (-(a / 2 / 2 * H)) ≤ 8 / a := by
      have : 4 / (a / 2) = 8 / a := by field_simp; norm_num
      have : 0 ≤ 4 / (a / 2) := by positivity
      nlinarith
    have h4 : 0 ≤ H * exp (-(a / 2 / 2 * H)) := by positivity
    have h5 : H ^ 2 * e = (H * exp (-(a / 2 / 2 * H))) ^ 2 := by
      rw [he, mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [h5]
    exact pow_le_pow_left₀ h4 h3 2
  have hHE₂ : H * E₂ = 17 * π / 2 * A * (H * e) + 8 * A * (H ^ 2 * e) := by
    rw [hE₂, hE]; ring
  have hk1 : 17 * π / 2 * A * (H * e) ≤ 17 * π / 2 * A * (4 / a) :=
    mul_le_mul_of_nonneg_left hHe (by positivity)
  have hk2 : 8 * A * (H ^ 2 * e) ≤ 8 * A * (8 / a) ^ 2 :=
    mul_le_mul_of_nonneg_left hHe2 (by positivity)
  have : 2 * c / a = c / a + c / a := by ring
  linarith

end Ovals

end
