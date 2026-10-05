module

public import UnitTangentIterates.ClosedPairs
public import UnitTangentIterates.FrontError
public import UnitTangentIterates.PeriodizationIntegral

/-!
# Proposition 4.3 for the periodized pulse

Let `y` be a pulse with the properties of Lemma 3.5: `0 < y ≤ b < 1`, `y ≤ A e^{-a|t|}`,
relative derivative bounds `|y'|, |y''| ≤ D y`, mass `∫_ℝ y = π`, and lower bound
`K_* ≥ b₀ y` for the isolated front curvature `K_* = y + y'/√(1 - y²)`.

For all sufficiently large `H`, the periodization `Y_H` takes values in `(0, 1)`, and the
steering angle `δ_H = arcsin Y_H` produces (via `closed_pair`) an exact closed pair
`𝒯 R_H = F_H` of centrally symmetric curves with half-perimeters `H` (front) and
`∫₀ᴴ cos δ_H = ∫₀ᴴ c_H` (rear), whose curvatures are both strictly positive.  The front
curvature is `K_H = Y_H + Y_H'/c_H` and the rear curvature is `tan δ_H = Y_H / c_H`.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- The periodized steering angle `δ_H = arcsin Y_H`. -/
noncomputable def periodizedAngle (y : ℝ → ℝ) (H : ℝ) (s : ℝ) : ℝ := Real.arcsin (periodize y H s)

/-- Its derivative `δ_H' = Y_H' / √(1 - Y_H²)`, with `Y_H' = periodize y' H`. -/
noncomputable def periodizedAngleDeriv (y y' : ℝ → ℝ) (H : ℝ) (s : ℝ) : ℝ :=
  periodize y' H s / √(1 - periodize y H s ^ 2)

/-- **Proposition 4.3 (closed pairs from the periodized pulse).**  For all sufficiently large
`H`, the angle `δ_H = arcsin Y_H` defines an exact pair `𝒯 R_H = F_H` of centrally symmetric
closed curves (half-period `H`); `F_H` is parametrized by arclength with curvature
`K_H = frontCurv Y_H > 0`; `R_H` has speed `cos δ_H` and curvature `tan δ_H > 0`. -/
theorem periodized_closed_pair {y y' y'' : ℝ → ℝ} {A a D b b₀ : ℝ} (θ₀ : ℝ)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hy' : ∀ t, HasDerivAt y' (y'' t) t)
    (hypos : ∀ t, 0 < y t) (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a)
    (hyD : ∀ t, |y' t| ≤ D * y t) (hyD2 : ∀ t, |y'' t| ≤ D * y t)
    (hyb : ∀ t, y t ≤ b) (hb : b < 1) (hmass : ∫ t, y t = π)
    (hb₀ : 0 < b₀) (hK : ∀ t, b₀ * y t ≤ frontCurv y t) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀,
      let δ := periodizedAngle y H
      let δ' := periodizedAngleDeriv y y' H
      (∀ s, 0 < periodize y H s ∧ periodize y H s < 1) ∧
      unitTangentTransform (pairRear θ₀ δ δ' H) = pairFront θ₀ δ δ' H ∧
      (∀ s, pairFront θ₀ δ δ' H (s + H) = -pairFront θ₀ δ δ' H s) ∧
      (∀ s, pairRear θ₀ δ δ' H (s + H) = -pairRear θ₀ δ δ' H s) ∧
      (∀ s, ‖deriv (pairFront θ₀ δ δ' H) s‖ = 1 ∧
        curvature (pairFront θ₀ δ δ' H) s = frontCurv (periodize y H) s ∧
        0 < curvature (pairFront θ₀ δ δ' H) s) ∧
      (∀ s, ‖deriv (pairRear θ₀ δ δ' H) s‖ = √(1 - periodize y H s ^ 2) ∧
        curvature (pairRear θ₀ δ δ' H) s =
          periodize y H s / √(1 - periodize y H s ^ 2) ∧
        0 < curvature (pairRear θ₀ δ δ' H) s) := by
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
  have hy''A := hexp hyD2
  obtain ⟨C, β, L₀, hβ, hfe⟩ := front_error hy hy0 hyA ha hyD hyb hb
  -- choose `H₀` so that the periodization stays below `(1 + b)/2` and `C e^{-βH} < b₀`
  have hev1 : ∀ᶠ H in atTop, 8 * A * exp (-(a / 2 * H)) < (1 - b) / 2 := by
    have ht : Tendsto (fun H : ℝ => 8 * A * exp (-(a / 2 * H))) atTop (𝓝 (8 * A * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < a / 2))).const_mul _
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ H in atTop, C * exp (-(β * H)) < b₀ := by
    have ht : Tendsto (fun H : ℝ => C * exp (-(β * H))) atTop (𝓝 (C * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hβ)).const_mul _
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds hb₀)
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨max (max (2 / a) L₀) H₁, fun H hH => ?_⟩
  have hHa : 2 / a ≤ H := (le_max_left _ _).trans ((le_max_left _ _).trans hH)
  have hHL : L₀ ≤ H := (le_max_right _ _).trans ((le_max_left _ _).trans hH)
  have hH1 : H₁ ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hHa
  obtain ⟨hsmall1, hsmall2⟩ := hH₁ H hH1
  set Y := periodize y H with hYdef
  -- basic properties of `Y`
  have hYpos : ∀ s, 0 < Y s := fun s => by
    have hs := summable_periodize hy0 hyA ha hH0 s
    have := hs.le_tsum 0 (fun j _ => hy0 _)
    simp only [Int.cast_zero, zero_mul, sub_zero] at this
    exact (hypos s).trans_le this
  have hYlt : ∀ s, Y s < 1 := fun s => by
    have := periodize_le hyA' ha hyb hHa s
    linarith
  have hYd : ∀ s, HasDerivAt Y (periodize y' H s) s :=
    hasDerivAt_periodize hy hyA' hy'A ha hH0
  have hY'd : ∀ s, HasDerivAt (periodize y' H) (periodize y'' H s) s :=
    hasDerivAt_periodize hy' hy'A hy''A ha hH0
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun s => (hYd s).continuousAt
  have hY'c : Continuous (periodize y' H) :=
    continuous_iff_continuousAt.2 fun s => (hY'd s).continuousAt
  have hsq : ∀ s, 0 < 1 - Y s ^ 2 := fun s => by nlinarith [hYpos s, hYlt s]
  have hYp : Function.Periodic Y H := fun s => by
    have := periodize_sub_int_mul y H s (-1)
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add] at this
    exact this
  -- the steering angle
  have hδ : ∀ s, HasDerivAt (periodizedAngle y H) (periodizedAngleDeriv y y' H s) s := by
    intro s
    have h := (Real.hasDerivAt_arcsin (by linarith [hYpos s]) (hYlt s).ne).comp s (hYd s)
    unfold periodizedAngle periodizedAngleDeriv
    convert h using 1
    rw [← hYdef]; ring
  have hδ'c : Continuous (periodizedAngleDeriv y y' H) := by
    unfold periodizedAngleDeriv
    exact hY'c.div (Real.continuous_sqrt.comp (continuous_const.sub (hYc.pow 2)))
      (fun s => (Real.sqrt_pos.2 (hsq s)).ne')
  have hδp : Function.Periodic (periodizedAngle y H) H := fun s => by
    unfold periodizedAngle; rw [← hYdef, hYp s]
  have hsin : ∀ s, Real.sin (periodizedAngle y H s) = Y s := fun s =>
    Real.sin_arcsin (by linarith [hYpos s]) (hYlt s).le
  have hcos : ∀ s, Real.cos (periodizedAngle y H s) = √(1 - Y s ^ 2) := fun s =>
    Real.cos_arcsin _
  have hδpos : ∀ s, 0 < periodizedAngle y H s := fun s => Real.arcsin_pos.2 (hYpos s)
  have hδlt : ∀ s, periodizedAngle y H s < π / 2 := fun s => by
    unfold periodizedAngle
    exact lt_of_le_of_ne (Real.arcsin_le_pi_div_two _)
      (fun h => (hYlt s).ne (by rw [← Real.sin_arcsin (by linarith [hYpos s]) (hYlt s).le, h,
        Real.sin_pi_div_two]))
  have hint : ∫ s in (0 : ℝ)..H, Real.sin (periodizedAngle y H s) = π := by
    simp_rw [hsin]
    rw [hYdef, integral_periodize (hyc := continuous_iff_continuousAt.2 fun t =>
      (hy t).continuousAt) hyA' ha hH0, hmass]
  obtain ⟨hT, hFs, hRs, hF, hR⟩ := closed_pair (θ₀ := θ₀) hδ hδ'c hδp hδpos hδlt hint
  -- the front curvature is `frontCurv Y`
  have hKF : ∀ s, periodizedAngleDeriv y y' H s + Real.sin (periodizedAngle y H s) =
      frontCurv Y s := fun s => by
    rw [hsin, frontCurv, (hYd s).deriv]; unfold periodizedAngleDeriv; rw [← hYdef]; ring
  -- positivity of the front curvature
  have hKpos : ∀ s, 0 < frontCurv Y s := fun s => by
    obtain ⟨hKs, hfe'⟩ := hfe H hHL s
    have hsum := summable_periodize hy0 hyA ha hH0 s
    have hlow : b₀ * Y s ≤ ∑' m : ℤ, frontCurv y (s - m * H) := by
      rw [hYdef, periodize, ← tsum_mul_left]
      exact (hsum.mul_left b₀).tsum_le_tsum (fun m => hK _) hKs
    have := (abs_le.1 hfe').1
    have hpos : 0 < (b₀ - C * exp (-(β * H))) * Y s := mul_pos (by linarith) (hYpos s)
    rw [← hYdef] at this
    nlinarith
  refine ⟨fun s => ⟨hYpos s, hYlt s⟩, hT, hFs, hRs, fun s => ?_, fun s => ?_⟩
  · refine ⟨(hF s).1, by rw [(hF s).2, hKF], ?_⟩
    rw [(hF s).2, hKF]; exact hKpos s
  · refine ⟨by rw [(hR s).1, hcos], ?_, (hR s).2.2⟩
    rw [(hR s).2.1, Real.tan_eq_sin_div_cos, hsin, hcos]

end Ovals

end
