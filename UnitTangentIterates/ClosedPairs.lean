module

public import UnitTangentIterates.CurveFromCurvature
public import UnitTangentIterates.RearFront

/-!
# Closed rear–front pairs from a periodic steering angle (Proposition 4.3, construction)

Let `δ` be a `C¹`, `L`-periodic steering angle with `0 < δ < π/2` and `∫₀ᴸ sin δ = π`.
Put `K = δ' + sin δ`.  Then `∫₀ᴸ K = π`, so the curve `F` of curvature `K` built in
`CurveFromCurvature` is centered and centrally symmetric (`F(s + L) = -F(s)`), and the rear
`R = F - τ(Θ - δ)` satisfies

* `𝒯 R = F`;
* `R(s + L) = -R(s)`;
* `R` is regular with speed `cos δ` (so its half-perimeter is `∫₀ᴸ cos δ`);
* the curvature of `R` is `tan δ > 0`, and the curvature of `F` is `K`.

In the paper this is applied to `δ_H = arcsin Y_H`, for which `sin δ_H = Y_H` and
`∫₀ᴴ Y_H = ∫_ℝ y = π`.
-/

@[expose] public section

namespace Ovals

open Complex Real intervalIntegral

variable {δ δ' : ℝ → ℝ} {L θ₀ : ℝ}

/-- The front curvature `K = δ' + sin δ` of a steering angle. -/
noncomputable def pairCurvature (δ δ' : ℝ → ℝ) (s : ℝ) : ℝ := δ' s + Real.sin (δ s)

/-- The front of the pair: the centered curve with curvature `δ' + sin δ`. -/
noncomputable def pairFront (θ₀ : ℝ) (δ δ' : ℝ → ℝ) (L : ℝ) : ℝ → ℂ :=
  curveOfCurvature θ₀ (pairCurvature δ δ') L

/-- The rear of the pair: `R = F - τ(Θ - δ)`. -/
noncomputable def pairRear (θ₀ : ℝ) (δ δ' : ℝ → ℝ) (L : ℝ) : ℝ → ℂ :=
  rearCurve (pairFront θ₀ δ δ' L) (angleOfCurvature θ₀ (pairCurvature δ δ')) δ

/-- The derivative of a periodic function is periodic. -/
theorem periodic_of_hasDerivAt (hδ : ∀ s, HasDerivAt δ (δ' s) s)
    (hδp : Function.Periodic δ L) : Function.Periodic δ' L := by
  intro s
  have h1 : HasDerivAt (fun x => δ (x + L)) (δ' (s + L)) s := by
    simpa using (hδ (s + L)).comp s ((hasDerivAt_id s).add_const L)
  have h2 : HasDerivAt (fun x => δ (x + L)) (δ' s) s := by
    have : (fun x => δ (x + L)) = δ := funext hδp
    rw [this]; exact hδ s
  exact h1.unique h2

section

variable (hδ : ∀ s, HasDerivAt δ (δ' s) s) (hδ'c : Continuous δ')

include hδ hδ'c in
theorem continuous_pairCurvature : Continuous (pairCurvature δ δ') := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun s => (hδ s).continuousAt
  exact hδ'c.add (Real.continuous_sin.comp hδc)

include hδ hδ'c in
/-- `∫₀ᴸ K = ∫₀ᴸ sin δ` for a periodic steering angle. -/
theorem integral_pairCurvature (hδp : Function.Periodic δ L) :
    ∫ s in (0 : ℝ)..L, pairCurvature δ δ' s = ∫ s in (0 : ℝ)..L, Real.sin (δ s) := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun s => (hδ s).continuousAt
  unfold pairCurvature
  rw [intervalIntegral.integral_add (f := δ') (g := fun s => Real.sin (δ s))
    (hδ'c.intervalIntegrable _ _)
    ((Real.continuous_sin.comp hδc).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hδ s)
      (hδ'c.intervalIntegrable _ _)]
  have := hδp 0
  rw [zero_add] at this
  rw [this]; ring

include hδ in
theorem hasDerivAt_steering_pair (s : ℝ) :
    HasDerivAt δ (pairCurvature δ δ' s - Real.sin (δ s)) s := by
  unfold pairCurvature; simpa using hδ s

include hδ hδ'c in
/-- **Proposition 4.3 (construction of the closed pair).**  For a `C¹` `L`-periodic
steering angle `0 < δ < π/2` with `∫₀ᴸ sin δ = π`, the front `F` and rear `R` satisfy
`𝒯 R = F`, both are centrally symmetric with half-period `L`, `F` is parametrized by arclength
with curvature `δ' + sin δ`, and `R` is regular with speed `cos δ` and curvature
`tan δ > 0`. -/
theorem closed_pair (hδp : Function.Periodic δ L)
    (hδpos : ∀ s, 0 < δ s) (hδlt : ∀ s, δ s < π / 2)
    (hint : ∫ s in (0 : ℝ)..L, Real.sin (δ s) = π) :
    unitTangentTransform (pairRear θ₀ δ δ' L) = pairFront θ₀ δ δ' L ∧
    (∀ s, pairFront θ₀ δ δ' L (s + L) = -pairFront θ₀ δ δ' L s) ∧
    (∀ s, pairRear θ₀ δ δ' L (s + L) = -pairRear θ₀ δ δ' L s) ∧
    (∀ s, ‖deriv (pairFront θ₀ δ δ' L) s‖ = 1 ∧
      curvature (pairFront θ₀ δ δ' L) s = δ' s + Real.sin (δ s)) ∧
    (∀ s, ‖deriv (pairRear θ₀ δ δ' L) s‖ = Real.cos (δ s) ∧
      curvature (pairRear θ₀ δ δ' L) s = Real.tan (δ s) ∧
      0 < curvature (pairRear θ₀ δ δ' L) s) := by
  have hKc := continuous_pairCurvature hδ hδ'c
  have hKp : Function.Periodic (pairCurvature δ δ') L := fun s => by
    unfold pairCurvature; rw [periodic_of_hasDerivAt hδ hδp s, hδp s]
  have hKint : ∫ s in (0 : ℝ)..L, pairCurvature δ δ' s = π := by
    rw [integral_pairCurvature hδ hδ'c hδp, hint]
  have hF : ∀ s, HasDerivAt (pairFront θ₀ δ δ' L)
      (tau (angleOfCurvature θ₀ (pairCurvature δ δ') s)) s :=
    fun s => hasDerivAt_curveOfCurvature hKc s
  have hΘ : ∀ s, HasDerivAt (angleOfCurvature θ₀ (pairCurvature δ δ'))
      (pairCurvature δ δ' s) s := fun s => hasDerivAt_angleOfCurvature hKc s
  have hδ2 := hasDerivAt_steering_pair (δ' := δ') hδ
  have hcos : ∀ s, 0 < Real.cos (δ s) := fun s =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hδpos s, Real.pi_pos], hδlt s⟩
  have hFsym : ∀ s, pairFront θ₀ δ δ' L (s + L) = -pairFront θ₀ δ δ' L s :=
    fun s => curveOfCurvature_add_period hKc hKp hKint s
  refine ⟨unitTangentTransform_rearCurve hF hΘ hδ2 hcos, hFsym, fun s => ?_,
    fun s => ⟨norm_deriv_curveOfCurvature hKc s, curvature_curveOfCurvature hKc s⟩,
    fun s => ⟨?_, curvature_rearCurve hF hΘ hδ2 hcos s, ?_⟩⟩
  · unfold pairRear rearCurve
    rw [hFsym s, angleOfCurvature_add_period hKc hKp hKint s, hδp s,
      show angleOfCurvature θ₀ (pairCurvature δ δ') s + π - δ s =
        (angleOfCurvature θ₀ (pairCurvature δ δ') s - δ s) + π by ring, tau_add_pi]
    ring
  · unfold pairRear
    rw [deriv_rearCurve hF hΘ hδ2, norm_mul, norm_tau, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hcos s)]
  · unfold pairRear
    rw [curvature_rearCurve hF hΘ hδ2 hcos s]
    exact Real.tan_pos_of_pos_of_lt_pi_div_two (hδpos s) (hδlt s)

end

end Ovals

end
