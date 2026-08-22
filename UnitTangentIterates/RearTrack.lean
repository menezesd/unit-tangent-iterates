import Mathlib
import UnitTangentIterates.Shadowing

/-!
# Reconstructing the rear track from the selected steering solution

This file formalizes the geometric half of the lemma *Selected inverse on the
closed strip* of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates*: once a periodic solution `δ` of the steering equation
`δ_s = K - sin δ` has been found inside the selected strip
`0 ≤ δ ≤ arcsin κ̂`, it **defines a regular convex rear track**.

Given a front `F` with unit tangent `e^{iΘ}`, `Θ_s = K`, and a steering angle
`δ`, put

`Ψ = Θ - δ`,  `x(s) = ∫₀ˢ cos δ`,  `R = F - e^{iΨ}`.

Then:

* `hasDerivAt_rearAngle` : `Ψ_s = sin δ`;
* `hasDerivAt_rearTrack` : `R_s = cos δ · e^{iΨ}`, so `e^{iΨ}` is the unit
  tangent of `R` wherever `cos δ > 0`, and `x` is its arclength;
* `unitTangentMap_rearTrack` : `𝒯R = R + τ_R = F`, i.e. the reconstructed
  curve really is a rear track of `F`;
* `strictMono_rearArclength`, `hasDerivAt_rearArclength` : on the selected
  strip `x_s = cos δ ≥ √(1-κ̂²) > 0`, so the rear is regular;
* `rear_curvature_eq_tan`, `rear_curvature_nonneg` : the rear curvature is
  `dΨ/dx = tan δ ≥ 0`, so the rear track is convex;
* `rear_periodic` : if `δ` is `P`-periodic and the front tangent turns by
  `2π` over a period, then the rear tangent direction is `P`-periodic as well.
-/

noncomputable section

open Real Complex MeasureTheory intervalIntegral

namespace RearTrack

variable {F : ℝ → ℂ} {Θ δ K : ℝ → ℝ}

/-- The rear tangent angle `Ψ = Θ - δ`. -/
def rearAngle (Θ δ : ℝ → ℝ) : ℝ → ℝ := fun s => Θ s - δ s

/-- The rear arclength `x(s) = ∫₀ˢ cos δ` measured from the marked point. -/
def rearArclength (δ : ℝ → ℝ) : ℝ → ℝ := fun s => ∫ u in (0:ℝ)..s, Real.cos (δ u)

/-- The rear track `R = F - e^{iΨ}` reconstructed from the steering angle. -/
def rearTrack (F : ℝ → ℂ) (Θ δ : ℝ → ℝ) : ℝ → ℂ :=
  fun s => F s - Complex.exp (Complex.I * (rearAngle Θ δ s : ℂ))

/-! ### The differential relations -/

/-- The rear tangent angle turns at rate `sin δ`. -/
theorem hasDerivAt_rearAngle {s : ℝ} (hΘ : HasDerivAt Θ (K s) s)
    (hδ : HasDerivAt δ (K s - Real.sin (δ s)) s) :
    HasDerivAt (rearAngle Θ δ) (Real.sin (δ s)) s := by
  have h := hΘ.sub hδ
  simpa [rearAngle] using h

/-- The derivative of the complex unit tangent `e^{iΨ}`. -/
theorem hasDerivAt_expRearAngle {s : ℝ} (hΘ : HasDerivAt Θ (K s) s)
    (hδ : HasDerivAt δ (K s - Real.sin (δ s)) s) :
    HasDerivAt (fun σ => Complex.exp (Complex.I * (rearAngle Θ δ σ : ℂ)))
      (Complex.I * (Real.sin (δ s) : ℂ)
        * Complex.exp (Complex.I * (rearAngle Θ δ s : ℂ))) s := by
  have hang := hasDerivAt_rearAngle hΘ hδ
  have hc : HasDerivAt (fun σ => (rearAngle Θ δ σ : ℂ)) ((Real.sin (δ s) : ℂ)) s := by
    simpa using (hang.ofReal_comp)
  have hmul : HasDerivAt (fun σ => Complex.I * (rearAngle Θ δ σ : ℂ))
      (Complex.I * (Real.sin (δ s) : ℂ)) s := hc.const_mul Complex.I
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.cexp

/-- **The rear track is regular with unit tangent `e^{iΨ}` and speed `cos δ`.** -/
theorem hasDerivAt_rearTrack {s : ℝ}
    (hF : HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : HasDerivAt Θ (K s) s) (hδ : HasDerivAt δ (K s - Real.sin (δ s)) s) :
    HasDerivAt (rearTrack F Θ δ)
      ((Real.cos (δ s) : ℂ) * Complex.exp (Complex.I * (rearAngle Θ δ s : ℂ))) s := by
  have h := hF.sub (hasDerivAt_expRearAngle hΘ hδ)
  have hsplit : Complex.exp (Complex.I * (Θ s : ℂ))
      = Complex.exp (Complex.I * (rearAngle Θ δ s : ℂ))
        * Complex.exp (Complex.I * (δ s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp [rearAngle]
    ring
  have hEuler : Complex.exp (Complex.I * (δ s : ℂ))
      = (Real.cos (δ s) : ℂ) + Complex.I * (Real.sin (δ s) : ℂ) := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin, mul_comm]
  refine h.congr_deriv ?_
  rw [hsplit, hEuler]
  ring

/-- **The reconstructed curve is a rear track of `F`**: adding its unit tangent
`e^{iΨ}` returns the front, `𝒯R = F`. -/
theorem unitTangentMap_rearTrack (s : ℝ) :
    rearTrack F Θ δ s + Complex.exp (Complex.I * (rearAngle Θ δ s : ℂ)) = F s := by
  simp [rearTrack]

/-! ### Regularity and convexity on the selected strip -/

theorem hasDerivAt_rearArclength (hδc : Continuous δ) (s : ℝ) :
    HasDerivAt (rearArclength δ) (Real.cos (δ s)) s := by
  have hc : Continuous fun u => Real.cos (δ u) := Real.continuous_cos.comp hδc
  simpa [rearArclength] using (hc.integral_hasStrictDerivAt (0:ℝ) s).hasDerivAt

/-- On the selected strip the rear speed is bounded below by `√(1-κ̂²) > 0`. -/
theorem rear_speed_ge {kap : ℝ} (hkap : kap < 1) (hkap0 : 0 ≤ kap) {s : ℝ}
    (hd0 : 0 ≤ δ s) (hd1 : δ s ≤ Real.arcsin kap) :
    0 < Real.cos (δ s) := by
  have h := Shadowing.cos_ge_of_mem_strip hd0 hd1
  have hpos : 0 < Real.sqrt (1 - kap ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  linarith

/-- **The rear is regular**: its arclength is strictly increasing. -/
theorem strictMono_rearArclength (hδc : Continuous δ) {kap : ℝ} (hkap : kap < 1)
    (hkap0 : 0 ≤ kap) (hd0 : ∀ s, 0 ≤ δ s) (hd1 : ∀ s, δ s ≤ Real.arcsin kap) :
    StrictMono (rearArclength δ) := by
  refine strictMono_of_deriv_pos ?_
  intro s
  rw [(hasDerivAt_rearArclength hδc s).deriv]
  exact rear_speed_ge hkap hkap0 (hd0 s) (hd1 s)

/-- **The rear curvature is `tan δ`**: the rear tangent angle turns at rate
`tan δ` with respect to rear arclength, `Ψ_s = tan δ · x_s`. -/
theorem rear_curvature_eq_tan {s : ℝ} (hΘ : HasDerivAt Θ (K s) s)
    (hδ : HasDerivAt δ (K s - Real.sin (δ s)) s) (hc : Real.cos (δ s) ≠ 0) :
    HasDerivAt (rearAngle Θ δ) (Real.tan (δ s) * Real.cos (δ s)) s := by
  have h := hasDerivAt_rearAngle hΘ hδ
  rwa [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hc]

/-- **The rear track is convex** on the selected strip: its curvature `tan δ`
is nonnegative. -/
theorem rear_curvature_nonneg {kap : ℝ} (hkap : kap < 1) (hkap0 : 0 ≤ kap) {s : ℝ}
    (hd0 : 0 ≤ δ s) (hd1 : δ s ≤ Real.arcsin kap) :
    0 ≤ Real.tan (δ s) := by
  have hcos : 0 < Real.cos (δ s) := rear_speed_ge hkap hkap0 hd0 hd1
  have hsin : 0 ≤ Real.sin (δ s) := by
    have harc : Real.arcsin kap ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two kap
    exact Real.sin_nonneg_of_nonneg_of_le_pi hd0 (by linarith [Real.pi_pos])
  rw [Real.tan_eq_sin_div_cos]
  positivity

/-! ### Periodicity -/

/-- If the steering angle is `P`-periodic and the front tangent angle increases
by `2π` over a period, then the rear unit tangent is `P`-periodic: the
reconstructed rear track closes up. -/
theorem rearTangent_periodic {P : ℝ} (hδ : Function.Periodic δ P)
    (hΘ : ∀ s, Θ (s + P) = Θ s + 2 * Real.pi) (s : ℝ) :
    Complex.exp (Complex.I * (rearAngle Θ δ (s + P) : ℂ))
      = Complex.exp (Complex.I * (rearAngle Θ δ s : ℂ)) := by
  have h : rearAngle Θ δ (s + P) = rearAngle Θ δ s + 2 * Real.pi := by
    simp [rearAngle, hΘ s, hδ s]
    ring
  have hpush : ((rearAngle Θ δ s + 2 * Real.pi : ℝ) : ℂ)
      = (rearAngle Θ δ s : ℂ) + 2 * (Real.pi : ℂ) := by push_cast; ring
  rw [h, hpush, mul_add, Complex.exp_add,
    show Complex.I * (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) * Complex.I from by ring,
    Complex.exp_two_pi_mul_I, mul_one]

end RearTrack
