import Mathlib
import UnitTangentIterates.CurvatureInterpolation

/-!
# Cores of the exact two-cap pairs

This file formalizes the self-contained computational ingredients of the
proposition *Exact two-cap pairs* of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*.

With the periodized steering mass `Y_H`, the paper sets
`δ_H = arcsin Y_H`, `c_H = √(1 - Y_H²)`, `K_H = δ_H' + Y_H` and builds the
front `F_H` with `F_H' = τ(Θ_H)`, `Θ_H' = K_H`, and the rear
`R_H = F_H - τ(Ψ_H)` with `Ψ_H = Θ_H - δ_H`.

Formalized here:

* `integral_curvature_eq_pi` : the total turning over one period is `π`,
  because `δ_H` is periodic and `∫₀^H Y_H = π`;
* `rear_hasDerivAt`, `rear_hasDerivAt_arcsin` : the rear track equation
  `R_H' = c_H τ(Ψ_H)`, so that the rear is traversed with speed `c_H`;
* `perimeter_defect` : `H - P(H) = ∫₀^H (1 - √(1 - Y_H²))`, the paper's
  `∫ Φ(Y_H)` with `Φ(z) = 1 - √(1 - z²)`;
* `front_curvature_ge`, `front_curvature_pos` : the positivity of the front
  curvature from the periodization error bound and `K_* ≥ b₀ y`.

The tangent direction `τ` is the one already introduced in
`UnitTangentIterates.CurvatureInterpolation`.
-/

noncomputable section

open Real MeasureTheory intervalIntegral CurvatureInterpolation

namespace TwoCapPairs

/-! ### Elementary properties of the tangent direction -/

theorem tau_add (a b : ℝ) : tau (a + b) = tau a * tau b := by
  simp [tau, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem tau_eq (a : ℝ) : tau a = (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I := by
  simp [tau, Complex.exp_mul_I]

/-! ### Total turning over one period -/

/-- **Total turning.**  If the steering angle `δ` is `H`-periodic and the
steering mass has total integral `π` over a period, then the front curvature
`K = δ' + Y` also has total integral `π`: the front tangent reverses after one
period. -/
theorem integral_curvature_eq_pi {delta dp Y : ℝ → ℝ} {H : ℝ}
    (hd : ∀ s, HasDerivAt delta (dp s) s) (hdc : Continuous dp)
    (hper : Function.Periodic delta H)
    (hYi : IntervalIntegrable Y volume 0 H)
    (hY : ∫ s in (0:ℝ)..H, Y s = Real.pi) :
    ∫ s in (0:ℝ)..H, (dp s + Y s) = Real.pi := by
  have hdpi : IntervalIntegrable dp volume 0 H := hdc.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hdpi hYi, hY]
  have hint : ∫ s in (0:ℝ)..H, dp s = delta H - delta 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hdpi
  have h0 : delta H = delta 0 := by simpa using hper 0
  rw [hint, h0]
  ring

/-! ### The rear track equation -/

/-- **The rear track equation.**  If the front satisfies `F' = τ(Ψ + δ)` and
the rear tangent angle satisfies `Ψ' = Y = sin δ`, then the rear
`R = F - τ(Ψ)` satisfies `R' = (cos δ) τ(Ψ)`. -/
theorem rear_hasDerivAt {F : ℝ → ℂ} {Psi : ℝ → ℝ} {Yv dv s : ℝ}
    (hF : HasDerivAt F (tau (Psi s + dv)) s)
    (hPsi : HasDerivAt Psi Yv s)
    (hsin : Real.sin dv = Yv) :
    HasDerivAt (fun t => F t - tau (Psi t)) ((Real.cos dv : ℂ) * tau (Psi s)) s := by
  have htau : HasDerivAt (fun t => tau (Psi t)) ((Yv : ℂ) * (Complex.I * tau (Psi s))) s := by
    simpa [Function.comp, Complex.real_smul, mul_comm] using
      (hasDerivAt_tau (Psi s)).scomp s hPsi
  have h := hF.sub htau
  convert h using 1
  rw [tau_add, tau_eq dv, ← hsin]
  ring

/-- The rear track equation with the paper's `δ = arcsin Y` and
`c = √(1 - Y²)`. -/
theorem rear_hasDerivAt_arcsin {F : ℝ → ℂ} {Psi : ℝ → ℝ} {Yv s : ℝ}
    (hY : |Yv| ≤ 1)
    (hF : HasDerivAt F (tau (Psi s + Real.arcsin Yv)) s)
    (hPsi : HasDerivAt Psi Yv s) :
    HasDerivAt (fun t => F t - tau (Psi t))
      ((Real.sqrt (1 - Yv ^ 2) : ℂ) * tau (Psi s)) s := by
  have habs := abs_le.mp hY
  have hsin : Real.sin (Real.arcsin Yv) = Yv := Real.sin_arcsin habs.1 habs.2
  have hcos : Real.cos (Real.arcsin Yv) = Real.sqrt (1 - Yv ^ 2) := Real.cos_arcsin Yv
  rw [← hcos]
  exact rear_hasDerivAt hF hPsi hsin

/-! ### The perimeter defect -/

/-- **The perimeter defect.**  With `P(H) = ∫₀^H c_H` and `c_H = √(1 - Y_H²)`,
one has `H - P(H) = ∫₀^H Φ(Y_H)` where `Φ(z) = 1 - √(1 - z²)`. -/
theorem perimeter_defect {Y : ℝ → ℝ} {H : ℝ}
    (hc : IntervalIntegrable (fun s => Real.sqrt (1 - Y s ^ 2)) volume 0 H) :
    H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - Y s ^ 2))
      = ∫ s in (0:ℝ)..H, (1 - Real.sqrt (1 - Y s ^ 2)) := by
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const hc]
  simp

/-! ### Positivity of the front curvature -/

/-- **Front curvature lower bound.**  If `K = ∑ K_* + E` with
`|E| ≤ Ce^{-βH} Y` and `∑ K_* ≥ b₀ Y`, then `K ≥ (b₀ - Ce^{-βH}) Y`. -/
theorem front_curvature_ge {K Ksum E Y b0 C beta H : ℝ}
    (hK : K = Ksum + E) (hE : |E| ≤ C * Real.exp (-beta * H) * Y)
    (hKsum : b0 * Y ≤ Ksum) :
    (b0 - C * Real.exp (-beta * H)) * Y ≤ K := by
  have h1 : -(C * Real.exp (-beta * H) * Y) ≤ E := (abs_le.mp hE).1
  rw [hK]
  nlinarith

/-- For `H` large enough that `Ce^{-βH} < b₀`, the front curvature is positive
wherever the steering mass is. -/
theorem front_curvature_pos {K Ksum E Y b0 C beta H : ℝ}
    (hK : K = Ksum + E) (hE : |E| ≤ C * Real.exp (-beta * H) * Y)
    (hKsum : b0 * Y ≤ Ksum) (hY : 0 < Y) (hsmall : C * Real.exp (-beta * H) < b0) :
    0 < K := by
  have h := front_curvature_ge hK hE hKsum
  nlinarith

end TwoCapPairs
