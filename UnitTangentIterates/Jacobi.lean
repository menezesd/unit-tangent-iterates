module

public import UnitTangentIterates.Embedded

/-!
# The Jacobi equation for the selected rear (equation (6.4) of Lemma 6.2)

Consider a path of fronts `F(t, u)` with speed `g = |∂ᵤF|` and tangent angle `Θ`, so
`∂ᵤF = g τ(Θ)`, and write its velocity as `∂ₜF = ξ τ(Θ) + η ν(Θ)` with `ν = iτ`.  The selected
rears are `R = F - τ(Θ - δ)`, where `δ(t, ·)` solves the steering equation
`∂ᵤδ = ∂ᵤΘ - g sin δ`; let `D = ∂ₜδ`, which solves the linearized equation
`∂ᵤD = ∂ᵤΘ̇ - ġ sin δ - g cos δ · D` (see `Ovals.steering_param_deriv`).  Equality of the mixed
partial derivatives `∂ₜ∂ᵤF = ∂ᵤ∂ₜF` amounts to

`g Θ̇ = ∂ᵤη + ξ ∂ᵤΘ`,  `ġ = ∂ᵤξ - η ∂ᵤΘ`.

In this file:

* `Ovals.rear_normal_velocity`: the normal velocity of the rear path is
  `η_R = ξ sin δ + η cos δ - (Θ̇ - D)`;
* `Ovals.jacobi_equation`: it satisfies `∂ᵤη_R = g η - g cos δ · η_R`, which is
  `(1 + ∂ₓ) η_R = sec δ · η` in rear arclength `dx = g cos δ du` (equation (6.4)).
-/

@[expose] public section

namespace Ovals

open Complex Real

/-- **The normal velocity of the rear.**  If the front moves with velocity
`ξ τ(Θ) + η iτ(Θ)` and the rear angle `Θ - δ` moves with speed `Θ̇ - D`, then the rear
`R = F - τ(Θ - δ)` moves with normal velocity `ξ sin δ + η cos δ - (Θ̇ - D)`. -/
theorem rear_normal_velocity (ξ η Θ δ Θdot D : ℝ) :
    (((ξ : ℂ) * tau Θ + (η : ℂ) * (I * tau Θ) - I * tau (Θ - δ) * ((Θdot - D : ℝ) : ℂ)) *
      (starRingEnd ℂ) (I * tau (Θ - δ))).re =
      ξ * Real.sin δ + η * Real.cos δ - (Θdot - D) := by
  have hΘ : tau Θ = tau (Θ - δ) * tau δ := by rw [← tau_add]; ring_nf
  rw [hΘ]
  have hc : (starRingEnd ℂ) (tau (Θ - δ)) * tau (Θ - δ) = 1 := conj_tau_mul_tau _
  have e : ((ξ : ℂ) * (tau (Θ - δ) * tau δ) + (η : ℂ) * (I * (tau (Θ - δ) * tau δ)) -
      I * tau (Θ - δ) * ((Θdot - D : ℝ) : ℂ)) * (starRingEnd ℂ) (I * tau (Θ - δ)) =
      ((ξ : ℂ) * tau δ + (η : ℂ) * (I * tau δ) - I * ((Θdot - D : ℝ) : ℂ)) * (-I) *
        ((starRingEnd ℂ) (tau (Θ - δ)) * tau (Θ - δ)) := by
    simp only [map_mul, Complex.conj_I]; ring
  rw [e, hc, mul_one, tau_eq]
  simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.mul_im, Complex.sub_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im]
  ring

/-- **The Jacobi equation (6.4).**  With the notation of the file header, the rear normal
velocity `η_R = ξ sin δ + η cos δ - (Θ̇ - D)` satisfies `∂ᵤη_R = g η - g cos δ · η_R`. -/
theorem jacobi_equation {ξ η g δ Θdot gdot D : ℝ → ℝ} {ξ' η' Θ' Θdot' : ℝ → ℝ} (u : ℝ)
    (hξ : HasDerivAt ξ (ξ' u) u) (hη : HasDerivAt η (η' u) u)
    (hδ : HasDerivAt δ (Θ' u - g u * Real.sin (δ u)) u)
    (hΘdot : HasDerivAt Θdot (Θdot' u) u)
    (hD : HasDerivAt D (Θdot' u - gdot u * Real.sin (δ u) -
      g u * Real.cos (δ u) * D u) u)
    (hrot : g u * Θdot u = η' u + ξ u * Θ' u) (hstretch : gdot u = ξ' u - η u * Θ' u) :
    HasDerivAt (fun u => ξ u * Real.sin (δ u) + η u * Real.cos (δ u) - (Θdot u - D u))
      (g u * η u - g u * Real.cos (δ u) *
        (ξ u * Real.sin (δ u) + η u * Real.cos (δ u) - (Θdot u - D u))) u := by
  have h1 := (hξ.mul hδ.sin).add (hη.mul hδ.cos)
  have h2 := h1.sub (hΘdot.sub hD)
  convert h2 using 1
  have hsc := Real.sin_sq_add_cos_sq (δ u)
  rw [hstretch] at *
  linear_combination (Real.cos (δ u)) * hrot - (g u * η u) * hsc

end Ovals

end
