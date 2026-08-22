import Mathlib

/-!
# One tangent step: rear and front tracks

This file formalizes the material of Section 2 of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*: the bicycle relations
relating a rear track `R` and its front track `F = 𝒯R`, and the
two quantitative ingredients of Lemma 2.1 (*Low-curvature inverse*): the
curvature bound `k_R ≤ κ/√(1-κ²)` and the contraction estimate behind the
uniqueness of the periodic solution.

Main results:

* `bicycle_relations` : `cos δ = x'` and `sin δ = x' k`, where `δ = Θ - Ψ` is
  the steering angle, `x` is rear arclength as a function of front arclength,
  and `k` is the rear curvature.
* `rear_curvature_eq_tan`, `rear_tangent_angle_deriv`, `front_curvature_eq`:
  the equations `k = tan δ`, `Ψ_s = sin δ` and `K = δ_s + sin δ`.
* `steering_deriv_angle` : the same equation in the tangent-angle
  parametrization, `δ_φ = 1 - q sin δ` with `q = 1/K`.
* `rear_curvature_le` : the bound `k_R = tan δ ≤ κ/√(1-κ²)`.
* `eq_zero_of_periodic_of_deriv_eq_neg_mul` : a periodic solution of
  `w' = -a w` with `a ≥ c > 0` vanishes identically; this is the uniqueness
  mechanism of Lemma 2.1.
-/

noncomputable section

open Real Complex

namespace Bicycle

section BicycleEquations

variable {F R : ℝ → ℂ} {x Θ Ψ k xp : ℝ → ℝ}

/-- The differentiated form of the link `F = 𝒯R`: in complex notation,
`e^{iΘ} = x' e^{iΨ}(1 + i k)`. -/
lemma bicycle_exp_identity
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hR : ∀ t, HasDerivAt R (Complex.exp (Complex.I * (Ψ t : ℂ))) t)
    (hΨ : ∀ t, HasDerivAt Ψ (k t) t)
    (hx : ∀ s, HasDerivAt x (xp s) s)
    (hlink : ∀ s, F s = R (x s) + Complex.exp (Complex.I * (Ψ (x s) : ℂ)))
    (s : ℝ) :
    Complex.exp (Complex.I * (Θ s : ℂ))
      = (xp s : ℂ) * Complex.exp (Complex.I * (Ψ (x s) : ℂ)) * (1 + Complex.I * (k (x s) : ℂ)) := by
  have hFeq : F = fun σ => R (x σ) + Complex.exp (Complex.I * (Ψ (x σ) : ℂ)) := funext hlink
  have h1 : HasDerivAt (fun σ => R (x σ))
      ((xp s : ℂ) * Complex.exp (Complex.I * (Ψ (x s) : ℂ))) s := by
    simpa [Function.comp_def] using (hR (x s)).scomp s (hx s)
  have hu : HasDerivAt (fun σ => Ψ (x σ)) (k (x s) * xp s) s := (hΨ (x s)).comp s (hx s)
  have hE : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)))
      (Complex.I * Complex.exp (Complex.I * (t : ℂ))) t := by
    intro t
    have h : HasDerivAt (fun t : ℝ => (Complex.I * (t : ℂ))) Complex.I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
    simpa [mul_comm] using h.cexp
  have h2 : HasDerivAt (fun σ => Complex.exp (Complex.I * (Ψ (x σ) : ℂ)))
      ((k (x s) * xp s : ℝ) • (Complex.I * Complex.exp (Complex.I * (Ψ (x s) : ℂ)))) s := by
    simpa [Function.comp_def] using (hE (Ψ (x s))).scomp s hu
  have h3 := h1.add h2
  rw [hFeq] at hF
  rw [(hF s).unique h3]
  push_cast [Complex.real_smul]
  ring

/-- **The bicycle relations.**  If `F s = R (x s) + τ_R (x s)` (that is, the
front track is the unit-tangent image of the rear track), where `Θ` and `Ψ` are
the tangent angles of `F` and `R`, `x` is the rear arclength as a function of
the front arclength `s`, and `k` is the rear curvature, then the steering angle
`δ = Θ - Ψ ∘ x` satisfies `cos δ = x'` and `sin δ = x' · k`. -/
theorem bicycle_relations
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hR : ∀ t, HasDerivAt R (Complex.exp (Complex.I * (Ψ t : ℂ))) t)
    (hΨ : ∀ t, HasDerivAt Ψ (k t) t)
    (hx : ∀ s, HasDerivAt x (xp s) s)
    (hlink : ∀ s, F s = R (x s) + Complex.exp (Complex.I * (Ψ (x s) : ℂ)))
    (s : ℝ) :
    Real.cos (Θ s - Ψ (x s)) = xp s ∧ Real.sin (Θ s - Ψ (x s)) = xp s * k (x s) := by
  have key := bicycle_exp_identity hF hR hΨ hx hlink s
  set d : ℝ := Θ s - Ψ (x s) with hd
  have hsplit : Complex.exp (Complex.I * (Θ s : ℂ))
      = Complex.exp (Complex.I * (d : ℂ)) * Complex.exp (Complex.I * (Ψ (x s) : ℂ)) := by
    rw [← Complex.exp_add, hd]
    push_cast
    ring_nf
  have hne : Complex.exp (Complex.I * (Ψ (x s) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have h6 : Complex.exp (Complex.I * (d : ℂ)) = (xp s : ℂ) * (1 + Complex.I * (k (x s) : ℂ)) := by
    apply mul_right_cancel₀ hne
    rw [← hsplit, key]
    ring
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at h6
  have hre := congrArg Complex.re h6
  have him := congrArg Complex.im h6
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im] at hre him
  constructor
  · linarith
  · nlinarith [hre, him]

/-- The rear curvature is the tangent of the steering angle (2.2). -/
theorem rear_curvature_eq_tan
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hR : ∀ t, HasDerivAt R (Complex.exp (Complex.I * (Ψ t : ℂ))) t)
    (hΨ : ∀ t, HasDerivAt Ψ (k t) t)
    (hx : ∀ s, HasDerivAt x (xp s) s)
    (hlink : ∀ s, F s = R (x s) + Complex.exp (Complex.I * (Ψ (x s) : ℂ)))
    (s : ℝ) (hc : Real.cos (Θ s - Ψ (x s)) ≠ 0) :
    k (x s) = Real.tan (Θ s - Ψ (x s)) := by
  obtain ⟨hcos, hsin⟩ := bicycle_relations hF hR hΨ hx hlink s
  have hxp : xp s ≠ 0 := by rw [← hcos]; exact hc
  rw [Real.tan_eq_sin_div_cos, hsin, hcos]
  field_simp

/-- The rear tangent angle turns at rate `sin δ` with respect to front
arclength. -/
theorem rear_tangent_angle_deriv
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hR : ∀ t, HasDerivAt R (Complex.exp (Complex.I * (Ψ t : ℂ))) t)
    (hΨ : ∀ t, HasDerivAt Ψ (k t) t)
    (hx : ∀ s, HasDerivAt x (xp s) s)
    (hlink : ∀ s, F s = R (x s) + Complex.exp (Complex.I * (Ψ (x s) : ℂ)))
    (s : ℝ) :
    HasDerivAt (fun σ => Ψ (x σ)) (Real.sin (Θ s - Ψ (x s))) s := by
  obtain ⟨-, hsin⟩ := bicycle_relations hF hR hΨ hx hlink s
  have hu : HasDerivAt (fun σ => Ψ (x σ)) (k (x s) * xp s) s := (hΨ (x s)).comp s (hx s)
  rw [hsin, mul_comm]
  exact hu

/-- The front curvature satisfies `K = δ_s + sin δ` (2.2). -/
theorem front_curvature_eq
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hR : ∀ t, HasDerivAt R (Complex.exp (Complex.I * (Ψ t : ℂ))) t)
    (hΨ : ∀ t, HasDerivAt Ψ (k t) t)
    (hx : ∀ s, HasDerivAt x (xp s) s)
    (hlink : ∀ s, F s = R (x s) + Complex.exp (Complex.I * (Ψ (x s) : ℂ)))
    {K : ℝ → ℝ} (hΘ : ∀ s, HasDerivAt Θ (K s) s) (s : ℝ) :
    HasDerivAt (fun σ => Θ σ - Ψ (x σ)) (K s - Real.sin (Θ s - Ψ (x s))) s :=
  (hΘ s).sub (rear_tangent_angle_deriv hF hR hΨ hx hlink s)

/-- **The bicycle equation in the tangent-angle parametrization** (2.3): if the
front is strictly convex and is parametrized by its tangent angle, with radius
of curvature `q = 1/K`, then the steering angle satisfies `δ_φ = 1 - q sin δ`. -/
theorem steering_deriv_angle {Phi D : ℝ → ℝ} {K d s : ℝ}
    (hPhi : HasDerivAt Phi K s) (hK : K ≠ 0)
    (hD : HasDerivAt D d (Phi s))
    (hsteer : HasDerivAt (fun σ => D (Phi σ)) (K - Real.sin (D (Phi s))) s) :
    d = 1 - (1 / K) * Real.sin (D (Phi s)) := by
  have hchain : HasDerivAt (fun σ => D (Phi σ)) (d * K) s := hD.comp s hPhi
  have huniq := hchain.unique hsteer
  field_simp
  linarith [huniq]

/-- The same equation, read off directly from the bicycle relations: writing the
steering angle as a function `D` of the front tangent angle `Θ`, and assuming
`K = Θ_s ≠ 0`, one has `D' = 1 - K⁻¹ sin D`. -/
theorem steering_deriv_angle_of_bicycle {D K : ℝ → ℝ} {d : ℝ}
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hR : ∀ t, HasDerivAt R (Complex.exp (Complex.I * (Ψ t : ℂ))) t)
    (hΨ : ∀ t, HasDerivAt Ψ (k t) t)
    (hx : ∀ s, HasDerivAt x (xp s) s)
    (hlink : ∀ s, F s = R (x s) + Complex.exp (Complex.I * (Ψ (x s) : ℂ)))
    (hΘ : ∀ s, HasDerivAt Θ (K s) s) (s : ℝ) (hK : K s ≠ 0)
    (hD : HasDerivAt D d (Θ s)) (hDΘ : ∀ σ, D (Θ σ) = Θ σ - Ψ (x σ)) :
    d = 1 - (1 / K s) * Real.sin (D (Θ s)) := by
  refine steering_deriv_angle (hΘ s) hK hD ?_
  have h := front_curvature_eq hF hR hΨ hx hlink hΘ s
  rw [hDΘ s]
  exact h.congr_of_eventuallyEq (by filter_upwards with σ using hDΘ σ)

end BicycleEquations

section LowCurvature

/-- The rear curvature bound of Lemma 2.1: on the selected branch
`0 ≤ δ ≤ arcsin κ` with `κ < 1`, the rear curvature `tan δ` is at most
`κ / √(1 - κ²)`. -/
theorem rear_curvature_le {δ κ : ℝ} (hκ1 : κ < 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.arcsin κ) :
    Real.tan δ ≤ κ / Real.sqrt (1 - κ ^ 2) := by
  have harc : Real.arcsin κ < π / 2 := Real.arcsin_lt_pi_div_two.mpr hκ1
  have hmono : Real.tan δ ≤ Real.tan (Real.arcsin κ) := by
    rcases eq_or_lt_of_le hδ with h | h
    · rw [h]
    · exact le_of_lt (Real.tan_lt_tan_of_lt_of_lt_pi_div_two
        (by linarith [Real.pi_pos]) harc h)
  rwa [Real.tan_arcsin] at hmono

/-- The contraction mechanism behind the uniqueness statement of Lemma 2.1:
a periodic solution of the linear equation `w' = -a·w` with `a ≥ c > 0`
vanishes identically. -/
theorem eq_zero_of_periodic_of_deriv_eq_neg_mul {w a : ℝ → ℝ} {P c : ℝ}
    (hP : 0 < P) (hper : Function.Periodic w P)
    (hw : ∀ t, HasDerivAt w (-(a t * w t)) t)
    (hc : 0 < c) (hac : ∀ t, c ≤ a t) : ∀ t, w t = 0 := by
  -- `v t = e^{2ct} w(t)²` is nonincreasing, while periodicity forces it to grow
  -- along `t ↦ t + P` unless `w` vanishes.
  set v : ℝ → ℝ := fun t => Real.exp (2 * c * t) * (w t) ^ 2 with hv
  have hvderiv : ∀ t, HasDerivAt v (2 * Real.exp (2 * c * t) * (w t) ^ 2 * (c - a t)) t := by
    intro t
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (2 * c * t)) (Real.exp (2 * c * t) * (2 * c)) t := by
      simpa using (Real.hasDerivAt_exp (2 * c * t)).comp t
        ((hasDerivAt_id t).const_mul (2 * c))
    have hsq : HasDerivAt (fun t : ℝ => (w t) ^ 2) (2 * w t * (-(a t * w t))) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (hw t).pow 2
    have h := hexp.mul hsq
    convert h using 1
    ring
  have hanti : Antitone v := by
    apply antitone_of_deriv_nonpos (fun t => (hvderiv t).differentiableAt)
    intro t
    rw [(hvderiv t).deriv]
    have h1 : c - a t ≤ 0 := by linarith [hac t]
    have h2 : 0 ≤ 2 * Real.exp (2 * c * t) * (w t) ^ 2 := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos h2 h1
  intro t
  have h1 : v (t + P) ≤ v t := hanti (by linarith)
  rw [hv] at h1
  simp only [hper t] at h1
  have hlt : Real.exp (2 * c * t) < Real.exp (2 * c * (t + P)) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hsq : w t ^ 2 ≤ 0 := by nlinarith [sq_nonneg (w t)]
  have : w t ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

end LowCurvature

end Bicycle
