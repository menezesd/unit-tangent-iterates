import Mathlib

/-!
# Cores of the hairpin pulse estimates (Lemma 3.5)

This file formalizes the three self-contained computational ingredients of the
lemma *Hairpin pulse estimates* of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*.

* `hasDerivAt_log_tan_half` : the exact half-angle equation
  `(log tan(θ/2))_u = θ_u / sin θ`, which the paper writes as `1/f(θ)`;
* `bounds_of_hasDerivAt_between` and `exp_bounds_of_log_deriv` : a derivative
  pinched between `1/M` and `1/m` forces two-sided exponential bounds
  `r(0)e^{u/M} ≤ r(u) ≤ r(0)e^{u/m}` for `u ≥ 0` (and the reversed pair for
  `u ≤ 0`).  This is the mechanism producing the exponential decay of the
  pulse at both ends;
* `translator_curvature_identity` : the Frenet identity
  `K(σ(u)) = (K' + K + K³)/(1 + K²)^{3/2}` relating the curvature of a track
  to the curvature of its unit-tangent image, in arclength `u` of the track.
-/

noncomputable section

open Real

namespace HairpinPulse

/-! ### The half-angle equation -/

/-- **The half-angle equation.**  If `0 < θ u < π` then the half-angle
variable `r = tan(θ/2)` satisfies `(log r)_u = θ_u / sin θ`. -/
theorem hasDerivAt_log_tan_half {theta : ℝ → ℝ} {tp : ℝ} {u : ℝ}
    (hth : HasDerivAt theta tp u) (h0 : 0 < theta u) (hpi : theta u < Real.pi) :
    HasDerivAt (fun t => Real.log (Real.tan (theta t / 2))) (tp / Real.sin (theta u)) u := by
  set a : ℝ := theta u / 2 with ha
  have ha0 : 0 < a := by simp only [ha]; linarith
  have ha2 : a < Real.pi / 2 := by simp only [ha]; linarith
  have hcos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha2⟩
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have htan : 0 < Real.tan a := Real.tan_pos_of_pos_of_lt_pi_div_two ha0 ha2
  -- derivative of the inner map
  have hhalf : HasDerivAt (fun t => theta t / 2) (tp / 2) u := hth.div_const 2
  have htanD : HasDerivAt Real.tan (1 / Real.cos a ^ 2) a :=
    Real.hasDerivAt_tan (ne_of_gt hcos)
  have hcomp : HasDerivAt (fun t => Real.tan (theta t / 2)) ((1 / Real.cos a ^ 2) * (tp / 2)) u := by
    simpa [Function.comp] using htanD.comp u hhalf
  have hlog := hcomp.log (ne_of_gt htan)
  convert hlog using 1
  rw [← ha, Real.tan_eq_sin_div_cos]
  have hsin2 : Real.sin (theta u) = 2 * Real.sin a * Real.cos a := by
    rw [show theta u = 2 * a from by simp only [ha]; ring, Real.sin_two_mul]
  rw [hsin2]
  field_simp

/-! ### Two-sided exponential bounds from a pinched logarithmic derivative -/

/-- If `g' ∈ [c, C]` everywhere then `g` grows at least linearly with slope `c`
and at most linearly with slope `C` to the right of the origin. -/
theorem bounds_of_hasDerivAt_between {g G : ℝ → ℝ} {c C : ℝ}
    (hg : ∀ u, HasDerivAt g (G u) u) (hlo : ∀ u, c ≤ G u) (hhi : ∀ u, G u ≤ C)
    {u : ℝ} (hu : 0 ≤ u) :
    g 0 + c * u ≤ g u ∧ g u ≤ g 0 + C * u := by
  have hdiff : Differentiable ℝ g := fun x => (hg x).differentiableAt
  constructor
  · have hmono : Monotone fun t => g t - c * t := by
      apply monotone_of_deriv_nonneg (by fun_prop)
      intro x
      have hd : HasDerivAt (fun t => g t - c * t) (G x - c) x := by
        simpa using (hg x).sub ((hasDerivAt_id x).const_mul c)
      rw [hd.deriv]
      linarith [hlo x]
    have := hmono hu
    simp only [mul_zero, sub_zero] at this
    linarith
  · have hmono : Monotone fun t => C * t - g t := by
      apply monotone_of_deriv_nonneg (by fun_prop)
      intro x
      have hd : HasDerivAt (fun t => C * t - g t) (C - G x) x := by
        simpa using ((hasDerivAt_id x).const_mul C).sub (hg x)
      rw [hd.deriv]
      linarith [hhi x]
    have := hmono hu
    simp only [mul_zero, zero_sub] at this
    linarith

/-- **Two-sided exponential bounds.**  A positive function whose logarithmic
derivative lies in `[1/M, 1/m]` (with `0 < m ≤ M`) grows exponentially at rate
between `1/M` and `1/m`. -/
theorem exp_bounds_of_log_deriv {r R : ℝ → ℝ} {m M : ℝ}
    (hpos : ∀ u, 0 < r u)
    (hlog : ∀ u, HasDerivAt (fun t => Real.log (r t)) (R u) u)
    (hlo : ∀ u, 1 / M ≤ R u) (hhi : ∀ u, R u ≤ 1 / m)
    {u : ℝ} (hu : 0 ≤ u) :
    r 0 * Real.exp (u / M) ≤ r u ∧ r u ≤ r 0 * Real.exp (u / m) := by
  obtain ⟨h1, h2⟩ := bounds_of_hasDerivAt_between hlog hlo hhi hu
  have hr0 : Real.log (r 0) + (1 / M) * u ≤ Real.log (r u) := h1
  have hr1 : Real.log (r u) ≤ Real.log (r 0) + (1 / m) * u := h2
  constructor
  · have := Real.exp_le_exp.mpr hr0
    rwa [Real.exp_add, Real.exp_log (hpos 0), Real.exp_log (hpos u),
      show (1 / M) * u = u / M from by ring] at this
  · have := Real.exp_le_exp.mpr hr1
    rwa [Real.exp_add, Real.exp_log (hpos 0), Real.exp_log (hpos u),
      show (1 / m) * u = u / m from by ring] at this

/-! ### The shifted curvature identity -/

/-- **The translator curvature identity.**  Let `K` be the curvature of a
track in its own arclength `u`, and let `σ` be the arclength of the
unit-tangent image, so that `σ' = √(1 + K²)`.  The steering angle is
`δ = arctan K`, and the curvature of the image is `δ_σ + sin δ`, which equals

`(K' + K + K³) / (1 + K²)^{3/2}`. -/
theorem translator_curvature_identity {K Kp sigma : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (Kp u) u)
    (hsigma : ∀ u, HasDerivAt sigma (Real.sqrt (1 + K u ^ 2)) u) (u : ℝ) :
    deriv (fun t => Real.arctan (K t)) u / deriv sigma u
        + Real.sin (Real.arctan (K u))
      = (Kp u + K u + K u ^ 3) / ((1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2)) := by
  have hpos : (0:ℝ) < 1 + K u ^ 2 := by positivity
  have hs : Real.sqrt (1 + K u ^ 2) > 0 := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (1 + K u ^ 2) ^ 2 = 1 + K u ^ 2 :=
    Real.sq_sqrt hpos.le
  have hd : deriv (fun t => Real.arctan (K t)) u = Kp u / (1 + K u ^ 2) := by
    have hda : HasDerivAt (fun t => Real.arctan (K t)) (Kp u / (1 + K u ^ 2)) u := by
      simpa [Function.comp, div_eq_mul_inv, mul_comm] using
        (Real.hasDerivAt_arctan (K u)).comp u (hK u)
    exact hda.deriv
  have hsig : deriv sigma u = Real.sqrt (1 + K u ^ 2) := (hsigma u).deriv
  rw [hd, hsig, Real.sin_arctan]
  field_simp
  ring

end HairpinPulse
