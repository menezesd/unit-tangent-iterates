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

/-- **The shifted-curvature evolution equation.**  If the curvature of the
unit-tangent image at front arclength `sigma u` is the same translated
intrinsic profile `K (sigma u)`, then the Frenet identity solves for the
intrinsic derivative exactly as in the TeX:

`K' = (1+K²) sqrt(1+K²) (K o sigma) - K - K³`.

No endpoint regularity is used. -/
theorem curvature_deriv_eq_of_translator {K Kp sigma : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (Kp u) u)
    (hsigma : ∀ u, HasDerivAt sigma (Real.sqrt (1 + K u ^ 2)) u)
    (htranslated : ∀ u,
      deriv (fun t => Real.arctan (K t)) u / deriv sigma u
          + Real.sin (Real.arctan (K u)) = K (sigma u)) (u : ℝ) :
    Kp u = (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) * K (sigma u)
      - K u - K u ^ 3 := by
  have hid := translator_curvature_identity hK hsigma u
  rw [htranslated u] at hid
  have hpos : 0 < 1 + K u ^ 2 := by positivity
  have hspos : 0 < Real.sqrt (1 + K u ^ 2) := Real.sqrt_pos.mpr hpos
  rw [eq_div_iff (mul_ne_zero hpos.ne' hspos.ne')] at hid
  nlinarith

/-- A bounded-shift Harnack comparison converts the shifted-curvature
evolution equation into the first relative derivative estimate.  This is the
first induction step in the TeX proof and uses no endpoint regularity. -/
theorem abs_curvatureDeriv_le_of_shift_harnack
    {K Kp sigma : ℝ → ℝ} {A Ch : ℝ}
    (hKpos : ∀ u, 0 < K u) (hA0 : 0 ≤ A) (hCh0 : 0 ≤ Ch)
    (hKA : ∀ u, K u ≤ A)
    (hshift : ∀ u, K (sigma u) ≤ Ch * K u)
    (hevol : ∀ u, Kp u =
      (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) * K (sigma u)
        - K u - K u ^ 3) :
    ∀ u, |Kp u| ≤
      ((1 + A ^ 2) * Real.sqrt (1 + A ^ 2) * Ch + 1 + A ^ 2) * K u := by
  intro u
  have hK0 : 0 ≤ K u := (hKpos u).le
  have hKs0 : 0 ≤ K (sigma u) := (hKpos (sigma u)).le
  have hsq : K u ^ 2 ≤ A ^ 2 := by nlinarith [hKA u]
  have hsqrt : Real.sqrt (1 + K u ^ 2) ≤ Real.sqrt (1 + A ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt (1 + K u ^ 2) := Real.sqrt_nonneg _
  have hSA0 : 0 ≤ Real.sqrt (1 + A ^ 2) := Real.sqrt_nonneg _
  have hden :
      (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) ≤
        (1 + A ^ 2) * Real.sqrt (1 + A ^ 2) := by
    exact mul_le_mul (by linarith) hsqrt hs0 (by positivity)
  have hmain :
      (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) * K (sigma u) ≤
        ((1 + A ^ 2) * Real.sqrt (1 + A ^ 2) * Ch) * K u := by
    calc
      (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) * K (sigma u)
          ≤ ((1 + A ^ 2) * Real.sqrt (1 + A ^ 2)) * K (sigma u) :=
            mul_le_mul_of_nonneg_right hden hKs0
      _ ≤ ((1 + A ^ 2) * Real.sqrt (1 + A ^ 2)) * (Ch * K u) :=
            mul_le_mul_of_nonneg_left (hshift u) (by positivity)
      _ = ((1 + A ^ 2) * Real.sqrt (1 + A ^ 2) * Ch) * K u := by ring
  have hfront0 : 0 ≤
      (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) * K (sigma u) := by
    positivity
  rw [hevol u]
  calc
    |(1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) * K (sigma u)
        - K u - K u ^ 3|
      ≤ (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) * K (sigma u)
          + K u + K u ^ 3 := by
        rw [abs_le]
        constructor <;> nlinarith [pow_nonneg hK0 3, hfront0]
    _ ≤ ((1 + A ^ 2) * Real.sqrt (1 + A ^ 2) * Ch) * K u
          + K u + A ^ 2 * K u := by
        have hcub : K u ^ 3 ≤ A ^ 2 * K u := by
          nlinarith [hsq, hK0]
        linarith
    _ = ((1 + A ^ 2) * Real.sqrt (1 + A ^ 2) * Ch + 1 + A ^ 2) * K u := by
        ring

/-- The derivative of the coefficient `(1+K²)^(3/2)` in the shifted
curvature evolution equation. -/
theorem hasDerivAt_curvatureAmp {K Kp : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (Kp u) u) (u : ℝ) :
    HasDerivAt (fun t => (1 + K t ^ 2) * Real.sqrt (1 + K t ^ 2))
      (3 * K u * Real.sqrt (1 + K u ^ 2) * Kp u) u := by
  have hinner : HasDerivAt (fun t => 1 + K t ^ 2) (2 * K u * Kp u) u := by
    convert (hasDerivAt_const u (1 : ℝ)).add ((hK u).pow 2) using 1 <;> ring
  have hpos : 0 < 1 + K u ^ 2 := by positivity
  have hsqrt := (Real.hasDerivAt_sqrt hpos.ne').comp u hinner
  have hprod := hinner.mul hsqrt
  convert hprod using 1
  have hs : Real.sqrt (1 + K u ^ 2) ^ 2 = 1 + K u ^ 2 :=
    Real.sq_sqrt hpos.le
  simp only [Function.comp_apply]
  field_simp
  rw [hs]
  ring

/-- The second derivative of the front-arclength shift
`sigma' = sqrt (1+K^2)`. -/
theorem hasDerivAt_sigmaSpeed {K Kp : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (Kp u) u) (u : ℝ) :
    HasDerivAt (fun t => Real.sqrt (1 + K t ^ 2))
      (K u * Kp u / Real.sqrt (1 + K u ^ 2)) u := by
  have hinner : HasDerivAt (fun t => 1 + K t ^ 2) (2 * K u * Kp u) u := by
    convert (hasDerivAt_const u (1 : ℝ)).add ((hK u).pow 2) using 1 <;> ring
  have hpos : 0 < 1 + K u ^ 2 := by positivity
  convert (Real.hasDerivAt_sqrt hpos.ne').comp u hinner using 1
  field_simp <;> ring

/-- The third derivative of the front-arclength shift. -/
theorem hasDerivAt_sigmaAccel {K Kp Kpp : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (Kp u) u)
    (hKp : ∀ u, HasDerivAt Kp (Kpp u) u) (u : ℝ) :
    HasDerivAt (fun t => K t * Kp t / Real.sqrt (1 + K t ^ 2))
      ((Kp u ^ 2 + K u * Kpp u) / Real.sqrt (1 + K u ^ 2)
        - K u ^ 2 * Kp u ^ 2 / (Real.sqrt (1 + K u ^ 2)) ^ 3) u := by
  have hs := hasDerivAt_sigmaSpeed hK u
  have hn : HasDerivAt (fun t => K t * Kp t)
      (Kp u ^ 2 + K u * Kpp u) u := by
    convert (hK u).mul (hKp u) using 1 <;> ring
  have hne : Real.sqrt (1 + K u ^ 2) ≠ 0 := by positivity
  have h := hn.div hs hne
  convert h using 1
  have hsq : Real.sqrt (1 + K u ^ 2) ^ 2 = 1 + K u ^ 2 :=
    Real.sq_sqrt (by positivity)
  field_simp

/-- **Second differentiated shifted-curvature equation.**  This is the exact
finite formula used for the order-two relative estimate. -/
theorem curvature_second_eq_of_translator
    {K Kp Kpp sigma : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (Kp u) u)
    (hKp : ∀ u, HasDerivAt Kp (Kpp u) u)
    (hsigma : ∀ u, HasDerivAt sigma (Real.sqrt (1 + K u ^ 2)) u)
    (hevol : ∀ u, Kp u =
      (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) * K (sigma u)
        - K u - K u ^ 3) (u : ℝ) :
    Kpp u =
      (3 * K u * Real.sqrt (1 + K u ^ 2) * Kp u) * K (sigma u)
      + ((1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2)) *
          (Kp (sigma u) * Real.sqrt (1 + K u ^ 2))
      - Kp u - 3 * K u ^ 2 * Kp u := by
  let amp : ℝ → ℝ := fun t => (1 + K t ^ 2) * Real.sqrt (1 + K t ^ 2)
  have hamp := hasDerivAt_curvatureAmp hK u
  have hcomp : HasDerivAt (fun t => K (sigma t))
      (Kp (sigma u) * Real.sqrt (1 + K u ^ 2)) u :=
    (hK (sigma u)).comp u (hsigma u)
  have hrhs : HasDerivAt
      (fun t => amp t * K (sigma t) - K t - K t ^ 3)
      ((3 * K u * Real.sqrt (1 + K u ^ 2) * Kp u) * K (sigma u)
        + amp u * (Kp (sigma u) * Real.sqrt (1 + K u ^ 2))
        - Kp u - 3 * K u ^ 2 * Kp u) u := by
    convert ((hamp.mul hcomp).sub (hK u)).sub ((hK u).pow 3) using 1 <;>
      simp [amp] <;> ring
  have heq : Kp = fun t => amp t * K (sigma t) - K t - K t ^ 3 := by
    funext t
    simpa [amp] using hevol t
  have := hKp u
  rw [heq] at this
  exact (this.unique hrhs)

/-- The exact second differentiated equation gives a relative second
derivative bound from the first relative bound and the same shifted Harnack
comparison. -/
theorem abs_curvatureSecond_le_of_shift_harnack
    {K Kp Kpp sigma : ℝ → ℝ} {A D1 Ch : ℝ}
    (hKpos : ∀ u, 0 < K u) (hA0 : 0 ≤ A) (hD10 : 0 ≤ D1) (hCh0 : 0 ≤ Ch)
    (hKA : ∀ u, K u ≤ A)
    (hKp : ∀ u, |Kp u| ≤ D1 * K u)
    (hshift : ∀ u, K (sigma u) ≤ Ch * K u)
    (hsecond : ∀ u, Kpp u =
      (3 * K u * Real.sqrt (1 + K u ^ 2) * Kp u) * K (sigma u)
      + ((1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2)) *
          (Kp (sigma u) * Real.sqrt (1 + K u ^ 2))
      - Kp u - 3 * K u ^ 2 * Kp u) :
    ∀ u, |Kpp u| ≤
      (3 * A ^ 2 * Real.sqrt (1 + A ^ 2) * D1 * Ch
        + (1 + A ^ 2) * Real.sqrt (1 + A ^ 2) * D1 * Ch *
            Real.sqrt (1 + A ^ 2)
        + D1 + 3 * A ^ 2 * D1) * K u := by
  intro u
  let S := Real.sqrt (1 + A ^ 2)
  have hK0 : 0 ≤ K u := (hKpos u).le
  have hKs0 : 0 ≤ K (sigma u) := (hKpos (sigma u)).le
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hsu0 : 0 ≤ Real.sqrt (1 + K u ^ 2) := Real.sqrt_nonneg _
  have hsq : K u ^ 2 ≤ A * K u := by nlinarith [hKA u]
  have hk3 : K u ^ 3 ≤ A ^ 2 * K u := by
    calc
      K u ^ 3 = K u ^ 2 * K u := by ring
      _ ≤ (A * K u) * K u := mul_le_mul_of_nonneg_right hsq hK0
      _ ≤ (A * K u) * A := mul_le_mul_of_nonneg_left (hKA u) (mul_nonneg hA0 hK0)
      _ = A ^ 2 * K u := by ring
  have hsqrt : Real.sqrt (1 + K u ^ 2) ≤ S := by
    apply Real.sqrt_le_sqrt
    nlinarith [hKA u]
  have hamp : (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) ≤
      (1 + A ^ 2) * S := by
    exact mul_le_mul (by nlinarith [hKA u]) hsqrt hsu0 (by positivity)
  let t1 := (3 * K u * Real.sqrt (1 + K u ^ 2) * Kp u) * K (sigma u)
  let t2 := ((1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2)) *
    (Kp (sigma u) * Real.sqrt (1 + K u ^ 2))
  let t4 := 3 * K u ^ 2 * Kp u
  have ht1 : |t1| ≤
      (3 * A ^ 2 * S * D1 * Ch) * K u := by
    dsimp [t1]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3),
      abs_of_nonneg hK0, abs_of_nonneg hsu0, abs_of_nonneg hKs0]
    calc
      3 * K u * Real.sqrt (1 + K u ^ 2) * |Kp u| * K (sigma u)
          ≤ 3 * K u * S * (D1 * K u) * (Ch * K u) := by
            gcongr
            · exact hKp u
            · exact hshift u
      _ = (3 * S * D1 * Ch) * K u ^ 3 := by ring
      _ ≤ (3 * S * D1 * Ch) * (A ^ 2 * K u) := by
        exact mul_le_mul_of_nonneg_left hk3 (by positivity)
      _ = (3 * A ^ 2 * S * D1 * Ch) * K u := by ring
  have ht2 : |t2| ≤
      ((1 + A ^ 2) * S * D1 * Ch * S) * K u := by
    dsimp [t2]
    simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + K u ^ 2),
      abs_of_nonneg hsu0]
    calc
      (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) *
          (|Kp (sigma u)| * Real.sqrt (1 + K u ^ 2))
          ≤ ((1 + A ^ 2) * S) * ((D1 * K (sigma u)) * S) := by
            gcongr
            exact hKp (sigma u)
      _ ≤ ((1 + A ^ 2) * S) * ((D1 * (Ch * K u)) * S) := by
            gcongr
            exact hshift u
      _ = ((1 + A ^ 2) * S * D1 * Ch * S) * K u := by ring
  have ht4 : |t4| ≤ (3 * A ^ 2 * D1) * K u := by
    dsimp [t4]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3),
      abs_of_nonneg (sq_nonneg (K u))]
    calc
      3 * K u ^ 2 * |Kp u| ≤ 3 * K u ^ 2 * (D1 * K u) := by
        gcongr
        exact hKp u
      _ = (3 * D1) * K u ^ 3 := by ring
      _ ≤ (3 * D1) * (A ^ 2 * K u) := by
        exact mul_le_mul_of_nonneg_left hk3 (by positivity)
      _ = (3 * A ^ 2 * D1) * K u := by ring
  rw [hsecond u]
  change |t1 + t2 - Kp u - t4| ≤ _
  calc
    |t1 + t2 - Kp u - t4| ≤ |t1| + |t2| + |Kp u| + |t4| := by
      calc
        |t1 + t2 - Kp u - t4| ≤ |t1 + t2 - Kp u| + |t4| := abs_sub _ _
        _ ≤ (|t1 + t2| + |Kp u|) + |t4| := by gcongr; exact abs_sub _ _
        _ ≤ (|t1| + |t2| + |Kp u|) + |t4| := by gcongr; exact abs_add_le _ _
        _ = |t1| + |t2| + |Kp u| + |t4| := by ring
    _ ≤ (3 * A ^ 2 * S * D1 * Ch
        + (1 + A ^ 2) * S * D1 * Ch * S
        + D1 + 3 * A ^ 2 * D1) * K u := by
      linarith [ht1, ht2, hKp u, ht4]
    _ = (3 * A ^ 2 * Real.sqrt (1 + A ^ 2) * D1 * Ch
        + (1 + A ^ 2) * Real.sqrt (1 + A ^ 2) * D1 * Ch *
            Real.sqrt (1 + A ^ 2)
        + D1 + 3 * A ^ 2 * D1) * K u := by rfl

/-- Exact third differentiated shifted-curvature equation.  Writing
`v=sqrt(1+K^2)`, this is the product/chain-rule expansion of the preceding
second-order identity. -/
theorem curvature_third_eq_of_translator
    {K Kp Kpp K3 sigma : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (Kp u) u)
    (hKp : ∀ u, HasDerivAt Kp (Kpp u) u)
    (hKpp : ∀ u, HasDerivAt Kpp (K3 u) u)
    (hsigma : ∀ u, HasDerivAt sigma (Real.sqrt (1 + K u ^ 2)) u)
    (hsecond : ∀ u, Kpp u =
      (3 * K u * Real.sqrt (1 + K u ^ 2) * Kp u) * K (sigma u)
      + ((1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2)) *
          (Kp (sigma u) * Real.sqrt (1 + K u ^ 2))
      - Kp u - 3 * K u ^ 2 * Kp u) (u : ℝ) :
    K3 u =
      ((3 * Real.sqrt (1 + K u ^ 2)
          + 3 * K u ^ 2 / Real.sqrt (1 + K u ^ 2)) * Kp u ^ 2
        + 3 * K u * Real.sqrt (1 + K u ^ 2) * Kpp u) * K (sigma u)
      + 2 * (3 * K u * Real.sqrt (1 + K u ^ 2)) * Kp u *
          Kp (sigma u) * Real.sqrt (1 + K u ^ 2)
      + ((1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2)) *
          Kpp (sigma u) * (1 + K u ^ 2)
      + ((1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2)) *
          Kp (sigma u) *
            (K u * Kp u / Real.sqrt (1 + K u ^ 2))
      - 6 * K u * Kp u ^ 2 - (1 + 3 * K u ^ 2) * Kpp u := by
  let v : ℝ → ℝ := fun t => Real.sqrt (1 + K t ^ 2)
  let a : ℝ → ℝ := fun t => (1 + K t ^ 2) * v t
  let a1 : ℝ → ℝ := fun t => 3 * K t * v t
  have hv : ∀ t, HasDerivAt v (K t * Kp t / v t) t := by
    intro t
    simpa [v] using hasDerivAt_sigmaSpeed hK t
  have ha : ∀ t, HasDerivAt a (a1 t * Kp t) t := by
    intro t
    simpa [a, a1, v] using hasDerivAt_curvatureAmp hK t
  have ha1 : HasDerivAt a1
      ((3 * v u + 3 * K u ^ 2 / v u) * Kp u) u := by
    have h := ((hasDerivAt_const u (3 : ℝ)).mul (hK u)).mul (hv u)
    convert h using 1 <;> simp [a1] <;> ring
  have hKs : HasDerivAt (fun t => K (sigma t))
      (Kp (sigma u) * v u) u := (hK (sigma u)).comp u (hsigma u)
  have hKps : HasDerivAt (fun t => Kp (sigma t))
      (Kpp (sigma u) * v u) u := (hKp (sigma u)).comp u (hsigma u)
  have ht1 := (((ha1.mul (hKp u)).mul hKs))
  have ht2 := ((ha u).mul ((hKps.mul (hv u))))
  have htail := (hKp u).add
    ((((hasDerivAt_const u (3 : ℝ)).mul ((hK u).pow 2)).mul (hKp u)))
  have hrhs : HasDerivAt
      (fun t => (a1 t * Kp t) * K (sigma t)
        + a t * (Kp (sigma t) * v t) - Kp t - 3 * K t ^ 2 * Kp t)
      (((3 * v u + 3 * K u ^ 2 / v u) * Kp u ^ 2
          + a1 u * Kpp u) * K (sigma u)
        + 2 * a1 u * Kp u * Kp (sigma u) * v u
        + a u * Kpp (sigma u) * v u ^ 2
        + a u * Kp (sigma u) * (K u * Kp u / v u)
        - 6 * K u * Kp u ^ 2 - (1 + 3 * K u ^ 2) * Kpp u) u := by
    convert (ht1.add ht2).sub htail using 1
    · funext t
      simp only [a, a1, v, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
        Pi.pow_apply]
      ring
    · simp [a, a1, v] <;> ring
  have heq : Kpp = fun t => (a1 t * Kp t) * K (sigma t)
      + a t * (Kp (sigma t) * v t) - Kp t - 3 * K t ^ 2 * Kp t := by
    funext t
    simpa [a, a1, v] using hsecond t
  have hd := hKpp u
  rw [heq] at hd
  have hu := hd.unique hrhs
  simpa [a, a1, v, show Real.sqrt (1 + K u ^ 2) ^ 2 = 1 + K u ^ 2 by
    exact Real.sq_sqrt (by positivity)] using hu

end HairpinPulse
