import Mathlib
import UnitTangentIterates.InterpolationNormal

/-!
# The estimate of the lemma *Curvature interpolation*

`UnitTangentIterates/CurvatureInterpolation.lean` builds the interpolating path

`X_t(s) = ∫₀ˢ τ(θ_t(r)) dr - ½ ∫₀ᴸ τ(θ_t(r)) dr`,  `θ_t = θ₀ + ∫₀ˢ κ_t`,
`κ_t = (1-t)κ⁰ + tκ¹`,

and `UnitTangentIterates/InterpolationNormal.lean` differentiates it in the path
parameter and bounds the Frenet components of its velocity by `(3/2)Lε`, where
`ε = ‖κ¹ - κ⁰‖_{L¹(0,L)}`.  What was still assumed there was the first
variation identity `θ̇ = η_s + κ ξ`, from which the paper deduces the bound on
`η_s`, and the passage from the pointwise bounds to the path functionals

`W(Γ) = ∫₀¹ ‖η_t‖_{L¹}`,  `S_j(Γ) = ∫₀¹ ‖∂_s^j η_t‖_{L^∞}`.

This file supplies both.  The normal and tangential velocities

`η_t(s) = ⟨Ẋ_t(s), ν_t(s)⟩`,  `ξ_t(s) = ⟨Ẋ_t(s), τ_t(s)⟩`

are differentiated in the arclength: since `∂_s Ẋ_t = i B τ_t` with
`B(s) = ∫₀ˢ (κ¹ - κ⁰)` the accumulated curvature difference, and
`∂_s τ_t = i κ_t τ_t`, one gets exactly

`∂_s η_t = B - κ_t ξ_t`,

which is the first variation identity `θ̇ = η_s + κ ξ` for this path
(`hasDerivAt_normalVel`).  Both velocities are `L`-periodic in the arclength,
because the curve is centrally symmetric (`normalVel_periodic`,
`tangentVel_periodic`), so the bounds proved on `[0, L]` hold everywhere, and
the three functionals of the lemma obey

`W ≤ 2L·(3/2)Lε`,  `S₀ ≤ (3/2)Lε`,  `S₁ ≤ (1 + (3/2)κ_*L)ε`,

whence `W + S₀ + S₁ ≤ 6(1+L)²ε` (`curvature_interpolation_estimate`), the
estimate of the lemma.

Main results:

* `hasDerivAt_normalVel` : the first variation identity `∂_s η = B - κ ξ`;
* `normalVel_periodic`, `tangentVel_periodic`, `normalVelDeriv_periodic` : the
  velocities are `L`-periodic;
* `abs_normalVel_le`, `abs_tangentVel_le` : `|η|, |ξ| ≤ (3/2)Lε` everywhere;
* `abs_normalVelDeriv_le` : `|∂_s η| ≤ (1 + (3/2)κ_*L)ε` everywhere;
* `normalVel_L1_le` : `‖η_t‖_{L¹(0,2L)} ≤ 2L·(3/2)Lε`;
* `curvature_interpolation_estimate` : `W + S₀ + S₁ ≤ 6(1+L)²ε`;
* `exists_interpolation_path` : the lemma itself, in one statement;
* `curvature_interpolation_estimate_instance` : the hypotheses are not vacuous.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace InterpolationEstimate

open CurvatureInterpolation InterpolationNormal

variable {k0 k1 : ℝ → ℝ} {θ₀ L : ℝ}

/-! ## The components of the unit tangent -/

theorem tau_re (θ : ℝ) : (tau θ).re = Real.cos θ := by
  simp [tau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem tau_im (θ : ℝ) : (tau θ).im = Real.sin θ := by
  simp [tau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem mul_I_tau_re (b θ : ℝ) :
    (Complex.I * (b : ℂ) * tau θ).re = -(b * Real.sin θ) := by
  simp [tau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.mul_re, Complex.mul_im]

theorem mul_I_tau_im (b θ : ℝ) :
    (Complex.I * (b : ℂ) * tau θ).im = b * Real.cos θ := by
  simp [tau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.mul_re, Complex.mul_im]

/-! ## The Frenet components of the velocity of the interpolation -/

/-- The `L¹` distance `ε = ‖κ¹ - κ⁰‖_{L¹(0,L)}` between the two curvatures. -/
def curvDist (k0 k1 : ℝ → ℝ) (L : ℝ) : ℝ := ∫ r in (0:ℝ)..L, |k1 r - k0 r|

/-- The normal velocity `η_t(s)` of the interpolating path. -/
def normalVel (k0 k1 : ℝ → ℝ) (θ₀ L t s : ℝ) : ℝ :=
  normalComp (interpVelocity k0 k1 θ₀ L t s) (tangentAngle (kappaInterp k0 k1 t) θ₀ s)

/-- The tangential velocity `ξ_t(s)` of the interpolating path. -/
def tangentVel (k0 k1 : ℝ → ℝ) (θ₀ L t s : ℝ) : ℝ :=
  tangentComp (interpVelocity k0 k1 θ₀ L t s) (tangentAngle (kappaInterp k0 k1 t) θ₀ s)

/-- The arclength derivative `∂_s η_t = B - κ_t ξ_t` of the normal velocity. -/
def normalVelDeriv (k0 k1 : ℝ → ℝ) (θ₀ L t s : ℝ) : ℝ :=
  angleShift k0 k1 s - kappaInterp k0 k1 t s * tangentVel k0 k1 θ₀ L t s

theorem continuous_integrand (hk0 : Continuous k0) (hk1 : Continuous k1) (t : ℝ) :
    Continuous fun r => Complex.I * (angleShift k0 k1 r : ℂ)
      * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r) :=
  (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_angleShift hk0 hk1))).mul
    (continuous_tau_tangentAngle (continuous_kappaInterp hk0 hk1))

/-- The velocity of the interpolation has arclength derivative `i B τ`. -/
theorem hasDerivAt_interpVelocity_arclength (hk0 : Continuous k0) (hk1 : Continuous k1)
    (t s : ℝ) :
    HasDerivAt (interpVelocity k0 k1 θ₀ L t)
      (Complex.I * (angleShift k0 k1 s : ℂ)
        * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ s)) s := by
  have hc := continuous_integrand (θ₀ := θ₀) hk0 hk1 t
  have hEq : interpVelocity k0 k1 θ₀ L t = fun x =>
      (∫ r in (0:ℝ)..x, Complex.I * (angleShift k0 k1 r : ℂ)
          * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r))
        - (1/2 : ℂ) * ∫ r in (0:ℝ)..L, Complex.I * (angleShift k0 k1 r : ℂ)
          * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r) := rfl
  rw [hEq]
  exact ((hc.integral_hasStrictDerivAt (0:ℝ) s).hasDerivAt).sub_const _

/-- **The first variation identity.**  In the unit-speed parametrization the
normal velocity of the interpolating path has arclength derivative
`∂_s η = B - κ ξ`, that is, `θ̇ = η_s + κ ξ` with `θ̇ = B`. -/
theorem hasDerivAt_normalVel (hk0 : Continuous k0) (hk1 : Continuous k1) (t s : ℝ) :
    HasDerivAt (normalVel k0 k1 θ₀ L t) (normalVelDeriv k0 k1 θ₀ L t s) s := by
  have hθ : HasDerivAt (tangentAngle (kappaInterp k0 k1 t) θ₀) (kappaInterp k0 k1 t s) s :=
    hasDerivAt_tangentAngle (continuous_kappaInterp hk0 hk1) s
  have hV := hasDerivAt_interpVelocity_arclength (θ₀ := θ₀) (L := L) hk0 hk1 t s
  have hre : HasDerivAt (fun x => (interpVelocity k0 k1 θ₀ L t x).re)
      (Complex.I * (angleShift k0 k1 s : ℂ)
        * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ s)).re s := by
    simpa using (Complex.reCLM.hasFDerivAt.comp s hV.hasFDerivAt).hasDerivAt
  have him : HasDerivAt (fun x => (interpVelocity k0 k1 θ₀ L t x).im)
      (Complex.I * (angleShift k0 k1 s : ℂ)
        * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ s)).im s := by
    simpa using (Complex.imCLM.hasFDerivAt.comp s hV.hasFDerivAt).hasDerivAt
  have hcos : HasDerivAt (fun x => Real.cos (tangentAngle (kappaInterp k0 k1 t) θ₀ x))
      (-Real.sin (tangentAngle (kappaInterp k0 k1 t) θ₀ s) * kappaInterp k0 k1 t s) s :=
    (Real.hasDerivAt_cos _).comp s hθ
  have hsin : HasDerivAt (fun x => Real.sin (tangentAngle (kappaInterp k0 k1 t) θ₀ x))
      (Real.cos (tangentAngle (kappaInterp k0 k1 t) θ₀ s) * kappaInterp k0 k1 t s) s :=
    (Real.hasDerivAt_sin _).comp s hθ
  have h := (him.mul hcos).sub (hre.mul hsin)
  convert h using 1
  rw [mul_I_tau_re, mul_I_tau_im]
  simp only [normalVelDeriv, tangentVel, tangentComp]
  have hpy := Real.sin_sq_add_cos_sq (tangentAngle (kappaInterp k0 k1 t) θ₀ s)
  linear_combination (-(angleShift k0 k1 s)) * hpy

/-! ## Periodicity of the velocities -/

section Periodic

variable (hk0 : Continuous k0) (hk1 : Continuous k1)
  (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
  (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
  (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi)

include hk0 hk1 hper0 hper1 htot0 htot1

/-- The accumulated curvature difference is `L`-periodic: both curvatures have
total turning `π` over a half period. -/
theorem angleShift_periodic : Function.Periodic (angleShift k0 k1) L := by
  intro s
  have h0 : IntervalIntegrable k0 volume 0 (s + L) := hk0.intervalIntegrable _ _
  have hsplit : ∀ f : ℝ → ℝ, Continuous f →
      (∫ u in (0:ℝ)..(s + L), f u) = (∫ u in (0:ℝ)..s, f u) + ∫ u in s..(s + L), f u := by
    intro f hf
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  have hd : Continuous fun u => k1 u - k0 u := by fun_prop
  have hshift : (∫ u in s..(s + L), (k1 u - k0 u)) = ∫ u in (0:ℝ)..L, (k1 u - k0 u) := by
    have hperd : Function.Periodic (fun u => k1 u - k0 u) L := fun x => by
      simp [hper0 x, hper1 x]
    simpa using hperd.intervalIntegral_add_eq s 0
  have hzero : (∫ u in (0:ℝ)..L, (k1 u - k0 u)) = 0 := by
    rw [intervalIntegral.integral_sub (hk1.intervalIntegrable _ _)
      (hk0.intervalIntegrable _ _), htot0, htot1, sub_self]
  simp only [angleShift]
  rw [hsplit _ hd, hshift, hzero, add_zero]

/-- The velocity of the interpolation reverses over a half period. -/
theorem interpVelocity_add_halfPeriod (t s : ℝ) :
    interpVelocity k0 k1 θ₀ L t (s + L) = -interpVelocity k0 k1 θ₀ L t s := by
  set g : ℝ → ℂ := fun r => Complex.I * (angleShift k0 k1 r : ℂ)
    * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r) with hg
  have hgc : Continuous g := continuous_integrand (θ₀ := θ₀) hk0 hk1 t
  have hflip : ∀ r, g (r + L) = -g r := by
    intro r
    have h1 : angleShift k0 k1 (r + L) = angleShift k0 k1 r :=
      angleShift_periodic hk0 hk1 hper0 hper1 htot0 htot1 r
    have h2 : tau (tangentAngle (kappaInterp k0 k1 t) θ₀ (r + L))
        = -tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r) :=
      tau_tangentAngle_add_halfPeriod (continuous_kappaInterp hk0 hk1)
        (periodic_kappaInterp (t := t) hper0 hper1)
        (integral_kappaInterp (t := t) hk0 hk1 htot0 htot1) r
    simp only [hg, h1, h2]
    ring
  have hsplit : (∫ r in (0:ℝ)..(s + L), g r)
      = (∫ r in (0:ℝ)..L, g r) + ∫ r in L..(s + L), g r := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
  have hshift : (∫ r in L..(s + L), g r) = -∫ r in (0:ℝ)..s, g r := by
    have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := s) g L
    rw [zero_add] at h
    rw [← h, ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun r _ => hflip r)
  simp only [interpVelocity, ← hg, hsplit, hshift]
  ring

/-- The normal velocity is `L`-periodic. -/
theorem normalVel_periodic (t : ℝ) :
    Function.Periodic (normalVel k0 k1 θ₀ L t) L := by
  intro s
  have hV := interpVelocity_add_halfPeriod (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 t s
  have hθ : tangentAngle (kappaInterp k0 k1 t) θ₀ (s + L)
      = tangentAngle (kappaInterp k0 k1 t) θ₀ s + Real.pi :=
    tangentAngle_add_halfPeriod (continuous_kappaInterp hk0 hk1)
      (periodic_kappaInterp (t := t) hper0 hper1)
      (integral_kappaInterp (t := t) hk0 hk1 htot0 htot1) s
  simp only [normalVel, normalComp, hV, hθ, Real.cos_add_pi, Real.sin_add_pi,
    Complex.neg_re, Complex.neg_im]
  ring

/-- The tangential velocity is `L`-periodic. -/
theorem tangentVel_periodic (t : ℝ) :
    Function.Periodic (tangentVel k0 k1 θ₀ L t) L := by
  intro s
  have hV := interpVelocity_add_halfPeriod (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 t s
  have hθ : tangentAngle (kappaInterp k0 k1 t) θ₀ (s + L)
      = tangentAngle (kappaInterp k0 k1 t) θ₀ s + Real.pi :=
    tangentAngle_add_halfPeriod (continuous_kappaInterp hk0 hk1)
      (periodic_kappaInterp (t := t) hper0 hper1)
      (integral_kappaInterp (t := t) hk0 hk1 htot0 htot1) s
  simp only [tangentVel, tangentComp, hV, hθ, Real.cos_add_pi, Real.sin_add_pi,
    Complex.neg_re, Complex.neg_im]
  ring

/-- The arclength derivative of the normal velocity is `L`-periodic. -/
theorem normalVelDeriv_periodic (t : ℝ) :
    Function.Periodic (normalVelDeriv k0 k1 θ₀ L t) L := by
  intro s
  simp only [normalVelDeriv,
    angleShift_periodic hk0 hk1 hper0 hper1 htot0 htot1 s,
    periodic_kappaInterp (t := t) hper0 hper1 s,
    tangentVel_periodic hk0 hk1 hper0 hper1 htot0 htot1 t s]

end Periodic

/-! ## The pointwise bounds -/

/-- `|B(s)| ≤ ε` on the fundamental interval. -/
theorem abs_angleShift_le (hk0 : Continuous k0) (hk1 : Continuous k1)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) :
    |angleShift k0 k1 s| ≤ curvDist k0 k1 L := by
  have hd : Continuous fun u => k1 u - k0 u := by fun_prop
  have hca : Continuous fun u => |k1 u - k0 u| := by fun_prop
  have h1 : |angleShift k0 k1 s| ≤ ∫ u in (0:ℝ)..s, |k1 u - k0 u| := by
    simpa [angleShift, abs_of_nonneg hs.1] using
      intervalIntegral.abs_integral_le_integral_abs (μ := volume) (a := (0:ℝ)) (b := s)
        (f := fun u => k1 u - k0 u) hs.1
  have h2 : (∫ u in (0:ℝ)..s, |k1 u - k0 u|) ≤ ∫ u in (0:ℝ)..L, |k1 u - k0 u| := by
    have hrest : 0 ≤ ∫ u in s..L, |k1 u - k0 u| := by
      have := intervalIntegral.integral_mono_on (μ := volume) (a := s) (b := L)
        (f := fun _ => (0:ℝ)) (g := fun u => |k1 u - k0 u|) hs.2
        (_root_.intervalIntegrable_const) (hca.intervalIntegrable _ _)
        (fun u _ => abs_nonneg _)
      simpa using this
    have hadd : (∫ u in (0:ℝ)..s, |k1 u - k0 u|) + (∫ u in s..L, |k1 u - k0 u|)
        = ∫ u in (0:ℝ)..L, |k1 u - k0 u| :=
      intervalIntegral.integral_add_adjacent_intervals
        (hca.intervalIntegrable _ _) (hca.intervalIntegrable _ _)
    linarith
  exact le_trans h1 h2

section Bounds

variable (hk0 : Continuous k0) (hk1 : Continuous k1)
  (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
  (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
  (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)

include hk0 hk1 hper0 hper1 htot0 htot1 hL

/-- **The sup bound on the normal velocity**, everywhere on the line:
`|η| ≤ (3/2)Lε`. -/
theorem abs_normalVel_le (t s : ℝ) :
    |normalVel k0 k1 θ₀ L t s| ≤ (3/2) * L * curvDist k0 k1 L := by
  obtain ⟨y, hy, hval⟩ :=
    (normalVel_periodic (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 t).exists_mem_Ico₀ hL s
  rw [hval]
  exact abs_normalComp_interpVelocity_le (θ₀ := θ₀) hk0 hk1 ⟨hy.1, hy.2.le⟩ t _

/-- The same bound for the tangential velocity. -/
theorem abs_tangentVel_le (t s : ℝ) :
    |tangentVel k0 k1 θ₀ L t s| ≤ (3/2) * L * curvDist k0 k1 L := by
  obtain ⟨y, hy, hval⟩ :=
    (tangentVel_periodic (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 t).exists_mem_Ico₀ hL s
  rw [hval]
  exact abs_tangentComp_interpVelocity_le (θ₀ := θ₀) hk0 hk1 ⟨hy.1, hy.2.le⟩ t _

/-- **The sup bound on the arclength derivative of the normal velocity**:
`|∂_s η| ≤ (1 + (3/2)κ_*L)ε`. -/
theorem abs_normalVelDeriv_le {kstar : ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) (s : ℝ) :
    |normalVelDeriv k0 k1 θ₀ L t s| ≤ (1 + (3/2) * kstar * L) * curvDist k0 k1 L := by
  have heps : 0 ≤ curvDist k0 k1 L :=
    integral_abs_sub_nonneg hk0 hk1 hL.le
  obtain ⟨y, hy, hval⟩ :=
    (normalVelDeriv_periodic (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 t).exists_mem_Ico₀ hL s
  rw [hval]
  refine abs_normalDeriv_le (thetadot := angleShift k0 k1 y)
    (etas := normalVelDeriv k0 k1 θ₀ L t y) (kappa := kappaInterp k0 k1 t y)
    (xi := tangentVel k0 k1 θ₀ L t y) (eps := curvDist k0 k1 L) (kstar := kstar) (L := L)
    (by simp [normalVelDeriv]) (abs_angleShift_le hk0 hk1 ⟨hy.1, hy.2.le⟩)
    (abs_tangentVel_le hk0 hk1 hper0 hper1 htot0 htot1 hL t y)
    ?_ ?_ hL.le heps
  · have h0 : 0 ≤ (1 - t) * k0 y := mul_nonneg (by linarith [ht.2]) (hk0nn y)
    have h1 : 0 ≤ t * k1 y := mul_nonneg ht.1 (hk1nn y)
    simpa [kappaInterp] using add_nonneg h0 h1
  · exact kappaInterp_le hk0le hk1le ht y

/-- **The `L¹` bound over a full period**: `‖η_t‖_{L¹(0,2L)} ≤ 2L·(3/2)Lε`. -/
theorem normalVel_L1_le (t : ℝ) :
    (∫ s in (0:ℝ)..(2 * L), |normalVel k0 k1 θ₀ L t s|)
      ≤ 2 * L * ((3/2) * L * curvDist k0 k1 L) := by
  have hcont : Continuous (normalVel k0 k1 θ₀ L t) :=
    continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_normalVel (θ₀ := θ₀) (L := L) hk0 hk1 t s).continuousAt
  exact integral_abs_le_of_sup_le (L := L) hL.le hcont
    (abs_normalVel_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL t)

end Bounds

/-! ## Joint continuity in the path parameter and the arclength -/

theorem continuous_uncurry_kappaInterp (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous fun p : ℝ × ℝ => kappaInterp k0 k1 p.1 p.2 := by
  simp only [kappaInterp]
  exact ((continuous_const.sub continuous_fst).mul (hk0.comp continuous_snd)).add
    (continuous_fst.mul (hk1.comp continuous_snd))

theorem continuous_uncurry_tangentAngle (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous fun p : ℝ × ℝ => tangentAngle (kappaInterp k0 k1 p.1) θ₀ p.2 := by
  have h := intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := volume) (a₀ := (0:ℝ)) (f := fun t r => kappaInterp k0 k1 t r)
    (continuous_uncurry_kappaInterp hk0 hk1)
  simp only [tangentAngle]
  exact continuous_const.add h

theorem continuous_uncurry_integrand (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous fun p : ℝ × ℝ => Complex.I * (angleShift k0 k1 p.2 : ℂ)
      * tau (tangentAngle (kappaInterp k0 k1 p.1) θ₀ p.2) :=
  (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_angleShift hk0 hk1).comp continuous_snd))).mul
    (continuous_tau.comp (continuous_uncurry_tangentAngle hk0 hk1))

theorem continuous_uncurry_interpVelocity (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous fun p : ℝ × ℝ => interpVelocity k0 k1 θ₀ L p.1 p.2 := by
  have h1 := intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := volume) (a₀ := (0:ℝ))
    (f := fun t r => Complex.I * (angleShift k0 k1 r : ℂ)
      * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r))
    (continuous_uncurry_integrand hk0 hk1)
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume)
    (f := fun t r => Complex.I * (angleShift k0 k1 r : ℂ)
      * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r))
    (continuous_uncurry_integrand hk0 hk1) (0:ℝ) L
  simp only [interpVelocity]
  exact h1.sub (continuous_const.mul (h2.comp continuous_fst))

theorem continuous_uncurry_normalVel (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous fun p : ℝ × ℝ => normalVel k0 k1 θ₀ L p.1 p.2 := by
  have hV := continuous_uncurry_interpVelocity (θ₀ := θ₀) (L := L) hk0 hk1
  have hθ := continuous_uncurry_tangentAngle (θ₀ := θ₀) hk0 hk1
  simp only [normalVel, normalComp]
  exact ((Complex.continuous_im.comp hV).mul (Real.continuous_cos.comp hθ)).sub
    ((Complex.continuous_re.comp hV).mul (Real.continuous_sin.comp hθ))

theorem continuous_uncurry_tangentVel (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous fun p : ℝ × ℝ => tangentVel k0 k1 θ₀ L p.1 p.2 := by
  have hV := continuous_uncurry_interpVelocity (θ₀ := θ₀) (L := L) hk0 hk1
  have hθ := continuous_uncurry_tangentAngle (θ₀ := θ₀) hk0 hk1
  simp only [tangentVel, tangentComp]
  exact ((Complex.continuous_re.comp hV).mul (Real.continuous_cos.comp hθ)).add
    ((Complex.continuous_im.comp hV).mul (Real.continuous_sin.comp hθ))

theorem continuous_uncurry_normalVelDeriv (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous fun p : ℝ × ℝ => normalVelDeriv k0 k1 θ₀ L p.1 p.2 := by
  simp only [normalVelDeriv]
  exact ((continuous_angleShift hk0 hk1).comp continuous_snd).sub
    ((continuous_uncurry_kappaInterp hk0 hk1).mul
      (continuous_uncurry_tangentVel (θ₀ := θ₀) (L := L) hk0 hk1))

/-! ## The path functionals -/

/-- The `L¹` norm over a period of the normal velocity at time `t`. -/
def Wnorm (k0 k1 : ℝ → ℝ) (θ₀ L t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..(2 * L), |normalVel k0 k1 θ₀ L t s|

/-- The sup norm of the normal velocity at time `t`; the normal velocity is
`L`-periodic, so the supremum over the fundamental interval is the sup norm. -/
def S0norm (k0 k1 : ℝ → ℝ) (θ₀ L t : ℝ) : ℝ :=
  sSup ((fun s => |normalVel k0 k1 θ₀ L t s|) '' Set.Icc 0 L)

/-- The sup norm of the arclength derivative of the normal velocity at time `t`. -/
def S1norm (k0 k1 : ℝ → ℝ) (θ₀ L t : ℝ) : ℝ :=
  sSup ((fun s => |normalVelDeriv k0 k1 θ₀ L t s|) '' Set.Icc 0 L)

theorem continuous_Wnorm (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous (Wnorm k0 k1 θ₀ L) := by
  show Continuous fun t : ℝ => ∫ s in (0:ℝ)..(2 * L), |normalVel k0 k1 θ₀ L t s|
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun t s => |normalVel k0 k1 θ₀ L t s|)
    (continuous_uncurry_normalVel (θ₀ := θ₀) (L := L) hk0 hk1).abs (0:ℝ) (2 * L)

theorem continuous_S0norm (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous (S0norm k0 k1 θ₀ L) := by
  show Continuous fun t : ℝ =>
    sSup ((fun s => |normalVel k0 k1 θ₀ L t s|) '' Set.Icc 0 L)
  exact isCompact_Icc.continuous_sSup
    (f := fun t s => |normalVel k0 k1 θ₀ L t s|)
    (continuous_uncurry_normalVel (θ₀ := θ₀) (L := L) hk0 hk1).abs

theorem continuous_S1norm (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous (S1norm k0 k1 θ₀ L) := by
  show Continuous fun t : ℝ =>
    sSup ((fun s => |normalVelDeriv k0 k1 θ₀ L t s|) '' Set.Icc 0 L)
  exact isCompact_Icc.continuous_sSup
    (f := fun t s => |normalVelDeriv k0 k1 θ₀ L t s|)
    (continuous_uncurry_normalVelDeriv (θ₀ := θ₀) (L := L) hk0 hk1).abs

/-- **The estimate of the lemma *Curvature interpolation*.**

Let `κ⁰, κ¹` be continuous, `L`-periodic, nonnegative curvatures bounded by
`κ_* ≤ 1` with total turning `π` over the half period `L`, and let `Γ` be the
path of curves `X_t` of the linear interpolation of their curvatures.  Then the
three functionals of the path satisfy

`W(Γ) + S₀(Γ) + S₁(Γ) ≤ 6(1+L)² ‖κ¹ - κ⁰‖_{L¹(0,L)}`.

The three norms are continuous in the path parameter
(`continuous_Wnorm`, `continuous_S0norm`, `continuous_S1norm`), so the
functionals are honest integrals. -/
theorem curvature_interpolation_estimate {kstar : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) (hkstar : kstar ≤ 1) :
    (∫ t in (0:ℝ)..1, Wnorm k0 k1 θ₀ L t) + (∫ t in (0:ℝ)..1, S0norm k0 k1 θ₀ L t)
        + (∫ t in (0:ℝ)..1, S1norm k0 k1 θ₀ L t)
      ≤ 6 * (1 + L) ^ 2 * curvDist k0 k1 L := by
  have heps : 0 ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
  have hWint : IntervalIntegrable (Wnorm k0 k1 θ₀ L) volume 0 1 :=
    (continuous_Wnorm hk0 hk1).intervalIntegrable _ _
  have hS0int : IntervalIntegrable (S0norm k0 k1 θ₀ L) volume 0 1 :=
    (continuous_S0norm hk0 hk1).intervalIntegrable _ _
  have hS1int : IntervalIntegrable (S1norm k0 k1 θ₀ L) volume 0 1 :=
    (continuous_S1norm hk0 hk1).intervalIntegrable _ _
  -- the three pointwise bounds, uniform in the path parameter
  have hWb : ∀ t ∈ Set.Icc (0:ℝ) 1,
      Wnorm k0 k1 θ₀ L t ≤ 2 * L * ((3/2) * L * curvDist k0 k1 L) := fun t _ =>
    normalVel_L1_le hk0 hk1 hper0 hper1 htot0 htot1 hL t
  have hS0b : ∀ t ∈ Set.Icc (0:ℝ) 1,
      S0norm k0 k1 θ₀ L t ≤ (3/2) * L * curvDist k0 k1 L := by
    intro t _
    refine Real.sSup_le ?_ (by positivity)
    rintro x ⟨s, -, rfl⟩
    exact abs_normalVel_le hk0 hk1 hper0 hper1 htot0 htot1 hL t s
  have hS1b : ∀ t ∈ Set.Icc (0:ℝ) 1,
      S1norm k0 k1 θ₀ L t ≤ (1 + (3/2) * kstar * L) * curvDist k0 k1 L := by
    intro t ht
    have hks : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
    refine Real.sSup_le ?_ (by positivity)
    rintro x ⟨s, -, rfl⟩
    exact abs_normalVelDeriv_le hk0 hk1 hper0 hper1 htot0 htot1 hL ht hk0nn hk1nn hk0le hk1le s
  -- integrate the three bounds over the unit time interval
  have hone : (0:ℝ) ≤ 1 := zero_le_one
  have hW : (∫ t in (0:ℝ)..1, Wnorm k0 k1 θ₀ L t)
      ≤ 2 * L * ((3/2) * L * curvDist k0 k1 L) := by
    have := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := 1)
      (f := Wnorm k0 k1 θ₀ L) (g := fun _ => 2 * L * ((3/2) * L * curvDist k0 k1 L))
      hone hWint (_root_.intervalIntegrable_const) hWb
    simpa using this
  have hS0 : (∫ t in (0:ℝ)..1, S0norm k0 k1 θ₀ L t) ≤ (3/2) * L * curvDist k0 k1 L := by
    have := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := 1)
      (f := S0norm k0 k1 θ₀ L) (g := fun _ => (3/2) * L * curvDist k0 k1 L)
      hone hS0int (_root_.intervalIntegrable_const) hS0b
    simpa using this
  have hS1 : (∫ t in (0:ℝ)..1, S1norm k0 k1 θ₀ L t)
      ≤ (1 + (3/2) * kstar * L) * curvDist k0 k1 L := by
    have := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := 1)
      (f := S1norm k0 k1 θ₀ L) (g := fun _ => (1 + (3/2) * kstar * L) * curvDist k0 k1 L)
      hone hS1int (_root_.intervalIntegrable_const) hS1b
    simpa using this
  exact pathFunctional_bound (L := L) hL.le heps hkstar hW hS0 hS1

/-- **The lemma *Curvature interpolation*, in one statement.**  Two marked
centrally symmetric ovals of the same half-perimeter `L` and the same marked
tangent direction, with intrinsic curvatures `0 < κ^i ≤ κ_* ≤ 1` of total
turning `π` over the half period, are joined by a path of curves `X_t` which
are unit speed with curvature `κ_t = (1-t)κ⁰ + tκ¹` — again positive and at
most `κ_*` — centrally symmetric and closed, and whose three path functionals
obey `W + S₀ + S₁ ≤ 6(1+L)²‖κ¹ - κ⁰‖_{L¹(0,L)}`. -/
theorem exists_interpolation_path {kstar : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hk0pos : ∀ r, 0 < k0 r) (hk1pos : ∀ r, 0 < k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) (hkstar : kstar ≤ 1) :
    ∃ X : ℝ → ℝ → ℂ,
      X 0 = interpCurve k0 θ₀ L ∧ X 1 = interpCurve k1 θ₀ L ∧
      (∀ t s, HasDerivAt (X t) (tau (tangentAngle (kappaInterp k0 k1 t) θ₀ s)) s) ∧
      (∀ t s, HasDerivAt (tangentAngle (kappaInterp k0 k1 t) θ₀)
        (kappaInterp k0 k1 t s) s) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s, 0 < kappaInterp k0 k1 t s ∧
        kappaInterp k0 k1 t s ≤ kstar) ∧
      (∀ t s, X t (s + L) = -X t s) ∧
      (∀ t, Function.Periodic (X t) (2 * L)) ∧
      (∫ t in (0:ℝ)..1, Wnorm k0 k1 θ₀ L t) + (∫ t in (0:ℝ)..1, S0norm k0 k1 θ₀ L t)
          + (∫ t in (0:ℝ)..1, S1norm k0 k1 θ₀ L t)
        ≤ 6 * (1 + L) ^ 2 * curvDist k0 k1 L := by
  have h0 : kappaInterp k0 k1 0 = k0 := funext fun r => by simp [kappaInterp]
  have h1 : kappaInterp k0 k1 1 = k1 := funext fun r => by simp [kappaInterp]
  refine ⟨fun t => interpCurve (kappaInterp k0 k1 t) θ₀ L, by simp only [h0], by simp only [h1],
    fun t s => hasDerivAt_interpCurve (continuous_kappaInterp hk0 hk1) s,
    fun t s => hasDerivAt_tangentAngle (continuous_kappaInterp hk0 hk1) s,
    fun t ht s => ⟨kappaInterp_pos hk0pos hk1pos ht s, kappaInterp_le hk0le hk1le ht s⟩,
    fun t s => interpCurve_add_halfPeriod (continuous_kappaInterp hk0 hk1)
      (periodic_kappaInterp (t := t) hper0 hper1)
      (integral_kappaInterp (t := t) hk0 hk1 htot0 htot1) s,
    fun t => interpCurve_periodic (continuous_kappaInterp hk0 hk1)
      (periodic_kappaInterp (t := t) hper0 hper1)
      (integral_kappaInterp (t := t) hk0 hk1 htot0 htot1),
    curvature_interpolation_estimate hk0 hk1 hper0 hper1 htot0 htot1 hL
      (fun r => (hk0pos r).le) (fun r => (hk1pos r).le) hk0le hk1le hkstar⟩

/-! ## The hypotheses are not vacuous -/

/-- The curvature of the circle of half-perimeter `2π`. -/
def kcirc : ℝ → ℝ := fun _ => 1 / 2

/-- A non-constant admissible curvature of the same half-perimeter `2π` and the
same total turning `π`. -/
def kwave : ℝ → ℝ := fun s => 1 / 2 + Real.cos s / 4

theorem continuous_kcirc : Continuous kcirc := continuous_const

theorem continuous_kwave : Continuous kwave := by unfold kwave; fun_prop

theorem kcirc_periodic : Function.Periodic kcirc (2 * Real.pi) := fun _ => rfl

theorem kwave_periodic : Function.Periodic kwave (2 * Real.pi) := fun x => by
  simp [kwave, Real.cos_add_two_pi]

theorem kcirc_total : (∫ r in (0:ℝ)..(2 * Real.pi), kcirc r) = Real.pi := by
  simp [kcirc]
  ring

theorem kwave_total : (∫ r in (0:ℝ)..(2 * Real.pi), kwave r) = Real.pi := by
  have hcos : (∫ s in (0:ℝ)..(2 * Real.pi), Real.cos s / 4) = 0 := by
    rw [intervalIntegral.integral_div]
    simp [integral_cos]
  have hsplit : (∫ s in (0:ℝ)..(2 * Real.pi), kwave s)
      = (∫ s in (0:ℝ)..(2 * Real.pi), (1/2 : ℝ))
        + ∫ s in (0:ℝ)..(2 * Real.pi), Real.cos s / 4 := by
    simp only [kwave]
    exact intervalIntegral.integral_add (_root_.intervalIntegrable_const)
      ((Real.continuous_cos.div_const 4).intervalIntegrable _ _)
  rw [hsplit, hcos]
  simp
  ring

theorem kcirc_nonneg (r : ℝ) : 0 ≤ kcirc r := by norm_num [kcirc]

theorem kwave_nonneg (r : ℝ) : 0 ≤ kwave r := by
  have := Real.neg_one_le_cos r
  simp only [kwave]
  linarith

theorem kcirc_le (r : ℝ) : kcirc r ≤ 3 / 4 := by norm_num [kcirc]

theorem kwave_le (r : ℝ) : kwave r ≤ 3 / 4 := by
  have := Real.cos_le_one r
  simp only [kwave]
  linarith

/-- **The estimate on a genuine pair of curvatures.**  The circle of curvature
`1/2` and the oval of curvature `1/2 + (cos s)/4` are two admissible marked
curves of half-perimeter `2π`, so the estimate of the lemma is not vacuous. -/
theorem curvature_interpolation_estimate_instance :
    (∫ t in (0:ℝ)..1, Wnorm kcirc kwave 0 (2 * Real.pi) t)
        + (∫ t in (0:ℝ)..1, S0norm kcirc kwave 0 (2 * Real.pi) t)
        + (∫ t in (0:ℝ)..1, S1norm kcirc kwave 0 (2 * Real.pi) t)
      ≤ 6 * (1 + 2 * Real.pi) ^ 2 * curvDist kcirc kwave (2 * Real.pi) :=
  curvature_interpolation_estimate (kstar := 3/4) (θ₀ := 0)
    continuous_kcirc continuous_kwave kcirc_periodic kwave_periodic kcirc_total kwave_total
    (by positivity) kcirc_nonneg kwave_nonneg kcirc_le kwave_le (by norm_num)

end InterpolationEstimate
