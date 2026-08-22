import Mathlib
import UnitTangentIterates.CurvatureInterpolation

/-!
# The normal component of the curvature-interpolation path

This file completes the quantitative half of the lemma *Curvature interpolation*
of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*.

`UnitTangentIterates/CurvatureInterpolation.lean` builds the interpolating path

`X_t(s) = ∫₀ˢ τ(θ_t(r)) dr - ½ ∫₀ᴸ τ(θ_t(r)) dr`,  `θ_t = θ₀ + ∫₀ˢ κ_t`,
`κ_t = (1-t)κ⁰ + tκ¹`,

and proves the sup-norm estimate `‖X_t(s) - X_{t'}(s)‖ ≤ (3/2) L |t - t'| ε`
with `ε = ‖κ¹ - κ⁰‖_{L¹(0,L)}`.  The paper then decomposes the velocity in the
Frenet frame, `Ẋ_t = ξ τ + η ν`, and deduces from `θ̇_t = η_s + κ_t ξ` the bounds

`‖η‖_∞ ≤ C L ε`,  `‖η_s‖_∞ ≤ C (1 + L) ε`,

and finally `W + S₀ + S₁ ≤ C (1 + L)² ε`.

Main results:

* `frame_decomp`, `abs_tangentComp_le`, `abs_normalComp_le` : the Frenet-frame
  coordinates `ξ = ⟨z, τ⟩`, `η = ⟨z, ν⟩` of a velocity vector, and the bound
  `|ξ|, |η| ≤ ‖z‖`;
* `abs_normalComp_deriv_le` : a velocity obtained as a derivative of a
  Lipschitz path has frame coordinates bounded by the Lipschitz constant;
* `hasDerivAt_interpCurve_param` : the interpolation path is differentiable in
  the path parameter, with velocity `interpVelocity` obtained by
  differentiating under the integral sign;
* `abs_normalComp_interpCurve_deriv_le`, `abs_normalComp_interpVelocity_le` :
  consequently the normal velocity of the interpolation path obeys
  `|η| ≤ (3/2) L ε`;
* `abs_normalDeriv_le` : from the unit-speed first variation
  `θ̇ = η_s + κ ξ`, the bound `|η_s| ≤ (1 + (3/2) κ_* L) ε`;
* `integral_abs_le_of_sup_le` : the `L¹`-over-a-period bound `‖η‖_{L¹} ≤ 2L‖η‖_∞`;
* `pathFunctional_bound` : the resulting estimate `W + S₀ + S₁ ≤ 6(1+L)² ε`.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace InterpolationNormal

open CurvatureInterpolation

/-! ## The Frenet frame coordinates of a velocity vector -/

/-- The tangential coordinate `⟨z, τ(θ)⟩` of a plane vector `z`. -/
def tangentComp (z : ℂ) (θ : ℝ) : ℝ := z.re * Real.cos θ + z.im * Real.sin θ

/-- The normal coordinate `⟨z, ν(θ)⟩` of a plane vector `z`, where
`ν(θ) = i τ(θ)` is the tangent rotated by `π/2`. -/
def normalComp (z : ℂ) (θ : ℝ) : ℝ := z.im * Real.cos θ - z.re * Real.sin θ

theorem tangentComp_eq (z : ℂ) (θ : ℝ) :
    tangentComp z θ = (z * (starRingEnd ℂ) (tau θ)).re := by
  simp [tangentComp, tau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem normalComp_eq (z : ℂ) (θ : ℝ) :
    normalComp z θ = (z * (starRingEnd ℂ) (Complex.I * tau θ)).re := by
  simp [normalComp, tau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **The Frenet decomposition** `z = ξ τ + η ν` of a plane vector. -/
theorem frame_decomp (z : ℂ) (θ : ℝ) :
    z = (tangentComp z θ : ℂ) * tau θ + (normalComp z θ : ℂ) * (Complex.I * tau θ) := by
  have hpy : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  apply Complex.ext
  · simp only [tangentComp, normalComp, tau, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination (-z.re) * hpy
  · simp only [tangentComp, normalComp, tau, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination (-z.im) * hpy

theorem sq_add_sq_frame (z : ℂ) (θ : ℝ) :
    tangentComp z θ ^ 2 + normalComp z θ ^ 2 = ‖z‖ ^ 2 := by
  have hpy : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hz, tangentComp, normalComp]
  nlinarith [hpy]

theorem abs_tangentComp_le (z : ℂ) (θ : ℝ) : |tangentComp z θ| ≤ ‖z‖ := by
  have h := sq_add_sq_frame z θ
  have h1 : tangentComp z θ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg (normalComp z θ)]
  exact abs_le.mpr (abs_le_of_sq_le_sq' h1 (norm_nonneg z))

theorem abs_normalComp_le (z : ℂ) (θ : ℝ) : |normalComp z θ| ≤ ‖z‖ := by
  have h := sq_add_sq_frame z θ
  have h1 : normalComp z θ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg (tangentComp z θ)]
  exact abs_le.mpr (abs_le_of_sq_le_sq' h1 (norm_nonneg z))

/-! ## Velocity bounds from a Lipschitz bound on the path -/

/-- If a path of plane vectors is `C`-Lipschitz, then any of its velocities has
norm at most `C`. -/
theorem norm_deriv_le_of_lipschitz_bound {f : ℝ → ℂ} {C : ℝ} {v : ℂ} {t : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ a b, ‖f a - f b‖ ≤ C * |a - b|) (h : HasDerivAt f v t) :
    ‖v‖ ≤ C := by
  refine h.le_of_lip' hC ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hlip x t

/-- The Frenet coordinates of the velocity of a `C`-Lipschitz path are bounded
by `C`. -/
theorem abs_normalComp_deriv_le {f : ℝ → ℂ} {C : ℝ} {v : ℂ} {t θ : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ a b, ‖f a - f b‖ ≤ C * |a - b|) (h : HasDerivAt f v t) :
    |normalComp v θ| ≤ C :=
  (abs_normalComp_le v θ).trans (norm_deriv_le_of_lipschitz_bound hC hlip h)

theorem abs_tangentComp_deriv_le {f : ℝ → ℂ} {C : ℝ} {v : ℂ} {t θ : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ a b, ‖f a - f b‖ ≤ C * |a - b|) (h : HasDerivAt f v t) :
    |tangentComp v θ| ≤ C :=
  (abs_tangentComp_le v θ).trans (norm_deriv_le_of_lipschitz_bound hC hlip h)

/-! ## The interpolation path -/

variable {k0 k1 : ℝ → ℝ} {θ₀ L : ℝ}

theorem integral_abs_sub_nonneg (hk0 : Continuous k0) (hk1 : Continuous k1) (hL : 0 ≤ L) :
    0 ≤ ∫ r in (0:ℝ)..L, |k1 r - k0 r| := by
  have hca : Continuous fun r => |k1 r - k0 r| := by fun_prop
  have := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := L)
    (f := fun _ => (0:ℝ)) (g := fun r => |k1 r - k0 r|) hL
    (_root_.intervalIntegrable_const) (hca.intervalIntegrable _ _) (fun r _ => abs_nonneg _)
  simpa using this

/-- The interpolation path is `(3/2)Lε`-Lipschitz in the path parameter, at every
point `s` of the fundamental interval. -/
theorem lipschitz_interpCurve (hk0 : Continuous k0) (hk1 : Continuous k1)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) (a b : ℝ) :
    ‖interpCurve (kappaInterp k0 k1 a) θ₀ L s - interpCurve (kappaInterp k0 k1 b) θ₀ L s‖
      ≤ ((3/2) * L * ∫ r in (0:ℝ)..L, |k1 r - k0 r|) * |a - b| := by
  have h := norm_interpCurve_interp_sub (k0 := k0) (k1 := k1) (θ₀ := θ₀) (L := L)
    hk0 hk1 (t := a) (t' := b) hs
  calc ‖interpCurve (kappaInterp k0 k1 a) θ₀ L s
        - interpCurve (kappaInterp k0 k1 b) θ₀ L s‖
      ≤ (3/2) * L * (|a - b| * ∫ r in (0:ℝ)..L, |k1 r - k0 r|) := h
    _ = ((3/2) * L * ∫ r in (0:ℝ)..L, |k1 r - k0 r|) * |a - b| := by ring

/-- **The sup bound on the normal velocity**: `‖η‖_∞ ≤ (3/2) L ε`. -/
theorem abs_normalComp_interpCurve_deriv_le (hk0 : Continuous k0) (hk1 : Continuous k1)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) {t θ : ℝ} {v : ℂ}
    (hv : HasDerivAt (fun r => interpCurve (kappaInterp k0 k1 r) θ₀ L s) v t) :
    |normalComp v θ| ≤ (3/2) * L * ∫ r in (0:ℝ)..L, |k1 r - k0 r| := by
  have hL : (0:ℝ) ≤ L := le_trans hs.1 hs.2
  have hC : 0 ≤ (3/2) * L * ∫ r in (0:ℝ)..L, |k1 r - k0 r| := by
    have := integral_abs_sub_nonneg hk0 hk1 (L := L) hL
    positivity
  exact abs_normalComp_deriv_le hC (lipschitz_interpCurve (θ₀ := θ₀) hk0 hk1 hs) hv

/-- The same bound for the tangential velocity. -/
theorem abs_tangentComp_interpCurve_deriv_le (hk0 : Continuous k0) (hk1 : Continuous k1)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) {t θ : ℝ} {v : ℂ}
    (hv : HasDerivAt (fun r => interpCurve (kappaInterp k0 k1 r) θ₀ L s) v t) :
    |tangentComp v θ| ≤ (3/2) * L * ∫ r in (0:ℝ)..L, |k1 r - k0 r| := by
  have hL : (0:ℝ) ≤ L := le_trans hs.1 hs.2
  have hC : 0 ≤ (3/2) * L * ∫ r in (0:ℝ)..L, |k1 r - k0 r| := by
    have := integral_abs_sub_nonneg hk0 hk1 (L := L) hL
    positivity
  exact abs_tangentComp_deriv_le hC (lipschitz_interpCurve (θ₀ := θ₀) hk0 hk1 hs) hv

/-! ## The velocity of the interpolation path -/

/-- The accumulated curvature difference `B(r) = ∫₀ʳ (κ¹ - κ⁰)`; the tangent
angle of the interpolation is affine in the path parameter with slope `B`. -/
def angleShift (k0 k1 : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u in (0:ℝ)..r, (k1 u - k0 u)

theorem tangentAngle_kappaInterp (hk0 : Continuous k0) (hk1 : Continuous k1) (t r : ℝ) :
    tangentAngle (kappaInterp k0 k1 t) θ₀ r
      = tangentAngle k0 θ₀ r + t * angleShift k0 k1 r := by
  have h0 : IntervalIntegrable k0 volume 0 r := hk0.intervalIntegrable _ _
  have h1 : IntervalIntegrable k1 volume 0 r := hk1.intervalIntegrable _ _
  simp only [tangentAngle, angleShift, kappaInterp]
  rw [show (∫ u in (0:ℝ)..r, ((1 - t) * k0 u + t * k1 u))
      = ((1 - t) * ∫ u in (0:ℝ)..r, k0 u) + t * ∫ u in (0:ℝ)..r, k1 u from by
    rw [intervalIntegral.integral_add (h0.const_mul _) (h1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul],
    intervalIntegral.integral_sub h1 h0]
  ring

theorem continuous_angleShift (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous (angleShift k0 k1) := by
  have hc : Continuous fun u => k1 u - k0 u := by fun_prop
  exact continuous_iff_continuousAt.mpr fun r =>
    ((hc.integral_hasStrictDerivAt (0:ℝ) r).hasDerivAt).continuousAt

/-- The tangent direction moves with velocity `i B τ` in the path parameter. -/
theorem hasDerivAt_tau_param (hk0 : Continuous k0) (hk1 : Continuous k1) (r t : ℝ) :
    HasDerivAt (fun x : ℝ => tau (tangentAngle (kappaInterp k0 k1 x) θ₀ r))
      (Complex.I * (angleShift k0 k1 r : ℂ)
        * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r)) t := by
  have hang : HasDerivAt (fun x : ℝ => tangentAngle (kappaInterp k0 k1 x) θ₀ r)
      (angleShift k0 k1 r) t := by
    have haff : HasDerivAt (fun x : ℝ => tangentAngle k0 θ₀ r + x * angleShift k0 k1 r)
        (angleShift k0 k1 r) t := by
      simpa using ((hasDerivAt_id t).mul_const (angleShift k0 k1 r)).const_add
        (tangentAngle k0 θ₀ r)
    exact haff.congr_of_eventuallyEq (by
      filter_upwards with x using tangentAngle_kappaInterp (θ₀ := θ₀) hk0 hk1 x r)
  have h := (hasDerivAt_tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r)).scomp t hang
  simpa [Function.comp, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using h

/-- Differentiation under the integral sign in the path parameter. -/
theorem hasDerivAt_integral_param (hk0 : Continuous k0) (hk1 : Continuous k1) (b t : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∫ r in (0:ℝ)..b, tau (tangentAngle (kappaInterp k0 k1 x) θ₀ r))
      (∫ r in (0:ℝ)..b, Complex.I * (angleShift k0 k1 r : ℂ)
        * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r)) t := by
  have hB : Continuous (angleShift k0 k1) := continuous_angleShift hk0 hk1
  have hcont : ∀ x : ℝ, Continuous fun r => tau (tangentAngle (kappaInterp k0 k1 x) θ₀ r) :=
    fun _ => continuous_tau_tangentAngle (continuous_kappaInterp hk0 hk1)
  have hF'cont : ∀ x : ℝ, Continuous fun r => Complex.I * (angleShift k0 k1 r : ℂ)
      * tau (tangentAngle (kappaInterp k0 k1 x) θ₀ r) := fun x =>
    (continuous_const.mul (Complex.continuous_ofReal.comp hB)).mul (hcont x)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0:ℝ)) (b := b) (x₀ := t) (s := Set.univ)
    (F := fun x r => tau (tangentAngle (kappaInterp k0 k1 x) θ₀ r))
    (F' := fun x r => Complex.I * (angleShift k0 k1 r : ℂ)
      * tau (tangentAngle (kappaInterp k0 k1 x) θ₀ r))
    (bound := fun r => |angleShift k0 k1 r|)
    Filter.univ_mem
    (by filter_upwards with x using (hcont x).aestronglyMeasurable.restrict)
    ((hcont t).intervalIntegrable _ _)
    ((hF'cont t).aestronglyMeasurable.restrict)
    (by
      filter_upwards with r _ x _
      simp [Complex.norm_I, norm_tau])
    ((continuous_abs.comp hB).intervalIntegrable _ _)
    (by
      filter_upwards with r _ x _
      exact hasDerivAt_tau_param hk0 hk1 r x)
  exact h.2

/-- **The velocity of the interpolation path** `Ẋ_t(s)`. -/
def interpVelocity (k0 k1 : ℝ → ℝ) (θ₀ L : ℝ) (t s : ℝ) : ℂ :=
  (∫ r in (0:ℝ)..s, Complex.I * (angleShift k0 k1 r : ℂ)
      * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r))
    - (1/2 : ℂ) * ∫ r in (0:ℝ)..L, Complex.I * (angleShift k0 k1 r : ℂ)
      * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r)

theorem hasDerivAt_interpCurve_param (hk0 : Continuous k0) (hk1 : Continuous k1) (s t : ℝ) :
    HasDerivAt (fun x : ℝ => interpCurve (kappaInterp k0 k1 x) θ₀ L s)
      (interpVelocity k0 k1 θ₀ L t s) t := by
  simp only [interpCurve, interpVelocity]
  exact (hasDerivAt_integral_param (θ₀ := θ₀) hk0 hk1 s t).sub
    (((hasDerivAt_integral_param (θ₀ := θ₀) hk0 hk1 L t)).const_mul (1/2 : ℂ))

/-- **The sup bound on the normal velocity**, unconditional form: the normal
component of the velocity of the interpolation path is at most `(3/2) L ε`. -/
theorem abs_normalComp_interpVelocity_le (hk0 : Continuous k0) (hk1 : Continuous k1)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) (t θ : ℝ) :
    |normalComp (interpVelocity k0 k1 θ₀ L t s) θ|
      ≤ (3/2) * L * ∫ r in (0:ℝ)..L, |k1 r - k0 r| :=
  abs_normalComp_interpCurve_deriv_le (θ₀ := θ₀) hk0 hk1 hs
    (hasDerivAt_interpCurve_param (θ₀ := θ₀) (L := L) hk0 hk1 s t)

/-- The same bound for the tangential component. -/
theorem abs_tangentComp_interpVelocity_le (hk0 : Continuous k0) (hk1 : Continuous k1)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) (t θ : ℝ) :
    |tangentComp (interpVelocity k0 k1 θ₀ L t s) θ|
      ≤ (3/2) * L * ∫ r in (0:ℝ)..L, |k1 r - k0 r| :=
  abs_tangentComp_interpCurve_deriv_le (θ₀ := θ₀) hk0 hk1 hs
    (hasDerivAt_interpCurve_param (θ₀ := θ₀) (L := L) hk0 hk1 s t)

/-! ## From the first variation to the estimate for `W + S₀ + S₁` -/

/-- **The first-order bound**: in a unit-speed parametrization the first
variation of the tangent angle is `θ̇ = η_s + κ ξ`, so a bound `|θ̇| ≤ ε` on the
angle together with `|ξ| ≤ (3/2)Lε` and `0 ≤ κ ≤ κ_*` gives
`|η_s| ≤ (1 + (3/2)κ_*L) ε`. -/
theorem abs_normalDeriv_le {thetadot etas kappa xi eps kstar L : ℝ}
    (hid : thetadot = etas + kappa * xi)
    (hth : |thetadot| ≤ eps) (hxi : |xi| ≤ (3/2) * L * eps)
    (hkappa0 : 0 ≤ kappa) (hkappa : kappa ≤ kstar) (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    |etas| ≤ (1 + (3/2) * kstar * L) * eps := by
  have hetas : etas = thetadot - kappa * xi := by linarith [hid]
  have h1 : |kappa * xi| ≤ kstar * ((3/2) * L * eps) := by
    rw [abs_mul, abs_of_nonneg hkappa0]
    have hx0 : 0 ≤ |xi| := abs_nonneg _
    have hb : 0 ≤ (3/2) * L * eps := by positivity
    calc kappa * |xi| ≤ kappa * ((3/2) * L * eps) := by nlinarith
      _ ≤ kstar * ((3/2) * L * eps) := by nlinarith
  calc |etas| = |thetadot - kappa * xi| := by rw [hetas]
    _ ≤ |thetadot| + |kappa * xi| := abs_sub _ _
    _ ≤ eps + kstar * ((3/2) * L * eps) := by linarith
    _ = (1 + (3/2) * kstar * L) * eps := by ring

/-- The `L¹`-over-a-period bound `‖η‖_{L¹(0,2L)} ≤ 2L ‖η‖_∞`. -/
theorem integral_abs_le_of_sup_le {eta : ℝ → ℝ} {M : ℝ} (hL : 0 ≤ L)
    (hcont : Continuous eta) (h : ∀ s, |eta s| ≤ M) :
    (∫ s in (0:ℝ)..(2 * L), |eta s|) ≤ 2 * L * M := by
  have hca : Continuous fun s => |eta s| := by fun_prop
  have h2L : (0:ℝ) ≤ 2 * L := by linarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := 2 * L)
    (f := fun s => |eta s|) (g := fun _ => M) h2L
    (hca.intervalIntegrable _ _) (_root_.intervalIntegrable_const) (fun s _ => h s)
  simpa [mul_comm] using hmono

/-- **The estimate of the lemma**: with `W ≤ 2L·(3/2)Lε`, `S₀ ≤ (3/2)Lε` and
`S₁ ≤ (1 + (3/2)κ_*L)ε`, the three path functionals add up to at most
`6(1+L)²ε`. -/
theorem pathFunctional_bound {W S0 S1 eps kstar : ℝ}
    (hL : 0 ≤ L) (heps : 0 ≤ eps) (hkstar : kstar ≤ 1)
    (hW : W ≤ 2 * L * ((3/2) * L * eps)) (hS0 : S0 ≤ (3/2) * L * eps)
    (hS1 : S1 ≤ (1 + (3/2) * kstar * L) * eps) :
    W + S0 + S1 ≤ 6 * (1 + L) ^ 2 * eps := by
  nlinarith [mul_nonneg hL heps, mul_nonneg (mul_nonneg hL hL) heps]

end InterpolationNormal
