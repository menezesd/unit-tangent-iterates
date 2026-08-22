import Mathlib
import UnitTangentIterates.PinchedPathBasic

/-!
# Running an admissible path on a flat time profile

The concatenation of two normal paths glues the two motions at the seam; the
glued family is continuous, and its velocity vanishes there, but it is not in
general smooth in the time, so the concatenation of two paths admissible for the
`C²` estimate (`SelInvTubePathDist.IsPinchedPath`, which asks the family of
slices to be jointly `C⁶`) need not be admissible.

This file removes the obstruction by running each path on a *flat* time profile.
For a path of duration `T` the profile

```
  w(t) = T · smoothTransition (2t/T − ½)
```

is smooth, nondecreasing, and equal to `0` on `(−∞, T/4]` and to `T` on
`[3T/4, ∞)`, so the reparametrized family stands still — identically equal to
its initial, resp. terminal, slice — on a *neighbourhood* of each endpoint of
the time interval, while the total cost is unchanged, the change of variables
being the substitution `∫₀^T m(w(t))w'(t)dt = ∫₀^T m`.

Main results: `flatTime`, `slow`, `cost_slow`, `isPinchedPath_slow`,
`slow_X_of_le`, `slow_X_of_ge`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist

variable {kminP kh : ℝ} {p q : Data}

/-! ### The flat time profile -/

/-- The flat time profile of duration `T`: it increases smoothly from `0` to
`T`, and is constant outside the window `[T/4, 3T/4]`. -/
def flatTime (T t : ℝ) : ℝ := T * Real.smoothTransition (2 * t / T - 1 / 2)

/-- The derivative of the flat time profile. -/
def flatSpeed (T : ℝ) : ℝ → ℝ := deriv (flatTime T)

theorem contDiff_flatTime {n : ℕ} (T : ℝ) : ContDiff ℝ (n : ℕ) (flatTime T) := by
  have hs : ContDiff ℝ (n : ℕ) Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := (n : ℕ∞))
  have hlin : ContDiff ℝ (n : ℕ) fun t : ℝ => 2 * t / T - 1 / 2 := by fun_prop
  exact contDiff_const.mul (hs.comp hlin)

theorem differentiable_flatTime (T : ℝ) : Differentiable ℝ (flatTime T) :=
  (contDiff_flatTime (n := 1) T).differentiable (by norm_num)

theorem hasDerivAt_flatTime (T t : ℝ) : HasDerivAt (flatTime T) (flatSpeed T t) t :=
  (differentiable_flatTime T t).hasDerivAt

theorem contDiff_flatSpeed {n : ℕ} (T : ℝ) : ContDiff ℝ (n : ℕ) (flatSpeed T) :=
  ContDiff.deriv' (contDiff_flatTime (n := n + 1) T)

theorem continuous_flatSpeed (T : ℝ) : Continuous (flatSpeed T) :=
  (contDiff_flatSpeed (n := 0) T).continuous

theorem monotone_flatTime {T : ℝ} (hT : 0 < T) : Monotone (flatTime T) := by
  intro a b hab
  have h : 2 * a / T - 1 / 2 ≤ 2 * b / T - 1 / 2 := by
    have h2 : 2 * a / T ≤ 2 * b / T := by gcongr
    linarith
  exact mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone h) hT.le

theorem flatSpeed_nonneg {T : ℝ} (hT : 0 < T) (t : ℝ) : 0 ≤ flatSpeed T t :=
  (monotone_flatTime hT).deriv_nonneg

theorem flatTime_of_le {T t : ℝ} (hT : 0 < T) (ht : t ≤ T / 4) : flatTime T t = 0 := by
  have h : 2 * t / T - 1 / 2 ≤ 0 := by
    have h1 : 2 * t / T ≤ 1 / 2 := by
      rw [div_le_iff₀ hT]; linarith
    linarith
  rw [flatTime, Real.smoothTransition.zero_of_nonpos h, mul_zero]

theorem flatTime_of_ge {T t : ℝ} (hT : 0 < T) (ht : 3 * T / 4 ≤ t) : flatTime T t = T := by
  have h : 1 ≤ 2 * t / T - 1 / 2 := by
    have h1 : 3 / 2 ≤ 2 * t / T := by
      rw [le_div_iff₀ hT]; linarith
    linarith
  rw [flatTime, Real.smoothTransition.one_of_one_le h, mul_one]

theorem flatTime_zero {T : ℝ} (hT : 0 < T) : flatTime T 0 = 0 :=
  flatTime_of_le hT (by positivity)

theorem flatTime_final {T : ℝ} (hT : 0 < T) : flatTime T T = T :=
  flatTime_of_ge hT (by linarith)

theorem flatSpeed_of_lt {T t : ℝ} (hT : 0 < T) (ht : t < T / 4) : flatSpeed T t = 0 := by
  have hev : flatTime T =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs using flatTime_of_le hT (le_of_lt hs)
  have := hev.deriv_eq
  simpa [flatSpeed] using this

theorem flatSpeed_of_gt {T t : ℝ} (hT : 0 < T) (ht : 3 * T / 4 < t) : flatSpeed T t = 0 := by
  have hev : flatTime T =ᶠ[nhds t] fun _ => T := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using flatTime_of_ge hT (le_of_lt hs)
  have := hev.deriv_eq
  simpa [flatSpeed] using this

theorem flatSpeed_eq_zero_outside {T t : ℝ} (hT : 0 < T) (ht : t ∉ Ioo (0 : ℝ) T) :
    flatSpeed T t = 0 := by
  rcases lt_or_ge t (T / 4) with h | h
  · exact flatSpeed_of_lt hT h
  · refine flatSpeed_of_gt hT ?_
    by_contra hcon
    push_neg at hcon
    exact ht ⟨by linarith, by linarith⟩

/-! ### The path run on the flat profile -/

/-- **An admissible path, run on the flat time profile.**  The motion is the
same, reparametrized in the time so that the family stands still near the two
ends of the time interval. -/
def slow (Γ : NormalPath p q) : NormalPath p q where
  T := Γ.T
  T_pos := Γ.T_pos
  X := fun t u => Γ.X (flatTime Γ.T t) u
  eta := fun t u => flatSpeed Γ.T t * Γ.eta (flatTime Γ.T t) u
  nu := fun t u => Γ.nu (flatTime Γ.T t) u
  m := fun t => flatSpeed Γ.T t * Γ.m (flatTime Γ.T t)
  start := fun u => by rw [flatTime_zero Γ.T_pos]; exact Γ.start u
  finish := fun u => by rw [flatTime_final Γ.T_pos]; exact Γ.finish u
  hasDerivAt_time := by
    intro t u
    have h := (Γ.hasDerivAt_time (flatTime Γ.T t) u).scomp t (hasDerivAt_flatTime Γ.T t)
    refine h.congr_deriv ?_
    simp [Complex.real_smul]
    ring
  cont_vel := by
    intro u
    have hcomp : Continuous fun t =>
        ((Γ.eta (flatTime Γ.T t) u : ℂ) * Γ.nu (flatTime Γ.T t) u) :=
      (Γ.cont_vel u).comp (differentiable_flatTime Γ.T).continuous
    have hfun : (fun t => ((flatSpeed Γ.T t * Γ.eta (flatTime Γ.T t) u : ℝ) : ℂ)
        * Γ.nu (flatTime Γ.T t) u)
        = fun t => ((flatSpeed Γ.T t : ℝ) : ℂ) *
          ((Γ.eta (flatTime Γ.T t) u : ℂ) * Γ.nu (flatTime Γ.T t) u) := by
      funext t; push_cast; ring
    rw [hfun]
    exact (Complex.continuous_ofReal.comp (continuous_flatSpeed Γ.T)).mul hcomp
  norm_nu := fun t u => Γ.norm_nu _ u
  cont_m := (continuous_flatSpeed Γ.T).mul
    (Γ.cont_m.comp (differentiable_flatTime Γ.T).continuous)
  m_nonneg := fun t =>
    mul_nonneg (flatSpeed_nonneg Γ.T_pos t) (Γ.m_nonneg _)
  m_stop := fun t ht => by rw [flatSpeed_eq_zero_outside Γ.T_pos ht, zero_mul]
  abs_eta_le := by
    intro t u
    rw [abs_mul, abs_of_nonneg (flatSpeed_nonneg Γ.T_pos t)]
    exact mul_le_mul_of_nonneg_left (Γ.abs_eta_le _ u) (flatSpeed_nonneg Γ.T_pos t)
  le_m_L1 := by
    intro t
    have hfun : (∫ u in (0:ℝ)..1, |flatSpeed Γ.T t * Γ.eta (flatTime Γ.T t) u|)
        = flatSpeed Γ.T t * ∫ u in (0:ℝ)..1, |Γ.eta (flatTime Γ.T t) u| := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [abs_mul, abs_of_nonneg (flatSpeed_nonneg Γ.T_pos t)]
    rw [hfun]
    exact mul_le_mul_of_nonneg_left (Γ.le_m_L1 _) (flatSpeed_nonneg Γ.T_pos t)
  le_m_sup := by
    intro t j hj
    rw [PathMetric.iteratedDeriv_const_mul' _ _ j,
      PathMetric.supNorm_const_mul (flatSpeed_nonneg Γ.T_pos t)]
    exact mul_le_mul_of_nonneg_left (Γ.le_m_sup _ j hj) (flatSpeed_nonneg Γ.T_pos t)

@[simp] theorem slow_T (Γ : NormalPath p q) : (slow Γ).T = Γ.T := rfl

/-- **Running a path on the flat profile does not change its cost.** -/
theorem cost_slow (Γ : NormalPath p q) : cost (slow Γ) = cost Γ := by
  have hsub : (∫ t in (0:ℝ)..Γ.T, flatSpeed Γ.T t • (Γ.m ∘ flatTime Γ.T) t)
      = ∫ s in (flatTime Γ.T 0)..(flatTime Γ.T Γ.T), Γ.m s :=
    intervalIntegral.integral_comp_smul_deriv
      (fun x _ => hasDerivAt_flatTime Γ.T x)
      (continuous_flatSpeed Γ.T).continuousOn Γ.cont_m
  rw [flatTime_zero Γ.T_pos, flatTime_final Γ.T_pos] at hsub
  simpa [cost, slow, Function.comp_def, smul_eq_mul] using hsub

/-- Near the start, the reparametrized family is the initial curve. -/
theorem slow_X_of_le (Γ : NormalPath p q) {t : ℝ} (ht : t ≤ Γ.T / 4) (u : ℝ) :
    (slow Γ).X t u = p.1 u := by
  show Γ.X (flatTime Γ.T t) u = p.1 u
  rw [flatTime_of_le Γ.T_pos ht]
  exact Γ.start u

/-- Near the end, the reparametrized family is the terminal curve. -/
theorem slow_X_of_ge (Γ : NormalPath p q) {t : ℝ} (ht : 3 * Γ.T / 4 ≤ t) (u : ℝ) :
    (slow Γ).X t u = q.1 u := by
  show Γ.X (flatTime Γ.T t) u = q.1 u
  rw [flatTime_of_ge Γ.T_pos ht]
  exact Γ.finish u

/-- **The path run on the flat profile is still admissible.** -/
theorem isPinchedPath_slow (Γ : NormalPath p q) (hΓ : IsPinchedPath kminP kh Γ) :
    IsPinchedPath kminP kh (slow Γ) := by
  have hX6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X) := hΓ.smooth
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry Γ.X) := hX6.of_le (by norm_num)
  have hd : Differentiable ℝ (uncurry Γ.X) := hX2.differentiable (by norm_num)
  have hphi : Differentiable ℝ (flatTime Γ.T) := differentiable_flatTime Γ.T
  refine
    { smooth := by
        show ContDiff ℝ (6 : ℕ) (uncurry fun t u => Γ.X (flatTime Γ.T t) u)
        exact contDiff_uncurry_timeComp hX6 (contDiff_flatTime (n := 6) Γ.T)
      speed := fun t u => ?_
      per := fun t => hΓ.per (flatTime Γ.T t)
      normal := fun t u => ?_
      kmin := fun t σ => ?_
      kmax := fun t σ => ?_
      short := fun t => ?_
      slit := fun t => ?_
      rest := fun t => ?_ }
  · show ‖pathVel (fun t u => Γ.X (flatTime Γ.T t) u) t u‖
      = ‖pathVel (fun t u => Γ.X (flatTime Γ.T t) u) t 0‖
    rw [pathVel_timeComp hd hphi, pathVel_timeComp hd hphi]
    exact hΓ.speed (flatTime Γ.T t) u
  · show Γ.nu (flatTime Γ.T t) u
      = Complex.I * (pathVel (fun t u => Γ.X (flatTime Γ.T t) u) t u
          / ((pathPerim (fun t u => Γ.X (flatTime Γ.T t) u) t : ℝ) : ℂ))
    rw [pathVel_timeComp hd hphi, pathPerim_timeComp hd hphi]
    exact hΓ.normal (flatTime Γ.T t) u
  · show kminP ≤ pathKn (fun t u => Γ.X (flatTime Γ.T t) u)
      (pathPerim fun t u => Γ.X (flatTime Γ.T t) u) t σ
    rw [pathKn_timeComp hX2 hphi]
    exact hΓ.kmin (flatTime Γ.T t) σ
  · show pathKn (fun t u => Γ.X (flatTime Γ.T t) u)
      (pathPerim fun t u => Γ.X (flatTime Γ.T t) u) t σ ≤ kh
    rw [pathKn_timeComp hX2 hphi]
    exact hΓ.kmax (flatTime Γ.T t) σ
  · show kh * pathPerim (fun t u => Γ.X (flatTime Γ.T t) u) t < 4 * Real.pi
    rw [pathPerim_timeComp hd hphi]
    exact hΓ.short (flatTime Γ.T t)
  · show pathVel (fun t u => Γ.X (flatTime Γ.T t) u) t 0 ∈ Complex.slitPlane
    rw [pathVel_timeComp hd hphi]
    exact hΓ.slit (flatTime Γ.T t)
  · show flatSpeed Γ.T t * Γ.eta (flatTime Γ.T t) 0 = 0
    rw [hΓ.rest (flatTime Γ.T t), mul_zero]

end PinchedPath
