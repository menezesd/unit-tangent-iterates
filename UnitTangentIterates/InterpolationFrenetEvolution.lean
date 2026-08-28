import Mathlib
import UnitTangentIterates.InterpolationSmooth
import UnitTangentIterates.InterpolationSecondOrder
import UnitTangentIterates.MixedPartials

/-! # Frenet time derivatives for curvature interpolation -/

noncomputable section

open Function

namespace InterpolationFrenetEvolution

open CurvatureInterpolation InterpolationNormal InterpolationEstimate
  InterpolationSecondOrder

variable {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L : ℝ}

/-- The time derivative of the tangent-angle lift is the accumulated curvature
difference. -/
theorem hasDerivAt_tangentAngle_time (hk0 : Continuous k0) (hk1 : Continuous k1)
    (t s : ℝ) :
    HasDerivAt
      (fun r => tangentAngle (kappaInterp k0 k1 r) theta0 s)
      (angleShift k0 k1 s) t := by
  simp only [tangentAngle_kappaInterp hk0 hk1]
  simpa using ((hasDerivAt_id t).mul_const (angleShift k0 k1 s)).const_add
    (tangentAngle k0 theta0 s)

/-- The time derivative of the linearly interpolated curvature. -/
theorem hasDerivAt_kappaInterp_time (t s : ℝ) :
    HasDerivAt (fun r => kappaInterp k0 k1 r s) (k1 s - k0 s) t := by
  simp only [kappaInterp]
  convert ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul_const (k0 s) |>.add
    ((hasDerivAt_id t).mul_const (k1 s)) using 1 <;> ring

/-- The spatial derivative of the tangent-angle time rate agrees with the
curvature time rate. -/
theorem hasDerivAt_angleShift (hk0 : Continuous k0) (hk1 : Continuous k1) (s : ℝ) :
    HasDerivAt (angleShift k0 k1) (k1 s - k0 s) s := by
  have hc : Continuous fun x => k1 x - k0 x := hk1.sub hk0
  simpa [angleShift] using (hc.integral_hasStrictDerivAt (0 : ℝ) s).hasDerivAt

/-- The three explicit interpolation frame rates are jointly continuous. -/
theorem continuous_frame_rates (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0' : Continuous k0') (hk1' : Continuous k1') :
    Continuous (uncurry fun (_ : ℝ) (s : ℝ) => angleShift k0 k1 s) ∧
    Continuous (uncurry fun (_ : ℝ) (s : ℝ) => k1 s - k0 s) ∧
    Continuous (uncurry fun t s => (1 - t) * k0' s + t * k1' s) := by
  refine ⟨(continuous_angleShift hk0 hk1).comp continuous_snd,
    (hk1.comp continuous_snd).sub (hk0.comp continuous_snd), ?_⟩
  exact ((continuous_const.sub continuous_fst).mul (hk0'.comp continuous_snd)).add
    (continuous_fst.mul (hk1'.comp continuous_snd))

/-- The `a`-derivative of the `x`-partial of a `C²` function of two real
variables exists, with the second total derivative as its value.  This is the
first half of the data behind Clairaut's theorem, exported as a differentiation
statement rather than as an identity between `deriv`s. -/
private theorem hasDerivAt_deriv_space_time {f : ℝ → ℝ → ℂ}
    (hf : ContDiff ℝ 2 (uncurry f)) (a x : ℝ) :
    HasDerivAt (fun a' => deriv (fun x' => f a' x') x)
      ((fderiv ℝ (fderiv ℝ (uncurry f)) (a, x) ((1, 0) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ)) a := by
  set g : ℝ × ℝ → ℂ := uncurry f with hgdef
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hf.fderiv_right le_rfl
  have hgd : ∀ p : ℝ × ℝ, HasFDerivAt g (fderiv ℝ g p) p := fun p =>
    (hf.differentiable (by norm_num) p).hasFDerivAt
  have hg2 : ∀ p : ℝ × ℝ,
      HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) p) p := fun p =>
    (hg1.differentiable (by norm_num) p).hasFDerivAt
  have hpx : ∀ a' : ℝ, HasDerivAt (fun x' => f a' x')
      (fderiv ℝ g (a', x) ((0, 1) : ℝ × ℝ)) x := by
    intro a'
    exact (hgd (a', x)).comp_hasDerivAt x ((hasDerivAt_const x a').prodMk (hasDerivAt_id x))
  have hLfun : (fun a' => deriv (fun x' => f a' x') x)
      = fun a' => fderiv ℝ g (a', x) ((0, 1) : ℝ × ℝ) := by
    funext a'; exact (hpx a').deriv
  rw [hLfun]
  have h3 : HasDerivAt (fun a' : ℝ => fderiv ℝ g (a', x))
      (fderiv ℝ (fderiv ℝ g) (a, x) ((1, 0) : ℝ × ℝ)) a :=
    (hg2 (a, x)).comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a x))
  exact (ContinuousLinearMap.apply ℝ ℂ ((0, 1) : ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt a h3

/-- The mirror statement: the `x`-derivative of the `a`-partial. -/
private theorem hasDerivAt_deriv_time_space {f : ℝ → ℝ → ℂ}
    (hf : ContDiff ℝ 2 (uncurry f)) (a x : ℝ) :
    HasDerivAt (fun x' => deriv (fun a' => f a' x') a)
      ((fderiv ℝ (fderiv ℝ (uncurry f)) (a, x) ((0, 1) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ)) x := by
  set g : ℝ × ℝ → ℂ := uncurry f with hgdef
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hf.fderiv_right le_rfl
  have hgd : ∀ p : ℝ × ℝ, HasFDerivAt g (fderiv ℝ g p) p := fun p =>
    (hf.differentiable (by norm_num) p).hasFDerivAt
  have hg2 : ∀ p : ℝ × ℝ,
      HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) p) p := fun p =>
    (hg1.differentiable (by norm_num) p).hasFDerivAt
  have hpa : ∀ x' : ℝ, HasDerivAt (fun a' => f a' x')
      (fderiv ℝ g (a, x') ((1, 0) : ℝ × ℝ)) a := by
    intro x'
    exact (hgd (a, x')).comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a x'))
  have hRfun : (fun x' => deriv (fun a' => f a' x') a)
      = fun x' => fderiv ℝ g (a, x') ((1, 0) : ℝ × ℝ) := by
    funext x'; exact (hpa x').deriv
  rw [hRfun]
  have h3 : HasDerivAt (fun x' : ℝ => fderiv ℝ g (a, x'))
      (fderiv ℝ (fderiv ℝ g) (a, x) ((0, 1) : ℝ × ℝ)) x :=
    (hg2 (a, x)).comp_hasDerivAt x ((hasDerivAt_const x a).prodMk (hasDerivAt_id x))
  exact (ContinuousLinearMap.apply ℝ ℂ ((1, 0) : ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt x h3

/-- Mixed time/space differentiation of `interpCurve`, in precisely the
existential form used by the normal-rate gauge theorem. -/
theorem exists_mixed_interpCurve
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hC2 : ContDiff ℝ 2 (uncurry fun t s => interpCurve (kappaInterp k0 k1 t) theta0 L s))
    (t s : ℝ) :
    ∃ W : ℂ,
      HasDerivAt
        (fun r => Complex.exp
          (Complex.I * (tangentAngle (kappaInterp k0 k1 r) theta0 s : ℂ))) W t ∧
      HasDerivAt (fun x => interpVelocity k0 k1 theta0 L t x) W s := by
  have hspace : ∀ a x : ℝ,
      deriv (fun x' => interpCurve (kappaInterp k0 k1 a) theta0 L x') x
        = Complex.exp (Complex.I * (tangentAngle (kappaInterp k0 k1 a) theta0 x : ℂ)) := by
    intro a x
    have h : HasDerivAt (fun x' => interpCurve (kappaInterp k0 k1 a) theta0 L x')
        (Complex.exp (Complex.I * (tangentAngle (kappaInterp k0 k1 a) theta0 x : ℂ))) x := by
      simpa [tau, mul_comm] using
        hasDerivAt_interpCurve (θ₀ := theta0) (L := L)
          (continuous_kappaInterp hk0 hk1) x
    exact h.deriv
  have htime : ∀ a x : ℝ,
      deriv (fun a' => interpCurve (kappaInterp k0 k1 a') theta0 L x) a
        = interpVelocity k0 k1 theta0 L a x := fun a x =>
    (hasDerivAt_interpCurve_param (θ₀ := theta0) (L := L) hk0 hk1 x a).deriv
  have hA := hasDerivAt_deriv_space_time hC2 t s
  have hB := hasDerivAt_deriv_time_space hC2 t s
  have hcomm := MixedPartials.deriv_partial_comm hC2 t s
  have hAB := (hA.deriv.symm.trans hcomm).trans hB.deriv
  rw [funext fun a' => hspace a' s] at hA
  rw [funext fun x' => htime t x'] at hB
  refine ⟨_, hA, ?_⟩
  rw [hAB]
  exact hB

/-- The complete qualitative frame-time block needed by
`GaugeNormalRateFundamental`. -/
theorem interpolation_frame_time_block
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0' : Continuous k0') (hk1' : Continuous k1')
    (hC2 : ContDiff ℝ 2 (uncurry fun t s => interpCurve (kappaInterp k0 k1 t) theta0 L s)) :
    (∀ t s, HasDerivAt
      (fun r => tangentAngle (kappaInterp k0 k1 r) theta0 s)
      (angleShift k0 k1 s) t) ∧
    (∀ t s, HasDerivAt (fun r => kappaInterp k0 k1 r s) (k1 s - k0 s) t) ∧
    (∀ (_ : ℝ) (s : ℝ), HasDerivAt (angleShift k0 k1) (k1 s - k0 s) s) ∧
    Continuous (uncurry fun (_ : ℝ) (s : ℝ) => angleShift k0 k1 s) ∧
    Continuous (uncurry fun (_ : ℝ) (s : ℝ) => k1 s - k0 s) ∧
    Continuous (uncurry fun t s => (1 - t) * k0' s + t * k1' s) ∧
    (∀ t s, ∃ W : ℂ,
      HasDerivAt
        (fun r => Complex.exp
          (Complex.I * (tangentAngle (kappaInterp k0 k1 r) theta0 s : ℂ))) W t ∧
      HasDerivAt (fun x => interpVelocity k0 k1 theta0 L t x) W s) := by
  obtain ⟨ha, hk, hkx⟩ := continuous_frame_rates hk0 hk1 hk0' hk1'
  exact ⟨hasDerivAt_tangentAngle_time hk0 hk1,
    fun t s => hasDerivAt_kappaInterp_time t s,
    fun _ s => hasDerivAt_angleShift hk0 hk1 s,
    ha, hk, hkx, exists_mixed_interpCurve hk0 hk1 hC2⟩

end InterpolationFrenetEvolution
