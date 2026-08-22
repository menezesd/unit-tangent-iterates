import Mathlib
import UnitTangentIterates.UniformFrameBounds
import UnitTangentIterates.RearFrameRegularity
import UnitTangentIterates.GaugePeriodRigidity

/-!
# The frame data of a unit-speed family, as a gauge bundle

The path-metric assembly for the selected rears
(`GaugePathRearFamily.pathDist_le_of_rear_family`, and the front-side reductions
of `RearOwnPathDist.lean`) still asks for a bundle
`UniformFrameBounds.GaugeFrameData` whose speed is `1` and whose tangential
component is that of the family of rear tracks written in its own arclength.
Here that bundle is *constructed*.

Two simplifications make it possible.  First, the family is written in its own
arclength, so its speed is identically `1`: the bundle's speed data is constant
and all the bounds attached to it are trivial.  Second — by
`GaugePeriodRigidity.rearFamily_period_constant`, the arclength period is
necessarily the same at every time of such a path — the tangential component is
genuinely *periodic* in the arclength, so it and its two arclength derivatives
are bounded over a compact window of times.  Clamping the time to the window
turns those into global bounds without changing any arclength derivative, and if
the family is at rest outside the window the bundle's tangential component is
the family's on the whole line.

Main results: `exists_gaugeFrameData_unitSpeed`,
`exists_gaugeFrameData_unitSpeed_frozen`, `exists_gaugeFrameData_frameTangential`.
-/

noncomputable section

open Set Function

namespace RearOwnFrameData

open UniformFrameBounds RearFamilyFrame RearFrameRegularity

/-! ### The bundle of a unit-speed family -/

/-- **The gauge frame bundle of a unit-speed family.**  A tangential component
which is `C³` in the pair and periodic in the arclength produces a bundle whose
speed is `1` and whose tangential component is the given one with the time
clamped to the window `[t₀, t₁]`. -/
theorem exists_gaugeFrameData_unitSpeed {xi : ℝ → ℝ → ℝ} {Q t0 t1 : ℝ}
    (hQ : 0 < Q) (ht : t0 ≤ t1) (hxi : ContDiff ℝ (3 : ℕ) (uncurry xi))
    (hxiper : ∀ a, Function.Periodic (xi a) Q) :
    ∃ D : GaugeFrameData, (∀ a x, D.v a x = 1) ∧
      (∀ a x, D.xi a x = xi (clampT t0 t1 a) x) := by
  have h3le2 : ((2 : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)
  have h3le1 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)
  have hxi2 : ContDiff ℝ (2 : ℕ) (uncurry xi) := hxi.of_le h3le2
  have hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi) := hxi.of_le h3le1
  set xiD := partialX xi with hxiDdef
  have hxiD2 : ContDiff ℝ (2 : ℕ) (uncurry xiD) := by
    have : ContDiff ℝ ((2 : ℕ) + 1) (uncurry xi) := by exact_mod_cast hxi
    exact contDiff_partialX this
  have hxiD1 : ContDiff ℝ (1 : ℕ) (uncurry xiD) :=
    hxiD2.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
  set xiDD := partialX xiD with hxiDDdef
  have hxiDD0 : ContDiff ℝ (1 : ℕ) (uncurry xiDD) := by
    have : ContDiff ℝ ((1 : ℕ) + 1) (uncurry xiD) := by exact_mod_cast hxiD2
    exact contDiff_partialX this
  have hxiDper : ∀ a, Function.Periodic (xiD a) Q := periodic_partialX hxi1 hxiper
  have hxiDDper : ∀ a, Function.Periodic (xiDD a) Q := periodic_partialX hxiD1 hxiDper
  obtain ⟨A1, hA1nn, hA1⟩ := exists_bound_of_periodic (t0 := t0) (t1 := t1) hQ
    hxiD1.continuous hxiDper
  obtain ⟨A2, hA2nn, hA2⟩ := exists_bound_of_periodic (t0 := t0) (t1 := t1) hQ
    hxiDD0.continuous hxiDDper
  refine ⟨{
      xi := timeClamp t0 t1 xi
      xi1 := timeClamp t0 t1 xiD
      xi2 := timeClamp t0 t1 xiDD
      v := fun _ _ => 1
      v1 := fun _ _ => 0
      v2 := fun _ _ => 0
      rateLip := A1
      rateBound2 := A2
      hxi := hasDerivAt_timeClamp (hasDerivAt_partialX hxi1)
      hxi1 := hasDerivAt_timeClamp (hasDerivAt_partialX hxiD1)
      hv := fun a x => hasDerivAt_const x (1 : ℝ)
      hv1 := fun a x => hasDerivAt_const x (0 : ℝ)
      hvne := fun _ _ => one_ne_zero
      hxic := continuous_timeClamp hxi1.continuous
      hxi1c := continuous_timeClamp hxiD1.continuous
      hxi2c := continuous_timeClamp hxiDD0.continuous
      hvc := continuous_const
      hv1c := continuous_const
      hv2c := continuous_const
      hrate1 := fun a x => by
        simpa [GaugeRate.gaugeRate1] using timeClamp_bound ht hA1 a x
      hrate2 := fun a x => by
        simpa [GaugeRate.gaugeRate2] using timeClamp_bound ht hA2 a x },
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- **The gauge frame bundle of a unit-speed family at rest outside the time
window.**  The bundle's tangential component is then the given one at *every*
time. -/
theorem exists_gaugeFrameData_unitSpeed_frozen {xi : ℝ → ℝ → ℝ} {Q t0 t1 : ℝ}
    (hQ : 0 < Q) (ht : t0 ≤ t1) (hxi : ContDiff ℝ (3 : ℕ) (uncurry xi))
    (hxiper : ∀ a, Function.Periodic (xi a) Q)
    (hfrozen : ∀ a x, xi a x = xi (clampT t0 t1 a) x) :
    ∃ D : GaugeFrameData, (∀ a x, D.v a x = 1) ∧ (∀ a x, D.xi a x = xi a x) := by
  obtain ⟨D, hv, hxiD⟩ := exists_gaugeFrameData_unitSpeed hQ ht hxi hxiper
  exact ⟨D, hv, fun a x => by rw [hxiD a x, ← hfrozen a x]⟩

/-! ### The tangential component of a moving frame -/

/-- **The tangential component of a moving frame is as smooth as the velocity
and the frame angle.** -/
theorem contDiff_frameTangential {Rdot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ} {n : ℕ}
    (hR : ContDiff ℝ (n : ℕ) (uncurry Rdot)) (hpsi : ContDiff ℝ (n : ℕ) (uncurry psi)) :
    ContDiff ℝ (n : ℕ) (uncurry (frameTangential Rdot psi)) := by
  have hang : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => ((uncurry psi p : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hpsi
  have hexp : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ => Complex.exp (-(Complex.I * ((uncurry psi p : ℝ) : ℂ)))) :=
    Complex.contDiff_exp.comp ((hang.const_smul Complex.I).neg)
  have hfun : uncurry (frameTangential Rdot psi)
      = ⇑Complex.reCLM ∘ (fun p : ℝ × ℝ =>
          uncurry Rdot p * Complex.exp (-(Complex.I * ((uncurry psi p : ℝ) : ℂ)))) := by
    funext p
    simp only [Function.comp_apply, frameTangential, uncurry, Complex.reCLM_apply, conj_exp_I]
  rw [hfun]
  exact Complex.reCLM.contDiff.comp (hR.mul hexp)

/-- **The tangential component of a moving frame is periodic in the arclength**
as soon as the velocity is and the frame angle turns by `2π` over the period. -/
theorem periodic_frameTangential {Rdot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ} {Q : ℝ}
    (hRper : ∀ a, Function.Periodic (Rdot a) Q)
    (hpsiper : ∀ a x, psi a (x + Q) = psi a x + 2 * Real.pi) (a : ℝ) :
    Function.Periodic (frameTangential Rdot psi a) Q := by
  intro x
  have key : ∀ A : ℂ, Complex.exp (-(Complex.I * (A + 2 * (Real.pi : ℂ))))
      = Complex.exp (-(Complex.I * A)) := by
    intro A
    have h2pi : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    rw [show -(Complex.I * (A + 2 * (Real.pi : ℂ)))
        = -(Complex.I * A) + (-(2 * (Real.pi : ℂ) * Complex.I)) by ring, Complex.exp_add,
      h2pi, mul_one]
  have hexp : Complex.exp (-(Complex.I * ((psi a (x + Q) : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * ((psi a x : ℝ) : ℂ))) := by
    rw [hpsiper a x]
    push_cast
    exact key _
  simp only [frameTangential, conj_exp_I, hRper a x, hexp]

/-- **The gauge frame bundle of the family of rear tracks written in its own
arclength.**

The family has unit speed, and its tangential component `ξ = ⟨Ẏ, e^{iΨ}⟩` is
periodic in the rear arclength `Q` because the velocity is and the rear tangent
angle turns by `2π` over one period.  If moreover the family is at rest outside
a compact window of times, the bundle produced has speed `1` and tangential
component exactly `ξ`, which is what
`GaugePathRearFamily.pathDist_le_of_rear_family` and the front-side reductions
of `RearOwnPathDist.lean` ask of it. -/
theorem exists_gaugeFrameData_frameTangential {Ydot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ}
    {Q t0 t1 : ℝ} (hQ : 0 < Q) (ht : t0 ≤ t1)
    (hY : ContDiff ℝ (3 : ℕ) (uncurry Ydot)) (hpsi : ContDiff ℝ (3 : ℕ) (uncurry psi))
    (hYper : ∀ a, Function.Periodic (Ydot a) Q)
    (hpsiper : ∀ a x, psi a (x + Q) = psi a x + 2 * Real.pi)
    (hfrozen : ∀ a x, Ydot a x = Ydot (clampT t0 t1 a) x)
    (hpsifrozen : ∀ a x, psi a x = psi (clampT t0 t1 a) x) :
    ∃ D : GaugeFrameData, (∀ a x, D.v a x = 1) ∧
      (∀ a x, D.xi a x = frameTangential Ydot psi a x) :=
  exists_gaugeFrameData_unitSpeed_frozen hQ ht (contDiff_frameTangential hY hpsi)
    (periodic_frameTangential hYper hpsiper)
    (fun a x => by simp only [frameTangential, hfrozen a x, hpsifrozen a x])

end RearOwnFrameData
