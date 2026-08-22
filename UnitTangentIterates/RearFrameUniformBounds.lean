import Mathlib
import UnitTangentIterates.UniformFrameBounds
import UnitTangentIterates.RearFrameRegularity

/-!
# The frame data of the family of selected rears is uniformly bounded

`UniformFrameBounds.lean` shows that frame data which is `C³` in the pair,
periodic in the arclength and of nonvanishing speed obeys the bounds required
by the comparison of the path functionals in the normal gauge, uniformly over a
compact window of times.

This file verifies those hypotheses for the frame data of the **family of
selected rears** of `RearFamilyFrame.lean`: the speed

`v(a, x) = cos δ(a, σ x) / cos δ(a₀, σ x)`

and the tangential component of the motion

`ξ(a, x) = ⟨Ḟ(a, σ x), e^{iΨ(a,x)}⟩`,  `Ψ = Θ - δ`,

where `σ` is the inverse of the rear arclength at the reference time.  Both are
`C³` as soon as the front data is (`contDiff_frameSpeed`,
`contDiff_frameTangential_rear`), and both are periodic in the rear arclength
`x` with the rear period `Q`, because the front data is periodic in the front
arclength `s` with the front period `P` — the tangent angle only up to its
`2π` turn, which the exponential does not see — and `σ(x + Q) = σ x + P`
(`periodic_frameSpeed`, `periodic_frameTangential_rear`).

Main result: `exists_gaugeFrameData_rear`, the bundle of frame data and
constants of `UniformFrameBounds.GaugeFrameData` for the family of selected
rears, agreeing with its frame data on the time window; through
`UniformFrameBounds.GaugeFrameData.gauge_functionals_comparison` it carries the
comparison of the path functionals in the normal gauge for that family.
-/

noncomputable section

open Set Function Real Complex

namespace RearFrameUniformBounds

open RearTrack RearFamilyFrame RearFrameRegularity UniformFrameBounds

variable {F Fdot : ℝ → ℝ → ℂ} {Θ δ Θdot w : ℝ → ℝ → ℝ} {σ : ℝ → ℝ} {a0 P Q : ℝ}

/-! ### The change of variable -/

/-- The reparametrization `(a, x) ↦ (a, σ x)`. -/
theorem contDiff_pairSigma {n : ℕ} (hσ : ContDiff ℝ (n : ℕ) σ) :
    ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => (p.1, σ p.2)) :=
  contDiff_fst.prodMk (hσ.comp contDiff_snd)

/-! ### The speed of the family -/

/-- **The speed of the family of selected rears is as smooth as the steering
angle and the change of variable.** -/
theorem contDiff_frameSpeed {n : ℕ} (hδ : ContDiff ℝ (n : ℕ) (uncurry δ))
    (hσ : ContDiff ℝ (n : ℕ) σ) (hcos : ∀ y, Real.cos (δ a0 y) ≠ 0) :
    ContDiff ℝ (n : ℕ) (uncurry (frameSpeed δ σ a0)) := by
  have hg : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => (p.1, σ p.2)) := contDiff_pairSigma hσ
  have hg0 : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => (a0, σ p.2)) :=
    contDiff_const.prodMk (hσ.comp contDiff_snd)
  have hnum : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => Real.cos (δ p.1 (σ p.2))) :=
    Real.contDiff_cos.comp (hδ.comp hg)
  have hden : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => Real.cos (δ a0 (σ p.2))) :=
    Real.contDiff_cos.comp (hδ.comp hg0)
  have := hnum.div hden (fun p => hcos (σ p.2))
  simpa [Function.uncurry, frameSpeed] using this

/-- **The speed of the family is periodic in the rear arclength.** -/
theorem periodic_frameSpeed (hσper : ∀ x, σ (x + Q) = σ x + P)
    (hδper : ∀ a, Function.Periodic (δ a) P) (a : ℝ) :
    Function.Periodic (frameSpeed δ σ a0 a) Q := by
  intro x
  simp only [frameSpeed, hσper x, hδper a (σ x), hδper a0 (σ x)]

/-- The speed never vanishes. -/
theorem frameSpeed_ne_zero (hcos : ∀ a y, Real.cos (δ a y) ≠ 0) (a x : ℝ) :
    frameSpeed δ σ a0 a x ≠ 0 :=
  div_ne_zero (hcos a (σ x)) (hcos a0 (σ x))

/-! ### The tangential component of the motion -/

/-- The tangential component of the motion of the family of selected rears,
written directly in terms of the front velocity: `ξ = ⟨Ḟ, e^{iΨ}⟩`. -/
def rearTangential (Fdot : ℝ → ℝ → ℂ) (Θ δ : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun a x => (Fdot a (σ x)
    * Complex.exp (-(Complex.I * ((Θ a (σ x) - δ a (σ x) : ℝ) : ℂ)))).re

/-- The two descriptions of the tangential component agree. -/
theorem rearTangential_eq (a x : ℝ) :
    frameTangential (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a x
      = rearTangential Fdot Θ δ σ a x := by
  rw [frameTangential_frameRdot, conj_exp_I]
  rfl

/-- **The tangential component of the motion is as smooth as the front data.** -/
theorem contDiff_rearTangential {n : ℕ} (hFdot : ContDiff ℝ (n : ℕ) (uncurry Fdot))
    (hΘ : ContDiff ℝ (n : ℕ) (uncurry Θ)) (hδ : ContDiff ℝ (n : ℕ) (uncurry δ))
    (hσ : ContDiff ℝ (n : ℕ) σ) :
    ContDiff ℝ (n : ℕ) (uncurry (rearTangential Fdot Θ δ σ)) := by
  have hg : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => (p.1, σ p.2)) := contDiff_pairSigma hσ
  have hang : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ => ((Θ p.1 (σ p.2) - δ p.1 (σ p.2) : ℝ) : ℂ)) := by
    have := Complex.ofRealCLM.contDiff.comp ((hΘ.comp hg).sub (hδ.comp hg))
    simpa [Function.uncurry, Function.comp_def] using this
  have hexp : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ => Complex.exp (-(Complex.I * ((Θ p.1 (σ p.2) - δ p.1 (σ p.2) : ℝ) : ℂ)))) :=
    Complex.contDiff_exp.comp ((hang.const_smul Complex.I).neg)
  have hF : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => Fdot p.1 (σ p.2)) := by
    simpa [Function.uncurry] using hFdot.comp hg
  have hfun : uncurry (rearTangential Fdot Θ δ σ)
      = ⇑Complex.reCLM ∘ (fun p : ℝ × ℝ => Fdot p.1 (σ p.2)
          * Complex.exp (-(Complex.I * ((Θ p.1 (σ p.2) - δ p.1 (σ p.2) : ℝ) : ℂ)))) := rfl
  rw [hfun]
  exact Complex.reCLM.contDiff.comp (hF.mul hexp)

/-- The rear tangent angle turns by `2π` over one rear period. -/
theorem frameAngle_shift (hσper : ∀ x, σ (x + Q) = σ x + P)
    (hΘper : ∀ a s, Θ a (s + P) = Θ a s + 2 * Real.pi)
    (hδper : ∀ a, Function.Periodic (δ a) P) (a x : ℝ) :
    (Θ a (σ (x + Q)) - δ a (σ (x + Q)) : ℝ) = (Θ a (σ x) - δ a (σ x)) + 2 * Real.pi := by
  rw [hσper x, hΘper a (σ x), hδper a (σ x)]
  ring

/-- **The tangential component of the motion is periodic in the rear
arclength.**  The `2π` turn of the tangent angle is invisible to the frame. -/
theorem periodic_rearTangential (hσper : ∀ x, σ (x + Q) = σ x + P)
    (hFdotper : ∀ a, Function.Periodic (Fdot a) P)
    (hΘper : ∀ a s, Θ a (s + P) = Θ a s + 2 * Real.pi)
    (hδper : ∀ a, Function.Periodic (δ a) P) (a : ℝ) :
    Function.Periodic (rearTangential Fdot Θ δ σ a) Q := by
  intro x
  have hF : Fdot a (σ (x + Q)) = Fdot a (σ x) := by
    rw [hσper x]; exact hFdotper a (σ x)
  have hang := frameAngle_shift (Q := Q) (P := P) hσper hΘper hδper a x
  have key : ∀ A : ℂ, Complex.exp (-(Complex.I * (A + 2 * (Real.pi : ℂ))))
      = Complex.exp (-(Complex.I * A)) := by
    intro A
    have h2pi : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    rw [show -(Complex.I * (A + 2 * (Real.pi : ℂ)))
        = -(Complex.I * A) + (-(2 * (Real.pi : ℂ) * Complex.I)) by ring, Complex.exp_add,
      h2pi, mul_one]
  have hexp : Complex.exp (-(Complex.I * ((Θ a (σ (x + Q)) - δ a (σ (x + Q)) : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * ((Θ a (σ x) - δ a (σ x) : ℝ) : ℂ))) := by
    rw [hang]
    push_cast
    exact key _
  simp only [rearTangential, hF, hexp]

/-! ### The bundle of frame data for the family of selected rears -/

/-- **The frame data of the family of selected rears obeys the bounds of the
gauge comparison uniformly along a compact path of fronts.**

The hypotheses are all on the *front* data: the front velocity `Ḟ`, the tangent
angle `Θ` and the selected steering angle `δ` are `C³` in the pair, `δ` stays in
the open strip (`cos δ ≠ 0`), the front data is periodic in the front arclength
`P` (the tangent angle up to its `2π` turn), and the inverse `σ` of the rear
arclength at the reference time shifts by `P` over one rear period `Q`.

The bundle produced agrees with the frame data of the family on the time window
`[t₀, t₁]`; through
`UniformFrameBounds.GaugeFrameData.gauge_functionals_comparison` it carries the
comparison of the path functionals in the normal gauge. -/
theorem exists_gaugeFrameData_rear {t0 t1 : ℝ} (hQ : 0 < Q) (ht : t0 ≤ t1)
    (hFdotc : ContDiff ℝ (3 : ℕ) (uncurry Fdot))
    (hΘc : ContDiff ℝ (3 : ℕ) (uncurry Θ))
    (hδc : ContDiff ℝ (3 : ℕ) (uncurry δ))
    (hσc : ContDiff ℝ (3 : ℕ) σ)
    (hcos : ∀ a y, Real.cos (δ a y) ≠ 0)
    (hσper : ∀ x, σ (x + Q) = σ x + P)
    (hFdotper : ∀ a, Function.Periodic (Fdot a) P)
    (hΘper : ∀ a s, Θ a (s + P) = Θ a s + 2 * Real.pi)
    (hδper : ∀ a, Function.Periodic (δ a) P) :
    ∃ D : GaugeFrameData,
      (∀ a ∈ Icc t0 t1, ∀ x,
        D.xi a x = frameTangential (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a x) ∧
      (∀ a ∈ Icc t0 t1, ∀ x, D.v a x = frameSpeed δ σ a0 a x) ∧
      (∀ a, Function.Periodic (D.xi a) Q) ∧ (∀ a, Function.Periodic (D.v a) Q) := by
  obtain ⟨D, hxi, hv, hxiper, hvper⟩ := exists_gaugeFrameData (xi := rearTangential Fdot Θ δ σ)
    (v := frameSpeed δ σ a0) (P := Q) (t0 := t0) (t1 := t1) hQ ht
    (contDiff_rearTangential hFdotc hΘc hδc hσc)
    (contDiff_frameSpeed hδc hσc (fun y => hcos a0 y))
    (periodic_rearTangential (P := P) hσper hFdotper hΘper hδper)
    (periodic_frameSpeed (P := P) hσper hδper)
    (fun a x => frameSpeed_ne_zero hcos a x)
  refine ⟨D, fun a ha x => ?_, hv, hxiper, hvper⟩
  rw [hxi a ha x, rearTangential_eq]

/-! ### The normal velocity of the reference slice -/

/-- The normal component of the motion of the family of selected rears at the
reference time, written in terms of the front data:
`η = ⟨Ḟ, ie^{iΨ}⟩ - (Θ̇ - ẇ)`. -/
def rearNormalSlice (Fdot : ℝ → ℝ → ℂ) (Θ δ Θdot w : ℝ → ℝ → ℝ) (σ : ℝ → ℝ)
    (a0 : ℝ) : ℝ → ℝ :=
  fun x => (Fdot a0 (σ x)
      * Complex.exp (-(Complex.I * ((Θ a0 (σ x) - δ a0 (σ x) : ℝ) : ℂ)))).im
    - (Θdot a0 (σ x) - w a0 (σ x))

/-- The two descriptions of the normal velocity agree. -/
theorem rearNormalSlice_eq (x : ℝ) :
    frameNormal (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a0 x
      = rearNormalSlice Fdot Θ δ Θdot w σ a0 x := by
  rw [frameNormal_frameRdot, conj_exp_I]
  rfl

/-- **The normal velocity of the reference slice is as smooth as the front
data.** -/
theorem contDiff_rearNormalSlice {n : ℕ} (hFdot : ContDiff ℝ (n : ℕ) (Fdot a0))
    (hΘ : ContDiff ℝ (n : ℕ) (Θ a0)) (hδ : ContDiff ℝ (n : ℕ) (δ a0))
    (hΘdot : ContDiff ℝ (n : ℕ) (Θdot a0)) (hw : ContDiff ℝ (n : ℕ) (w a0))
    (hσ : ContDiff ℝ (n : ℕ) σ) :
    ContDiff ℝ (n : ℕ) (rearNormalSlice Fdot Θ δ Θdot w σ a0) := by
  have hang : ContDiff ℝ (n : ℕ)
      (fun x : ℝ => ((Θ a0 (σ x) - δ a0 (σ x) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((hΘ.comp hσ).sub (hδ.comp hσ))
  have hexp : ContDiff ℝ (n : ℕ)
      (fun x : ℝ => Complex.exp (-(Complex.I * ((Θ a0 (σ x) - δ a0 (σ x) : ℝ) : ℂ)))) :=
    Complex.contDiff_exp.comp ((hang.const_smul Complex.I).neg)
  have hprod : ContDiff ℝ (n : ℕ) (fun x : ℝ => (Fdot a0 (σ x)
      * Complex.exp (-(Complex.I * ((Θ a0 (σ x) - δ a0 (σ x) : ℝ) : ℂ)))).im) :=
    Complex.imCLM.contDiff.comp ((hFdot.comp hσ).mul hexp)
  exact hprod.sub ((hΘdot.comp hσ).sub (hw.comp hσ))

/-- **The normal velocity of the reference slice is periodic in the rear
arclength.** -/
theorem periodic_rearNormalSlice (hσper : ∀ x, σ (x + Q) = σ x + P)
    (hFdotper : ∀ a, Function.Periodic (Fdot a) P)
    (hΘper : ∀ a s, Θ a (s + P) = Θ a s + 2 * Real.pi)
    (hδper : ∀ a, Function.Periodic (δ a) P)
    (hΘdotper : ∀ a, Function.Periodic (Θdot a) P)
    (hwper : ∀ a, Function.Periodic (w a) P) :
    Function.Periodic (rearNormalSlice Fdot Θ δ Θdot w σ a0) Q := by
  intro x
  have hF : Fdot a0 (σ (x + Q)) = Fdot a0 (σ x) := by
    rw [hσper x]; exact hFdotper a0 (σ x)
  have hang := frameAngle_shift (Q := Q) (P := P) hσper hΘper hδper a0 x
  have key : ∀ A : ℂ, Complex.exp (-(Complex.I * (A + 2 * (Real.pi : ℂ))))
      = Complex.exp (-(Complex.I * A)) := by
    intro A
    have h2pi : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    rw [show -(Complex.I * (A + 2 * (Real.pi : ℂ)))
        = -(Complex.I * A) + (-(2 * (Real.pi : ℂ) * Complex.I)) by ring, Complex.exp_add,
      h2pi, mul_one]
  have hexp : Complex.exp (-(Complex.I * ((Θ a0 (σ (x + Q)) - δ a0 (σ (x + Q)) : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * ((Θ a0 (σ x) - δ a0 (σ x) : ℝ) : ℂ))) := by
    rw [hang]; push_cast; exact key _
  have hΘdot : Θdot a0 (σ (x + Q)) = Θdot a0 (σ x) := by
    rw [hσper x]; exact hΘdotper a0 (σ x)
  have hw : w a0 (σ (x + Q)) = w a0 (σ x) := by
    rw [hσper x]; exact hwper a0 (σ x)
  simp only [rearNormalSlice, hF, hexp, hΘdot, hw]

/-- **The comparison of the path functionals in the normal gauge, for the
family of selected rears.**  The normal velocity of the reference slice is the
quantity the path metric measures; it is `C²` and periodic because the front
data is, so all the boundedness hypotheses of the comparison are automatic.
The bundle `D` is the one produced by `exists_gaugeFrameData_rear`. -/
theorem gauge_functionals_comparison_rear (D : GaugeFrameData)
    {Phi : ℝ → ℝ → ℝ} {ell : ℝ} (hQ : 0 < Q)
    (hFdot : ContDiff ℝ (2 : ℕ) (Fdot a0)) (hΘ : ContDiff ℝ (2 : ℕ) (Θ a0))
    (hδ : ContDiff ℝ (2 : ℕ) (δ a0)) (hΘdot : ContDiff ℝ (2 : ℕ) (Θdot a0))
    (hw : ContDiff ℝ (2 : ℕ) (w a0)) (hσ : ContDiff ℝ (2 : ℕ) σ)
    (hσper : ∀ x, σ (x + Q) = σ x + P)
    (hFdotper : ∀ a, Function.Periodic (Fdot a) P)
    (hΘper : ∀ a s, Θ a (s + P) = Θ a s + 2 * Real.pi)
    (hδper : ∀ a, Function.Periodic (δ a) P)
    (hΘdotper : ∀ a, Function.Periodic (Θdot a) P)
    (hwper : ∀ a, Function.Periodic (w a) P)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    MarkedTopology.supNorm
        (fun u => rearNormalSlice Fdot Θ δ Θdot w σ a0 (Phi t u))
      ≤ MarkedTopology.supNorm (rearNormalSlice Fdot Θ δ Θdot w σ a0) ∧
    MarkedTopology.supNorm (deriv fun u => rearNormalSlice Fdot Θ δ Θdot w σ a0 (Phi t u))
        ≤ MarkedTopology.supNorm (deriv (rearNormalSlice Fdot Θ δ Θdot w σ a0))
            * (ell * Real.exp (D.rateLip * |t|)) ∧
    MarkedTopology.supNorm
          (deriv (deriv fun u => rearNormalSlice Fdot Θ δ Θdot w σ a0 (Phi t u)))
        ≤ MarkedTopology.supNorm (deriv (deriv (rearNormalSlice Fdot Θ δ Θdot w σ a0)))
              * (ell * Real.exp (D.rateLip * |t|)) ^ 2
          + MarkedTopology.supNorm (deriv (rearNormalSlice Fdot Θ δ Θdot w σ a0))
              * (D.rateBound2 * ell ^ 2 * |t| * Real.exp (2 * D.rateLip * |t|)) ∧
    (∫ u in a..b, |rearNormalSlice Fdot Θ δ Θdot w σ a0 (Phi t u)|)
        ≤ (1 / (ell * Real.exp (-(D.rateLip * |t|))))
            * ∫ x in (Phi t a)..(Phi t b), |rearNormalSlice Fdot Θ δ Θdot w σ a0 x| :=
  D.gauge_functionals_comparison_periodic hQ
    (contDiff_rearNormalSlice hFdot hΘ hδ hΘdot hw hσ)
    (periodic_rearNormalSlice (P := P) hσper hFdotper hΘper hδper hΘdotper hwper)
    hell hPhi0 hPhid hab t

/-- The hypotheses above are satisfiable: the constant path of the unit circle,
with `δ ≡ 0`, `Θ(a, s) = s`, `Ḟ ≡ 0` and `σ` the identity — the rear arclength
of a vanishing steering angle is the front arclength. -/
example : ∃ (Fdot : ℝ → ℝ → ℂ) (Θ δ : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (P Q : ℝ),
    0 < Q ∧ ContDiff ℝ (3 : ℕ) (uncurry Fdot) ∧ ContDiff ℝ (3 : ℕ) (uncurry Θ) ∧
      ContDiff ℝ (3 : ℕ) (uncurry δ) ∧ ContDiff ℝ (3 : ℕ) σ ∧
      (∀ a y, Real.cos (δ a y) ≠ 0) ∧ (∀ x, σ (x + Q) = σ x + P) ∧
      (∀ a, Function.Periodic (Fdot a) P) ∧
      (∀ a s, Θ a (s + P) = Θ a s + 2 * Real.pi) ∧
      (∀ a, Function.Periodic (δ a) P) := by
  refine ⟨fun _ _ => 0, fun _ s => s, fun _ _ => 0, id, 2 * Real.pi, 2 * Real.pi,
    by positivity, contDiff_const, ?_, contDiff_const, contDiff_id, ?_, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · simpa [Function.uncurry] using (contDiff_snd : ContDiff ℝ (3 : ℕ) fun p : ℝ × ℝ => p.2)
  · intro a y; simp

end RearFrameUniformBounds
