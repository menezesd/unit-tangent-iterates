import Mathlib
import UnitTangentIterates.RearOwnArclength
import UnitTangentIterates.GaugePathRearFamily

/-!
# The motion of the family of rears in its own arclength

`RearOwnArclength.lean` produces the family `Y(t,x) = R(t, sf(t,x))` of selected
rear tracks, each slice written in its own arclength, and proves that it is
jointly `C¹`, of unit tangent, and closing up with the rear period.  What the
path metric still needs of it is its *motion*: that it be

`∂_t Y = ξ · τ + η · iτ`  with  `∂_x η = sec δ · η_F ∘ sf - η`,

the inverse Jacobi ODE.

Sliding the parameter is a purely tangential motion, so the normal component of
the motion of `Y` is the same as the normal component of the motion of the
family `RearFamilyFrame.rearFamily F Θ δ (sf t)` in which the parametrization is
*frozen* at the time `t`; for that family the inverse Jacobi ODE is
`RearFamilyFrame.hasDerivAt_frameNormal_jacobi`.  This file makes that
comparison and transports the ODE.

* `frameNormal_add_tangential` — a tangential vector does not change the normal
  component;
* `hasDerivAt_rearOwn_time` — the motion of the family, in the moving frame;
* `rearOwn_normal_eq_frozen` — the normal component is that of the frozen
  family;
* `hasDerivAt_rearOwn_normal_jacobi` — **the inverse Jacobi ODE for the normal
  velocity of the family in its own arclength**.
-/

noncomputable section

open Function Set Complex RearTrack ArclengthInverse RearFamilyFrame

namespace RearOwnMotion

variable {F Fdot Gdot : ℝ → ℝ → ℂ} {Θ δ K sf sft : ℝ → ℝ → ℝ}

/-- The rear track family read in the front arclength. -/
def frontParamTrack (F : ℝ → ℝ → ℂ) (Θ δ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun t s => rearTrack (F t) (Θ t) (δ t) s

@[simp] theorem frontParamTrack_apply (t s : ℝ) :
    frontParamTrack F Θ δ t s = rearTrack (F t) (Θ t) (δ t) s := rfl

/-- **A tangential vector does not change the normal component.** -/
theorem frameNormal_add_tangential (z : ℂ) (c psi : ℝ) :
    ((z + (c : ℂ) * Complex.exp (Complex.I * (psi : ℂ)))
        * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))).im
      = (z * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))).im := by
  have hEE : Complex.exp (Complex.I * (psi : ℂ))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))) = 1 :=
    RearSmoothDependence.exp_mul_conj psi
  have h : (z + (c : ℂ) * Complex.exp (Complex.I * (psi : ℂ)))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))
      = z * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))) + (c : ℂ) := by
    rw [add_mul, mul_assoc, hEE, mul_one]
  rw [h]
  simp

/-- **The motion of the family in its own arclength.**  Differentiating along
the moving parameter, the velocity is the velocity of the frozen family plus a
tangential term. -/
theorem hasDerivAt_rearOwn_time
    (hG : ContDiff ℝ (1 : ℕ) (uncurry (frontParamTrack F Θ δ))
      )
    (hGx : ∀ t s, HasDerivAt (frontParamTrack F Θ δ t)
      ((Real.cos (δ t s) : ℂ) * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) s : ℂ))) s)
    (hGt : ∀ t s, HasDerivAt (fun r => frontParamTrack F Θ δ r s) (Gdot t s) t)
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t) (t x : ℝ) :
    HasDerivAt (fun r => RearOwnArclength.rearOwn F Θ δ sf r x)
      (Gdot t (sf t x) + (sft t x) •
        ((Real.cos (δ t (sf t x)) : ℂ)
          * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ)))) t :=
  GaugePathRearFamily.hasDerivAt_along_curve (Y := frontParamTrack F Θ δ)
    (tauY := fun t s => (Real.cos (δ t s) : ℂ)
      * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) s : ℂ)))
    (Yt := Gdot) (phi := fun r => sf r x) hG hGx hGt (hsft t x)

/-- **The motion of the family in the moving frame.**  Whatever the motion of
the family, it is `ξ · τ + η · iτ` for its frame components — the shape a
normal path asks for. -/
theorem hasDerivAt_rearOwn_time_frame {Ydot : ℝ → ℝ → ℂ} {t x : ℝ}
    (hYd : HasDerivAt (fun r => RearOwnArclength.rearOwn F Θ δ sf r x) (Ydot t x) t) :
    HasDerivAt (fun r => RearOwnArclength.rearOwn F Θ δ sf r x)
      ((frameTangential Ydot (RearOwnArclength.rearOwnAngle Θ δ sf) t x : ℂ)
          * RearOwnArclength.rearOwnTangent Θ δ sf t x
        + (frameNormal Ydot (RearOwnArclength.rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * RearOwnArclength.rearOwnTangent Θ δ sf t x)) t := by
  refine hYd.congr_deriv ?_
  have h := frame_reconstruct (Ydot t x) (RearOwnArclength.rearOwnAngle Θ δ sf t x)
  rw [RearOwnArclength.rearOwnTangent]
  rw [← h]
  simp only [frameTangential, frameNormal]
  ring

/-- **The normal component of the motion is that of the frozen family.**  The
sliding of the parameter is tangential, so it does not contribute. -/
theorem rearOwn_normal_eq_frozen (Ydot : ℝ → ℝ → ℂ)
    (hlink : ∀ t x, Ydot t x = Gdot t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ)))) (t x : ℝ) :
    frameNormal Ydot (RearOwnArclength.rearOwnAngle Θ δ sf) t x
      = frameNormal (fun a y => Gdot a (sf t y)) (frameAngle Θ δ (sf t)) t x := by
  have hmul : (sft t x) • ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ)))
      = ((sft t x * Real.cos (δ t (sf t x)) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ)) := by
    push_cast [Complex.real_smul]
    ring
  simp only [frameNormal, RearOwnArclength.rearOwnAngle, frameAngle, hlink t x, hmul]
  exact frameNormal_add_tangential (Gdot t (sf t x))
    (sft t x * Real.cos (δ t (sf t x))) (rearAngle (Θ t) (δ t) (sf t x))

/-- **The inverse Jacobi ODE for the family in its own arclength.**  Let
`F(t,s)` be a path of unit-speed fronts with tangent angles `Θ`, selected
steering angles `δ` solving the steering equation, and let `sf(t, ·)` invert the
rear arclength at the *same* time.  If the frozen families are `C²` and their
frame data are differentiable — the hypotheses of
`RearFamilyFrame.hasDerivAt_frameNormal_jacobi` at every time — then the normal
velocity of the family in its own arclength solves

`∂_x η = sec δ · η_F ∘ sf - η`. -/
theorem hasDerivAt_rearOwn_normal_jacobi {vdot psidot xix etax : ℝ → ℝ → ℝ}
    (Ydot : ℝ → ℝ → ℂ)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hδ : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hGt : ∀ t s, HasDerivAt (fun r => frontParamTrack F Θ δ r s) (Gdot t s) t)
    (hFa : ∀ t s, HasDerivAt (fun r => F r s) (Fdot t s) t)
    (hR2 : ∀ t, ContDiff ℝ 2 (uncurry (rearFamily F Θ δ (sf t))))
    (hv : ∀ t x, HasDerivAt (fun a' => frameSpeed δ (sf t) t a' x) (vdot t x) t)
    (hpsia : ∀ t x, HasDerivAt (fun a' => frameAngle Θ δ (sf t) a' x) (psidot t x) t)
    (hxi : ∀ t x, HasDerivAt
      (fun x' => frameTangential (fun a y => Gdot a (sf t y)) (frameAngle Θ δ (sf t)) t x')
      (xix t x) x)
    (heta : ∀ t x, HasDerivAt
      (fun x' => frameNormal (fun a y => Gdot a (sf t y)) (frameAngle Θ δ (sf t)) t x')
      (etax t x) x)
    (hlink : ∀ t x, Ydot t x = Gdot t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ)))) (t x : ℝ) :
    HasDerivAt (fun x' => frameNormal Ydot (RearOwnArclength.rearOwnAngle Θ δ sf) t x')
      (frontNormalVelocityAt Fdot Θ δ t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (RearOwnArclength.rearOwnAngle Θ δ sf) t x) x := by
  have hfun : (fun x' => frameNormal Ydot (RearOwnArclength.rearOwnAngle Θ δ sf) t x')
      = fun x' => frameNormal (fun a y => Gdot a (sf t y)) (frameAngle Θ δ (sf t)) t x' :=
    funext fun x' => rearOwn_normal_eq_frozen (Gdot := Gdot) (sft := sft) Ydot hlink t x'
  rw [hfun, rearOwn_normal_eq_frozen (Gdot := Gdot) (sft := sft) Ydot hlink t x]
  have hRa : ∀ a y, HasDerivAt (fun a' => rearFamily F Θ δ (sf t) a' y) (Gdot a (sf t y)) a :=
    fun a y => hGt a (sf t y)
  exact hasDerivAt_frameNormal_jacobi (F := F) (Θ := Θ) (δ := δ) (K := K) (σ := sf t) (a0 := t)
    (Rdot := fun a y => Gdot a (sf t y)) (Fdot := Fdot)
    (vdot := vdot t) (psidot := psidot t) (xix := xix t) (etax := etax t)
    hF hΘ hδ (hsf t) (fun y => hcos t y) hRa hFa (hR2 t) (hv t) (hpsia t) (hxi t) (heta t) x

/-! ### The ODE with the regularity of the frozen families discharged -/

/-- The velocity of the rear track family in the front arclength:
`Ṙ = Ḟ − i(Θ̇ − ẇ)e^{iΨ}`. -/
def trackVelocity (Fdot : ℝ → ℝ → ℂ) (Θdot w Θ δ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun t s => Fdot t s - Complex.I * ((Θdot t s - w t s : ℝ) : ℂ)
    * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) s : ℂ))

/-- The velocity of the frozen family is that of the track family, read at the
frozen parameter. -/
theorem frameRdot_eq_trackVelocity {Fdot : ℝ → ℝ → ℂ} {Θdot w : ℝ → ℝ → ℝ} (σ : ℝ → ℝ)
    (a x : ℝ) :
    RearFrameRegularity.frameRdot Fdot Θdot w Θ δ σ a x
      = trackVelocity Fdot Θdot w Θ δ a (σ x) := rfl

/-- **The rear track family really moves with `trackVelocity`**, by the smooth
dependence of the front data on the path parameter. -/
theorem hasDerivAt_frontParamTrack_time {Fdot : ℝ → ℝ → ℂ} {Θdot w : ℝ → ℝ → ℝ}
    (hFa : ∀ t s, HasDerivAt (fun r => F r s) (Fdot t s) t)
    (hΘa : ∀ t s, HasDerivAt (fun r => Θ r s) (Θdot t s) t)
    (hδa : ∀ t s, HasDerivAt (fun r => δ r s) (w t s) t) (t s : ℝ) :
    HasDerivAt (fun r => frontParamTrack F Θ δ r s) (trackVelocity Fdot Θdot w Θ δ t s) t :=
  RearSmoothDependence.hasDerivAt_rearTrack_param (F := F) (Θ := Θ) (delta := δ)
    (Fdot := Fdot t) (Θdot := Θdot t) (w := w t) (a0 := t) (s := s)
    (hFa t s) (hΘa t s) (hδa t s)

/-- **The inverse Jacobi ODE for the family in its own arclength, from smooth
dependence alone.**  Same as `hasDerivAt_rearOwn_normal_jacobi`, with every
hypothesis on the frozen families replaced by the data of the paper's lemma
*Smooth dependence of the selected rear*: the front, its tangent angle and the
selected steering angle are differentiable in the path parameter, those
parameter derivatives are differentiable in the arclength, and the three are
jointly `C²`. -/
theorem hasDerivAt_rearOwn_normal_jacobi_of_smoothDependence
    {Θdot w Θdots ws : ℝ → ℝ → ℝ} {Ydot Fdots : ℝ → ℝ → ℂ}
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hδ : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hFa : ∀ t s, HasDerivAt (fun r => F r s) (Fdot t s) t)
    (hΘa : ∀ t s, HasDerivAt (fun r => Θ r s) (Θdot t s) t)
    (hδa : ∀ t s, HasDerivAt (fun r => δ r s) (w t s) t)
    (hFdots : ∀ t s, HasDerivAt (Fdot t) (Fdots t s) s)
    (hΘdots : ∀ t s, HasDerivAt (Θdot t) (Θdots t s) s)
    (hws : ∀ t s, HasDerivAt (w t) (ws t s) s)
    (hFc2 : ContDiff ℝ (2 : ℕ) (uncurry F))
    (hΘc2 : ContDiff ℝ (2 : ℕ) (uncurry Θ))
    (hδc2 : ContDiff ℝ (2 : ℕ) (uncurry δ))
    (hlink : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ)))) (t x : ℝ) :
    HasDerivAt (fun x' => frameNormal Ydot (RearOwnArclength.rearOwnAngle Θ δ sf) t x')
      (frontNormalVelocityAt Fdot Θ δ t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (RearOwnArclength.rearOwnAngle Θ δ sf) t x) x := by
  have hfun : (fun x' => frameNormal Ydot (RearOwnArclength.rearOwnAngle Θ δ sf) t x')
      = fun x' => frameNormal
          (RearFrameRegularity.frameRdot Fdot Θdot w Θ δ (sf t)) (frameAngle Θ δ (sf t)) t x' :=
    funext fun x' =>
      rearOwn_normal_eq_frozen (Gdot := trackVelocity Fdot Θdot w Θ δ) (sft := sft) Ydot hlink t x'
  rw [hfun, rearOwn_normal_eq_frozen (Gdot := trackVelocity Fdot Θdot w Θ δ) (sft := sft)
    Ydot hlink t x]
  exact RearFrameRegularity.hasDerivAt_frameNormal_jacobi_of_smoothDependence
    (K := K) (σ := sf t) (a0 := t) (Fdot := Fdot) (Θdot := Θdot) (w := w)
    (Fdots := Fdots t) (Θdots := Θdots t) (ws := ws t)
    hF hΘ hδ (hsf t) (fun y => hcos t y) hFa hΘa hδa (hFdots t) (hΘdots t) (hws t)
    hFc2 hΘc2 hδc2 x

end RearOwnMotion
