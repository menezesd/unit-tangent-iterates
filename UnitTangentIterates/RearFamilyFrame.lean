import Mathlib
import UnitTangentIterates.GeneralVariation

/-!
# The frame data of a family of selected rears

`UnitTangentIterates/GeneralVariation.lean` proves the transport identity, and hence
the inverse Jacobi ODE, for a `C²` family of rears `R(a,x)` which

* is parametrized at the reference time by its own arclength, and
* moves with an arbitrary velocity `(ξ + iη) e^{iΨ}`.

This file produces exactly such a family from the data the paper actually
supplies: a family of fronts `F(a, s)` in front arclength, with tangent angles
`Θ(a, s)` and selected steering angles `δ(a, s)` solving `δ_s = K - sin δ`.
The rear tracks `R̃(a,s) = F(a,s) - e^{iΨ(a,s)}`, `Ψ = Θ - δ`, of
`RearTrack.lean` are parametrized by the *front* arclength; composing with the
inverse `σ` of the rear arclength **at the reference time** — a single
reparametrization, the same for every `a` — turns them into a family
parametrized by the reference rear arclength, without imposing any gauge on
the motion.

* `rearFamily`, `frameAngle`, `frameSpeed`, `frameTangential`, `frameNormal` —
  the frame data;
* `hasDerivAt_rearFamily_space`, `frameSpeed_reference`,
  `hasDerivAt_frameAngle_space` — the space derivatives: `∂_x R = v e^{iΨ}`,
  `v(a₀, ·) = 1`, `∂_xΨ = tan δ` at the reference time;
* `hasDerivAt_rearFamily_time` — the time derivative in the moving frame,
  `∂_a R = (ξ + iη) e^{iΨ}`;
* `hasDerivAt_frameNormal_jacobi` — the inverse Jacobi ODE
  `η' = sec δ · η_F ∘ σ - η` for the normal component `η` of the motion of the
  selected rears.
-/

noncomputable section

open Real Complex

namespace RearFamilyFrame

open RearTrack GeneralVariation SelectedInverseJacobiODE

/-! ### The frame data -/

/-- The family of rear tracks, reparametrized by the rear arclength at the
reference time (`σ` is the inverse of that arclength). -/
def rearFamily (F : ℝ → ℝ → ℂ) (Θ δ : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun a x => rearTrack (F a) (Θ a) (δ a) (σ x)

/-- The rear tangent angle of the family. -/
def frameAngle (Θ δ : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun a x => rearAngle (Θ a) (δ a) (σ x)

/-- The speed of the family in the reference rear arclength:
`v = cos δ(a, σ x) / cos δ(a₀, σ x)`. -/
def frameSpeed (δ : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (a0 : ℝ) : ℝ → ℝ → ℝ :=
  fun a x => Real.cos (δ a (σ x)) / Real.cos (δ a0 (σ x))

/-- The tangential component of the motion of the family. -/
def frameTangential (Rdot : ℝ → ℝ → ℂ) (psi : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun a x => (Rdot a x * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi a x : ℂ)))).re

/-- The normal component of the motion of the family: the quantity the path
metric measures. -/
def frameNormal (Rdot : ℝ → ℝ → ℂ) (psi : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun a x => (Rdot a x * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi a x : ℂ)))).im

/-- **Frame decomposition of a vector.**  Every vector is
`(ξ + iη) e^{iΨ}` with `ξ, η` its components in the moving frame. -/
theorem frame_decomposition (z : ℂ) (psi : ℝ) :
    (((z * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))).re : ℝ) : ℂ)
        + Complex.I
          * (((z * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))).im : ℝ) : ℂ)
      = z * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))) := by
  simpa [mul_comm] using
    Complex.re_add_im (z * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))))

/-- The frame components reconstruct the vector: `(ξ + iη) e^{iΨ} = z`. -/
theorem frame_reconstruct (z : ℂ) (psi : ℝ) :
    ((((z * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))).re : ℝ) : ℂ)
        + Complex.I
          * (((z * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))).im : ℝ) : ℂ))
      * Complex.exp (Complex.I * (psi : ℂ)) = z := by
  rw [frame_decomposition]
  have hEE : Complex.exp (Complex.I * (psi : ℂ))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))) = 1 :=
    RearSmoothDependence.exp_mul_conj psi
  calc z * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))
        * Complex.exp (Complex.I * (psi : ℂ))
      = z * (Complex.exp (Complex.I * (psi : ℂ))
          * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))) := by ring
    _ = z := by rw [hEE, mul_one]

/-! ### The space derivatives -/

variable {F : ℝ → ℝ → ℂ} {Θ δ K : ℝ → ℝ → ℝ} {σ : ℝ → ℝ} {a0 : ℝ}

/-- **The family is regular with unit tangent `e^{iΨ}`**, of speed
`v = cos δ(a, σ x)/cos δ(a₀, σ x)` in the reference rear arclength. -/
theorem hasDerivAt_rearFamily_space
    (hF : ∀ a s, HasDerivAt (F a) (Complex.exp (Complex.I * (Θ a s : ℂ))) s)
    (hΘ : ∀ a s, HasDerivAt (Θ a) (K a s) s)
    (hδ : ∀ a s, HasDerivAt (δ a) (K a s - Real.sin (δ a s)) s)
    (hσ : ∀ x, HasDerivAt σ (1 / Real.cos (δ a0 (σ x))) x) (a x : ℝ) :
    HasDerivAt (fun x' => rearFamily F Θ δ σ a x')
      ((frameSpeed δ σ a0 a x : ℂ)
        * Complex.exp (Complex.I * (frameAngle Θ δ σ a x : ℂ))) x := by
  have hcomp := (hasDerivAt_rearTrack (F := F a) (Θ := Θ a) (δ := δ a) (K := K a)
    (hF a (σ x)) (hΘ a (σ x)) (hδ a (σ x))).scomp x (hσ x)
  refine hcomp.congr_deriv ?_
  simp only [frameSpeed, frameAngle, Complex.real_smul]
  push_cast
  rw [rearAngle]
  ring

/-- At the reference time the parameter is the rear arclength: `v(a₀, ·) = 1`. -/
theorem frameSpeed_reference (hcos : ∀ y, Real.cos (δ a0 y) ≠ 0) (x : ℝ) :
    frameSpeed δ σ a0 a0 x = 1 := by
  simp [frameSpeed, div_self (hcos (σ x))]

/-- **The rear curvature in the reference rear arclength is `tan δ`.** -/
theorem hasDerivAt_frameAngle_space
    (hΘ : ∀ a s, HasDerivAt (Θ a) (K a s) s)
    (hδ : ∀ a s, HasDerivAt (δ a) (K a s - Real.sin (δ a s)) s)
    (hσ : ∀ x, HasDerivAt σ (1 / Real.cos (δ a0 (σ x))) x) (x : ℝ) :
    HasDerivAt (fun x' => frameAngle Θ δ σ a0 x') (Real.tan (δ a0 (σ x))) x := by
  have hcomp := (hasDerivAt_rearAngle (Θ := Θ a0) (δ := δ a0) (K := K a0)
    (hΘ a0 (σ x)) (hδ a0 (σ x))).comp x (hσ x)
  refine hcomp.congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-! ### The time derivative -/

/-- **The motion of the family in the moving frame.**  Whatever the motion of
the rear tracks, it is `(ξ + iη) e^{iΨ}` for the frame components `ξ, η`; no
gauge condition is imposed. -/
theorem hasDerivAt_rearFamily_time {Rdot : ℝ → ℝ → ℂ}
    (hRa : ∀ a x, HasDerivAt (fun a' => rearFamily F Θ δ σ a' x) (Rdot a x) a)
    (a x : ℝ) :
    HasDerivAt (fun a' => rearFamily F Θ δ σ a' x)
      (((frameTangential Rdot (frameAngle Θ δ σ) a x : ℂ)
          + Complex.I * (frameNormal Rdot (frameAngle Θ δ σ) a x : ℂ))
        * Complex.exp (Complex.I * (frameAngle Θ δ σ a x : ℂ))) a := by
  refine (hRa a x).congr_deriv ?_
  simpa [frameTangential, frameNormal] using
    (frame_reconstruct (Rdot a x) (frameAngle Θ δ σ a x)).symm

/-- The front of the family is the unit-tangent transform of the rear
(`𝒯R = F`), so the two move together. -/
theorem hasDerivAt_front_time {Fdot : ℝ → ℝ → ℂ}
    (hFa : ∀ a s, HasDerivAt (fun a' => F a' s) (Fdot a s) a) (a x : ℝ) :
    HasDerivAt (fun a' => rearFamily F Θ δ σ a' x
      + Complex.exp (Complex.I * (frameAngle Θ δ σ a' x : ℂ))) (Fdot a (σ x)) a := by
  have hfun : (fun a' => rearFamily F Θ δ σ a' x
      + Complex.exp (Complex.I * (frameAngle Θ δ σ a' x : ℂ)))
      = fun a' => F a' (σ x) := by
    funext a'
    simpa [rearFamily, frameAngle] using
      unitTangentMap_rearTrack (F := F a') (Θ := Θ a') (δ := δ a') (σ x)
  rw [hfun]
  exact hFa a (σ x)

/-! ### The inverse Jacobi ODE -/

/-- The normal velocity of the front, as a function of the **front**
arclength. -/
def frontNormalVelocityAt (Fdot : ℝ → ℝ → ℂ) (Θ δ : ℝ → ℝ → ℝ) (a0 : ℝ) : ℝ → ℝ :=
  fun s => frontNormalVelocity (Fdot a0 s) (rearAngle (Θ a0) (δ a0) s) (δ a0 s)

/-- **The inverse Jacobi ODE for the family of selected rears.**  Let `F(a,s)`
be a family of unit-speed fronts with tangent angles `Θ(a,s)` and selected
steering angles `δ(a,s)` solving `δ_s = K - sin δ`, and let `σ` invert the rear
arclength at the reference time `a₀`.  If the reparametrized family of rear
tracks is `C²` in the pair and its frame components are differentiable, then
its normal velocity `η` solves

`η' = sec δ · η_F ∘ σ - η`,

the ODE driving the inverse Jacobi estimates — with **no** gauge assumption on
the motion of the rears. -/
theorem hasDerivAt_frameNormal_jacobi {Rdot Fdot : ℝ → ℝ → ℂ}
    {vdot psidot xix etax : ℝ → ℝ}
    (hF : ∀ a s, HasDerivAt (F a) (Complex.exp (Complex.I * (Θ a s : ℂ))) s)
    (hΘ : ∀ a s, HasDerivAt (Θ a) (K a s) s)
    (hδ : ∀ a s, HasDerivAt (δ a) (K a s - Real.sin (δ a s)) s)
    (hσ : ∀ x, HasDerivAt σ (1 / Real.cos (δ a0 (σ x))) x)
    (hcos : ∀ y, Real.cos (δ a0 y) ≠ 0)
    (hRa : ∀ a x, HasDerivAt (fun a' => rearFamily F Θ δ σ a' x) (Rdot a x) a)
    (hFa : ∀ a s, HasDerivAt (fun a' => F a' s) (Fdot a s) a)
    (hR2 : ContDiff ℝ 2 (Function.uncurry (rearFamily F Θ δ σ)))
    (hv : ∀ x, HasDerivAt (fun a' => frameSpeed δ σ a0 a' x) (vdot x) a0)
    (hpsia : ∀ x, HasDerivAt (fun a' => frameAngle Θ δ σ a' x) (psidot x) a0)
    (hxi : ∀ x, HasDerivAt
      (fun x' => frameTangential Rdot (frameAngle Θ δ σ) a0 x') (xix x) x)
    (heta : ∀ x, HasDerivAt
      (fun x' => frameNormal Rdot (frameAngle Θ δ σ) a0 x') (etax x) x)
    (x : ℝ) :
    HasDerivAt (fun x' => frameNormal Rdot (frameAngle Θ δ σ) a0 x')
      (frontNormalVelocityAt Fdot Θ δ a0 (σ x) / Real.cos (δ a0 (σ x))
        - frameNormal Rdot (frameAngle Θ δ σ) a0 x) x :=
  hasDerivAt_etaR_of_general_family_arclength
    (R := rearFamily F Θ δ σ) (v := frameSpeed δ σ a0)
    (xi := frameTangential Rdot (frameAngle Θ δ σ))
    (eta := frameNormal Rdot (frameAngle Θ δ σ)) (psi := frameAngle Θ δ σ)
    (Fdot := fun x' => Fdot a0 (σ x')) (a0 := a0) (vdot := vdot) (psidot := psidot)
    (xix := xix) (etax := etax) (psix := fun x' => Real.tan (δ a0 (σ x')))
    (etaF := frontNormalVelocityAt Fdot Θ δ a0) (sf := σ) (delta := δ a0)
    hR2 (hasDerivAt_rearFamily_space hF hΘ hδ hσ) (hasDerivAt_rearFamily_time hRa)
    (frameSpeed_reference hcos) hv hpsia hxi heta
    (hasDerivAt_frameAngle_space hΘ hδ hσ)
    (fun x' => hasDerivAt_front_time hFa a0 x')
    (fun x' => hcos (σ x')) (fun _ => rfl) (fun _ => rfl) x

/-- The hypotheses of `hasDerivAt_frameNormal_jacobi` are consistent and its
conclusion is not vacuous: the horizontal lines `F(a,s) = s + i a` (unit speed,
tangent angle `0`, steering angle `0`, so `σ = id`) have rear tracks
`R(a,x) = x + i a - 1` moving with normal velocity `η = 1`, and the front normal
velocity is `1` as well, so the ODE reads `0 = 1/cos 0 - 1`. -/
example (x : ℝ) :
    HasDerivAt (fun x' => frameNormal (fun _ _ => Complex.I)
        (frameAngle (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) id) 0 x')
      (frontNormalVelocityAt (fun _ _ => Complex.I) (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) 0
          (id x) / Real.cos 0
        - frameNormal (fun _ _ => Complex.I)
            (frameAngle (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) id) 0 x) x := by
  have hone : ∀ y : ℝ, HasDerivAt (fun y' : ℝ => ((y' : ℝ) : ℂ)) 1 y := fun y => by
    simpa using (hasDerivAt_id y).ofReal_comp
  have hang : frameAngle (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) id = fun _ _ => (0:ℝ) := by
    funext a y; simp [frameAngle, rearAngle]
  have hnormal : frameNormal (fun _ _ => Complex.I)
      (frameAngle (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) id) = fun _ _ => (1:ℝ) := by
    funext a y; simp [frameNormal, hang]
  have htang : frameTangential (fun _ _ => Complex.I)
      (frameAngle (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) id) = fun _ _ => (0:ℝ) := by
    funext a y; simp [frameTangential, hang]
  have hspeed : frameSpeed (fun _ _ => (0:ℝ)) id 0 = fun _ _ => (1:ℝ) := by
    funext a y; simp [frameSpeed]
  have hfam : Function.uncurry
      (rearFamily (fun a s => (s : ℂ) + Complex.I * (a : ℂ)) (fun _ _ => (0:ℝ))
        (fun _ _ => (0:ℝ)) id)
      = fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) + Complex.I * ((p.1 : ℝ) : ℂ) - 1 := by
    funext p; simp [Function.uncurry, rearFamily, rearTrack, rearAngle]
  refine hasDerivAt_frameNormal_jacobi
    (F := fun a s => (s : ℂ) + Complex.I * (a : ℂ)) (Θ := fun _ _ => (0:ℝ))
    (δ := fun _ _ => (0:ℝ)) (K := fun _ _ => (0:ℝ)) (σ := id) (a0 := 0)
    (Rdot := fun _ _ => Complex.I) (Fdot := fun _ _ => Complex.I)
    (vdot := fun _ => 0) (psidot := fun _ => 0) (xix := fun _ => 0) (etax := fun _ => 0)
    ?_ (fun _ s => hasDerivAt_const s (0:ℝ)) (fun _ s => by simpa using hasDerivAt_const s (0:ℝ))
    ?_ (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ x
  · intro a s
    simpa using (hone s).add_const (Complex.I * (a : ℂ))
  · intro y
    simpa using hasDerivAt_id y
  · intro a y
    have h := ((hone a).const_mul Complex.I).const_add ((y : ℝ) : ℂ)
    simpa [rearFamily, rearTrack, rearAngle] using h.sub_const 1
  · intro a s
    simpa using ((hone a).const_mul Complex.I).const_add ((s : ℝ) : ℂ)
  · rw [hfam]
    exact (((Complex.ofRealCLM.contDiff).comp contDiff_snd).add
      (((Complex.ofRealCLM.contDiff).comp contDiff_fst).const_smul Complex.I)).sub
      contDiff_const
  · intro y
    rw [hspeed]
    exact hasDerivAt_const 0 (1:ℝ)
  · intro y
    rw [hang]
    exact hasDerivAt_const 0 (0:ℝ)
  · intro y
    rw [htang]
    exact hasDerivAt_const y (0:ℝ)
  · intro y
    rw [hnormal]
    exact hasDerivAt_const y (1:ℝ)

end RearFamilyFrame
