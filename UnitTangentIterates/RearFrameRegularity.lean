import Mathlib
import UnitTangentIterates.RearFamilyFrame
import UnitTangentIterates.RearSmoothDependence

/-!
# Regularity of the frame data of the family of selected rears

`UnitTangentIterates/RearFamilyFrame.lean` builds the frame data of the family of
selected rear tracks and proves the inverse Jacobi ODE for its normal velocity,
but it *assumes* the differentiability of that frame data: the existence of the
velocity `Ṙ` of the rear family, and the differentiability of the speed `v`,
the frame angle `Ψ` and the frame components `ξ`, `η`.

This file discharges those hypotheses from the paper's lemma *Smooth dependence
of the selected rear*, that is, from the differentiability of the **front**
data `F`, `Θ` and of the selected steering angle `δ` in the path parameter
(`UnitTangentIterates/RearSmoothDependence.lean`), together with the
differentiability in the arclength of those parameter derivatives.

Main results:

* `frameRdot` — the velocity of the family of selected rears,
  `Ṙ = Ḟ − i(Θ̇ − ẇ) e^{iΨ}`, and `hasDerivAt_rearFamily_param`, which shows it
  really is the parameter derivative of the family;
* `hasDerivAt_frameSpeed_param`, `hasDerivAt_frameAngle_param` — the parameter
  derivatives of the speed and of the frame angle;
* `hasDerivAt_frameTangential_space`, `hasDerivAt_frameNormal_space` — the
  arclength derivatives of the frame components of an arbitrary velocity field,
  in the frame form `ξ' = ⟨Ṙ', τ⟩ + Ψ' η`, `η' = ⟨Ṙ', ν⟩ − Ψ' ξ`;
* `frameTangential_frameRdot`, `frameNormal_frameRdot` — the frame components
  of the rear velocity in terms of the front velocity: `ξ = ⟨Ḟ, τ⟩`,
  `η = ⟨Ḟ, ν⟩ − (Θ̇ − ẇ)`;
* `hasDerivAt_frameTangential_rear`, `hasDerivAt_frameNormal_rear` — their
  arclength derivatives for the family of selected rears.
-/

noncomputable section

open Real Complex

namespace RearFrameRegularity

open RearTrack RearFamilyFrame

/-! ### The velocity of the family of selected rears -/

/-- The velocity of the family of selected rears: `Ṙ = Ḟ − i(Θ̇ − ẇ) e^{iΨ}`,
where `Ḟ`, `Θ̇` are the parameter derivatives of the front and its tangent
angle and `ẇ` is that of the selected steering angle. -/
def frameRdot (Fdot : ℝ → ℝ → ℂ) (Θdot w : ℝ → ℝ → ℝ) (Θ δ : ℝ → ℝ → ℝ)
    (σ : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun a x => Fdot a (σ x) - Complex.I * ((Θdot a (σ x) - w a (σ x) : ℝ) : ℂ)
    * Complex.exp (Complex.I * (frameAngle Θ δ σ a x : ℂ))

variable {F : ℝ → ℝ → ℂ} {Θ δ : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
  {Fdot : ℝ → ℝ → ℂ} {Θdot w : ℝ → ℝ → ℝ}

/-- **The family of selected rears really moves with the velocity
`frameRdot`.**  This is the hypothesis `hRa` of
`RearFamilyFrame.hasDerivAt_frameNormal_jacobi`, discharged from the smooth
dependence of the front data and of the selected steering angle on the path
parameter. -/
theorem hasDerivAt_rearFamily_param
    (hFa : ∀ a s, HasDerivAt (fun a' => F a' s) (Fdot a s) a)
    (hΘa : ∀ a s, HasDerivAt (fun a' => Θ a' s) (Θdot a s) a)
    (hδa : ∀ a s, HasDerivAt (fun a' => δ a' s) (w a s) a) (a x : ℝ) :
    HasDerivAt (fun a' => rearFamily F Θ δ σ a' x)
      (frameRdot Fdot Θdot w Θ δ σ a x) a := by
  have h := RearSmoothDependence.hasDerivAt_rearTrack_param
    (F := F) (Θ := Θ) (delta := δ) (Fdot := Fdot a) (Θdot := Θdot a) (w := w a)
    (a0 := a) (s := σ x) (hFa a (σ x)) (hΘa a (σ x)) (hδa a (σ x))
  exact h.congr_deriv rfl

/-- **The parameter derivative of the speed** of the family in the reference
rear arclength: `v̇ = −tan δ · ẇ` at the reference time. -/
theorem hasDerivAt_frameSpeed_param {a0 : ℝ}
    (hδa : ∀ a s, HasDerivAt (fun a' => δ a' s) (w a s) a) (x : ℝ) :
    HasDerivAt (fun a' => frameSpeed δ σ a0 a' x)
      (-(Real.sin (δ a0 (σ x)) * w a0 (σ x)) / Real.cos (δ a0 (σ x))) a0 := by
  have hc : HasDerivAt (fun a' => Real.cos (δ a' (σ x)))
      (-Real.sin (δ a0 (σ x)) * w a0 (σ x)) a0 := by
    simpa using (Real.hasDerivAt_cos (δ a0 (σ x))).comp a0 (hδa a0 (σ x))
  have := hc.div_const (Real.cos (δ a0 (σ x)))
  refine this.congr_deriv ?_
  ring

/-- **The parameter derivative of the frame angle**: `Ψ̇ = Θ̇ − ẇ`. -/
theorem hasDerivAt_frameAngle_param {a0 : ℝ}
    (hΘa : ∀ a s, HasDerivAt (fun a' => Θ a' s) (Θdot a s) a)
    (hδa : ∀ a s, HasDerivAt (fun a' => δ a' s) (w a s) a) (x : ℝ) :
    HasDerivAt (fun a' => frameAngle Θ δ σ a' x)
      (Θdot a0 (σ x) - w a0 (σ x)) a0 :=
  (hΘa a0 (σ x)).sub (hδa a0 (σ x))

/-! ### The arclength derivatives of the frame components -/

/-- Rewriting the conjugate of the unit tangent. -/
theorem conj_exp_I (t : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ)))
      = Complex.exp (-(Complex.I * (t : ℂ))) := by
  rw [← Complex.exp_conj]
  simp [Complex.conj_I]

/-- The derivative of `x ↦ Ṙ(x) · conj e^{iΨ(x)}`. -/
theorem hasDerivAt_frameProduct {Rdot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ}
    {Rdotx : ℂ} {psix a0 x : ℝ}
    (hR : HasDerivAt (fun x' => Rdot a0 x') Rdotx x)
    (hpsi : HasDerivAt (fun x' => psi a0 x') psix x) :
    HasDerivAt
      (fun x' => Rdot a0 x' * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi a0 x' : ℂ))))
      (Rdotx * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi a0 x : ℂ)))
        + (-(Complex.I * (psix : ℂ)))
          * (Rdot a0 x * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi a0 x : ℂ))))) x := by
  have hfun : (fun x' => Rdot a0 x'
        * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi a0 x' : ℂ))))
      = fun x' => Rdot a0 x' * Complex.exp (-(Complex.I * (psi a0 x' : ℂ))) := by
    funext x'; rw [conj_exp_I]
  have hpsiC : HasDerivAt (fun x' => ((psi a0 x' : ℝ) : ℂ)) ((psix : ℝ) : ℂ) x :=
    hpsi.ofReal_comp
  have hE : HasDerivAt (fun x' => Complex.exp (-(Complex.I * (psi a0 x' : ℂ))))
      ((-(Complex.I * (psix : ℂ))) * Complex.exp (-(Complex.I * (psi a0 x : ℂ)))) x := by
    have := ((hpsiC.const_mul Complex.I).neg).cexp
    simpa [mul_comm] using this
  have hg := hR.mul hE
  rw [hfun]
  refine hg.congr_deriv ?_
  rw [conj_exp_I]
  ring

/-- **The arclength derivative of the tangential component** of a velocity
field in the moving frame: `ξ' = ⟨Ṙ', τ⟩ + Ψ' η`. -/
theorem hasDerivAt_frameTangential_space {Rdot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ}
    {Rdotx : ℂ} {psix a0 x : ℝ}
    (hR : HasDerivAt (fun x' => Rdot a0 x') Rdotx x)
    (hpsi : HasDerivAt (fun x' => psi a0 x') psix x) :
    HasDerivAt (fun x' => frameTangential Rdot psi a0 x')
      ((Rdotx * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi a0 x : ℂ)))).re
        + psix * frameNormal Rdot psi a0 x) x := by
  have hg := hasDerivAt_frameProduct hR hpsi
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hg
  refine hre.congr_deriv ?_
  simp [frameNormal, Complex.add_re, Complex.mul_re, Complex.mul_im]

/-- **The arclength derivative of the normal component** of a velocity field in
the moving frame: `η' = ⟨Ṙ', ν⟩ − Ψ' ξ`. -/
theorem hasDerivAt_frameNormal_space {Rdot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ}
    {Rdotx : ℂ} {psix a0 x : ℝ}
    (hR : HasDerivAt (fun x' => Rdot a0 x') Rdotx x)
    (hpsi : HasDerivAt (fun x' => psi a0 x') psix x) :
    HasDerivAt (fun x' => frameNormal Rdot psi a0 x')
      ((Rdotx * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi a0 x : ℂ)))).im
        - psix * frameTangential Rdot psi a0 x) x := by
  have hg := hasDerivAt_frameProduct hR hpsi
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hg
  refine him.congr_deriv ?_
  simp [frameTangential, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

/-! ### The frame components of the rear velocity -/

/-- The tangential component of the rear velocity is that of the **front**
velocity: the correction `−i(Θ̇ − ẇ)e^{iΨ}` is purely normal. -/
theorem frameTangential_frameRdot (a x : ℝ) :
    frameTangential (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a x
      = (Fdot a (σ x)
          * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a x : ℂ)))).re := by
  set psi := frameAngle Θ δ σ a x with hpsi
  set E := Complex.exp (Complex.I * (psi : ℂ)) with hE
  set c : ℝ := Θdot a (σ x) - w a (σ x) with hc
  have hEE : E * (starRingEnd ℂ) E = 1 := RearSmoothDependence.exp_mul_conj psi
  have hsplit : (Fdot a (σ x) - Complex.I * (c : ℂ) * E) * (starRingEnd ℂ) E
      = Fdot a (σ x) * (starRingEnd ℂ) E - Complex.I * (c : ℂ) * (E * (starRingEnd ℂ) E) := by
    ring
  simp only [frameTangential, frameRdot, ← hpsi, ← hE, ← hc, hsplit, hEE, mul_one]
  simp [Complex.sub_re]

/-- The normal component of the rear velocity is that of the front velocity,
corrected by the rotation rate `Θ̇ − ẇ` of the rear tangent. -/
theorem frameNormal_frameRdot (a x : ℝ) :
    frameNormal (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a x
      = (Fdot a (σ x)
          * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a x : ℂ)))).im
        - (Θdot a (σ x) - w a (σ x)) := by
  set psi := frameAngle Θ δ σ a x with hpsi
  set E := Complex.exp (Complex.I * (psi : ℂ)) with hE
  set c : ℝ := Θdot a (σ x) - w a (σ x) with hc
  have hEE : E * (starRingEnd ℂ) E = 1 := RearSmoothDependence.exp_mul_conj psi
  have hsplit : (Fdot a (σ x) - Complex.I * (c : ℂ) * E) * (starRingEnd ℂ) E
      = Fdot a (σ x) * (starRingEnd ℂ) E - Complex.I * (c : ℂ) * (E * (starRingEnd ℂ) E) := by
    ring
  simp only [frameNormal, frameRdot, ← hpsi, ← hE, ← hc, hsplit, hEE, mul_one]
  simp [Complex.sub_im]

/-! ### The arclength derivatives of the frame components of the rear family -/

variable {K : ℝ → ℝ → ℝ} {Fdots : ℝ → ℂ} {Θdots ws : ℝ → ℝ} {a0 : ℝ}

/-- The front velocity, read in the reference rear arclength, is
differentiable, with derivative `Ḟ_s · sec δ`. -/
theorem hasDerivAt_frontVelocity_rearArclength
    (hσ : ∀ x, HasDerivAt σ (1 / Real.cos (δ a0 (σ x))) x)
    (hFdots : ∀ s, HasDerivAt (Fdot a0) (Fdots s) s) (x : ℝ) :
    HasDerivAt (fun x' => Fdot a0 (σ x'))
      (((1 / Real.cos (δ a0 (σ x)) : ℝ) : ℂ) * Fdots (σ x)) x := by
  have h := (hFdots (σ x)).scomp x (hσ x)
  refine h.congr_deriv ?_
  simp [Complex.real_smul]

/-- **The arclength derivative of the tangential component of the rear
velocity.**  This is the hypothesis `hxi` of
`RearFamilyFrame.hasDerivAt_frameNormal_jacobi`, discharged from the
differentiability of the front velocity in the front arclength. -/
theorem hasDerivAt_frameTangential_rear
    (hΘ : ∀ a s, HasDerivAt (Θ a) (K a s) s)
    (hδ : ∀ a s, HasDerivAt (δ a) (K a s - Real.sin (δ a s)) s)
    (hσ : ∀ x, HasDerivAt σ (1 / Real.cos (δ a0 (σ x))) x)
    (hFdots : ∀ s, HasDerivAt (Fdot a0) (Fdots s) s) (x : ℝ) :
    HasDerivAt
      (fun x' => frameTangential (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a0 x')
      (((((1 / Real.cos (δ a0 (σ x)) : ℝ) : ℂ) * Fdots (σ x))
            * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a0 x : ℂ)))).re
        + Real.tan (δ a0 (σ x))
          * (Fdot a0 (σ x)
              * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a0 x : ℂ)))).im) x := by
  have hV := hasDerivAt_frontVelocity_rearArclength (δ := δ) (Fdot := Fdot) hσ hFdots x
  have hpsi := hasDerivAt_frameAngle_space (Θ := Θ) (δ := δ) (K := K) (σ := σ) hΘ hδ hσ x
  have h := hasDerivAt_frameTangential_space (Rdot := fun a y => Fdot a (σ y))
    (psi := frameAngle Θ δ σ) hV hpsi
  have hfun : (fun x' => frameTangential (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a0 x')
      = fun x' => frameTangential (fun a y => Fdot a (σ y)) (frameAngle Θ δ σ) a0 x' := by
    funext x'
    rw [frameTangential_frameRdot]
    rfl
  rw [hfun]
  exact h.congr_deriv rfl

/-- **The arclength derivative of the normal component of the rear velocity.**
This is the hypothesis `heta` of
`RearFamilyFrame.hasDerivAt_frameNormal_jacobi`, discharged from the
differentiability of the front velocity, of the rotation rate of the front
tangent and of the parameter derivative of the steering angle. -/
theorem hasDerivAt_frameNormal_rear
    (hΘ : ∀ a s, HasDerivAt (Θ a) (K a s) s)
    (hδ : ∀ a s, HasDerivAt (δ a) (K a s - Real.sin (δ a s)) s)
    (hσ : ∀ x, HasDerivAt σ (1 / Real.cos (δ a0 (σ x))) x)
    (hFdots : ∀ s, HasDerivAt (Fdot a0) (Fdots s) s)
    (hΘdots : ∀ s, HasDerivAt (Θdot a0) (Θdots s) s)
    (hws : ∀ s, HasDerivAt (w a0) (ws s) s) (x : ℝ) :
    HasDerivAt
      (fun x' => frameNormal (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a0 x')
      (((((1 / Real.cos (δ a0 (σ x)) : ℝ) : ℂ) * Fdots (σ x))
            * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a0 x : ℂ)))).im
        - Real.tan (δ a0 (σ x))
          * (Fdot a0 (σ x)
              * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a0 x : ℂ)))).re
        - (Θdots (σ x) - ws (σ x)) * (1 / Real.cos (δ a0 (σ x)))) x := by
  have hV := hasDerivAt_frontVelocity_rearArclength (δ := δ) (Fdot := Fdot) hσ hFdots x
  have hpsi := hasDerivAt_frameAngle_space (Θ := Θ) (δ := δ) (K := K) (σ := σ) hΘ hδ hσ x
  have h := hasDerivAt_frameNormal_space (Rdot := fun a y => Fdot a (σ y))
    (psi := frameAngle Θ δ σ) hV hpsi
  have hc : HasDerivAt (fun x' => Θdot a0 (σ x') - w a0 (σ x'))
      ((Θdots (σ x) - ws (σ x)) * (1 / Real.cos (δ a0 (σ x)))) x := by
    have h1 := (hΘdots (σ x)).comp x (hσ x)
    have h2 := (hws (σ x)).comp x (hσ x)
    have := h1.sub h2
    refine this.congr_deriv ?_
    ring
  have hsub := h.sub hc
  have hfun : (fun x' => frameNormal (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a0 x')
      = fun x' => frameNormal (fun a y => Fdot a (σ y)) (frameAngle Θ δ σ) a0 x'
          - (Θdot a0 (σ x') - w a0 (σ x')) := by
    funext x'
    rw [frameNormal_frameRdot]
    rfl
  rw [hfun]
  refine hsub.congr_deriv ?_
  simp only [frameTangential]

/-! ### Joint regularity of the reparametrized family of rears -/

/-- **The inverse of the rear arclength is one derivative smoother than the
steering angle.**  If `δ(a₀, ·) ∈ Cⁿ` and `σ' = sec δ(a₀, σ)`, then
`σ ∈ Cⁿ⁺¹`. -/
theorem contDiff_sigma_succ {δ0 σ' : ℝ → ℝ} :
    ∀ n : ℕ, ContDiff ℝ (n : ℕ) δ0 → (∀ y, Real.cos (δ0 y) ≠ 0) →
      (∀ x, HasDerivAt σ' (1 / Real.cos (δ0 (σ' x))) x) → ContDiff ℝ ((n : ℕ) + 1) σ' := by
  intro n
  induction n with
  | zero =>
    intro hδ hcos hd
    have hdiff : Differentiable ℝ σ' := fun x => (hd x).differentiableAt
    have hderivEq : deriv σ' = fun x => 1 / Real.cos (δ0 (σ' x)) := by
      funext x; exact (hd x).deriv
    have hcont : Continuous fun x => 1 / Real.cos (δ0 (σ' x)) := by
      have hδc : Continuous δ0 := by simpa using hδ.continuous
      exact (continuous_const.div ((Real.continuous_cos.comp hδc).comp hdiff.continuous)
        (fun x => hcos (σ' x)))
    have : ContDiff ℝ ((0 : ℕ) + 1) σ' := by
      refine contDiff_succ_iff_deriv.mpr ⟨hdiff, by simp, ?_⟩
      rw [hderivEq]
      simpa using hcont
    exact this
  | succ n ih =>
    intro hδ hcos hd
    have hδn : ContDiff ℝ (n : ℕ) δ0 := hδ.of_le (by exact_mod_cast Nat.le_succ n)
    have hσn : ContDiff ℝ ((n : ℕ) + 1) σ' := ih hδn hcos hd
    have hdiff : Differentiable ℝ σ' := fun x => (hd x).differentiableAt
    have hderivEq : deriv σ' = fun x => 1 / Real.cos (δ0 (σ' x)) := by
      funext x; exact (hd x).deriv
    have hcomp : ContDiff ℝ ((n : ℕ) + 1) (fun x => Real.cos (δ0 (σ' x))) :=
      Real.contDiff_cos.comp (hδ.comp hσn)
    have hinv : ContDiff ℝ ((n : ℕ) + 1) (fun x => 1 / Real.cos (δ0 (σ' x))) := by
      simpa [one_div] using hcomp.inv (fun x => hcos (σ' x))
    have : ContDiff ℝ (((n : ℕ) + 1) + 1) σ' := by
      refine contDiff_succ_iff_deriv.mpr ⟨hdiff, by simp, ?_⟩
      rw [hderivEq]
      exact hinv
    exact_mod_cast this

/-- **Joint regularity of the reparametrized family of rears.**  The rear
tracks `R(a,x) = F(a, σ x) - e^{i(Θ - δ)(a, σ x)}` are as smooth in the pair as
the front data, the steering angle and the change of variable are. -/
theorem contDiff_rearFamily {n : ℕ}
    (hF : ContDiff ℝ (n : ℕ) (Function.uncurry F))
    (hΘ : ContDiff ℝ (n : ℕ) (Function.uncurry Θ))
    (hδ : ContDiff ℝ (n : ℕ) (Function.uncurry δ))
    (hσ : ContDiff ℝ (n : ℕ) σ) :
    ContDiff ℝ (n : ℕ) (Function.uncurry (rearFamily F Θ δ σ)) := by
  have hg : ContDiff ℝ (n : ℕ) (fun q : ℝ × ℝ => (q.1, σ q.2)) :=
    contDiff_fst.prodMk (hσ.comp contDiff_snd)
  have hfun : Function.uncurry (rearFamily F Θ δ σ)
      = fun q : ℝ × ℝ => Function.uncurry F (q.1, σ q.2)
        - Complex.exp (Complex.I
            * ((Function.uncurry Θ (q.1, σ q.2) - Function.uncurry δ (q.1, σ q.2) : ℝ) : ℂ)) := by
    funext q
    simp [Function.uncurry, rearFamily, rearTrack, rearAngle]
  rw [hfun]
  have hang : ContDiff ℝ (n : ℕ)
      (fun q : ℝ × ℝ =>
        ((Function.uncurry Θ (q.1, σ q.2) - Function.uncurry δ (q.1, σ q.2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((hΘ.comp hg).sub (hδ.comp hg))
  exact (hF.comp hg).sub (Complex.contDiff_exp.comp (hang.const_smul Complex.I))

/-- **The joint `C²` regularity of the rear family from that of the front data.**
This is the hypothesis `hR2` of
`RearFamilyFrame.hasDerivAt_frameNormal_jacobi`, reduced to the joint `C²`
regularity of the front, of its tangent angle and of the selected steering
angle: the change of variable `σ` needs no separate assumption, being one
derivative smoother than the steering angle. -/
theorem contDiff_two_rearFamily
    (hF : ContDiff ℝ (2 : ℕ) (Function.uncurry F))
    (hΘ : ContDiff ℝ (2 : ℕ) (Function.uncurry Θ))
    (hδ : ContDiff ℝ (2 : ℕ) (Function.uncurry δ))
    (hcos : ∀ y, Real.cos (δ a0 y) ≠ 0)
    (hσ : ∀ x, HasDerivAt σ (1 / Real.cos (δ a0 (σ x))) x) :
    ContDiff ℝ (2 : ℕ) (Function.uncurry (rearFamily F Θ δ σ)) := by
  have hslice : ContDiff ℝ (1 : ℕ) (δ a0) := by
    have hmap : ContDiff ℝ (2 : ℕ) (fun x : ℝ => (a0, x)) :=
      contDiff_const.prodMk contDiff_id
    have hle : ((1 : ℕ) : WithTop ℕ∞) ≤ ((2 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)
    have := (hδ.comp hmap).of_le hle
    simpa [Function.uncurry] using this
  have hσ2 : ContDiff ℝ (2 : ℕ) σ := by
    have := contDiff_sigma_succ (δ0 := δ a0) (σ' := σ) 1 hslice hcos hσ
    exact_mod_cast this
  exact contDiff_rearFamily hF hΘ hδ hσ2

/-! ### The inverse Jacobi ODE with the regularity discharged -/

/-- **The inverse Jacobi ODE for the family of selected rears, from smooth
dependence alone.**  This is `RearFamilyFrame.hasDerivAt_frameNormal_jacobi`
with its four regularity hypotheses on the frame data (`hRa`, `hv`, `hpsia`,
`hxi`, `heta`) replaced by the data of the paper's lemma *Smooth dependence of
the selected rear*: the front `F`, its tangent angle `Θ` and the selected
steering angle `δ` are differentiable in the path parameter, and those
parameter derivatives are differentiable in the front arclength.  The joint
`C²` regularity of the family of rears is not assumed either: it is deduced
from the joint `C²` regularity of the front data by
`contDiff_two_rearFamily`. -/
theorem hasDerivAt_frameNormal_jacobi_of_smoothDependence
    (hF : ∀ a s, HasDerivAt (F a) (Complex.exp (Complex.I * (Θ a s : ℂ))) s)
    (hΘ : ∀ a s, HasDerivAt (Θ a) (K a s) s)
    (hδ : ∀ a s, HasDerivAt (δ a) (K a s - Real.sin (δ a s)) s)
    (hσ : ∀ x, HasDerivAt σ (1 / Real.cos (δ a0 (σ x))) x)
    (hcos : ∀ y, Real.cos (δ a0 y) ≠ 0)
    (hFa : ∀ a s, HasDerivAt (fun a' => F a' s) (Fdot a s) a)
    (hΘa : ∀ a s, HasDerivAt (fun a' => Θ a' s) (Θdot a s) a)
    (hδa : ∀ a s, HasDerivAt (fun a' => δ a' s) (w a s) a)
    (hFdots : ∀ s, HasDerivAt (Fdot a0) (Fdots s) s)
    (hΘdots : ∀ s, HasDerivAt (Θdot a0) (Θdots s) s)
    (hws : ∀ s, HasDerivAt (w a0) (ws s) s)
    (hFc2 : ContDiff ℝ (2 : ℕ) (Function.uncurry F))
    (hΘc2 : ContDiff ℝ (2 : ℕ) (Function.uncurry Θ))
    (hδc2 : ContDiff ℝ (2 : ℕ) (Function.uncurry δ)) (x : ℝ) :
    HasDerivAt
      (fun x' => frameNormal (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a0 x')
      (frontNormalVelocityAt Fdot Θ δ a0 (σ x) / Real.cos (δ a0 (σ x))
        - frameNormal (frameRdot Fdot Θdot w Θ δ σ) (frameAngle Θ δ σ) a0 x) x :=
  hasDerivAt_frameNormal_jacobi (K := K)
    (Rdot := frameRdot Fdot Θdot w Θ δ σ) (Fdot := Fdot)
    (vdot := fun x' => -(Real.sin (δ a0 (σ x')) * w a0 (σ x')) / Real.cos (δ a0 (σ x')))
    (psidot := fun x' => Θdot a0 (σ x') - w a0 (σ x'))
    (xix := fun x' =>
      ((((1 / Real.cos (δ a0 (σ x')) : ℝ) : ℂ) * Fdots (σ x'))
            * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a0 x' : ℂ)))).re
        + Real.tan (δ a0 (σ x'))
          * (Fdot a0 (σ x')
              * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a0 x' : ℂ)))).im)
    (etax := fun x' =>
      ((((1 / Real.cos (δ a0 (σ x')) : ℝ) : ℂ) * Fdots (σ x'))
            * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a0 x' : ℂ)))).im
        - Real.tan (δ a0 (σ x'))
          * (Fdot a0 (σ x')
              * (starRingEnd ℂ) (Complex.exp (Complex.I * (frameAngle Θ δ σ a0 x' : ℂ)))).re
        - (Θdots (σ x') - ws (σ x')) * (1 / Real.cos (δ a0 (σ x'))))
    hF hΘ hδ hσ hcos (hasDerivAt_rearFamily_param hFa hΘa hδa) hFa
    (by exact_mod_cast contDiff_two_rearFamily (a0 := a0) hFc2 hΘc2 hδc2 hcos hσ)
    (hasDerivAt_frameSpeed_param hδa)
    (hasDerivAt_frameAngle_param hΘa hδa)
    (hasDerivAt_frameTangential_rear hΘ hδ hσ hFdots)
    (hasDerivAt_frameNormal_rear hΘ hδ hσ hFdots hΘdots hws) x

end RearFrameRegularity
