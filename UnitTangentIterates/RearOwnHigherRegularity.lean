import Mathlib
import UnitTangentIterates.RearOwnPathDistGeometric

/-!
# Higher joint regularity of the data of the selected rears

The path-distance assemblies for the selected rears ask two regularity
hypotheses that are not about the front: the joint `C³` regularity of the
velocity `Ẏ` of the family of rear tracks written in its own arclength, and of
the rear tangent angle `Ψ` of that family.  This file produces both from the
joint regularity of the *front* data alone: if the front `F`, its tangent angle
`Θ` and the selected steering angle `δ` are jointly `C⁴`, then `Ẏ` and `Ψ` are
jointly `C³`.

The chain is:

* a partial derivative of a jointly `C^{n+1}` family is jointly `Cⁿ`
  (`contDiff_partialTime_of_hasDerivAt`);
* the primitive `∫₀ˢ g(t,u) du` of a jointly `Cⁿ` family is jointly `Cⁿ`
  (`contDiff_primitive`) — one further arclength derivative is available, but
  the joint order is not raised, the parameter derivatives of the primitive
  being no better than those of the integrand;
* the family of inverses of a jointly `C^{n+1}` family whose space derivative
  is bounded below is jointly `C^{n+1}` (`contDiff_inverse_family`), by the
  global inverse function theorem;
* hence the change of variable `sf` from the front to the rear arclength is as
  smooth as the steering angle (`contDiff_sf`), and `Ψ` and `Ẏ` follow.
-/

noncomputable section

open Set Function Complex MeasureTheory RearTrack RearOwnArclength RearOwnMotion
  ArclengthInverse

namespace RearOwnHigherRegularity

/-! ### Partial derivatives of a smooth family -/

section Partials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The parameter derivative of a family, as the derivative of the joint map in
the direction `(1,0)`. -/
def partialTime (f : ℝ → ℝ → E) : ℝ → ℝ → E := fun t x => fderiv ℝ (uncurry f) (t, x) (1, 0)

/-- If the joint map is differentiable, `partialTime f` really is the parameter
derivative. -/
theorem hasDerivAt_partialTime {f : ℝ → ℝ → E} (hf : Differentiable ℝ (uncurry f)) (t x : ℝ) :
    HasDerivAt (fun r => f r x) (partialTime f t x) t := by
  have h1 : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (t, x)) (t, x) :=
    (hf (t, x)).hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × ℝ)) (1, 0) t := by
    simpa using ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have h2 := h1.comp_hasDerivAt t hc
  simpa [Function.comp_def, uncurry, partialTime] using h2

/-- The arclength derivative of a family, as the derivative of the joint map in
the direction `(0,1)`. -/
def partialArc (f : ℝ → ℝ → E) : ℝ → ℝ → E := fun t x => fderiv ℝ (uncurry f) (t, x) (0, 1)

/-- Likewise in the second variable. -/
theorem hasDerivAt_partialArc {f : ℝ → ℝ → E} (hf : Differentiable ℝ (uncurry f)) (t x : ℝ) :
    HasDerivAt (f t) (partialArc f t x) x := by
  have h1 : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (t, x)) (t, x) :=
    (hf (t, x)).hasFDerivAt
  have hc : HasDerivAt (fun y : ℝ => ((t, y) : ℝ × ℝ)) (0, 1) x := by
    simpa using ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))
  have h2 := h1.comp_hasDerivAt x hc
  simpa [Function.comp_def, uncurry, partialArc] using h2

/-- **A partial derivative of a jointly `C^{n+1}` family is jointly `Cⁿ`.** -/
theorem contDiff_partialTime_of_hasDerivAt {f fdot : ℝ → ℝ → E} {n : ℕ}
    (hf : ContDiff ℝ ((n + 1 : ℕ)) (uncurry f))
    (hd : ∀ t x, HasDerivAt (fun r => f r x) (fdot t x) t) :
    ContDiff ℝ (n : ℕ) (uncurry fdot) := by
  have hdiff : Differentiable ℝ (uncurry f) := hf.differentiable (by norm_num)
  have heq : uncurry fdot
      = fun p => (ContinuousLinearMap.apply ℝ E ((1, 0) : ℝ × ℝ)) (fderiv ℝ (uncurry f) p) := by
    funext p
    obtain ⟨t, x⟩ := p
    exact (hd t x).unique (hasDerivAt_partialTime hdiff t x)
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ E ((1, 0) : ℝ × ℝ)).contDiff.comp
    (hf.fderiv_right (by push_cast; exact le_refl _))

/-- The same for the arclength derivative. -/
theorem contDiff_partialArc_of_hasDerivAt {f fx : ℝ → ℝ → E} {n : ℕ}
    (hf : ContDiff ℝ ((n + 1 : ℕ)) (uncurry f))
    (hd : ∀ t x, HasDerivAt (f t) (fx t x) x) :
    ContDiff ℝ (n : ℕ) (uncurry fx) := by
  have hdiff : Differentiable ℝ (uncurry f) := hf.differentiable (by norm_num)
  have heq : uncurry fx
      = fun p => (ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ)) (fderiv ℝ (uncurry f) p) := by
    funext p
    obtain ⟨t, x⟩ := p
    exact (hd t x).unique (hasDerivAt_partialArc hdiff t x)
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ)).contDiff.comp
    (hf.fderiv_right (by push_cast; exact le_refl _))

/-- The parameter derivative of a jointly `C^{n+1}` family, as a function of the
pair, is jointly `Cⁿ`. -/
theorem contDiff_partialTime_self {f : ℝ → ℝ → E} {n : ℕ}
    (hf : ContDiff ℝ ((n + 1 : ℕ)) (uncurry f)) : ContDiff ℝ (n : ℕ) (uncurry (partialTime f)) :=
  contDiff_partialTime_of_hasDerivAt hf (hasDerivAt_partialTime (hf.differentiable (by norm_num)))

/-- The same for the arclength derivative. -/
theorem contDiff_partialArc_self {f : ℝ → ℝ → E} {n : ℕ}
    (hf : ContDiff ℝ ((n + 1 : ℕ)) (uncurry f)) : ContDiff ℝ (n : ℕ) (uncurry (partialArc f)) :=
  contDiff_partialArc_of_hasDerivAt hf (hasDerivAt_partialArc (hf.differentiable (by norm_num)))

end Partials

/-! ### The primitive of a smooth family -/

/-- **The primitive of a jointly `Cⁿ` family is jointly `Cⁿ`.**  Its arclength
derivative is the integrand, so it is one derivative smoother in the arclength;
the joint order is not raised, the parameter derivative of the primitive being
the primitive of the parameter derivative. -/
theorem contDiff_primitive :
    ∀ (n : ℕ) (g : ℝ → ℝ → ℝ), ContDiff ℝ (n : ℕ) (uncurry g) →
      ContDiff ℝ (n : ℕ) (uncurry fun t s => ∫ u in (0:ℝ)..s, g t u) := by
  intro n
  induction n with
  | zero =>
    intro g hg
    have hgc : Continuous (uncurry g) := by simpa using hg.continuous
    have hcont : Continuous (uncurry fun t s => ∫ u in (0:ℝ)..s, g t u) := by
      simpa using
        intervalIntegral.continuous_parametric_primitive_of_continuous (f := g) (a₀ := 0) hgc
    simpa using (contDiff_zero (𝕜 := ℝ)
      (f := uncurry fun t s => ∫ u in (0:ℝ)..s, g t u)).mpr hcont
  | succ n ih =>
    intro g hg
    have hgc : Continuous (uncurry g) := hg.continuous
    have hgdiff : Differentiable ℝ (uncurry g) := hg.differentiable (by norm_num)
    have hgt : ContDiff ℝ (n : ℕ) (uncurry (partialTime g)) :=
      contDiff_partialTime_of_hasDerivAt hg (hasDerivAt_partialTime hgdiff)
    have hgtc : Continuous (uncurry (partialTime g)) := hgt.continuous
    have hP1 : ∀ t s, HasDerivAt (fun r => ∫ u in (0:ℝ)..s, g r u)
        ((fun t s => ∫ u in (0:ℝ)..s, partialTime g t u) t s) t := fun t s =>
      ParametricPrimitive.hasDerivAt_primitive_param hgc (hasDerivAt_partialTime hgdiff) hgtc t s
    have hP2 : ∀ t s, HasDerivAt (fun s' => ∫ u in (0:ℝ)..s', g t u) (g t s) s := fun t s =>
      ParametricPrimitive.hasDerivAt_primitive_space hgc t s
    have hgn : ContDiff ℝ (n : ℕ) (uncurry g) := hg.of_le (by exact_mod_cast Nat.le_succ n)
    exact RearOwnTangential.contDiff_succ_of_partials hP1 hP2 (ih _ hgt) hgn

/-! ### A family of inverses -/

variable {A a sf : ℝ → ℝ → ℝ} {c : ℝ}

/-- **The family of inverses of a jointly `C^{n+1}` family is jointly
`C^{n+1}`.**  Global inverse function theorem for the shear
`(t,s) ↦ (t, A t s)`, invertible because `∂_s A ≥ c > 0`. -/
theorem contDiff_inverse_family {n : ℕ} (hc : 0 < c)
    (hAC : ContDiff ℝ ((n + 1 : ℕ)) (uncurry A))
    (hAs : ∀ t s, HasDerivAt (A t) (a t s) s)
    (hca : ∀ t s, c ≤ a t s) (hsf : ∀ t x, A t (sf t x) = x) :
    ContDiff ℝ ((n + 1 : ℕ)) (uncurry sf) := by
  set f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, A p.1 p.2) with hfdef
  set g : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, sf q.1 q.2) with hgdef
  have hane : ∀ t s, a t s ≠ 0 := fun t s => ne_of_gt (lt_of_lt_of_le hc (hca t s))
  have hAdiff : Differentiable ℝ (uncurry A) := hAC.differentiable (by norm_num)
  have hfC : ContDiff ℝ ((n + 1 : ℕ)) f := contDiff_fst.prodMk hAC
  have hf' : ∀ p : ℝ × ℝ, ∃ e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasFDerivAt f (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    rintro ⟨t, s⟩
    refine ⟨GlobalInverseSmooth.shearEquiv (partialTime A t s) (a t s) (hane t s), ?_⟩
    have hA : HasFDerivAt (uncurry A) (fderiv ℝ (uncurry A) (t, s)) (t, s) :=
      (hAdiff (t, s)).hasFDerivAt
    have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((t, s) : ℝ × ℝ))).prodMk hA
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    have hsplit : ((u, v) : ℝ × ℝ) = u • ((1, 0) : ℝ × ℝ) + v • ((0, 1) : ℝ × ℝ) := by
      simp
    have hL : (fderiv ℝ (uncurry A) (t, s)) (u, v)
        = u * partialTime A t s + v * a t s := by
      have hx : (fderiv ℝ (uncurry A) (t, s)) (0, 1) = a t s :=
        (hasDerivAt_partialArc hAdiff t s).unique (hAs t s) ▸ rfl
      rw [hsplit, map_add, map_smul, map_smul, hx]
      simp [partialTime, smul_eq_mul]
    apply Prod.ext
    · simp
    · simpa [GlobalInverseSmooth.shearEquiv, ContinuousLinearEquiv.equivOfInverse,
        JointC1.partialCLM_apply, smul_eq_mul, mul_comm] using hL
  have hgf : ∀ p, g (f p) = p := by
    rintro ⟨t, s⟩
    simp only [hfdef, hgdef]
    rw [GlobalInverseSmooth.leftInverse_slice hc hAs hca hsf t s]
  have hfg : ∀ q, f (g q) = q := by
    rintro ⟨t, x⟩
    simp only [hfdef, hgdef]
    rw [hsf t x]
  have hgC : ContDiff ℝ ((n + 1 : ℕ)) g :=
    GlobalInverseSmooth.contDiff_of_globalInverse hfC (by positivity) hf' hgf hfg
  have huc : uncurry sf = fun q : ℝ × ℝ => (g q).2 := rfl
  rw [huc]
  exact contDiff_snd.comp hgC

/-! ### The change of variable and the frame data of the selected rears -/

variable {δ Θ : ℝ → ℝ → ℝ} {kh : ℝ}

/-- The rear arclength of a family of steering angles, as a function of the
pair, is as smooth as the steering angle. -/
theorem contDiff_rearArclengthFamily {n : ℕ} (hδ : ContDiff ℝ (n : ℕ) (uncurry δ)) :
    ContDiff ℝ (n : ℕ) (uncurry fun t s => rearArclength (δ t) s) := by
  have hcos : ContDiff ℝ (n : ℕ) (uncurry fun t s => Real.cos (δ t s)) :=
    Real.contDiff_cos.comp hδ
  simpa [rearArclength] using contDiff_primitive n (fun t s => Real.cos (δ t s)) hcos

/-- **The change of variable from the front to the rear arclength is as smooth
as the steering angle.** -/
theorem contDiff_sf {n : ℕ} {sf : ℝ → ℝ → ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hδ : ContDiff ℝ ((n + 1 : ℕ)) (uncurry δ))
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x) :
    ContDiff ℝ ((n + 1 : ℕ)) (uncurry sf) := by
  have hδc : Continuous (uncurry δ) := hδ.continuous
  have hA : ContDiff ℝ ((n + 1 : ℕ)) (uncurry fun t s => rearArclength (δ t) s) :=
    contDiff_rearArclengthFamily hδ
  have hAs : ∀ t s, HasDerivAt (fun s' => rearArclength (δ t) s')
      ((fun t s => Real.cos (δ t s)) t s) s := fun t s =>
    SelectedChangeOfVariable.hasDerivAt_rearArclength_space hδc t s
  have hpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hca : ∀ t s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (δ t s) := fun t s =>
    (RearOwnTangential.strip_bounds hkh0 hkh1 (hstrip0 t s) (hstrip1 t s)).2.1
  exact contDiff_inverse_family hpos hA hAs hca hsfinv

/-- **The rear tangent angle of the family written in its own arclength is as
smooth as the front data.** -/
theorem contDiff_rearOwnAngle {n : ℕ} {sf : ℝ → ℝ → ℝ}
    (hΘ : ContDiff ℝ (n : ℕ) (uncurry Θ)) (hδ : ContDiff ℝ (n : ℕ) (uncurry δ))
    (hsf : ContDiff ℝ (n : ℕ) (uncurry sf)) :
    ContDiff ℝ (n : ℕ) (uncurry (rearOwnAngle Θ δ sf)) := by
  have hcomp : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => (p.1, uncurry sf p)) :=
    contDiff_fst.prodMk hsf
  have hfun : uncurry (rearOwnAngle Θ δ sf)
      = fun p : ℝ × ℝ => uncurry Θ (p.1, uncurry sf p) - uncurry δ (p.1, uncurry sf p) := by
    funext p; simp [uncurry, rearOwnAngle, rearAngle]
  rw [hfun]
  exact (hΘ.comp hcomp).sub (hδ.comp hcomp)

/-- **The front normal velocity is as smooth as the front data.**  It is
`⟨Ḟ, i e^{iΘ}⟩`, so it depends only on the velocity of the front and on its
tangent angle. -/
theorem contDiff_frontNormalVelocityAt {n : ℕ} {Fdot : ℝ → ℝ → ℂ}
    (hFdot : ContDiff ℝ (n : ℕ) (uncurry Fdot)) (hΘ : ContDiff ℝ (n : ℕ) (uncurry Θ)) :
    ContDiff ℝ (n : ℕ) (uncurry (RearFamilyFrame.frontNormalVelocityAt Fdot Θ δ)) := by
  have hfun : uncurry (RearFamilyFrame.frontNormalVelocityAt Fdot Θ δ)
      = fun p : ℝ × ℝ => (uncurry Fdot p *
        (starRingEnd ℂ) (Complex.I * Complex.exp (Complex.I * ((uncurry Θ p : ℝ) : ℂ)))).re := by
    funext p
    simp [uncurry, RearFamilyFrame.frontNormalVelocityAt,
      SelectedInverseJacobiODE.frontNormalVelocity, rearAngle]
  rw [hfun]
  have hexp : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ => Complex.I * Complex.exp (Complex.I * ((uncurry Θ p : ℝ) : ℂ))) :=
    (Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp hΘ).const_smul Complex.I)).const_smul Complex.I
  have hconj : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ =>
        (starRingEnd ℂ) (Complex.I * Complex.exp (Complex.I * ((uncurry Θ p : ℝ) : ℂ)))) := by
    have h := Complex.conjCLE.contDiff.comp hexp
    rw [Function.comp_def] at h
    exact h
  exact Complex.reCLM.contDiff.comp (hFdot.mul hconj)

/-- **The velocity of the family of rear tracks written in its own arclength is
one derivative less smooth than the front data.** -/
theorem contDiff_rearOwnVelocity {n : ℕ} {sf sft : ℝ → ℝ → ℝ} {Fdot Ydot : ℝ → ℝ → ℂ}
    {Θdot w : ℝ → ℝ → ℝ}
    (hΘ : ContDiff ℝ (n : ℕ) (uncurry Θ)) (hδ : ContDiff ℝ (n : ℕ) (uncurry δ))
    (hsf : ContDiff ℝ (n : ℕ) (uncurry sf))
    (hFdot : ContDiff ℝ (n : ℕ) (uncurry Fdot)) (hΘdot : ContDiff ℝ (n : ℕ) (uncurry Θdot))
    (hw : ContDiff ℝ (n : ℕ) (uncurry w)) (hsft : ContDiff ℝ (n : ℕ) (uncurry sft))
    (hYdot : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ)))) :
    ContDiff ℝ (n : ℕ) (uncurry Ydot) := by
  have hcomp : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => (p.1, uncurry sf p)) :=
    contDiff_fst.prodMk hsf
  have hang : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ => uncurry Θ (p.1, uncurry sf p) - uncurry δ (p.1, uncurry sf p)) :=
    (hΘ.comp hcomp).sub (hδ.comp hcomp)
  have hexp : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ => Complex.exp (Complex.I *
        ((uncurry Θ (p.1, uncurry sf p) - uncurry δ (p.1, uncurry sf p) : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp hang).const_smul Complex.I)
  have htrack : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ => uncurry Fdot (p.1, uncurry sf p)
        - Complex.I * ((uncurry Θdot (p.1, uncurry sf p) - uncurry w (p.1, uncurry sf p) : ℝ) : ℂ)
          * Complex.exp (Complex.I *
            ((uncurry Θ (p.1, uncurry sf p) - uncurry δ (p.1, uncurry sf p) : ℝ) : ℂ))) := by
    refine (hFdot.comp hcomp).sub ?_
    exact ((contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp ((hΘdot.comp hcomp).sub (hw.comp hcomp)))).mul hexp)
  have hcos : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ => ((Real.cos (uncurry δ (p.1, uncurry sf p)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp (hδ.comp hcomp))
  have hsecond : ContDiff ℝ (n : ℕ)
      (fun p : ℝ × ℝ => ((uncurry sft p : ℝ) : ℂ) *
        (((Real.cos (uncurry δ (p.1, uncurry sf p)) : ℝ) : ℂ) *
          Complex.exp (Complex.I *
            ((uncurry Θ (p.1, uncurry sf p) - uncurry δ (p.1, uncurry sf p) : ℝ) : ℂ)))) :=
    (Complex.ofRealCLM.contDiff.comp hsft).mul (hcos.mul hexp)
  have hfun : uncurry Ydot = fun p : ℝ × ℝ =>
      (uncurry Fdot (p.1, uncurry sf p)
        - Complex.I * ((uncurry Θdot (p.1, uncurry sf p) - uncurry w (p.1, uncurry sf p) : ℝ) : ℂ)
          * Complex.exp (Complex.I *
            ((uncurry Θ (p.1, uncurry sf p) - uncurry δ (p.1, uncurry sf p) : ℝ) : ℂ)))
      + ((uncurry sft p : ℝ) : ℂ) *
        (((Real.cos (uncurry δ (p.1, uncurry sf p)) : ℝ) : ℂ) *
          Complex.exp (Complex.I *
            ((uncurry Θ (p.1, uncurry sf p) - uncurry δ (p.1, uncurry sf p) : ℝ) : ℂ))) := by
    funext p
    obtain ⟨t, x⟩ := p
    simp only [uncurry]
    rw [hYdot t x]
    simp [trackVelocity, rearAngle, real_smul]
  rw [hfun]
  exact htrack.add hsecond

end RearOwnHigherRegularity
