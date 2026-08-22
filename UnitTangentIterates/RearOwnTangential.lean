import Mathlib
import UnitTangentIterates.RearOwnPathDistFrameBounds

/-!
# The tangential drift of the selected rears is controlled by the geometry

`RearOwnPathDistFrameBounds.pathDist_le_of_front_frame_bounds` states the
path-pseudodistance bound for the selected rears with the two gauge constants
`rL`, `rB` *prescribed*: the caller has to supply bounds for the first two
arclength derivatives of the tangential component

`ξ(t,x) = ⟨∂_t Y(t,x), e^{iΨ(t,x)}⟩`

of the motion of the family `Y` of rear tracks written in its own arclength.
Nothing in the project supplied them from the geometry, and that was the last
piece of data of that statement that was not read off the front.

This file supplies them.  The mechanism is the first-variation identity: for a
family written in its own arclength the speed is constantly `1`, so the speed
equation `∂_t v = ∂_xξ − η ∂_xΨ` of `GeneralVariation.lean` degenerates to

`∂_xξ = η · ∂_xΨ`,

the tangential drift being exactly the normal velocity times the curvature.
Both factors are geometric: the rear curvature is `tan δ` and the rear normal
velocity solves the inverse Jacobi ODE `∂_xη = sec δ · η_F − η`.  Differentiating
once more,

`∂_x²ξ = (sec δ · η_F − η) tan δ + η (K − sin δ) sec³δ`,

so on the selected strip `0 ≤ δ ≤ arcsin κ̂`, `|K| ≤ κ̂`, sup bounds `E₀` for the
rear normal velocity and `E_F` for the front normal velocity give

`|∂_xξ| ≤ E₀ κ̂/√(1−κ̂²)`,
`|∂_x²ξ| ≤ (E_F/√(1−κ̂²) + E₀) κ̂/√(1−κ̂²) + 2E₀ κ̂/(1−κ̂²)^{3/2}`.

Main results:

* `contDiff_succ_of_partials` — joint `C^{n+1}` regularity from partial
  derivatives which are jointly `C^n` (the order-`n` companion of
  `JointC1.contDiff_one_of_continuous_partials`);
* `partialX_tangential_unitSpeed` — `∂_xξ = η ∂_xΨ` for a unit-speed family;
* `partialX_frameTangential_rearOwn` — the same for the family of selected
  rears, with `∂_xΨ = tan δ`;
* `abs_partialX_frameTangential_le`, `abs_partialX_partialX_frameTangential_le`
  — the two bounds;
* `pathDist_le_of_front_frame_geometric` — the path-pseudodistance bound with
  the two gauge constants replaced by the geometric ones.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnTangential

open UniformFrameBounds GaugePathDistVariable RearOwnPathDist RearOwnFrameDrift
  JointC1 GeneralVariation

/-! ### Joint smoothness from the partial derivatives -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The differential `(u,v) ↦ u • a + v • b` as a continuous linear function of
the pair `(a, b)` of partial derivatives. -/
def partialCLM₂ : (E × E) →L[ℝ] ((ℝ × ℝ) →L[ℝ] E) :=
  (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.fst ℝ E E)
  + (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.snd ℝ E E)

theorem partialCLM₂_apply (a b : E) : partialCLM₂ (a, b) = partialCLM a b := by
  simp [partialCLM₂, partialCLM]

/-- **Joint `C^{n+1}` regularity from the partial derivatives.**  A family
`f : ℝ → ℝ → E` whose two partial derivatives exist everywhere and are jointly
`C^n` is jointly `C^{n+1}`. -/
theorem contDiff_succ_of_partials {f f1 f2 : ℝ → ℝ → E} {n : ℕ}
    (h1 : ∀ t x, HasDerivAt (fun r => f r x) (f1 t x) t)
    (h2 : ∀ t x, HasDerivAt (f t) (f2 t x) x)
    (hc1 : ContDiff ℝ (n : ℕ) (uncurry f1)) (hc2 : ContDiff ℝ (n : ℕ) (uncurry f2)) :
    ContDiff ℝ ((n + 1 : ℕ)) (uncurry f) := by
  have hfd : ∀ p : ℝ × ℝ,
      HasFDerivAt (uncurry f) (partialCLM (f1 p.1 p.2) (f2 p.1 p.2)) p := by
    rintro ⟨t, x⟩
    exact hasFDerivAt_of_continuous_partials h1 h2 hc1.continuous hc2.continuous t x
  have heq : fderiv ℝ (uncurry f)
      = fun p : ℝ × ℝ => partialCLM₂ ((uncurry f1) p, (uncurry f2) p) := by
    funext p
    rw [(hfd p).fderiv, partialCLM₂_apply]
    rfl
  have hstep : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (uncurry f) := by
    refine contDiff_succ_iff_fderiv.mpr ⟨fun p => (hfd p).differentiableAt, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · rw [heq]
      exact (partialCLM₂ : (E × E) →L[ℝ] _).contDiff.comp (hc1.prodMk hc2)
  simpa using hstep

/-! ### The tangential drift of a unit-speed family -/

/-- **The first-variation identity for a family written in its own arclength.**
If `Y` is a `C²` family with `∂_x Y = e^{iΨ}` — so that every slice has unit
speed — then the arclength derivative of the tangential component of the motion
is the normal component times the curvature:

`∂_xξ = η ∂_xΨ`.

Indeed the speed equation of `GeneralVariation.mixed_partial_general_variation`
reads `∂_t v = ∂_xξ − η ∂_xΨ`, and here `v ≡ 1`. -/
theorem partialX_tangential_unitSpeed {Y Ydot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ}
    {t x psidot psix xix etax : ℝ}
    (hY2 : ContDiff ℝ 2 (uncurry Y))
    (hx : ∀ a y, HasDerivAt (Y a) (Complex.exp (Complex.I * (psi a y : ℂ))) y)
    (ha : ∀ a y, HasDerivAt (fun r => Y r y) (Ydot a y) a)
    (hpsia : HasDerivAt (fun r => psi r x) psidot t)
    (hxi : HasDerivAt (frameTangential Ydot psi t) xix x)
    (heta : HasDerivAt (frameNormal Ydot psi t) etax x)
    (hpsix : HasDerivAt (psi t) psix x) :
    xix = frameNormal Ydot psi t x * psix := by
  have hxv : ∀ a y, HasDerivAt (fun y' => Y a y')
      ((((fun _ _ => (1 : ℝ)) a y : ℝ) : ℂ)
        * Complex.exp (Complex.I * (psi a y : ℂ))) y := by
    intro a y; simpa using hx a y
  have hav : ∀ a y, HasDerivAt (fun r => Y r y)
      ((((frameTangential Ydot psi a y : ℝ) : ℂ)
          + Complex.I * ((frameNormal Ydot psi a y : ℝ) : ℂ))
        * Complex.exp (Complex.I * (psi a y : ℂ))) a := by
    intro a y
    refine (ha a y).congr_deriv ?_
    simpa [frameTangential, frameNormal] using
      (frame_reconstruct (Ydot a y) (psi a y)).symm
  have hmix := mixed_partial_of_frame_general (R := Y) (v := fun _ _ => (1 : ℝ))
    (xi := frameTangential Ydot psi) (eta := frameNormal Ydot psi) (psi := psi)
    (a0 := t) (x0 := x) (vdot := 0) (psidot := psidot) (xix := xix) (etax := etax)
    (psix := psix) hY2 hxv hav (hasDerivAt_const t (1 : ℝ)) hpsia hxi heta hpsix
  have h := (mixed_partial_general_variation hmix).1
  linarith

/-! ### Regularity of the frame components -/

/-- The unit tangent of a family is as smooth as its tangent angle. -/
theorem contDiff_expI {n : ℕ} {psi : ℝ → ℝ → ℝ} (hpsi : ContDiff ℝ (n : ℕ) (uncurry psi)) :
    ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => Complex.exp (Complex.I * ((uncurry psi p : ℝ) : ℂ))) := by
  have h1 : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ => Complex.I * ((uncurry psi p : ℝ) : ℂ) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hpsi)
  exact Complex.contDiff_exp.comp h1

/-- The two frame components of a motion are as smooth as the motion and the
tangent angle. -/
theorem contDiff_frameTangential {n : ℕ} {Rdot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ}
    (hR : ContDiff ℝ (n : ℕ) (uncurry Rdot)) (hpsi : ContDiff ℝ (n : ℕ) (uncurry psi)) :
    ContDiff ℝ (n : ℕ) (uncurry (frameTangential Rdot psi)) := by
  have hprod : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ =>
      (uncurry Rdot) p * (starRingEnd ℂ) (Complex.exp (Complex.I * ((uncurry psi p : ℝ) : ℂ))) := by
    refine hR.mul ?_
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp (contDiff_expI (n := n) hpsi)
    simpa [Function.comp_def] using this
  have h2 := Complex.reCLM.contDiff.comp hprod
  rw [Function.comp_def] at h2
  exact h2

theorem contDiff_frameNormal {n : ℕ} {Rdot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ}
    (hR : ContDiff ℝ (n : ℕ) (uncurry Rdot)) (hpsi : ContDiff ℝ (n : ℕ) (uncurry psi)) :
    ContDiff ℝ (n : ℕ) (uncurry (frameNormal Rdot psi)) := by
  have hprod : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ =>
      (uncurry Rdot) p * (starRingEnd ℂ) (Complex.exp (Complex.I * ((uncurry psi p : ℝ) : ℂ))) := by
    refine hR.mul ?_
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp (contDiff_expI (n := n) hpsi)
    simpa [Function.comp_def] using this
  have h2 := Complex.imCLM.contDiff.comp hprod
  rw [Function.comp_def] at h2
  exact h2

/-! ### The rear curvature and its arclength derivative -/

section Rear

variable {F Fdot Ydot : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ}

/-- **The curvature of the selected rear in its own arclength is `tan δ`.** -/
theorem hasDerivAt_rearOwnAngle_space
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x) (t x : ℝ) :
    HasDerivAt (rearOwnAngle Θ δ sf t) (Real.tan (δ t (sf t x))) x :=
  hasDerivAt_frameAngle_space (a0 := t) (σ := sf t) (K := K) hΘ hsteer (hsf t) x

/-- **The arclength derivative of the rear curvature** is
`(K − sin δ) sec³δ`. -/
theorem hasDerivAt_rearCurv_space
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0) (t x : ℝ) :
    HasDerivAt (fun x' => Real.tan (δ t (sf t x')))
      ((K t (sf t x) - Real.sin (δ t (sf t x))) / Real.cos (δ t (sf t x)) ^ 3) x := by
  have hd : HasDerivAt (fun x' => δ t (sf t x'))
      ((K t (sf t x) - Real.sin (δ t (sf t x))) * (1 / Real.cos (δ t (sf t x)))) x :=
    (hsteer t (sf t x)).comp x (hsf t x)
  have htan := (Real.hasDerivAt_tan (hcos t (sf t x))).comp x hd
  refine htan.congr_deriv ?_
  field_simp

/-! ### The tangential drift of the selected rears -/

/-- **The tangential drift of the family of selected rears.**  The family of
rear tracks written in its own arclength has unit speed, so the arclength
derivative of the tangential component of its motion is the normal velocity
times the rear curvature `tan δ`. -/
theorem partialX_frameTangential_rearOwn
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf))) (t x : ℝ) :
    partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x
      = frameNormal Ydot (rearOwnAngle Θ δ sf) t x * Real.tan (δ t (sf t x)) := by
  have htanC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnTangent Θ δ sf)) := by
    simpa [rearOwnTangent, uncurry] using contDiff_expI (n := 1) hangC
  have hspace : ∀ a y, HasDerivAt (rearOwn F Θ δ sf a)
      (Complex.exp (Complex.I * (rearOwnAngle Θ δ sf a y : ℂ))) y := fun a y =>
    hasDerivAt_rearOwn_space hF hΘ hsteer hsf hcos a y
  have hY2 : ContDiff ℝ 2 (uncurry (rearOwn F Θ δ sf)) := by
    have h := contDiff_succ_of_partials (f := rearOwn F Θ δ sf) (f1 := Ydot)
      (f2 := rearOwnTangent Θ δ sf) (n := 1) hYt hspace hYdotC htanC
    exact_mod_cast h
  have hxiC : ContDiff ℝ (1 : ℕ)
      (uncurry (frameTangential Ydot (rearOwnAngle Θ δ sf))) :=
    contDiff_frameTangential hYdotC hangC
  have hetaC : ContDiff ℝ (1 : ℕ)
      (uncurry (frameNormal Ydot (rearOwnAngle Θ δ sf))) :=
    contDiff_frameNormal hYdotC hangC
  have hpsia : DifferentiableAt ℝ (fun r => rearOwnAngle Θ δ sf r x) t := by
    have h1 : DifferentiableAt ℝ (uncurry (rearOwnAngle Θ δ sf)) (t, x) :=
      (hangC.differentiable (by norm_num)) (t, x)
    have h2 : DifferentiableAt ℝ (fun r : ℝ => ((r, x) : ℝ × ℝ)) t :=
      differentiableAt_id.prodMk (differentiableAt_const x)
    simpa [Function.comp_def, uncurry] using h1.comp t h2
  exact partialX_tangential_unitSpeed (Y := rearOwn F Θ δ sf) (Ydot := Ydot)
    (psi := rearOwnAngle Θ δ sf) hY2 hspace hYt hpsia.hasDerivAt
    (hasDerivAt_partialX hxiC t x) (hasDerivAt_partialX hetaC t x)
    (hasDerivAt_rearOwnAngle_space hΘ hsteer hsf t x)

/-- **The second arclength derivative of the tangential drift.**  Differentiating
`∂_xξ = η tan δ` once more and substituting the inverse Jacobi ODE
`∂_xη = sec δ · η_F − η` gives

`∂_x²ξ = (sec δ · η_F − η) tan δ + η (K − sin δ) sec³δ`. -/
theorem partialX_partialX_frameTangential_rearOwn {etaF : ℝ → ℝ → ℝ}
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x) (t x : ℝ) :
    partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x
      = (etaF t (sf t x) / Real.cos (δ t (sf t x))
            - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) * Real.tan (δ t (sf t x))
        + frameNormal Ydot (rearOwnAngle Θ δ sf) t x
          * ((K t (sf t x) - Real.sin (δ t (sf t x))) / Real.cos (δ t (sf t x)) ^ 3) := by
  have h1 : ContDiff ℝ (1 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have h1a : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) := hangC.of_le (by norm_num)
  have hfun : partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t
      = fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x' * Real.tan (δ t (sf t x')) :=
    funext fun x' =>
      partialX_frameTangential_rearOwn hF hΘ hsteer hsf hcos hYt h1 h1a t x'
  have hxiC2 : ContDiff ℝ (2 : ℕ) (uncurry (frameTangential Ydot (rearOwnAngle Θ δ sf))) :=
    contDiff_frameTangential hYdotC hangC
  have hpxC : ContDiff ℝ (1 : ℕ)
      (uncurry (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)))) :=
    contDiff_partialX (n := 1) (by exact_mod_cast hxiC2)
  have hderiv := hasDerivAt_partialX hpxC t x
  rw [hfun] at hderiv
  exact hderiv.unique ((hjac t x).mul (hasDerivAt_rearCurv_space hsteer hsf hcos t x))

/-! ### The two bounds on the selected strip -/

/-- The elementary bounds on the selected strip: the steering angle has
`sin δ ≤ κ̂` and `cos δ ≥ √(1−κ̂²) > 0`. -/
theorem strip_bounds {kh d : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hd0 : 0 ≤ d)
    (hd1 : d ≤ Real.arcsin kh) :
    Real.sin d ≤ kh ∧ Real.sqrt (1 - kh ^ 2) ≤ Real.cos d ∧ 0 < Real.sqrt (1 - kh ^ 2)
      ∧ 0 ≤ Real.sin d := by
  have harc : Real.arcsin kh ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two kh
  have hs : Real.sin d ≤ Real.sin (Real.arcsin kh) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) harc hd1
  rw [Real.sin_arcsin (by linarith) (by linarith)] at hs
  refine ⟨hs, ?_, Real.sqrt_pos.mpr (by nlinarith),
    Real.sin_nonneg_of_nonneg_of_le_pi hd0 (by linarith [Real.pi_pos])⟩
  have hmono : Real.cos (Real.arcsin kh) ≤ Real.cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi hd0 (harc.trans (by linarith [Real.pi_pos])) hd1
  rwa [Real.cos_arcsin] at hmono

/-- The rear curvature is bounded on the selected strip. -/
theorem abs_tan_le_strip {kh d : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hd0 : 0 ≤ d)
    (hd1 : d ≤ Real.arcsin kh) :
    |Real.tan d| ≤ kh / Real.sqrt (1 - kh ^ 2) := by
  obtain ⟨hs, hc, hcpos, hs0⟩ := strip_bounds hkh0 hkh1 hd0 hd1
  have hcos : 0 < Real.cos d := lt_of_lt_of_le hcpos hc
  rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_nonneg hs0, abs_of_pos hcos]
  exact div_le_div₀ hkh0 hs hcpos hc

/-- The arclength derivative of the rear curvature is bounded on the selected
strip. -/
theorem abs_curvDeriv_le_strip {kh Kv d : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hd0 : 0 ≤ d)
    (hd1 : d ≤ Real.arcsin kh) (hK : |Kv| ≤ kh) :
    |(Kv - Real.sin d) / Real.cos d ^ 3| ≤ 2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3 := by
  obtain ⟨hs, hc, hcpos, hs0⟩ := strip_bounds hkh0 hkh1 hd0 hd1
  have hcos : 0 < Real.cos d := lt_of_lt_of_le hcpos hc
  have hnum : |Kv - Real.sin d| ≤ 2 * kh := by
    rw [abs_le] at hK ⊢
    constructor <;> linarith [hK.1, hK.2]
  have hden : Real.sqrt (1 - kh ^ 2) ^ 3 ≤ Real.cos d ^ 3 := pow_le_pow_left₀ hcpos.le hc 3
  rw [abs_div, abs_of_pos (show (0 : ℝ) < Real.cos d ^ 3 by positivity)]
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

/-- The normal velocity of the front, divided by `cos δ`, is bounded on the
selected strip. -/
theorem abs_div_cos_le_strip {kh EF v d : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hd0 : 0 ≤ d)
    (hd1 : d ≤ Real.arcsin kh) (hv : |v| ≤ EF) :
    |v / Real.cos d| ≤ EF / Real.sqrt (1 - kh ^ 2) := by
  obtain ⟨hs, hc, hcpos, hs0⟩ := strip_bounds hkh0 hkh1 hd0 hd1
  have hcos : 0 < Real.cos d := lt_of_lt_of_le hcpos hc
  rw [abs_div, abs_of_pos hcos]
  exact div_le_div₀ (le_trans (abs_nonneg v) hv) hv hcpos hc

/-! ### The two gauge constants, from the geometry -/

/-- **The first gauge constant.**  A sup bound `E₀` for the normal velocity of
the selected rears bounds the first arclength derivative of the tangential
component of their motion by `E₀ κ̂/√(1−κ̂²)`. -/
theorem abs_partialX_frameTangential_le {E0 kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hE0 : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ E0) (t x : ℝ) :
    |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x|
      ≤ E0 * (kh / Real.sqrt (1 - kh ^ 2)) := by
  rw [partialX_frameTangential_rearOwn hF hΘ hsteer hsf hcos hYt hYdotC hangC t x, abs_mul]
  exact mul_le_mul (hE0 t x)
    (abs_tan_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x)))
    (abs_nonneg _) (le_trans (abs_nonneg _) (hE0 t x))

/-- **The second gauge constant.**  Sup bounds `E₀` for the normal velocity of
the selected rears and `E_F` for the normal velocity of the fronts bound the
second arclength derivative of the tangential component. -/
theorem abs_partialX_partialX_frameTangential_le {etaF : ℝ → ℝ → ℝ} {E0 EF kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hE0 : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ E0)
    (hEF : ∀ t s, |etaF t s| ≤ EF) (t x : ℝ) :
    |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x|
      ≤ (EF / Real.sqrt (1 - kh ^ 2) + E0) * (kh / Real.sqrt (1 - kh ^ 2))
        + E0 * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) := by
  rw [partialX_partialX_frameTangential_rearOwn hF hΘ hsteer hsf hcos hYt hYdotC hangC hjac t x]
  have hE0nn : 0 ≤ E0 := le_trans (abs_nonneg _) (hE0 t x)
  have hEFnn : 0 ≤ EF := le_trans (abs_nonneg _) (hEF t (sf t x))
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := (strip_bounds hkh0 hkh1
    (hstrip0 t (sf t x)) (hstrip1 t (sf t x))).2.2.1
  have hA : |etaF t (sf t x) / Real.cos (δ t (sf t x))
      - frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ EF / Real.sqrt (1 - kh ^ 2) + E0 := by
    refine le_trans (abs_sub _ _) (add_le_add ?_ (hE0 t x))
    exact abs_div_cos_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x))
      (hEF t (sf t x))
  have hAnn : 0 ≤ EF / Real.sqrt (1 - kh ^ 2) + E0 := by positivity
  calc |(etaF t (sf t x) / Real.cos (δ t (sf t x))
            - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) * Real.tan (δ t (sf t x))
        + frameNormal Ydot (rearOwnAngle Θ δ sf) t x
          * ((K t (sf t x) - Real.sin (δ t (sf t x))) / Real.cos (δ t (sf t x)) ^ 3)|
      ≤ |(etaF t (sf t x) / Real.cos (δ t (sf t x))
            - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) * Real.tan (δ t (sf t x))|
        + |frameNormal Ydot (rearOwnAngle Θ δ sf) t x
          * ((K t (sf t x) - Real.sin (δ t (sf t x))) / Real.cos (δ t (sf t x)) ^ 3)| :=
        abs_add_le _ _
    _ ≤ (EF / Real.sqrt (1 - kh ^ 2) + E0) * (kh / Real.sqrt (1 - kh ^ 2))
        + E0 * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) := by
        rw [abs_mul, abs_mul]
        refine add_le_add (mul_le_mul hA
          (abs_tan_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x)))
          (abs_nonneg _) hAnn) (mul_le_mul (hE0 t x)
          (abs_curvDeriv_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x))
            (hK t (sf t x))) (abs_nonneg _) hE0nn)

/-! ### The rear normal velocity is controlled by the front's -/

/-- **A maximum principle for the periodic solutions of `η' = g − η`.**  A
solution which is periodic attains its extrema; at them the derivative
vanishes, so the solution equals `g` there, and hence it is bounded by the sup
bound of `g` everywhere. -/
theorem abs_le_of_periodic_ode {eta g : ℝ → ℝ} {Q B : ℝ} (hQ : 0 < Q)
    (hper : Function.Periodic eta Q)
    (hderiv : ∀ x, HasDerivAt eta (g x - eta x) x)
    (hg : ∀ x, |g x| ≤ B) (x : ℝ) : |eta x| ≤ B := by
  have hcont : Continuous eta :=
    continuous_iff_continuousAt.mpr fun y => (hderiv y).continuousAt
  have hne : (Icc (0 : ℝ) Q).Nonempty := ⟨0, by constructor <;> simp [hQ.le]⟩
  obtain ⟨xM, hxM, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont.continuousOn
  obtain ⟨xm, hxm, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont.continuousOn
  have hglobmax : ∀ y, eta y ≤ eta xM := by
    intro y
    obtain ⟨z, hz, hzy⟩ := hper.exists_mem_Ico₀ hQ y
    rw [hzy]
    exact hmax ⟨hz.1, hz.2.le⟩
  have hglobmin : ∀ y, eta xm ≤ eta y := by
    intro y
    obtain ⟨z, hz, hzy⟩ := hper.exists_mem_Ico₀ hQ y
    rw [hzy]
    exact hmin ⟨hz.1, hz.2.le⟩
  have hMzero : g xM - eta xM = 0 :=
    IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hglobmax) (hderiv xM)
  have hmzero : g xm - eta xm = 0 :=
    IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hglobmin) (hderiv xm)
  have h1 : eta xM ≤ B := by
    have := hg xM; rw [abs_le] at this; linarith
  have h2 : -B ≤ eta xm := by
    have := hg xm; rw [abs_le] at this; linarith
  rw [abs_le]
  exact ⟨le_trans h2 (hglobmin x), le_trans (hglobmax x) h1⟩

/-- **The normal velocity of the selected rears is bounded by that of the
fronts.**  Since the rear normal velocity solves the inverse Jacobi ODE
`∂_xη = sec δ · η_F − η` and is periodic — the slices being closed curves — the
maximum principle gives `‖η‖_∞ ≤ ‖η_F‖_∞/√(1−κ̂²)`, so the sup bound on the
rear side need not be assumed. -/
theorem abs_frameNormal_le_of_periodic {etaF : ℝ → ℝ → ℝ} {EF kh : ℝ} {Q : ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hQpos : ∀ t, 0 < Q t)
    (hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hEF : ∀ t s, |etaF t s| ≤ EF) (t x : ℝ) :
    |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ EF / Real.sqrt (1 - kh ^ 2) :=
  abs_le_of_periodic_ode (hQpos t) (hper t) (hjac t)
    (fun y => abs_div_cos_le_strip hkh0 hkh1 (hstrip0 t (sf t y)) (hstrip1 t (sf t y))
      (hEF t (sf t y))) x

end Rear

end RearOwnTangential
