import Mathlib
import UnitTangentIterates.GlobalODE
import UnitTangentIterates.NormalGauge
import UnitTangentIterates.RearFamilyFrame

/-!
# The normal gauge of a family given in the moving frame

`NormalGauge.lean` shows that reparametrizing a family of curves by a flow
`φ` solving `φ_t = -ξ/g` turns the velocity `ξ τ + η ν` into `η ν`.  Its
hypotheses are stated for the total derivative of the family.  This file
restates it for a family given, as in `RearFamilyFrame.lean`, by its frame
data:

`∂_x R = v e^{iΨ}`,   `∂_a R = (ξ + iη) e^{iΨ}` ,

so that the tangent is `τ = e^{iΨ}` and the normal is `ν = i e^{iΨ}`.  The
conclusion is that the reparametrized family `a ↦ R(a, φ(a))` moves with the
purely normal velocity `η ν` — which is exactly the shape of the hypothesis
`hderiv` (and `hnu`) of
`SelectedInverseFrontPath.exists_normalPath_of_front_path`.

Main results:

* `frame_velocity_split` — `(ξ + iη)e^{iΨ} = ξ τ + η ν` for that frame;
* `norm_frameNormalVector` — the frame normal is a unit vector;
* `hasDerivAt_normalGauge_of_frame` — the normal gauge for frame data;
* `hasDerivAt_normalGauge_rearFamily` — the same for the family of selected
  rears of `RearFamilyFrame.lean`;
* `exists_normalGauge_flow` — the flow itself exists, by the global existence
  theorem of `GlobalODE.lean`, as soon as the tangential rate `-ξ/v` is bounded
  and Lipschitz in the parameter: the reparametrized family then moves normally
  at every time.
-/

noncomputable section

open Real Complex

namespace NormalGaugeFrame

open RearFamilyFrame

/-- The unit normal of the moving frame `e^{iΨ}`. -/
def frameNormalVector (psi : ℝ) : ℂ := Complex.I * Complex.exp (Complex.I * (psi : ℂ))

/-- The frame normal is a unit vector. -/
theorem norm_frameNormalVector (psi : ℝ) : ‖frameNormalVector psi‖ = 1 := by
  simp [frameNormalVector, Complex.norm_exp]

/-- The velocity `(ξ + iη)e^{iΨ}` split into its tangential and normal parts. -/
theorem frame_velocity_split (xi eta psi : ℝ) :
    ((xi : ℂ) + Complex.I * (eta : ℂ)) * Complex.exp (Complex.I * (psi : ℂ))
      = (xi : ℂ) * Complex.exp (Complex.I * (psi : ℂ))
        + (eta : ℂ) * frameNormalVector psi := by
  simp [frameNormalVector]
  ring

/-- **The normal gauge for a family given by its frame data.**  If
`∂_x R = v e^{iΨ}` with `v ≠ 0` at the point, `∂_a R = (ξ + iη) e^{iΨ}`, and the
flow `φ` solves `φ' = -ξ/v`, then the reparametrized family `a ↦ R(a, φ(a))`
moves with the purely normal velocity `η · i e^{iΨ}`. -/
theorem hasDerivAt_normalGauge_of_frame {R : ℝ → ℝ → ℂ} {v xi eta psi : ℝ → ℝ → ℝ}
    {phi : ℝ → ℝ} {a0 : ℝ}
    (hR : ContDiff ℝ 1 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (((xi a x : ℂ) + Complex.I * (eta a x : ℂ))
        * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hv : v a0 (phi a0) ≠ 0)
    (hphi : HasDerivAt phi (-(xi a0 (phi a0) / v a0 (phi a0))) a0) :
    HasDerivAt (fun r => R r (phi r))
      ((eta a0 (phi a0) : ℂ) * frameNormalVector (psi a0 (phi a0))) a0 := by
  set x0 := phi a0 with hx0
  have hdiff : DifferentiableAt ℝ (Function.uncurry R) (a0, x0) :=
    (hR.differentiable one_ne_zero) (a0, x0)
  set L := fderiv ℝ (Function.uncurry R) (a0, x0) with hL
  have hF : HasFDerivAt (Function.uncurry R) L (a0, x0) := hdiff.hasFDerivAt
  -- the two partial derivatives
  have hcurve1 : HasDerivAt (fun t : ℝ => (t, x0)) ((1 : ℝ), (0 : ℝ)) a0 :=
    (hasDerivAt_id a0).prodMk (hasDerivAt_const a0 x0)
  have hcurve2 : HasDerivAt (fun t : ℝ => (a0, t)) ((0 : ℝ), (1 : ℝ)) x0 :=
    (hasDerivAt_const x0 a0).prodMk (hasDerivAt_id x0)
  have hLt : L (1, 0) = ((xi a0 x0 : ℂ) + Complex.I * (eta a0 x0 : ℂ))
      * Complex.exp (Complex.I * (psi a0 x0 : ℂ)) := by
    have h1 : HasDerivAt (fun t : ℝ => R t x0) (L (1, 0)) a0 := by
      simpa [Function.comp, Function.uncurry] using hF.comp_hasDerivAt a0 hcurve1
    exact h1.unique (ha a0 x0)
  have hLu : L (0, 1) = (v a0 x0 : ℂ) * Complex.exp (Complex.I * (psi a0 x0 : ℂ)) := by
    have h2 : HasDerivAt (fun t : ℝ => R a0 t) (L (0, 1)) x0 := by
      simpa [Function.comp, Function.uncurry] using hF.comp_hasDerivAt x0 hcurve2
    exact h2.unique (hx a0 x0)
  exact NormalGauge.hasDerivAt_normalGauge (F := Function.uncurry R) (L := L)
    (phi := phi) (xi := xi a0 x0) (eta := eta a0 x0) (g := v a0 x0)
    (tau := Complex.exp (Complex.I * (psi a0 x0 : ℂ)))
    (nu := frameNormalVector (psi a0 x0)) hF hphi
    (by rw [hLt, frame_velocity_split]) hLu hv

/-- **The normal gauge for the family of selected rears.**  With the frame data
of `RearFamilyFrame.lean`, a flow `φ` solving `φ' = -ξ/v` turns the motion of
the family of selected rear tracks into a purely normal motion, of normal
velocity the frame component `η`. -/
theorem hasDerivAt_normalGauge_rearFamily {F : ℝ → ℝ → ℂ} {Θ δ K : ℝ → ℝ → ℝ}
    {σ phi : ℝ → ℝ} {Rdot : ℝ → ℝ → ℂ} {a0 : ℝ}
    (hR : ContDiff ℝ 1 (Function.uncurry (rearFamily F Θ δ σ)))
    (hF : ∀ a s, HasDerivAt (F a) (Complex.exp (Complex.I * (Θ a s : ℂ))) s)
    (hΘ : ∀ a s, HasDerivAt (Θ a) (K a s) s)
    (hδ : ∀ a s, HasDerivAt (δ a) (K a s - Real.sin (δ a s)) s)
    (hσ : ∀ x, HasDerivAt σ (1 / Real.cos (δ a0 (σ x))) x)
    (hRa : ∀ a x, HasDerivAt (fun a' => rearFamily F Θ δ σ a' x) (Rdot a x) a)
    (hv : frameSpeed δ σ a0 a0 (phi a0) ≠ 0)
    (hphi : HasDerivAt phi
      (-(frameTangential Rdot (frameAngle Θ δ σ) a0 (phi a0)
        / frameSpeed δ σ a0 a0 (phi a0))) a0) :
    HasDerivAt (fun r => rearFamily F Θ δ σ r (phi r))
      ((frameNormal Rdot (frameAngle Θ δ σ) a0 (phi a0) : ℂ)
        * frameNormalVector (frameAngle Θ δ σ a0 (phi a0))) a0 :=
  hasDerivAt_normalGauge_of_frame hR (hasDerivAt_rearFamily_space hF hΘ hδ hσ)
    (hasDerivAt_rearFamily_time hRa) hv hphi

/-- **The normal gauge exists.**  If the tangential rate `-ξ/v` of the family
is bounded and globally Lipschitz in the parameter (and continuous in the
time), the flow `φ' = -ξ/v` exists on the whole line for every initial
parameter, and the reparametrized family `a ↦ R(a, φ(a))` moves with the purely
normal velocity `η · i e^{iΨ}` at **every** time. -/
theorem exists_normalGauge_flow {R : ℝ → ℝ → ℂ} {v xi eta psi : ℝ → ℝ → ℝ}
    {K L : NNReal} {a0 x0 : ℝ}
    (hR : ContDiff ℝ 1 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (((xi a x : ℂ) + Complex.I * (eta a x : ℂ))
        * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hvne : ∀ a x, v a x ≠ 0)
    (hlip : ∀ a, LipschitzWith K (fun x => -(xi a x / v a x)))
    (hcont : ∀ x, Continuous fun a => -(xi a x / v a x))
    (hbd : ∀ a x, |(-(xi a x / v a x))| ≤ (L : ℝ)) :
    ∃ phi : ℝ → ℝ, phi a0 = x0 ∧ ∀ a, HasDerivAt (fun r => R r (phi r))
      ((eta a (phi a) : ℂ) * frameNormalVector (psi a (phi a))) a := by
  obtain ⟨phi, hphi0, hphid⟩ :=
    GlobalODE.exists_global_solution_real (h := fun a x => -(xi a x / v a x))
      hlip hcont hbd a0 x0
  refine ⟨phi, hphi0, fun a => ?_⟩
  exact hasDerivAt_normalGauge_of_frame (a0 := a) hR hx ha (hvne a (phi a)) (hphid a)

end NormalGaugeFrame
