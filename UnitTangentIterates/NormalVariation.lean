import Mathlib
import UnitTangentIterates.MixedPartials
import UnitTangentIterates.RearSmoothDependence

/-!
# The first variation of a normal deformation, and the transport identity

The whole chain of *inverse Jacobi estimates* takes as its input the identity

```
  (1 + ∂_x) η_R = sec δ · η_F ,
```

relating the normal velocity `η_R` of the rear (in its own arclength `x`) to
the normal velocity `η_F` of the front.  This file derives that identity from
the geometry of the bicycle correspondence `F = R + e^{iΨ}`, `Θ = Ψ + δ`.

The two ingredients are:

* the **frame decomposition** `eq_of_frame_eq`: a complex identity written in
  the moving frame `e^{iΨ}` splits into its tangential and normal parts, and
  applied to the equality of the mixed partial derivatives of a normally
  deformed curve (`mixed_partial_normal_variation`) it yields the classical
  first-variation formulas — the speed varies at rate `-η ∂_xΨ` and the
  tangent angle rotates at rate `∂_x η / v`, so at a parameter which is
  arclength at the reference time, `Ψ̇ = ∂_x η_R`;
* the **frame computation** `front_normal_velocity`: if the rear moves
  normally, `Ṙ = i η_R e^{iΨ}`, then `Ḟ = i(η_R + Ψ̇) e^{iΨ}`
  (`hasDerivAt_front_of_normal_rear`), whose component along the *front*
  normal `i e^{iΘ}` is `(η_R + Ψ̇) cos δ`.

Combining the two gives `transport_identity`: `η_R + ∂_x η_R = sec δ · η_F`,
which is exactly the hypothesis `G = sec δ · η_F ∘ s` of
`JacobiEstimates.lean`.
-/

noncomputable section

open Real Complex

namespace NormalVariation

/-- **Frame decomposition.**  An identity between two vectors written in the
moving frame `e^{iψ}` splits into its tangential and normal components. -/
theorem eq_of_frame_eq {psi A B C D : ℝ}
    (h : ((A : ℂ) + Complex.I * (B : ℂ)) * Complex.exp (Complex.I * (psi : ℂ))
      = ((C : ℂ) + Complex.I * (D : ℂ)) * Complex.exp (Complex.I * (psi : ℂ))) :
    A = C ∧ B = D := by
  have hexp : Complex.exp (Complex.I * (psi : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have h' : ((A : ℂ) + Complex.I * (B : ℂ)) = ((C : ℂ) + Complex.I * (D : ℂ)) :=
    mul_right_cancel₀ hexp h
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp at hre him
  exact ⟨hre, him⟩

/-- **The first variation of a normal deformation.**  If a family of curves is
deformed normally, `∂_a R = i η e^{iΨ}`, and has velocity `∂_x R = v e^{iΨ}`,
then the equality of mixed partial derivatives
`∂_a(v e^{iΨ}) = ∂_x(i η e^{iΨ})` says exactly that the speed varies at rate
`-η ∂_xΨ` (the curvature term) and that the tangent angle rotates at rate
`∂_x η / v`. -/
theorem mixed_partial_normal_variation {psi vdot v psidot etax eta psix : ℝ}
    (h : (vdot : ℂ) * Complex.exp (Complex.I * (psi : ℂ))
        + Complex.I * ((v * psidot : ℝ) : ℂ) * Complex.exp (Complex.I * (psi : ℂ))
      = Complex.I * (etax : ℂ) * Complex.exp (Complex.I * (psi : ℂ))
        + Complex.I * (eta : ℂ) * (Complex.I * (psix : ℂ))
          * Complex.exp (Complex.I * (psi : ℂ))) :
    vdot = -(eta * psix) ∧ v * psidot = etax := by
  refine eq_of_frame_eq (psi := psi) ?_
  push_cast at h ⊢
  linear_combination h
    + (Complex.exp (Complex.I * (psi : ℂ)) * (eta : ℂ) * (psix : ℂ)) * Complex.I_sq

/-- **The hypothesis of `mixed_partial_normal_variation` holds for a `C²`
family.**  If a `C²` family of curves `R(a, x)` has `∂_x R = v e^{iΨ}` and
`∂_a R = i η e^{iΨ}`, then Clairaut's theorem gives exactly the identity
relating `∂_a v`, `v ∂_aΨ`, `∂_x η` and `η ∂_xΨ`. -/
theorem mixed_partial_of_frame
    {R : ℝ → ℝ → ℂ} {v eta psi : ℝ → ℝ → ℝ} {a0 x0 vdot psidot etax psix : ℝ}
    (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (Complex.I * (eta a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hv : HasDerivAt (fun a' => v a' x0) vdot a0)
    (hpsia : HasDerivAt (fun a' => psi a' x0) psidot a0)
    (heta : HasDerivAt (fun x' => eta a0 x') etax x0)
    (hpsix : HasDerivAt (fun x' => psi a0 x') psix x0) :
    (vdot : ℂ) * Complex.exp (Complex.I * (psi a0 x0 : ℂ))
        + Complex.I * ((v a0 x0 * psidot : ℝ) : ℂ) * Complex.exp (Complex.I * (psi a0 x0 : ℂ))
      = Complex.I * (etax : ℂ) * Complex.exp (Complex.I * (psi a0 x0 : ℂ))
        + Complex.I * (eta a0 x0 : ℂ) * (Complex.I * (psix : ℂ))
          * Complex.exp (Complex.I * (psi a0 x0 : ℂ)) := by
  have hclair := MixedPartials.deriv_partial_comm hR a0 x0
  have hLfun : (fun a' => deriv (fun x' => R a' x') x0)
      = fun a' => (v a' x0 : ℂ) * Complex.exp (Complex.I * (psi a' x0 : ℂ)) := by
    funext a'; exact (hx a' x0).deriv
  have hRfun : (fun x' => deriv (fun a' => R a' x') a0)
      = fun x' => Complex.I * (eta a0 x' : ℂ) * Complex.exp (Complex.I * (psi a0 x' : ℂ)) := by
    funext x'; exact (ha a0 x').deriv
  rw [hLfun, hRfun] at hclair
  have dL : HasDerivAt (fun a' => (v a' x0 : ℂ) * Complex.exp (Complex.I * (psi a' x0 : ℂ)))
      ((vdot : ℂ) * Complex.exp (Complex.I * (psi a0 x0 : ℂ))
        + (v a0 x0 : ℂ) * (Complex.exp (Complex.I * (psi a0 x0 : ℂ))
          * (Complex.I * (psidot : ℂ)))) a0 := by
    have hvc : HasDerivAt (fun a' => ((v a' x0 : ℝ) : ℂ)) ((vdot : ℝ) : ℂ) a0 := by
      simpa using hv.ofReal_comp
    have hpc : HasDerivAt (fun a' => Complex.I * ((psi a' x0 : ℝ) : ℂ))
        (Complex.I * ((psidot : ℝ) : ℂ)) a0 := by
      simpa using (hpsia.ofReal_comp).const_mul Complex.I
    exact hvc.mul hpc.cexp
  have dR : HasDerivAt
      (fun x' => Complex.I * (eta a0 x' : ℂ) * Complex.exp (Complex.I * (psi a0 x' : ℂ)))
      (Complex.I * ((etax : ℝ) : ℂ) * Complex.exp (Complex.I * (psi a0 x0 : ℂ))
        + Complex.I * (eta a0 x0 : ℂ) * (Complex.exp (Complex.I * (psi a0 x0 : ℂ))
          * (Complex.I * ((psix : ℝ) : ℂ)))) x0 := by
    have hec : HasDerivAt (fun x' => Complex.I * ((eta a0 x' : ℝ) : ℂ))
        (Complex.I * ((etax : ℝ) : ℂ)) x0 := by
      simpa using (heta.ofReal_comp).const_mul Complex.I
    have hpc : HasDerivAt (fun x' => Complex.I * ((psi a0 x' : ℝ) : ℂ))
        (Complex.I * ((psix : ℝ) : ℂ)) x0 := by
      simpa using (hpsix.ofReal_comp).const_mul Complex.I
    exact hec.mul hpc.cexp
  rw [dL.deriv, dR.deriv] at hclair
  push_cast
  linear_combination hclair

/-- **The rotation rate of the tangent angle under a normal deformation**, at a
parameter which is arclength at the reference time (`v = 1`): `Ψ̇ = ∂_x η`. -/
theorem psidot_eq_etax {psi vdot psidot etax eta psix : ℝ}
    (h : (vdot : ℂ) * Complex.exp (Complex.I * (psi : ℂ))
        + Complex.I * ((1 * psidot : ℝ) : ℂ) * Complex.exp (Complex.I * (psi : ℂ))
      = Complex.I * (etax : ℂ) * Complex.exp (Complex.I * (psi : ℂ))
        + Complex.I * (eta : ℂ) * (Complex.I * (psix : ℂ))
          * Complex.exp (Complex.I * (psi : ℂ))) :
    psidot = etax := by
  have := (mixed_partial_normal_variation (v := 1) h).2
  simpa using this

/-- **A normally moving rear pushes the front along `i(η_R + Ψ̇) e^{iΨ}`.** -/
theorem hasDerivAt_front_of_normal_rear
    {R : ℝ → ℂ} {psi : ℝ → ℝ} {a0 eta p : ℝ}
    (hR : HasDerivAt R (Complex.I * (eta : ℂ) * Complex.exp (Complex.I * (psi a0 : ℂ))) a0)
    (hpsi : HasDerivAt psi p a0) :
    HasDerivAt (fun a => R a + Complex.exp (Complex.I * (psi a : ℂ)))
      (Complex.I * ((eta + p : ℝ) : ℂ) * Complex.exp (Complex.I * (psi a0 : ℂ))) a0 := by
  have hc : HasDerivAt (fun a => ((psi a : ℝ) : ℂ)) ((p : ℝ) : ℂ) a0 := by
    simpa using hpsi.ofReal_comp
  have hmul : HasDerivAt (fun a => Complex.I * ((psi a : ℝ) : ℂ))
      (Complex.I * ((p : ℝ) : ℂ)) a0 := hc.const_mul Complex.I
  have hexp : HasDerivAt (fun a => Complex.exp (Complex.I * (psi a : ℂ)))
      (Complex.I * ((p : ℝ) : ℂ) * Complex.exp (Complex.I * (psi a0 : ℂ))) a0 := by
    simpa [mul_comm] using hmul.cexp
  refine (hR.add hexp).congr_deriv ?_
  push_cast
  ring

/-- **The normal velocity of the front.**  The front's unit normal is
`i e^{iΘ}` with `Θ = Ψ + δ`, so the component of `i(η + p) e^{iΨ}` along it is
`(η + p) cos δ`. -/
theorem front_normal_velocity (psi d eta p : ℝ) :
    ((Complex.I * ((eta + p : ℝ) : ℂ) * Complex.exp (Complex.I * (psi : ℂ)))
        * (starRingEnd ℂ) (Complex.I * Complex.exp (Complex.I * ((psi + d : ℝ) : ℂ)))).re
      = (eta + p) * Real.cos d := by
  have hsplit : Complex.exp (Complex.I * ((psi + d : ℝ) : ℂ))
      = Complex.exp (Complex.I * (psi : ℂ)) * Complex.exp (Complex.I * (d : ℂ)) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  have hEE : Complex.exp (Complex.I * (psi : ℂ))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))) = 1 :=
    RearSmoothDependence.exp_mul_conj psi
  rw [hsplit]
  have hexpand : (Complex.I * ((eta + p : ℝ) : ℂ) * Complex.exp (Complex.I * (psi : ℂ)))
      * (starRingEnd ℂ) (Complex.I * (Complex.exp (Complex.I * (psi : ℂ))
        * Complex.exp (Complex.I * (d : ℂ))))
      = ((eta + p : ℝ) : ℂ) * (Complex.I * (-Complex.I))
        * (Complex.exp (Complex.I * (psi : ℂ))
          * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))))
        * (starRingEnd ℂ) (Complex.exp (Complex.I * (d : ℂ))) := by
    simp only [map_mul, Complex.conj_I]
    ring
  rw [hexpand, hEE]
  have hI : Complex.I * (-Complex.I) = 1 := by simp [Complex.I_mul_I]
  rw [hI]
  have hconj : (starRingEnd ℂ) (Complex.exp (Complex.I * (d : ℂ)))
      = Complex.exp (-(Complex.I * (d : ℂ))) := by
    rw [← Complex.exp_conj]
    simp
  rw [hconj]
  have hexpneg : Complex.exp (-(Complex.I * (d : ℂ)))
      = (Real.cos d : ℂ) - Complex.I * (Real.sin d : ℂ) := by
    have h1 : -(Complex.I * (d : ℂ)) = ((-d : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast [Real.cos_neg, Real.sin_neg]
    ring
  rw [hexpneg]
  simp [Complex.mul_re, Complex.cos_ofReal_re]

/-- **The transport identity.**  If the rear moves normally with velocity
`η_R`, its tangent angle rotates at rate `∂_x η_R` (`psidot_eq_etax`), and the
resulting front normal velocity is `η_F = (η_R + ∂_x η_R) cos δ`; on the
selected strip `cos δ > 0`, so

`η_R + ∂_x η_R = sec δ · η_F`,

which is the input of the inverse Jacobi estimates. -/
theorem transport_identity {etaR etaRx etaF d : ℝ} (hcos : Real.cos d ≠ 0)
    (h : etaF = (etaR + etaRx) * Real.cos d) :
    etaR + etaRx = etaF / Real.cos d := by
  rw [h]
  field_simp

/-- **The transport identity, assembled.**  Let the rear `R` move normally with
velocity `η_R`, let its tangent angle `Ψ` rotate at rate `p`, and let the mixed
partial derivatives agree at a parameter which is the rear arclength at the
reference time.  Then the front `F = R + e^{iΨ}` moves with velocity `Ḟ`, and
its normal velocity `η_F = ⟨Ḟ, i e^{iΘ}⟩` (with `Θ = Ψ + δ`) satisfies

`η_R + ∂_x η_R = sec δ · η_F`,

the input identity of the inverse Jacobi estimates. -/
theorem transport_identity_of_normal_variation
    {R : ℝ → ℂ} {psi : ℝ → ℝ} {Fdot : ℂ} {a0 etaR etaRx eta psix p vdot d : ℝ}
    (hR : HasDerivAt R (Complex.I * (etaR : ℂ) * Complex.exp (Complex.I * (psi a0 : ℂ))) a0)
    (hpsi : HasDerivAt psi p a0)
    (hF : HasDerivAt (fun a => R a + Complex.exp (Complex.I * (psi a : ℂ))) Fdot a0)
    (hmix : (vdot : ℂ) * Complex.exp (Complex.I * (psi a0 : ℂ))
        + Complex.I * ((1 * p : ℝ) : ℂ) * Complex.exp (Complex.I * (psi a0 : ℂ))
      = Complex.I * (etaRx : ℂ) * Complex.exp (Complex.I * (psi a0 : ℂ))
        + Complex.I * (eta : ℂ) * (Complex.I * (psix : ℂ))
          * Complex.exp (Complex.I * (psi a0 : ℂ)))
    (hcos : Real.cos d ≠ 0) :
    etaR + etaRx
      = (Fdot * (starRingEnd ℂ)
            (Complex.I * Complex.exp (Complex.I * ((psi a0 + d : ℝ) : ℂ)))).re
        / Real.cos d := by
  have hp : p = etaRx := psidot_eq_etax hmix
  have hFd : Fdot = Complex.I * ((etaR + p : ℝ) : ℂ) * Complex.exp (Complex.I * (psi a0 : ℂ)) :=
    hF.unique (hasDerivAt_front_of_normal_rear hR hpsi)
  rw [hFd, front_normal_velocity, hp]
  field_simp

/-- **The transport identity for a `C²` family.**  Same as
`transport_identity_of_normal_variation`, with the equality of mixed partial
derivatives supplied by Clairaut's theorem: for a `C²` family of curves
`R(a,x)` with `∂_x R = v e^{iΨ}`, `∂_a R = i η e^{iΨ}`, at a parameter which is
arclength at the reference time (`v(a₀,x₀) = 1`), the rear and front normal
velocities are related by `η_R + ∂_x η_R = sec δ · η_F`. -/
theorem transport_identity_of_contDiff
    {R : ℝ → ℝ → ℂ} {v eta psi : ℝ → ℝ → ℝ} {Fdot : ℂ}
    {a0 x0 vdot psidot etax psix d : ℝ}
    (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (Complex.I * (eta a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hunit : v a0 x0 = 1)
    (hv : HasDerivAt (fun a' => v a' x0) vdot a0)
    (hpsia : HasDerivAt (fun a' => psi a' x0) psidot a0)
    (heta : HasDerivAt (fun x' => eta a0 x') etax x0)
    (hpsix : HasDerivAt (fun x' => psi a0 x') psix x0)
    (hF : HasDerivAt (fun a => R a x0 + Complex.exp (Complex.I * (psi a x0 : ℂ))) Fdot a0)
    (hcos : Real.cos d ≠ 0) :
    eta a0 x0 + etax
      = (Fdot * (starRingEnd ℂ)
            (Complex.I * Complex.exp (Complex.I * ((psi a0 x0 + d : ℝ) : ℂ)))).re
        / Real.cos d := by
  have hmix := mixed_partial_of_frame hR hx ha hv hpsia heta hpsix
  rw [hunit] at hmix
  exact transport_identity_of_normal_variation (R := fun a => R a x0)
    (psi := fun a => psi a x0) (a0 := a0) (etaR := eta a0 x0) (etaRx := etax)
    (ha a0 x0) hpsia hF hmix hcos

/-- **The transport identity is the ODE driving the inverse Jacobi estimates.**
Once `η_R + ∂_x η_R = G` with `G = sec δ · η_F`, the rear normal velocity solves
`η_R' = G - η_R`, which is the hypothesis `hetaR` of
`JacobiAssembly.jacobi_estimates` and
`JacobiNormalized.jacobi_estimates_normalized_of_geometry`. -/
theorem hasDerivAt_etaR_of_transport {etaR etaRx G : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt etaR (etaRx x) x)
    (htr : ∀ x, etaR x + etaRx x = G x) (x : ℝ) :
    HasDerivAt etaR (G x - etaR x) x := by
  refine (hd x).congr_deriv ?_
  have := htr x
  linarith

/-- The hypotheses of `transport_identity_of_contDiff` are consistent and the
conclusion is not vacuous: the horizontal lines `R(a,x) = x + i a`, translated
normally at unit speed, have `v = 1`, `Ψ = 0`, `η_R = 1`, `∂_xη_R = 0`, and the
front `F = R + 1` indeed moves with normal velocity `1 = (η_R + ∂_xη_R) cos 0`. -/
example : (1 : ℝ) + 0
    = (Complex.I * (starRingEnd ℂ)
        (Complex.I * Complex.exp (Complex.I * ((0 + 0 : ℝ) : ℂ)))).re / Real.cos 0 := by
  have hone : ∀ x : ℝ, HasDerivAt (fun x' : ℝ => ((x' : ℝ) : ℂ)) 1 x := by
    intro x
    simpa using (hasDerivAt_id x).ofReal_comp
  refine transport_identity_of_contDiff (R := fun a x => (x : ℂ) + Complex.I * (a : ℂ))
    (v := fun _ _ => 1) (eta := fun _ _ => 1) (psi := fun _ _ => 0) (a0 := 0) (x0 := 0)
    (vdot := 0) (psidot := 0) (etax := 0) (psix := 0) (d := 0) (Fdot := Complex.I)
    ?_ ?_ ?_ rfl (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
    (hasDerivAt_const _ _) ?_ (by norm_num)
  · exact ((Complex.ofRealCLM.contDiff).comp contDiff_snd).add
      (((Complex.ofRealCLM.contDiff).comp contDiff_fst).const_smul Complex.I)
  · intro a x
    simpa using (hone x).add_const (Complex.I * (a : ℂ))
  · intro a x
    simpa using ((hone a).const_mul Complex.I).const_add ((x : ℂ))
  · have h := ((hone 0).const_mul Complex.I).const_add ((0 : ℝ) : ℂ)
    simpa using h.add_const (Complex.exp (Complex.I * ((0 : ℝ) : ℂ)))

end NormalVariation
