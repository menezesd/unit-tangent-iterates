import Mathlib
import UnitTangentIterates.NormalVariation
import UnitTangentIterates.SelectedInverseJacobiODE

/-!
# The transport identity for an arbitrary variation

`UnitTangentIterates/NormalVariation.lean` derives the transport identity

`η_R + ∂_x η_R = sec δ · η_F`

for a family of rears moving with a **purely normal** velocity
`∂_a R = i η e^{iΨ}`.  A path of selected rears produced by a path of fronts
does not come in that gauge: its velocity `Ṙ = Ḟ - i(Θ̇ - w) e^{iΨ}` (the
lemma *Smooth dependence of the selected rear*, `RearSmoothDependence.lean`)
has a tangential component as well, and removing it requires the
reparametrization of `NormalGauge.lean`.

This file shows that the reparametrization is not needed for the transport
identity: for a family with the general velocity

`∂_a R = (ξ + i η) e^{iΨ}`,

parametrized at the reference time by its own arclength, the tangential
component `ξ` cancels out of the front normal velocity and the identity holds
verbatim.  The reason is the first variation `Ψ̇ = ∂_xη + κ ξ` of the tangent
angle, whose extra term `κ ξ = tan δ · ξ` is exactly compensated by the
tangential contribution `-ξ sin δ` to the front normal velocity.

Main results:

* `front_normal_velocity_general` — the normal component of
  `(ξ + i w) e^{iΨ}` along the front normal `i e^{i(Ψ+δ)}` is
  `w cos δ - ξ sin δ`;
* `mixed_partial_general_variation` — the first variation formulas
  `v̇ = ∂_xξ - η ∂_xΨ`, `v Ψ̇ = ∂_xη + ξ ∂_xΨ`;
* `transport_identity_of_contDiff_general` — the transport identity for a
  `C²` family with an arbitrary variation;
* `hasDerivAt_etaR_of_general_family_arclength` — the resulting inverse Jacobi
  ODE;
* `exists_normalPath_of_general_rear_families` —
  `SelectedInverseJacobiODE.exists_normalPath_of_rear_families` with the
  normal-gauge hypothesis on the family removed.
-/

noncomputable section

open Real Complex

namespace GeneralVariation

open RearTrack SelectedInverseJacobiODE

/-! ### The frame computations -/

/-- **The normal velocity of the front for a general variation.**  The front's
unit normal is `i e^{iΘ}` with `Θ = Ψ + δ`, so the component of
`(ξ + i w) e^{iΨ}` along it is `w cos δ - ξ sin δ`. -/
theorem front_normal_velocity_general (psi d xi w : ℝ) :
    ((((xi : ℝ) : ℂ) + Complex.I * ((w : ℝ) : ℂ)) * Complex.exp (Complex.I * (psi : ℂ))
        * (starRingEnd ℂ) (Complex.I * Complex.exp (Complex.I * ((psi + d : ℝ) : ℂ)))).re
      = w * Real.cos d - xi * Real.sin d := by
  have hsplit : Complex.exp (Complex.I * ((psi + d : ℝ) : ℂ))
      = Complex.exp (Complex.I * (psi : ℂ)) * Complex.exp (Complex.I * (d : ℂ)) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  have hEE : Complex.exp (Complex.I * (psi : ℂ))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))) = 1 :=
    RearSmoothDependence.exp_mul_conj psi
  rw [hsplit]
  have hexpand : ((((xi : ℝ) : ℂ) + Complex.I * ((w : ℝ) : ℂ))
        * Complex.exp (Complex.I * (psi : ℂ)))
      * (starRingEnd ℂ) (Complex.I * (Complex.exp (Complex.I * (psi : ℂ))
        * Complex.exp (Complex.I * (d : ℂ))))
      = ((((xi : ℝ) : ℂ) + Complex.I * ((w : ℝ) : ℂ)) * (-Complex.I))
        * (Complex.exp (Complex.I * (psi : ℂ))
          * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))))
        * (starRingEnd ℂ) (Complex.exp (Complex.I * (d : ℂ))) := by
    simp only [map_mul, Complex.conj_I]
    ring
  rw [hexpand, hEE]
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
  simp only [mul_one]
  simp [Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re, Complex.cos_ofReal_re]
  ring

/-- **The first variation of a general deformation.**  If a family of curves
has velocity `∂_x R = v e^{iΨ}` and moves with `∂_a R = (ξ + i η) e^{iΨ}`, the
equality of the mixed partial derivatives says that the speed varies at rate
`∂_xξ - η ∂_xΨ` and that the tangent angle rotates at rate
`(∂_xη + ξ ∂_xΨ)/v`. -/
theorem mixed_partial_general_variation
    {psi vdot v psidot xix etax xi eta psix : ℝ}
    (h : (vdot : ℂ) * Complex.exp (Complex.I * (psi : ℂ))
        + Complex.I * ((v * psidot : ℝ) : ℂ) * Complex.exp (Complex.I * (psi : ℂ))
      = ((xix : ℂ) + Complex.I * (etax : ℂ)) * Complex.exp (Complex.I * (psi : ℂ))
        + ((xi : ℂ) + Complex.I * (eta : ℂ)) * (Complex.I * (psix : ℂ))
          * Complex.exp (Complex.I * (psi : ℂ))) :
    vdot = xix - eta * psix ∧ v * psidot = etax + xi * psix := by
  refine NormalVariation.eq_of_frame_eq (psi := psi) ?_
  push_cast at h ⊢
  linear_combination h
    + (Complex.exp (Complex.I * (psi : ℂ)) * (eta : ℂ) * (psix : ℂ)) * Complex.I_sq

/-- **The hypothesis of `mixed_partial_general_variation` holds for a `C²`
family.**  Clairaut's theorem applied to a `C²` family `R(a,x)` with
`∂_x R = v e^{iΨ}` and `∂_a R = (ξ + i η) e^{iΨ}`. -/
theorem mixed_partial_of_frame_general
    {R : ℝ → ℝ → ℂ} {v xi eta psi : ℝ → ℝ → ℝ} {a0 x0 vdot psidot xix etax psix : ℝ}
    (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (((xi a x : ℂ) + Complex.I * (eta a x : ℂ))
        * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hv : HasDerivAt (fun a' => v a' x0) vdot a0)
    (hpsia : HasDerivAt (fun a' => psi a' x0) psidot a0)
    (hxi : HasDerivAt (fun x' => xi a0 x') xix x0)
    (heta : HasDerivAt (fun x' => eta a0 x') etax x0)
    (hpsix : HasDerivAt (fun x' => psi a0 x') psix x0) :
    (vdot : ℂ) * Complex.exp (Complex.I * (psi a0 x0 : ℂ))
        + Complex.I * ((v a0 x0 * psidot : ℝ) : ℂ)
          * Complex.exp (Complex.I * (psi a0 x0 : ℂ))
      = ((xix : ℂ) + Complex.I * (etax : ℂ)) * Complex.exp (Complex.I * (psi a0 x0 : ℂ))
        + ((xi a0 x0 : ℂ) + Complex.I * (eta a0 x0 : ℂ)) * (Complex.I * (psix : ℂ))
          * Complex.exp (Complex.I * (psi a0 x0 : ℂ)) := by
  have hclair := MixedPartials.deriv_partial_comm hR a0 x0
  have hLfun : (fun a' => deriv (fun x' => R a' x') x0)
      = fun a' => (v a' x0 : ℂ) * Complex.exp (Complex.I * (psi a' x0 : ℂ)) := by
    funext a'; exact (hx a' x0).deriv
  have hRfun : (fun x' => deriv (fun a' => R a' x') a0)
      = fun x' => ((xi a0 x' : ℂ) + Complex.I * (eta a0 x' : ℂ))
          * Complex.exp (Complex.I * (psi a0 x' : ℂ)) := by
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
      (fun x' => ((xi a0 x' : ℂ) + Complex.I * (eta a0 x' : ℂ))
        * Complex.exp (Complex.I * (psi a0 x' : ℂ)))
      ((((xix : ℝ) : ℂ) + Complex.I * ((etax : ℝ) : ℂ))
          * Complex.exp (Complex.I * (psi a0 x0 : ℂ))
        + ((xi a0 x0 : ℂ) + Complex.I * (eta a0 x0 : ℂ))
          * (Complex.exp (Complex.I * (psi a0 x0 : ℂ))
            * (Complex.I * ((psix : ℝ) : ℂ)))) x0 := by
    have hxc : HasDerivAt (fun x' => ((xi a0 x' : ℝ) : ℂ)) ((xix : ℝ) : ℂ) x0 := by
      simpa using hxi.ofReal_comp
    have hec : HasDerivAt (fun x' => Complex.I * ((eta a0 x' : ℝ) : ℂ))
        (Complex.I * ((etax : ℝ) : ℂ)) x0 := by
      simpa using (heta.ofReal_comp).const_mul Complex.I
    have hpc : HasDerivAt (fun x' => Complex.I * ((psi a0 x' : ℝ) : ℂ))
        (Complex.I * ((psix : ℝ) : ℂ)) x0 := by
      simpa using (hpsix.ofReal_comp).const_mul Complex.I
    exact (hxc.add hec).mul hpc.cexp
  rw [dL.deriv, dR.deriv] at hclair
  push_cast
  linear_combination hclair

/-! ### The transport identity -/

/-- **A general variation of the rear pushes the front along
`(ξ + i(η + Ψ̇)) e^{iΨ}`.** -/
theorem hasDerivAt_front_of_general_rear
    {R : ℝ → ℂ} {psi : ℝ → ℝ} {a0 xi eta p : ℝ}
    (hR : HasDerivAt R (((xi : ℂ) + Complex.I * (eta : ℂ))
      * Complex.exp (Complex.I * (psi a0 : ℂ))) a0)
    (hpsi : HasDerivAt psi p a0) :
    HasDerivAt (fun a => R a + Complex.exp (Complex.I * (psi a : ℂ)))
      (((xi : ℂ) + Complex.I * ((eta + p : ℝ) : ℂ))
        * Complex.exp (Complex.I * (psi a0 : ℂ))) a0 := by
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

/-- **The transport identity for an arbitrary variation.**  For a `C²` family
`R(a,x)` with `∂_x R = v e^{iΨ}` and `∂_a R = (ξ + i η) e^{iΨ}`, parametrized at
the reference time by its own arclength (`v(a₀,x₀) = 1`) and whose curvature at
the point is the rear curvature `∂_xΨ = tan δ`, the tangential component `ξ`
drops out and

`η + ∂_x η = sec δ · η_F`,

with `η_F` the normal velocity of the front `F = R + e^{iΨ}`. -/
theorem transport_identity_of_contDiff_general
    {R : ℝ → ℝ → ℂ} {v xi eta psi : ℝ → ℝ → ℝ} {Fdot : ℂ}
    {a0 x0 vdot psidot xix etax psix d : ℝ}
    (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (((xi a x : ℂ) + Complex.I * (eta a x : ℂ))
        * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hunit : v a0 x0 = 1)
    (hv : HasDerivAt (fun a' => v a' x0) vdot a0)
    (hpsia : HasDerivAt (fun a' => psi a' x0) psidot a0)
    (hxi : HasDerivAt (fun x' => xi a0 x') xix x0)
    (heta : HasDerivAt (fun x' => eta a0 x') etax x0)
    (hpsix : HasDerivAt (fun x' => psi a0 x') psix x0)
    (hF : HasDerivAt (fun a => R a x0 + Complex.exp (Complex.I * (psi a x0 : ℂ))) Fdot a0)
    (hcos : Real.cos d ≠ 0) (hcurv : psix = Real.tan d) :
    eta a0 x0 + etax
      = frontNormalVelocity Fdot (psi a0 x0) d / Real.cos d := by
  have hmix := mixed_partial_of_frame_general hR hx ha hv hpsia hxi heta hpsix
  rw [hunit] at hmix
  have hpsidot : psidot = etax + xi a0 x0 * psix := by
    have := (mixed_partial_general_variation (v := 1) hmix).2
    simpa using this
  have hFd : Fdot = (((xi a0 x0 : ℝ) : ℂ) + Complex.I * ((eta a0 x0 + psidot : ℝ) : ℂ))
      * Complex.exp (Complex.I * (psi a0 x0 : ℂ)) :=
    hF.unique (hasDerivAt_front_of_general_rear (R := fun a => R a x0)
      (psi := fun a => psi a x0) (ha a0 x0) hpsia)
  have hfnv : frontNormalVelocity Fdot (psi a0 x0) d
      = (eta a0 x0 + psidot) * Real.cos d - xi a0 x0 * Real.sin d := by
    rw [frontNormalVelocity, hFd]
    exact front_normal_velocity_general (psi a0 x0) d (xi a0 x0) (eta a0 x0 + psidot)
  have htan : Real.sin d = Real.tan d * Real.cos d := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  rw [hfnv, hpsidot, hcurv, htan]
  field_simp
  ring

/-! ### The inverse Jacobi ODE and the normal path -/

/-- **The inverse Jacobi ODE for a `C²` family with an arbitrary variation**,
with the front normal velocity expressed in front arclength through the
change of variable `sf`. -/
theorem hasDerivAt_etaR_of_general_family_arclength
    {R : ℝ → ℝ → ℂ} {v xi eta psi : ℝ → ℝ → ℝ}
    {Fdot : ℝ → ℂ} {a0 : ℝ} {vdot psidot xix etax psix : ℝ → ℝ}
    {etaF sf delta : ℝ → ℝ}
    (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (((xi a x : ℂ) + Complex.I * (eta a x : ℂ))
        * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hunit : ∀ x, v a0 x = 1)
    (hv : ∀ x, HasDerivAt (fun a' => v a' x) (vdot x) a0)
    (hpsia : ∀ x, HasDerivAt (fun a' => psi a' x) (psidot x) a0)
    (hxi : ∀ x, HasDerivAt (fun x' => xi a0 x') (xix x) x)
    (heta : ∀ x, HasDerivAt (fun x' => eta a0 x') (etax x) x)
    (hpsix : ∀ x, HasDerivAt (fun x' => psi a0 x') (psix x) x)
    (hF : ∀ x, HasDerivAt (fun a => R a x + Complex.exp (Complex.I * (psi a x : ℂ)))
      (Fdot x) a0)
    (hcos : ∀ x, Real.cos (delta (sf x)) ≠ 0)
    (hcurv : ∀ x, psix x = Real.tan (delta (sf x)))
    (hlink : ∀ x, frontNormalVelocity (Fdot x) (psi a0 x) (delta (sf x)) = etaF (sf x))
    (x : ℝ) :
    HasDerivAt (fun x' => eta a0 x')
      (etaF (sf x) / Real.cos (delta (sf x)) - eta a0 x) x := by
  have htr : ∀ y, eta a0 y + etax y
      = etaF (sf y) / Real.cos (delta (sf y)) := by
    intro y
    have h := transport_identity_of_contDiff_general (d := delta (sf y)) hR hx ha
      (hunit y) (hv y) (hpsia y) (hxi y) (heta y) (hpsix y) (hF y) (hcos y) (hcurv y)
    rwa [hlink y] at h
  exact NormalVariation.hasDerivAt_etaR_of_transport heta htr x

/-- **The normal path of selected rears from a family with an arbitrary
variation.**  This is
`SelectedInverseJacobiODE.exists_normalPath_of_rear_families` with the
normal-gauge hypothesis on the family of rears removed: the family is only
required to be `C²`, parametrized by its own arclength at each reference time,
and to move with *some* velocity `(ξ + iη)e^{iΨ}` whose tangent-angle
derivative is the rear curvature `tan δ`.  The normal velocity `η` of the rear
still solves the inverse Jacobi ODE, so the conclusion is unchanged. -/
theorem exists_normalPath_of_general_rear_families {p q p' q' : MarkedSpace.Data}
    (Γ : PathMetric.NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs sf : ℝ → ℝ → ℝ}
    {R : ℝ → ℝ → ℝ → ℂ} {v xi eta psi : ℝ → ℝ → ℝ → ℝ} {Fdot : ℝ → ℝ → ℂ}
    {vdot psidot xix etax psix : ℝ → ℝ → ℝ}
    {XR : ℝ → ℝ → ℂ} {nuR : ℝ → ℝ → ℂ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    -- the `C²` family of rears, with an arbitrary variation
    (hR : ∀ t, ContDiff ℝ 2 (Function.uncurry (R t)))
    (hx : ∀ t a x, HasDerivAt (fun x' => R t a x')
      ((v t a x : ℂ) * Complex.exp (Complex.I * (psi t a x : ℂ))) x)
    (ha : ∀ t a x, HasDerivAt (fun a' => R t a' x)
      (((xi t a x : ℂ) + Complex.I * (eta t a x : ℂ))
        * Complex.exp (Complex.I * (psi t a x : ℂ))) a)
    (hunit : ∀ t x, v t t x = 1)
    (hv : ∀ t x, HasDerivAt (fun a' => v t a' x) (vdot t x) t)
    (hpsia : ∀ t x, HasDerivAt (fun a' => psi t a' x) (psidot t x) t)
    (hxi : ∀ t x, HasDerivAt (fun x' => xi t t x') (xix t x) x)
    (heta : ∀ t x, HasDerivAt (fun x' => eta t t x') (etax t x) x)
    (hpsix : ∀ t x, HasDerivAt (fun x' => psi t t x') (psix t x) x)
    (hcurv : ∀ t x, psix t x = Real.tan (delta t (sf t x)))
    (hFd : ∀ t x, HasDerivAt (fun a => R t a x + Complex.exp (Complex.I * (psi t a x : ℂ)))
      (Fdot t x) t)
    (hnormal : ∀ t x,
      frontNormalVelocity (Fdot t x) (psi t t x) (delta t (sf t x)) = etaF t (sf t x))
    (hetaRper : ∀ t, Function.Periodic (fun x => eta t t x)
      (rearArclength (delta t) (P t)))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u)
      ((eta t t (rearArclength (delta t) (P t) * u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t =>
      (eta t t (rearArclength (delta t) (P t) * u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1) :
    ∃ Δ : PathMetric.NormalPath p' q', Δ.T = Γ.T ∧
      PathMetric.NormalPath.cost Δ = PathMetricJacobi.jacobiConst
        (SelectedInversePathGeometry.uconstW P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (SelectedInversePathGeometry.uconst0 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (SelectedInversePathGeometry.uconst1 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (SelectedInversePathGeometry.uconst2 P0 P1 (Real.sqrt (1 - kh ^ 2)) kh)
        * PathMetric.NormalPath.cost Γ := by
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcos : ∀ t x, Real.cos (delta t (sf t x)) ≠ 0 := by
    intro t x
    have h := Shadowing.cos_ge_of_mem_strip (hstrip0 t (sf t x)) (hstrip1 t (sf t x))
    exact ne_of_gt (lt_of_lt_of_le hcpos h)
  have hetaR : ∀ t x, HasDerivAt (fun x' => eta t t x')
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - eta t t x) x := fun t x =>
    hasDerivAt_etaR_of_general_family_arclength (hR t) (hx t) (ha t) (hunit t) (hv t)
      (hpsia t) (hxi t) (heta t) (hpsix t) (hFd t) (hcos t) (hcurv t) (hnormal t) x
  exact SelectedInversePathGeometry.exists_normalPath_of_geometry Γ hP0 hkh0 hkh1 hPl hPu
    hsteer hstrip0 hstrip1 hdper hK hetaFd hetaFsc hetaFper hsfinv hetaR hetaRper hlink
    hstart hfinish hderiv hcont hnu

/-- The hypotheses of `hasDerivAt_etaR_of_general_family_arclength` are
consistent, with a **nonzero tangential component**: the horizontal line
`R(a,x) = x + a` sliding along itself has `v = 1`, `Ψ = 0`, `ξ = 1`, `η = 0`,
and the front `F = R + 1` slides with it, so its normal velocity vanishes and
the ODE reads `0 = 0 - 0`. -/
example : HasDerivAt (fun _ : ℝ => (0:ℝ)) ((0:ℝ) / Real.cos 0 - 0) 0 := by
  have hone : ∀ x : ℝ, HasDerivAt (fun x' : ℝ => ((x' : ℝ) : ℂ)) 1 x := fun x => by
    simpa using (hasDerivAt_id x).ofReal_comp
  refine hasDerivAt_etaR_of_general_family_arclength
    (R := fun a x => ((x : ℂ) + (a : ℂ)))
    (v := fun _ _ => 1) (xi := fun _ _ => 1) (eta := fun _ _ => 0) (psi := fun _ _ => 0)
    (a0 := 0) (vdot := fun _ => 0) (psidot := fun _ => 0) (xix := fun _ => 0)
    (etax := fun _ => 0) (psix := fun _ => 0) (Fdot := fun _ => 1)
    (etaF := fun _ => 0) (sf := id) (delta := fun _ => 0)
    ?_ ?_ ?_ (fun _ => rfl) (fun _ => hasDerivAt_const _ _) (fun _ => hasDerivAt_const _ _)
    (fun _ => hasDerivAt_const _ _) (fun _ => hasDerivAt_const _ _)
    (fun _ => hasDerivAt_const _ _) ?_ (fun _ => by norm_num) (fun _ => by simp) ?_ 0
  · exact ((Complex.ofRealCLM.contDiff).comp contDiff_snd).add
      ((Complex.ofRealCLM.contDiff).comp contDiff_fst)
  · intro a x
    simpa using (hone x).add_const ((a : ℂ))
  · intro a x
    simpa using (hone a).const_add ((x : ℂ))
  · intro x
    have h := (hone 0).const_add ((x : ℝ) : ℂ)
    simpa using h.add_const (Complex.exp (Complex.I * ((0 : ℝ) : ℂ)))
  · intro x
    simp [frontNormalVelocity, Complex.conj_I]

end GeneralVariation
