import Mathlib
import UnitTangentIterates.NormalVariation
import UnitTangentIterates.SelectedInversePathGeometry

/-!
# The inverse Jacobi ODE for a `C²` family of rears

`UnitTangentIterates/SelectedInversePathGeometry.lean` produces the normal path of
selected rears from the geometry of one slice, but still *assumes* the inverse
Jacobi ODE

`η_R' = sec δ · η_F ∘ sf − η_R`

for the rear normal velocity.  `UnitTangentIterates/NormalVariation.lean` proves the
transport identity `η_R + ∂_x η_R = sec δ · η_F` behind it, at one point, for a
`C²` family of curves in the moving frame.  This file joins the two: for a `C²`
family of rears `R(a, x)`, parametrized at the reference time by its own
arclength, moving with purely normal velocity `η`, whose front
`F = R + e^{iΨ}` moves with velocity `Ḟ`, the rear normal velocity solves the
inverse Jacobi ODE at **every** rear arclength, hence is admissible in the
hypothesis `hetaR` of
`SelectedInversePathGeometry.exists_normalPath_of_geometry`.

* `frontNormalVelocity` — the normal component `⟨Ḟ, i e^{i(Ψ+δ)}⟩` of the front
  velocity, the quantity the path metric of the front measures;
* `hasDerivAt_etaR_of_family` — the inverse Jacobi ODE for the family;
* `hasDerivAt_etaR_of_family_arclength` — the same, with the front normal
  velocity given in front arclength through the change of variable `sf`.
-/

noncomputable section

open Set MeasureTheory RearTrack

namespace SelectedInverseJacobiODE

/-- The normal velocity of the front: the component of the front velocity `Ḟ`
along the front unit normal `i e^{i(Ψ+δ)}`. -/
def frontNormalVelocity (Fdot : ℂ) (psi d : ℝ) : ℝ :=
  (Fdot * (starRingEnd ℂ) (Complex.I * Complex.exp (Complex.I * ((psi + d : ℝ) : ℂ)))).re

/-- **The inverse Jacobi ODE for a `C²` family of rears.**  Let `R(a, x)` be a
`C²` family of curves with `∂_x R = v e^{iΨ}` and `∂_a R = i η e^{iΨ}` — that
is, moving with purely normal velocity `η` — parametrized at the reference time
`a₀` by its own arclength (`v(a₀, ·) = 1`), and let the corresponding front
`F = R + e^{iΨ}` move with velocity `Ḟ`.  If `δ` is the steering angle, so that
the front unit normal is `i e^{i(Ψ+δ)}`, then the rear normal velocity solves

`η' = sec δ · η_F − η`,

the ODE driving the inverse Jacobi estimates. -/
theorem hasDerivAt_etaR_of_family {R : ℝ → ℝ → ℂ} {v eta psi : ℝ → ℝ → ℝ}
    {Fdot : ℝ → ℂ} {a0 : ℝ} {vdot psidot etax psix d : ℝ → ℝ}
    (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (Complex.I * (eta a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hunit : ∀ x, v a0 x = 1)
    (hv : ∀ x, HasDerivAt (fun a' => v a' x) (vdot x) a0)
    (hpsia : ∀ x, HasDerivAt (fun a' => psi a' x) (psidot x) a0)
    (heta : ∀ x, HasDerivAt (fun x' => eta a0 x') (etax x) x)
    (hpsix : ∀ x, HasDerivAt (fun x' => psi a0 x') (psix x) x)
    (hF : ∀ x, HasDerivAt (fun a => R a x + Complex.exp (Complex.I * (psi a x : ℂ)))
      (Fdot x) a0)
    (hcos : ∀ x, Real.cos (d x) ≠ 0) (x : ℝ) :
    HasDerivAt (fun x' => eta a0 x')
      (frontNormalVelocity (Fdot x) (psi a0 x) (d x) / Real.cos (d x) - eta a0 x) x := by
  have htr : ∀ y, eta a0 y + etax y
      = frontNormalVelocity (Fdot y) (psi a0 y) (d y) / Real.cos (d y) := fun y =>
    NormalVariation.transport_identity_of_contDiff hR hx ha (hunit y) (hv y) (hpsia y)
      (heta y) (hpsix y) (hF y) (hcos y)
  exact NormalVariation.hasDerivAt_etaR_of_transport heta htr x

/-- The same ODE with the front normal velocity expressed in **front
arclength**: if `sf` is the inverse of the rear arclength and `η_F` is the
front normal velocity as a function of front arclength, the rear normal
velocity solves `η' = sec δ · η_F ∘ sf − η`, which is exactly the hypothesis
`hetaR` of
`SelectedInversePathGeometry.exists_normalPath_of_geometry`. -/
theorem hasDerivAt_etaR_of_family_arclength {R : ℝ → ℝ → ℂ} {v eta psi : ℝ → ℝ → ℝ}
    {Fdot : ℝ → ℂ} {a0 : ℝ} {vdot psidot etax psix : ℝ → ℝ} {etaF sf delta : ℝ → ℝ}
    (hR : ContDiff ℝ 2 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (Complex.I * (eta a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hunit : ∀ x, v a0 x = 1)
    (hv : ∀ x, HasDerivAt (fun a' => v a' x) (vdot x) a0)
    (hpsia : ∀ x, HasDerivAt (fun a' => psi a' x) (psidot x) a0)
    (heta : ∀ x, HasDerivAt (fun x' => eta a0 x') (etax x) x)
    (hpsix : ∀ x, HasDerivAt (fun x' => psi a0 x') (psix x) x)
    (hF : ∀ x, HasDerivAt (fun a => R a x + Complex.exp (Complex.I * (psi a x : ℂ)))
      (Fdot x) a0)
    (hcos : ∀ x, Real.cos (delta (sf x)) ≠ 0)
    (hlink : ∀ x, frontNormalVelocity (Fdot x) (psi a0 x) (delta (sf x)) = etaF (sf x))
    (x : ℝ) :
    HasDerivAt (fun x' => eta a0 x')
      (etaF (sf x) / Real.cos (delta (sf x)) - eta a0 x) x := by
  have h := hasDerivAt_etaR_of_family (d := fun y => delta (sf y)) hR hx ha hunit hv hpsia
    heta hpsix hF hcos x
  rwa [hlink x] at h

/-- **The normal path of selected rears, with the inverse Jacobi ODE
discharged.**  This is
`SelectedInversePathGeometry.exists_normalPath_of_geometry` with its ODE
hypothesis replaced by the geometric data it comes from: a family `R t a x` of
rear curves, `C²` in the pair (path parameter, rear parameter), moving with
purely normal velocity `η`, parametrized by its own arclength at each reference
time (`v t t · = 1`), whose front `F = R + e^{iΨ}` moves with velocity `Ḟ`
whose normal component is the front normal velocity `η_F`.  Everything else is
as in `exists_normalPath_of_geometry`: the steering equation on the selected
strip, the periodicities, and two-sided bounds for the front period. -/
theorem exists_normalPath_of_rear_families {p q p' q' : MarkedSpace.Data}
    (Γ : PathMetric.NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs sf : ℝ → ℝ → ℝ}
    {R : ℝ → ℝ → ℝ → ℂ} {v eta psi : ℝ → ℝ → ℝ → ℝ} {Fdot : ℝ → ℝ → ℂ}
    {vdot psidot etax psix : ℝ → ℝ → ℝ}
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
    -- the `C²` family of rears
    (hR : ∀ t, ContDiff ℝ 2 (Function.uncurry (R t)))
    (hx : ∀ t a x, HasDerivAt (fun x' => R t a x')
      ((v t a x : ℂ) * Complex.exp (Complex.I * (psi t a x : ℂ))) x)
    (ha : ∀ t a x, HasDerivAt (fun a' => R t a' x)
      (Complex.I * (eta t a x : ℂ) * Complex.exp (Complex.I * (psi t a x : ℂ))) a)
    (hunit : ∀ t x, v t t x = 1)
    (hv : ∀ t x, HasDerivAt (fun a' => v t a' x) (vdot t x) t)
    (hpsia : ∀ t x, HasDerivAt (fun a' => psi t a' x) (psidot t x) t)
    (heta : ∀ t x, HasDerivAt (fun x' => eta t t x') (etax t x) x)
    (hpsix : ∀ t x, HasDerivAt (fun x' => psi t t x') (psix t x) x)
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
    hasDerivAt_etaR_of_family_arclength (hR t) (hx t) (ha t) (hunit t) (hv t) (hpsia t)
      (heta t) (hpsix t) (hFd t) (hcos t) (hnormal t) x
  exact SelectedInversePathGeometry.exists_normalPath_of_geometry Γ hP0 hkh0 hkh1 hPl hPu
    hsteer hstrip0 hstrip1 hdper hK hetaFd hetaFsc hetaFper hsfinv hetaR hetaRper hlink
    hstart hfinish hderiv hcont hnu

/-- The hypotheses of `hasDerivAt_etaR_of_family_arclength` are consistent and
its conclusion is not vacuous: the horizontal lines `R(a,x) = x + i a`,
translated normally at unit speed, have `v = 1`, `Ψ = 0`, `η_R = 1`, and the
front `F = R + 1` moves with normal velocity `1`, so the ODE reads `0 = 1 − 1`. -/
example : HasDerivAt (fun _ : ℝ => (1:ℝ)) ((1:ℝ) / Real.cos 0 - 1) 0 := by
  have hone : ∀ x : ℝ, HasDerivAt (fun x' : ℝ => ((x' : ℝ) : ℂ)) 1 x := fun x => by
    simpa using (hasDerivAt_id x).ofReal_comp
  refine hasDerivAt_etaR_of_family_arclength (R := fun a x => (x : ℂ) + Complex.I * (a : ℂ))
    (v := fun _ _ => 1) (eta := fun _ _ => 1) (psi := fun _ _ => 0) (a0 := 0)
    (vdot := fun _ => 0) (psidot := fun _ => 0) (etax := fun _ => 0) (psix := fun _ => 0)
    (Fdot := fun _ => Complex.I) (etaF := fun _ => 1) (sf := id) (delta := fun _ => 0)
    ?_ ?_ ?_ (fun _ => rfl) (fun _ => hasDerivAt_const _ _) (fun _ => hasDerivAt_const _ _)
    (fun _ => hasDerivAt_const _ _) (fun _ => hasDerivAt_const _ _) ?_
    (fun _ => by norm_num) ?_ 0
  · exact ((Complex.ofRealCLM.contDiff).comp contDiff_snd).add
      (((Complex.ofRealCLM.contDiff).comp contDiff_fst).const_smul Complex.I)
  · intro a x
    simpa using (hone x).add_const (Complex.I * (a : ℂ))
  · intro a x
    simpa using ((hone a).const_mul Complex.I).const_add ((x : ℂ))
  · intro x
    have h := ((hone 0).const_mul Complex.I).const_add ((x : ℝ) : ℂ)
    simpa using h.add_const (Complex.exp (Complex.I * ((0 : ℝ) : ℂ)))
  · intro x
    simp [frontNormalVelocity, Complex.conj_I]

/-- A check that the hypotheses of `exists_normalPath_of_rear_families` are
not contradictory: the constant path of fronts of curvature `1/2`, with
steering angle `arcsin(1/2)`, rear arclength `x(s) = s·cos(arcsin ½)`, a rear
family at rest and vanishing normal velocities, satisfies them all. -/
example (p p' : MarkedSpace.Data) :
    ∃ Δ : PathMetric.NormalPath p' p', Δ.T = (PathMetric.NormalPath.const p).T ∧
      PathMetric.NormalPath.cost Δ = PathMetricJacobi.jacobiConst
        (SelectedInversePathGeometry.uconstW 1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
        (SelectedInversePathGeometry.uconst0 1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
        (SelectedInversePathGeometry.uconst1 1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
        (SelectedInversePathGeometry.uconst2 1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2)) (1/2))
        * PathMetric.NormalPath.cost (PathMetric.NormalPath.const p) := by
  set A : ℝ := Real.arcsin (1/2) with hA
  have hsinA : Real.sin A = 1/2 := Real.sin_arcsin (by norm_num) (by norm_num)
  have hcosA : Real.cos A = Real.sqrt (1 - (1/2 : ℝ) ^ 2) := by
    rw [hA, Real.cos_arcsin]
  have hcosApos : 0 < Real.cos A := by
    rw [hcosA]
    exact Real.sqrt_pos.mpr (by norm_num)
  have hArc : rearArclength (fun _ : ℝ => A) = fun y => y * Real.cos A := by
    funext y
    simp [rearArclength]
  have hone : ∀ x : ℝ, HasDerivAt (fun x' : ℝ => ((x' : ℝ) : ℂ)) 1 x := fun x => by
    simpa using (hasDerivAt_id x).ofReal_comp
  refine exists_normalPath_of_rear_families (p' := p') (q' := p')
    (PathMetric.NormalPath.const p)
    (P0 := 1) (P1 := 1) (kh := 1/2) (P := fun _ => 1) (delta := fun _ _ => A)
    (K := fun _ _ => 1/2) (etaF := fun _ _ => 0) (etaFs := fun _ _ => 0)
    (sf := fun _ x => x / Real.cos A) (R := fun _ _ x => (x : ℂ))
    (v := fun _ _ _ => 1) (eta := fun _ _ _ => 0) (psi := fun _ _ _ => 0)
    (Fdot := fun _ _ => 0) (vdot := fun _ _ => 0) (psidot := fun _ _ => 0)
    (etax := fun _ _ => 0) (psix := fun _ _ => 0)
    (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    one_pos (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ s => (hasDerivAt_const s A).congr_deriv (by rw [hsinA]; ring))
    (fun _ _ => Real.arcsin_nonneg.mpr (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => rfl) (fun _ _ => by norm_num)
    (fun _ s => hasDerivAt_const s (0:ℝ)) (fun _ => continuous_const) (fun _ _ => rfl)
    (fun _ x => by rw [hArc]; field_simp)
    (fun _ => Complex.ofRealCLM.contDiff.comp contDiff_snd)
    (fun _ _ x => by simpa using hone x)
    (fun _ a x => by simpa using hasDerivAt_const a ((x : ℝ) : ℂ))
    (fun _ _ => rfl) (fun t _ => hasDerivAt_const t (1:ℝ))
    (fun t _ => hasDerivAt_const t (0:ℝ)) (fun _ x => hasDerivAt_const x (0:ℝ))
    (fun _ x => hasDerivAt_const x (0:ℝ))
    (fun t x => by simpa using hasDerivAt_const t ((x : ℝ) : ℂ))
    (fun _ _ => by simp [frontNormalVelocity])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun t u => by simpa using hasDerivAt_const t (p'.1 u))
    (fun _ => by simpa using continuous_const) (fun _ _ => by simp)

end SelectedInverseJacobiODE
