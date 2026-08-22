import Mathlib
import UnitTangentIterates.RearFamilyFrame

/-!
# The normal path of selected rears of a path of fronts

This file joins the two previous ones.  `RearFamilyFrame.lean` builds, from a
family of fronts and their selected steering angles, the frame data of the
family of selected rear tracks reparametrized by the rear arclength at the
reference time, and proves the inverse Jacobi ODE for its normal velocity with
no gauge assumption on the motion.  `SelectedInversePathGeometry.lean` turns
that ODE, together with the geometry of one slice, into a normal path of rears
whose cost is a uniform constant times the cost of the front path.

`exists_normalPath_of_front_path` states the combination: for a normal path of
fronts `Γ`, given

* the steering equation `δ_s = K − sin δ` on the selected strip, with the
  periodicities and two-sided bounds `0 < P₀ ≤ P t ≤ P₁` for the front period;
* the inverse `σ t` of the rear arclength of the slice `t`;
* the family of fronts `F t a s` (unit speed, tangent angle `Θ t a s`), whose
  rear tracks are jointly `C²` after the reparametrization and whose frame
  components are differentiable;
* the identification of the normal velocity of `Γ` with the front normal
  velocity, and of the endpoints of the rear path with `p'`, `q'`;

the selected rears form a normal path from `p'` to `q'` of cost
`jacobiConst (uconstW …) (uconst0 …) (uconst1 …) (uconst2 …)` times the cost of
`Γ`.  No hypothesis on the *gauge* of the motion of the rears is imposed: the
tangential component of their velocity is arbitrary.
-/

noncomputable section

open Real Complex

namespace SelectedInverseFrontPath

open RearTrack RearFamilyFrame GeneralVariation SelectedInverseJacobiODE

/-- **The selected rears of a normal path of fronts form a normal path**, of
cost a uniform constant times the cost of the front path. -/
theorem exists_normalPath_of_front_path {p q p' q' : MarkedSpace.Data}
    (Γ : PathMetric.NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ → ℂ} {Θ δ K : ℝ → ℝ → ℝ → ℝ} {σ : ℝ → ℝ → ℝ}
    {Rdot Fdot : ℝ → ℝ → ℝ → ℂ} {vdot psidot xix etax etaFs : ℝ → ℝ → ℝ}
    {XR : ℝ → ℝ → ℂ} {nuR : ℝ → ℝ → ℂ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    -- the geometry of one slice
    (hstrip0 : ∀ t s, 0 ≤ δ t t s) (hstrip1 : ∀ t s, δ t t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t t) (P t))
    (hK : ∀ t s, |K t t s| ≤ kh)
    (hcos : ∀ t y, Real.cos (δ t t y) ≠ 0)
    (hsfinv : ∀ t x, rearArclength (δ t t) (σ t x) = x)
    (hσ : ∀ t x, HasDerivAt (σ t) (1 / Real.cos (δ t t (σ t x))) x)
    -- the family of fronts and its selected steering angles
    (hF : ∀ t a s, HasDerivAt (F t a) (Complex.exp (Complex.I * (Θ t a s : ℂ))) s)
    (hΘ : ∀ t a s, HasDerivAt (Θ t a) (K t a s) s)
    (hδ : ∀ t a s, HasDerivAt (δ t a) (K t a s - Real.sin (δ t a s)) s)
    (hRa : ∀ t a x,
      HasDerivAt (fun a' => rearFamily (F t) (Θ t) (δ t) (σ t) a' x) (Rdot t a x) a)
    (hFa : ∀ t a s, HasDerivAt (fun a' => F t a' s) (Fdot t a s) a)
    (hR2 : ∀ t, ContDiff ℝ 2 (Function.uncurry (rearFamily (F t) (Θ t) (δ t) (σ t))))
    (hv : ∀ t x, HasDerivAt (fun a' => frameSpeed (δ t) (σ t) t a' x) (vdot t x) t)
    (hpsia : ∀ t x, HasDerivAt (fun a' => frameAngle (Θ t) (δ t) (σ t) a' x) (psidot t x) t)
    (hxi : ∀ t x, HasDerivAt
      (fun x' => frameTangential (Rdot t) (frameAngle (Θ t) (δ t) (σ t)) t x') (xix t x) x)
    (heta : ∀ t x, HasDerivAt
      (fun x' => frameNormal (Rdot t) (frameAngle (Θ t) (δ t) (σ t)) t x') (etax t x) x)
    -- the front normal velocity, and the periodicities
    (hetaFd : ∀ t s, HasDerivAt (frontNormalVelocityAt (Fdot t) (Θ t) (δ t) t)
      (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (frontNormalVelocityAt (Fdot t) (Θ t) (δ t) t) (P t))
    (hetaRper : ∀ t, Function.Periodic
      (fun x => frameNormal (Rdot t) (frameAngle (Θ t) (δ t) (σ t)) t x)
      (rearArclength (δ t t) (P t)))
    (hlink : ∀ t u, Γ.eta t u = frontNormalVelocityAt (Fdot t) (Θ t) (δ t) t (P t * u))
    -- the rear path in normal gauge
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u)
      ((frameNormal (Rdot t) (frameAngle (Θ t) (δ t) (σ t)) t
        (rearArclength (δ t t) (P t) * u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t =>
      (frameNormal (Rdot t) (frameAngle (Θ t) (δ t) (σ t)) t
        (rearArclength (δ t t) (P t) * u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1) :
    ∃ Δ : PathMetric.NormalPath p' q', Δ.T = Γ.T ∧
      PathMetric.NormalPath.cost Δ = PathMetricJacobi.jacobiConst
        (SelectedInversePathGeometry.uconstW P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (SelectedInversePathGeometry.uconst0 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (SelectedInversePathGeometry.uconst1 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (SelectedInversePathGeometry.uconst2 P0 P1 (Real.sqrt (1 - kh ^ 2)) kh)
        * PathMetric.NormalPath.cost Γ :=
  exists_normalPath_of_general_rear_families Γ
    (P := P) (delta := fun t => δ t t) (K := fun t => K t t)
    (etaF := fun t => frontNormalVelocityAt (Fdot t) (Θ t) (δ t) t) (etaFs := etaFs)
    (sf := σ) (R := fun t => rearFamily (F t) (Θ t) (δ t) (σ t))
    (v := fun t => frameSpeed (δ t) (σ t) t)
    (xi := fun t => frameTangential (Rdot t) (frameAngle (Θ t) (δ t) (σ t)))
    (eta := fun t => frameNormal (Rdot t) (frameAngle (Θ t) (δ t) (σ t)))
    (psi := fun t => frameAngle (Θ t) (δ t) (σ t))
    (Fdot := fun t x => Fdot t t (σ t x)) (vdot := vdot) (psidot := psidot)
    (xix := xix) (etax := etax) (psix := fun t x => Real.tan (δ t t (σ t x)))
    (XR := XR) (nuR := nuR)
    hP0 hkh0 hkh1 hPl hPu (fun t s => hδ t t s) hstrip0 hstrip1 hdper hK
    hetaFd hetaFsc hetaFper hsfinv
    hR2
    (fun t => hasDerivAt_rearFamily_space (hF t) (hΘ t) (hδ t) (hσ t))
    (fun t => hasDerivAt_rearFamily_time (hRa t))
    (fun t => frameSpeed_reference (hcos t)) hv hpsia hxi heta
    (fun t => hasDerivAt_frameAngle_space (K := K t) (hΘ t) (hδ t) (hσ t))
    (fun _ _ => rfl)
    (fun t => hasDerivAt_front_time (hFa t) t)
    (fun _ _ => rfl) hetaRper hlink hstart hfinish hderiv hcont hnu

/-- **The hypotheses of `exists_normalPath_of_front_path` are consistent.**
The constant path of the front `F(s) = -2i e^{is/2}` (a circle of radius `2`,
of curvature `1/2`), with steering angle `arcsin(1/2)`, rear arclength
`x(s) = s cos(arcsin ½)`, a rear family at rest and vanishing normal
velocities, satisfies them all. -/
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
  have hcosA : Real.cos A = Real.sqrt (1 - (1/2 : ℝ) ^ 2) := by rw [hA, Real.cos_arcsin]
  have hcosApos : 0 < Real.cos A := by
    rw [hcosA]; exact Real.sqrt_pos.mpr (by norm_num)
  have hcosAne : Real.cos A ≠ 0 := ne_of_gt hcosApos
  -- the data
  set Fr : ℝ → ℝ → ℝ → ℂ :=
    fun _ _ s => -2 * Complex.I * Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ)) with hFr
  set Th : ℝ → ℝ → ℝ → ℝ := fun _ _ s => s / 2 with hTh
  set de : ℝ → ℝ → ℝ → ℝ := fun _ _ _ => A with hde
  set sg : ℝ → ℝ → ℝ := fun _ x => x / Real.cos A with hsg
  have hFront : ∀ s : ℝ, HasDerivAt (fun s' : ℝ => -2 * Complex.I
      * Complex.exp (Complex.I * ((s' / 2 : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ))) s := by
    intro s
    have hlin : HasDerivAt (fun s' : ℝ => Complex.I * ((s' / 2 : ℝ) : ℂ))
        (Complex.I * (1 / 2 : ℂ)) s := by
      have h : HasDerivAt (fun s' : ℝ => ((s' / 2 : ℝ) : ℂ)) ((1 / 2 : ℂ)) s := by
        simpa using (((hasDerivAt_id s).div_const 2).ofReal_comp)
      simpa using h.const_mul Complex.I
    have hexp := hlin.cexp
    have := hexp.const_mul (-2 * Complex.I)
    refine this.congr_deriv ?_
    have : Complex.I * (Complex.I * (1/2 : ℂ)) = -(1/2 : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I]; ring
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  refine exists_normalPath_of_front_path (p' := p') (q' := p')
    (PathMetric.NormalPath.const p)
    (P0 := 1) (P1 := 1) (kh := 1/2) (P := fun _ => 1)
    (F := Fr) (Θ := Th) (δ := de) (K := fun _ _ _ => 1/2) (σ := sg)
    (Rdot := fun _ _ _ => 0) (Fdot := fun _ _ _ => 0)
    (vdot := fun _ _ => 0) (psidot := fun _ _ => 0) (xix := fun _ _ => 0)
    (etax := fun _ _ => 0) (etaFs := fun _ _ => 0)
    (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    one_pos (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ _ => Real.arcsin_nonneg.mpr (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => rfl) (fun _ _ => by norm_num) (fun _ _ => hcosAne) ?_ ?_
    (fun _ _ s => hFront s) (fun _ _ s => by
      simpa using ((hasDerivAt_id s).div_const 2))
    (fun _ _ s => (hasDerivAt_const s A).congr_deriv (by rw [hde, hsinA]; ring))
    (fun t a x => hasDerivAt_const a (rearFamily (Fr t) (Th t) (de t) (sg t) a x))
    (fun t a s => hasDerivAt_const a (Fr t a s)) ?_
    (fun t x => hasDerivAt_const t (frameSpeed (de t) (sg t) t t x))
    (fun t x => hasDerivAt_const t (frameAngle (Th t) (de t) (sg t) t x)) ?_ ?_ ?_
    (fun _ => continuous_const) ?_ ?_ ?_ (fun _ => rfl) (fun _ => rfl) ?_ ?_ (fun _ _ => by simp)
  · -- the inverse of the rear arclength
    intro t x
    have : rearArclength (de t t) (sg t x) = (x / Real.cos A) * Real.cos A := by
      simp [rearArclength, hde, hsg]
    rw [this]
    field_simp
  · -- the derivative of that inverse
    intro t x
    simpa [hsg, hde] using (hasDerivAt_id x).div_const (Real.cos A)
  · -- joint regularity of the rear family
    intro t
    have hfun : Function.uncurry (rearFamily (Fr t) (Th t) (de t) (sg t))
        = fun q : ℝ × ℝ => -2 * Complex.I
            * Complex.exp (Complex.I * ((q.2 / Real.cos A / 2 : ℝ) : ℂ))
          - Complex.exp (Complex.I * ((q.2 / Real.cos A / 2 - A : ℝ) : ℂ)) := by
      funext q
      simp [Function.uncurry, rearFamily, rearTrack, rearAngle, hFr, hTh, hde, hsg]
    rw [hfun]
    have hbase : ContDiff ℝ 2 (fun q : ℝ × ℝ => ((q.2 / Real.cos A / 2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (((contDiff_snd.div_const _).div_const _))
    have hbase' : ContDiff ℝ 2 (fun q : ℝ × ℝ => ((q.2 / Real.cos A / 2 - A : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        ((((contDiff_snd.div_const _).div_const _)).sub contDiff_const)
    have hexp : ContDiff ℝ 2 Complex.exp := Complex.contDiff_exp
    exact ((hexp.comp (hbase.const_smul Complex.I)).const_smul (-2 * Complex.I)).sub
      (hexp.comp (hbase'.const_smul Complex.I))
  · -- the tangential component vanishes
    intro t x
    have hfun : (fun x' => frameTangential (fun _ _ => (0:ℂ))
        (frameAngle (Th t) (de t) (sg t)) t x') = fun _ => (0:ℝ) := by
      funext x'; simp [frameTangential]
    rw [hfun]
    exact hasDerivAt_const x (0:ℝ)
  · -- the normal component vanishes
    intro t x
    have hfun : (fun x' => frameNormal (fun _ _ => (0:ℂ))
        (frameAngle (Th t) (de t) (sg t)) t x') = fun _ => (0:ℝ) := by
      funext x'; simp [frameNormal]
    rw [hfun]
    exact hasDerivAt_const x (0:ℝ)
  · -- the front normal velocity vanishes
    intro t s
    have hfun : frontNormalVelocityAt (fun _ _ => (0:ℂ)) (Th t) (de t) t
        = fun _ => (0:ℝ) := by
      funext s'; simp [frontNormalVelocityAt, frontNormalVelocity]
    rw [hfun]
    exact hasDerivAt_const s (0:ℝ)
  · -- its periodicity
    intro t s
    simp [frontNormalVelocityAt, frontNormalVelocity]
  · -- periodicity of the rear normal velocity
    intro t x
    simp [frameNormal]
  · -- the link with the front path
    intro t u
    simp [PathMetric.NormalPath.const, frontNormalVelocityAt, frontNormalVelocity]
  · -- the rear path is at rest
    intro t u
    have hfun : (fun x' => frameNormal (fun _ _ => (0:ℂ))
        (frameAngle (Th t) (de t) (sg t)) t x') = fun _ => (0:ℝ) := by
      funext x'; simp [frameNormal]
    simpa [hfun] using hasDerivAt_const t (p'.1 u)
  · -- continuity of the velocity
    intro u
    have hfun : ∀ t : ℝ, frameNormal (fun _ _ => (0:ℂ))
        (frameAngle (Th t) (de t) (sg t)) t
        (rearArclength (de t t) 1 * u) = 0 := by
      intro t; simp [frameNormal]
    simpa [hfun] using continuous_const

end SelectedInverseFrontPath
