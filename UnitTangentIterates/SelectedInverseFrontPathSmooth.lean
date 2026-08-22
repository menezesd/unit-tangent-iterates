import Mathlib
import UnitTangentIterates.RearFrameRegularity
import UnitTangentIterates.SelectedInverseFrontPath

/-!
# The normal path of selected rears, from smooth dependence alone

`UnitTangentIterates/SelectedInverseFrontPath.lean` produces the normal path of
selected rears of a normal path of fronts, but assumes the differentiability of
the frame data of the rear family: the existence of its velocity `Ṙ` and the
differentiability of the speed `v`, the frame angle `Ψ` and the frame
components `ξ`, `η`.

`UnitTangentIterates/RearFrameRegularity.lean` discharges all of those from the
paper's lemma *Smooth dependence of the selected rear*.  This file states the
resulting theorem: the only regularity still assumed of the rear family is the
joint `C²` dependence `hR2` of the reparametrized rear tracks on the pair
(path parameter, arclength); everything else is now expressed in terms of the
fronts, of their tangent angles and of the selected steering angles, together
with the parameter derivatives `Ḟ`, `Θ̇`, `ẇ` of those and their arclength
derivatives.

Main result: `exists_normalPath_of_front_path_smooth`.
-/

noncomputable section

open Real Complex

namespace SelectedInverseFrontPathSmooth

open RearTrack RearFamilyFrame RearFrameRegularity SelectedInverseJacobiODE

/-- **The selected rears of a normal path of fronts form a normal path**, of
cost a uniform constant times the cost of the front path — with the frame data
of the rear family no longer assumed differentiable, but *computed* from the
smooth dependence of the front and of the selected steering angle on the path
parameter. -/
theorem exists_normalPath_of_front_path_smooth {p q p' q' : MarkedSpace.Data}
    (Γ : PathMetric.NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ}
    {F : ℝ → ℝ → ℝ → ℂ} {Θ δ K : ℝ → ℝ → ℝ → ℝ} {σ : ℝ → ℝ → ℝ}
    {Fdot : ℝ → ℝ → ℝ → ℂ} {Θdot w : ℝ → ℝ → ℝ → ℝ}
    {Fdots : ℝ → ℝ → ℂ} {Θdots ws etaFs : ℝ → ℝ → ℝ}
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
    -- smooth dependence on the path parameter
    (hFa : ∀ t a s, HasDerivAt (fun a' => F t a' s) (Fdot t a s) a)
    (hΘa : ∀ t a s, HasDerivAt (fun a' => Θ t a' s) (Θdot t a s) a)
    (hδa : ∀ t a s, HasDerivAt (fun a' => δ t a' s) (w t a s) a)
    (hFdots : ∀ t s, HasDerivAt (Fdot t t) (Fdots t s) s)
    (hΘdots : ∀ t s, HasDerivAt (Θdot t t) (Θdots t s) s)
    (hws : ∀ t s, HasDerivAt (w t t) (ws t s) s)
    -- joint regularity of the front data
    (hFc2 : ∀ t, ContDiff ℝ (2 : ℕ) (Function.uncurry (F t)))
    (hΘc2 : ∀ t, ContDiff ℝ (2 : ℕ) (Function.uncurry (Θ t)))
    (hδc2 : ∀ t, ContDiff ℝ (2 : ℕ) (Function.uncurry (δ t)))
    -- the front normal velocity, and the periodicities
    (hetaFd : ∀ t s, HasDerivAt (frontNormalVelocityAt (Fdot t) (Θ t) (δ t) t)
      (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (frontNormalVelocityAt (Fdot t) (Θ t) (δ t) t) (P t))
    (hetaRper : ∀ t, Function.Periodic
      (fun x => frameNormal (frameRdot (Fdot t) (Θdot t) (w t) (Θ t) (δ t) (σ t))
        (frameAngle (Θ t) (δ t) (σ t)) t x)
      (rearArclength (δ t t) (P t)))
    (hlink : ∀ t u, Γ.eta t u = frontNormalVelocityAt (Fdot t) (Θ t) (δ t) t (P t * u))
    -- the rear path in normal gauge
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u)
      ((frameNormal (frameRdot (Fdot t) (Θdot t) (w t) (Θ t) (δ t) (σ t))
        (frameAngle (Θ t) (δ t) (σ t)) t
        (rearArclength (δ t t) (P t) * u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t =>
      (frameNormal (frameRdot (Fdot t) (Θdot t) (w t) (Θ t) (δ t) (σ t))
        (frameAngle (Θ t) (δ t) (σ t)) t
        (rearArclength (δ t t) (P t) * u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1) :
    ∃ Δ : PathMetric.NormalPath p' q', Δ.T = Γ.T ∧
      PathMetric.NormalPath.cost Δ = PathMetricJacobi.jacobiConst
        (SelectedInversePathGeometry.uconstW P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (SelectedInversePathGeometry.uconst0 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (SelectedInversePathGeometry.uconst1 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (SelectedInversePathGeometry.uconst2 P0 P1 (Real.sqrt (1 - kh ^ 2)) kh)
        * PathMetric.NormalPath.cost Γ :=
  SelectedInverseFrontPath.exists_normalPath_of_front_path Γ
    (Rdot := fun t => frameRdot (Fdot t) (Θdot t) (w t) (Θ t) (δ t) (σ t))
    (Fdot := Fdot)
    (vdot := fun t x =>
      -(Real.sin (δ t t (σ t x)) * w t t (σ t x)) / Real.cos (δ t t (σ t x)))
    (psidot := fun t x => Θdot t t (σ t x) - w t t (σ t x))
    (xix := fun t x =>
      ((((1 / Real.cos (δ t t (σ t x)) : ℝ) : ℂ) * Fdots t (σ t x))
            * (starRingEnd ℂ)
              (Complex.exp (Complex.I * (frameAngle (Θ t) (δ t) (σ t) t x : ℂ)))).re
        + Real.tan (δ t t (σ t x))
          * (Fdot t t (σ t x)
              * (starRingEnd ℂ)
                (Complex.exp (Complex.I * (frameAngle (Θ t) (δ t) (σ t) t x : ℂ)))).im)
    (etax := fun t x =>
      ((((1 / Real.cos (δ t t (σ t x)) : ℝ) : ℂ) * Fdots t (σ t x))
            * (starRingEnd ℂ)
              (Complex.exp (Complex.I * (frameAngle (Θ t) (δ t) (σ t) t x : ℂ)))).im
        - Real.tan (δ t t (σ t x))
          * (Fdot t t (σ t x)
              * (starRingEnd ℂ)
                (Complex.exp (Complex.I * (frameAngle (Θ t) (δ t) (σ t) t x : ℂ)))).re
        - (Θdots t (σ t x) - ws t (σ t x)) * (1 / Real.cos (δ t t (σ t x))))
    hP0 hkh0 hkh1 hPl hPu hstrip0 hstrip1 hdper hK hcos hsfinv hσ hF hΘ hδ
    (fun t => hasDerivAt_rearFamily_param (hFa t) (hΘa t) (hδa t))
    hFa
    (fun t => by
      exact_mod_cast contDiff_two_rearFamily (a0 := t) (hFc2 t) (hΘc2 t) (hδc2 t)
        (hcos t) (hσ t))
    (fun t => hasDerivAt_frameSpeed_param (hδa t))
    (fun t => hasDerivAt_frameAngle_param (hΘa t) (hδa t))
    (fun t => hasDerivAt_frameTangential_rear (K := K t) (hΘ t) (hδ t) (hσ t) (hFdots t))
    (fun t => hasDerivAt_frameNormal_rear (K := K t) (hΘ t) (hδ t) (hσ t) (hFdots t)
      (hΘdots t) (hws t))
    hetaFd hetaFsc hetaFper hetaRper hlink hstart hfinish hderiv hcont hnu

/-- **The hypotheses of `exists_normalPath_of_front_path_smooth` are
consistent.**  As in `SelectedInverseFrontPath.lean`, the constant path of the
front `F(s) = -2i e^{is/2}` (a circle of radius `2`, of curvature `1/2`), with
steering angle `arcsin(1/2)`, rear arclength `x(s) = s cos(arcsin ½)` and all
parameter derivatives vanishing, satisfies them all. -/
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
  refine exists_normalPath_of_front_path_smooth (p' := p') (q' := p')
    (PathMetric.NormalPath.const p)
    (P0 := 1) (P1 := 1) (kh := 1/2) (P := fun _ => 1)
    (F := Fr) (Θ := Th) (δ := de) (K := fun _ _ _ => 1/2) (σ := sg)
    (Fdot := fun _ _ _ => 0) (Θdot := fun _ _ _ => 0) (w := fun _ _ _ => 0)
    (Fdots := fun _ _ => 0) (Θdots := fun _ _ => 0) (ws := fun _ _ => 0)
    (etaFs := fun _ _ => 0)
    (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    one_pos (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ _ => Real.arcsin_nonneg.mpr (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => rfl) (fun _ _ => by norm_num) (fun _ _ => hcosAne) ?_ ?_
    (fun _ _ s => hFront s) (fun _ _ s => by
      simpa using ((hasDerivAt_id s).div_const 2))
    (fun _ _ s => (hasDerivAt_const s A).congr_deriv (by rw [hde, hsinA]; ring))
    (fun t a s => hasDerivAt_const a (Fr t a s))
    (fun t a s => hasDerivAt_const a (Th t a s))
    (fun t a s => hasDerivAt_const a (de t a s))
    (fun _ s => hasDerivAt_const s (0 : ℂ))
    (fun _ s => hasDerivAt_const s (0 : ℝ))
    (fun _ s => hasDerivAt_const s (0 : ℝ)) ?_ ?_ ?_ ?_
    (fun _ => continuous_const) ?_ ?_ ?_ (fun _ => rfl) (fun _ => rfl) ?_ ?_
    (fun _ _ => by simp)
  · -- the inverse of the rear arclength
    intro t x
    have : rearArclength (de t t) (sg t x) = (x / Real.cos A) * Real.cos A := by
      simp [rearArclength, hde, hsg]
    rw [this]
    field_simp
  · -- the derivative of that inverse
    intro t x
    simpa [hsg, hde] using (hasDerivAt_id x).div_const (Real.cos A)
  · -- joint regularity of the front
    intro t
    have hfun : Function.uncurry (Fr t)
        = fun q : ℝ × ℝ => -2 * Complex.I
            * Complex.exp (Complex.I * ((q.2 / 2 : ℝ) : ℂ)) := by
      funext q
      simp [Function.uncurry, hFr]
    rw [hfun]
    have hbase : ContDiff ℝ (2 : ℕ) (fun q : ℝ × ℝ => ((q.2 / 2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_snd.div_const _)
    have hexp : ContDiff ℝ (2 : ℕ) Complex.exp := Complex.contDiff_exp
    exact (hexp.comp (hbase.const_smul Complex.I)).const_smul (-2 * Complex.I)
  · -- joint regularity of the tangent angle
    intro t
    have h : ContDiff ℝ (2 : ℕ) (fun q : ℝ × ℝ => q.2 / 2) := contDiff_snd.div_const 2
    simpa [Function.uncurry, hTh] using h
  · -- joint regularity of the steering angle
    intro t
    have h : ContDiff ℝ (2 : ℕ) (fun _ : ℝ × ℝ => A) := contDiff_const
    simpa [Function.uncurry, hde] using h
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
    simp [frameNormal, frameRdot]
  · -- the link with the front path
    intro t u
    simp [PathMetric.NormalPath.const, frontNormalVelocityAt, frontNormalVelocity]
  · -- the rear path is at rest
    intro t u
    have hfun : ∀ r : ℝ, frameNormal (frameRdot (fun _ _ => (0:ℂ)) (fun _ _ => (0:ℝ))
        (fun _ _ => (0:ℝ)) (Th r) (de r) (sg r))
        (frameAngle (Th r) (de r) (sg r)) r
        (rearArclength (de r r) 1 * u) = 0 := by
      intro r; simp [frameNormal, frameRdot]
    simpa [hfun] using hasDerivAt_const t (p'.1 u)
  · -- continuity of the velocity
    intro u
    have hfun : ∀ t : ℝ, frameNormal (frameRdot (fun _ _ => (0:ℂ)) (fun _ _ => (0:ℝ))
        (fun _ _ => (0:ℝ)) (Th t) (de t) (sg t))
        (frameAngle (Th t) (de t) (sg t)) t
        (rearArclength (de t t) 1 * u) = 0 := by
      intro t; simp [frameNormal, frameRdot]
    simpa [hfun] using continuous_const

end SelectedInverseFrontPathSmooth
