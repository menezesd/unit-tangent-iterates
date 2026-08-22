import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfRearFamily
import UnitTangentIterates.GaugeFlowVariableSpeedPathCircle

/-!
# Non-vacuity of the rear-family assembly

`GaugeMarkedDataOfRearFamily.exists_variableSpeed_normalPath_of_rearFamily`
carries a long hypothesis block: the geometry of the family of selected rears,
the inverse Jacobi ODE of its normal rate, and two numerical conditions
relating the constants `κ̂`, `c`, `d`, `r`, `k_x` and `P₀`.  This file exhibits a
configuration satisfying all of it at once, so that the block is consistent.

The configuration is the selected rear of a **circle of radius `2`**, at rest.
It is a genuine selected-rear configuration and not a degenerate one: the front
has curvature `K ≡ 1/2`, the steering angle is the constant `δ = π/6` solving
`sin δ = K` (so the rear track really is the selected one), the rear curvature
`tan δ = 1/√3` is not zero, and the strip bounds `0 ≤ δ ≤ arcsin κ̂` hold with
equality at `κ̂ = 1/2`.  The comparison constants therefore take the values
`κ₁ = rearKappa1 (1/2) = 2/3` and `P₀ = √(3/4)/2`, and both numerical conditions
are checked.

Main result: `exists_variableSpeed_normalPath_staticCircleRear`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfRearFamilyCircle

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugeMarkedDataOfRearFamily
  NormalPathC2IncrementVariableSpeed RearFamilyFrame RearOwnArclength

/-! ### The configuration -/

/-- The front: the circle of radius `2`, carried in its own arclength. -/
def cFront : ℝ → ℝ → ℂ := fun _ s => 2 * Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ))

/-- The tangent angle of the front. -/
def cTheta : ℝ → ℝ → ℝ := fun _ s => s / 2 + Real.pi / 2

/-- The curvature of the front. -/
def cCurv : ℝ → ℝ → ℝ := fun _ _ => 1 / 2

/-- The steering angle: the constant solving `sin δ = K`. -/
def cSteer : ℝ → ℝ → ℝ := fun _ _ => Real.pi / 6

/-- The change of variable from the rear arclength to the front arclength. -/
def cSf : ℝ → ℝ → ℝ := fun _ x => x / Real.cos (Real.pi / 6)

/-- The family is at rest. -/
def cYdot : ℝ → ℝ → ℂ := fun _ _ => 0

/-- The front normal velocity vanishes. -/
def cEtaF : ℝ → ℝ → ℝ := fun _ _ => 0

@[simp] theorem cTheta_apply (t s : ℝ) : cTheta t s = s / 2 + Real.pi / 2 := rfl

@[simp] theorem cCurv_apply (t s : ℝ) : cCurv t s = 1 / 2 := rfl

@[simp] theorem cSteer_apply (t s : ℝ) : cSteer t s = Real.pi / 6 := rfl

@[simp] theorem cSf_apply (t x : ℝ) : cSf t x = x / Real.cos (Real.pi / 6) := rfl

@[simp] theorem cYdot_apply (t x : ℝ) : cYdot t x = 0 := rfl

@[simp] theorem cEtaF_apply (t s : ℝ) : cEtaF t s = 0 := rfl

/-- The curvature bound of the configuration. -/
def cKh : ℝ := 1 / 2

/-- The constant of the comparison: it dominates both the rear curvature
`tan(π/6)` and the first gauge constant `rearKappa1 (1/2) = 2/3`. -/
def cKhat : ℝ := 2 / 3

/-- The root `√(1 − κ̂²) = √(3/4)`. -/
def cRoot : ℝ := Real.sqrt (1 - cKh ^ 2)

/-- The lower bound on the speed of the slices. -/
def cP0 : ℝ := cRoot / 2

/-! ### Elementary facts about the configuration -/

theorem cSteer_eq_arcsin : Real.arcsin cKh = Real.pi / 6 := by
  have h : Real.sin (Real.pi / 6) = cKh := by rw [Real.sin_pi_div_six, cKh]
  rw [← h, Real.arcsin_sin] <;> nlinarith [Real.pi_pos]

theorem cCos_pos : 0 < Real.cos (Real.pi / 6) := by
  rw [Real.cos_pi_div_six]
  positivity

theorem cCos_ne : Real.cos (Real.pi / 6) ≠ 0 := cCos_pos.ne'

theorem cSin : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six

theorem cRoot_sq : cRoot ^ 2 = 3 / 4 := by
  rw [cRoot, Real.sq_sqrt] <;> norm_num [cKh]

theorem cRoot_pos : 0 < cRoot := by
  rw [cRoot]
  apply Real.sqrt_pos.2
  norm_num [cKh]

theorem cRoot_lt_one : cRoot < 1 := by
  nlinarith [cRoot_sq, cRoot_pos]

/-- The rear tangent angle of the configuration is affine in the rear
arclength. -/
theorem cAngle_eq (t x : ℝ) :
    rearOwnAngle cTheta cSteer cSf t x
      = x / Real.cos (Real.pi / 6) / 2 + Real.pi / 2 - Real.pi / 6 := by
  simp [rearOwnAngle, RearTrack.rearAngle, cTheta, cSteer, cSf]

/-- The tangential component of the motion vanishes. -/
theorem cTangential_eq (t x : ℝ) :
    frameTangential cYdot (rearOwnAngle cTheta cSteer cSf) t x = 0 := by
  simp [frameTangential, cYdot]

/-- The normal component of the motion vanishes. -/
theorem cNormal_eq (t x : ℝ) :
    frameNormal cYdot (rearOwnAngle cTheta cSteer cSf) t x = 0 := by
  simp [frameNormal, cYdot]

/-- The rear curvature `tan(π/6)` is dominated by `cKhat`. -/
theorem cTan_le : |Real.tan (Real.pi / 6)| ≤ cKhat := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_six, Real.cos_pi_div_six]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h32 : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by nlinarith
  rw [abs_of_nonneg (by positivity), cKhat, div_le_iff₀ (by positivity)]
  nlinarith

/-- The first gauge constant of the configuration is `2/3`. -/
theorem cRearKappa1 : rearKappa1 cKh = cKhat := by
  rw [rearKappa1, cKh, cKhat]
  norm_num

/-! ### The two numerical conditions -/

theorem cNumA : 2 + 2 * cKhat * 0 ≤ 1 / cP0 := by
  have hr := cRoot_pos
  have hlt := cRoot_lt_one
  rw [cP0, one_div_div, le_div_iff₀ hr]
  nlinarith

theorem cNumK : (0 + 2) + cKhat ^ 2 + 2 * 0 * 0 ≤ 1 / cP0 ^ 2 + cKhat ^ 2 := by
  have hsq := cRoot_sq
  have hP : (1 : ℝ) / cP0 ^ 2 = 16 / 3 := by
    rw [cP0, div_pow, one_div_div, hsq]
    norm_num
  rw [hP]
  norm_num

/-! ### The assembly -/

/-- **The hypothesis block of the rear-family assembly is consistent.**  The
selected rear of a circle of radius `2`, at rest, satisfies it, and the
comparison path it produces exists. -/
theorem exists_variableSpeed_normalPath_staticCircleRear (p : Data) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = 1 * u) ∧
      (∀ u t, HasDerivAt (fun s => Phi s u)
        (-frameTangential cYdot (rearOwnAngle cTheta cSteer cSf) t (Phi t u)) t) ∧
      ∀ a b : Data,
        (∀ u, rearOwn cFront cTheta cSteer cSf 0 (Phi 0 u) = a.1 u) →
        (∀ u, rearOwn cFront cTheta cSteer cSf (const p).T (Phi (const p).T u) = b.1 u) →
        (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm (iteratedDeriv j
          (fun u => frameNormal cYdot (rearOwnAngle cTheta cSteer cSf) t (Phi t u)))
            ≤ (const p).m t) →
        ∃ Γ' : NormalPath a b, Γ'.T = (const p).T ∧ Γ'.m = (const p).m ∧
          cost Γ' = (∫ t in (0 : ℝ)..(const p).T, (const p).m t) ∧
          IsVariableSpeedNormalPath cP0
            (costP1 1 cKhat (∫ t in (0 : ℝ)..(const p).T, (const p).m t)) cKhat
            (costG1 1 cKhat (rearKappa2 cKh)
              (∫ t in (0 : ℝ)..(const p).T, (const p).m t))
            (cKhat * costG1 1 cKhat (rearKappa2 cKh)
                (∫ t in (0 : ℝ)..(const p).T, (const p).m t)
              + rearKappa2 cKh
                * costP1 1 cKhat (∫ t in (0 : ℝ)..(const p).T, (const p).m t) ^ 2) Γ' := by
  have hcos := cCos_ne
  have hcospos := cCos_pos
  have hangle : uncurry (rearOwnAngle cTheta cSteer cSf)
      = fun z : ℝ × ℝ => z.2 / Real.cos (Real.pi / 6) / 2 + Real.pi / 2 - Real.pi / 6 := by
    funext z
    exact cAngle_eq z.1 z.2
  have hxi : uncurry (frameTangential cYdot (rearOwnAngle cTheta cSteer cSf))
      = fun _ : ℝ × ℝ => (0 : ℝ) := by
    funext z
    exact cTangential_eq z.1 z.2
  have hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle cTheta cSteer cSf)) := by
    rw [hangle]
    exact (((contDiff_snd.div_const _).div_const _).add contDiff_const).sub contDiff_const
  refine exists_variableSpeed_normalPath_of_rearFamily (F := cFront) (Θ := cTheta)
    (δ := cSteer) (K := cCurv) (sf := cSf) (Ydot := cYdot) (etaF := cEtaF)
    (Q := fun _ => 1) (P := fun _ => 1) (Kx := fun _ => 0) (Rb := fun _ => 0)
    (Dd := fun _ => 0) (alphaT := fun _ _ => 0) (kT := fun _ _ => 0)
    (gS := fun _ _ => 0) (ell := 1) (P0 := cP0) (khat := cKhat) (d := 0)
    (r := 0) (kx := 0) (kh := cKh) (m := (const p).m) (const p)
    (by norm_num [cKh]) (by norm_num [cKh]) one_pos ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ _ => hcos)
    ?_ ?_ ?_ ?_ ?_ contDiff_const hangC ?_ (fun _ => one_pos) ?_ ?_ (fun _ => one_pos) ?_
    (le_of_eq cRearKappa1) ?_ ?_ continuous_const continuous_const ?_ ?_ ?_
    (fun _ => le_rfl) (fun _ => le_rfl) ?_ ?_ (fun _ => by norm_num) le_rfl ?_
    (fun _ _ => by norm_num) (fun _ => by norm_num) (const p).cont_m (const p).m_nonneg
    (const p).m_stop (fun _ => by
      show (0 : ℝ) / Real.sqrt (1 - cKh ^ 2) ≤ 0
      simp) cNumA cNumK
  -- `0 ≤ δ`
  · exact fun _ _ => by rw [cSteer_apply]; positivity
  -- `δ ≤ arcsin κ̂`
  · exact fun _ _ => by rw [cSteer_apply, cSteer_eq_arcsin]
  -- `|K| ≤ κ̂`
  · exact fun _ _ => by rw [cCurv_apply, cKh]; norm_num
  -- the front is carried in its own arclength
  · intro t s
    have h : HasDerivAt (fun y : ℝ => 2 * Complex.exp (Complex.I * ((y / 2 : ℝ) : ℂ)))
        (2 * (Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ)) * (Complex.I * (1 / 2)))) s := by
      have hlin : HasDerivAt (fun y : ℝ => Complex.I * ((y / 2 : ℝ) : ℂ))
          (Complex.I * (1 / 2)) s := by
        have := ((Complex.ofRealCLM.hasDerivAt (x := s)).div_const 2).const_mul Complex.I
        simpa using this
      exact (hlin.cexp).const_mul 2
    refine h.congr_deriv ?_
    have hsplit : Complex.exp (Complex.I * ((cTheta t s : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, cTheta_apply]
      push_cast
      ring_nf
    rw [hsplit, GaugeFlowVariableSpeedPathCircle.exp_I_pi_div_two]
    ring
  -- the tangent angle
  · intro t s
    show HasDerivAt (fun y : ℝ => y / 2 + Real.pi / 2) (cCurv t s) s
    rw [cCurv_apply]
    simpa [one_div] using ((hasDerivAt_id s).div_const 2).add_const (Real.pi / 2)
  -- the steering ODE
  · intro t s
    show HasDerivAt (fun _ : ℝ => Real.pi / 6) (cCurv t s - Real.sin (cSteer t s)) s
    have h : cCurv t s - Real.sin (cSteer t s) = 0 := by
      rw [cCurv_apply, cSteer_apply, cSin]
      ring
    rw [h]
    exact hasDerivAt_const s (Real.pi / 6)
  -- the change of variable
  · intro t x
    show HasDerivAt (fun y : ℝ => y / Real.cos (Real.pi / 6))
      (1 / Real.cos (cSteer t (cSf t x))) x
    rw [cSteer_apply]
    simpa [one_div] using (hasDerivAt_id x).div_const (Real.cos (Real.pi / 6))
  -- the family is at rest
  · intro t x
    have h : (fun r => rearOwn cFront cTheta cSteer cSf r x)
        = fun _ => rearOwn cFront cTheta cSteer cSf 0 x := rfl
    rw [h, cYdot_apply]
    exact hasDerivAt_const t _
  -- regularity of the front
  · have : uncurry cFront
        = fun z : ℝ × ℝ => 2 * Complex.exp (Complex.I * ((z.2 / 2 : ℝ) : ℂ)) := rfl
    rw [this]
    exact contDiff_const.mul (Complex.contDiff_exp.comp
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_snd.div_const 2))))
  -- regularity of the tangent angle
  · exact (contDiff_snd.div_const 2).add contDiff_const
  -- regularity of the steering angle
  · exact contDiff_const
  -- regularity of the change of variable
  · exact contDiff_snd.div_const _
  -- regularity of the rear curvature
  · have h : (uncurry fun t x => Real.tan (cSteer t (cSf t x)))
        = fun _ : ℝ × ℝ => Real.tan (Real.pi / 6) := rfl
    rw [h]
    exact contDiff_const
  -- the normal rate is periodic
  · intro t y
    simp [cNormal_eq]
  -- the inverse Jacobi ODE
  · intro t x
    have hf : (fun x' => frameNormal cYdot (rearOwnAngle cTheta cSteer cSf) t x')
        = fun _ => (0 : ℝ) := by
      funext y
      exact cNormal_eq t y
    have hv : cEtaF t (cSf t x) / Real.cos (cSteer t (cSf t x))
        - frameNormal cYdot (rearOwnAngle cTheta cSteer cSf) t x = 0 := by
      rw [cNormal_eq, cEtaF_apply]
      simp
    rw [hf, hv]
    exact hasDerivAt_const x (0 : ℝ)
  -- the link with the cost density
  · intro t u
    rfl
  -- the time derivative of the tangent angle
  · intro t x
    have : (fun r => rearOwnAngle cTheta cSteer cSf r x)
        = fun _ => rearOwnAngle cTheta cSteer cSf 0 x := by
      funext r
      rw [cAngle_eq, cAngle_eq]
    rw [this]
    exact hasDerivAt_const t _
  -- the time derivative of the curvature
  · intro t x
    show HasDerivAt (fun _ : ℝ => Real.tan (Real.pi / 6)) 0 t
    exact hasDerivAt_const t (Real.tan (Real.pi / 6))
  -- the space derivative of the angular rate
  · exact fun t s => hasDerivAt_const s (0 : ℝ)
  -- the mixed derivative
  · intro t s
    refine ⟨0, ?_, ?_⟩
    · have : (fun r => Complex.exp (Complex.I * ((rearOwnAngle cTheta cSteer cSf r s : ℝ) : ℂ)))
          = fun _ => Complex.exp (Complex.I
            * ((rearOwnAngle cTheta cSteer cSf 0 s : ℝ) : ℂ)) := by
        funext r
        rw [cAngle_eq, cAngle_eq]
      rw [this]
      exact hasDerivAt_const t _
    · have : (fun x => ((frameTangential cYdot (rearOwnAngle cTheta cSteer cSf) t x : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((rearOwnAngle cTheta cSteer cSf t x : ℝ) : ℂ))
          + ((frameNormal cYdot (rearOwnAngle cTheta cSteer cSf) t x : ℝ) : ℂ)
            * (Complex.I * Complex.exp (Complex.I
              * ((rearOwnAngle cTheta cSteer cSf t x : ℝ) : ℂ))))
          = fun _ => (0 : ℂ) := by
        funext y
        rw [cTangential_eq, cNormal_eq]
        simp
      rw [this]
      exact hasDerivAt_const s (0 : ℂ)
  -- the bound on the derivative of the curvature
  · intro t x
    have h : cCurv t (cSf t x) - Real.sin (cSteer t (cSf t x)) = 0 := by
      rw [cCurv_apply, cSteer_apply, cSin]
      ring
    rw [h]
    simp
  -- continuity of that derivative
  · have h : (uncurry fun t x => (cCurv t (cSf t x) - Real.sin (cSteer t (cSf t x)))
        / Real.cos (cSteer t (cSf t x)) ^ 3) = fun _ : ℝ × ℝ => (0 : ℝ) := by
      funext z
      rw [uncurry, cCurv_apply, cSteer_apply, cSin]
      norm_num
    rw [h]
    exact continuous_const
  -- the bound on the tangential component
  · intro t x
    rw [cTangential_eq]
    simp
  -- the derivative of the source of the ODE
  · intro t x
    have h : (fun x' => cEtaF t (cSf t x') / Real.cos (cSteer t (cSf t x')))
        = fun _ => (0 : ℝ) := by
      funext y
      rw [cEtaF_apply]
      simp
    rw [h]
    exact hasDerivAt_const x (0 : ℝ)

end GaugeMarkedDataOfRearFamilyCircle
