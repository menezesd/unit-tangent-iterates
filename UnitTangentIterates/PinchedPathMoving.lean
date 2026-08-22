import Mathlib
import UnitTangentIterates.PinchedPathRigidity
import UnitTangentIterates.PinchedPathSlow
import UnitTangentIterates.SelInvLipUniversalCircle

/-!
# The rigidity of the admissible paths is sharp: the dilating circle

`PinchedPathRigidity.lean` shows that the hypothesis block of
`SelInvTubePathDist.IsPinchedPath` — jointly smooth slices of constant speed,
normal gauge, curvature at least `kminP > 0`, marked point at rest — forces the
family to stand still.  This file isolates the hypothesis responsible.

Dropping the condition `rest` that the marked point does not move, and keeping
*every* other one, the class becomes non-rigid: the **dilating circle**

```
  X(t, u) = R(t) e^{2πiu},   R(t) = r + a·w(t),
```

run on the flat time profile `w = flatTime 1` of `PinchedPathSlow.lean`, is a
normal path of duration one from the marked circle of radius `r` to the marked
circle of radius `r + a`, all of whose slices are circles: they are closed, of
constant speed `2πR(t)`, of curvature `1/R(t)` pinched between `1/(r+a)` and
`1/r`, short when `a < r`, and the path moves along their unit normal.  Its cost
is `a > 0`, and its two ends are different curves.

So the constant-speed condition and the resting-marked-point condition are
individually harmless; it is their conjunction, in the presence of positive
curvature, that is empty.

Main results: `dilX`, `dilCirclePath`, `IsPinchedPathFree`,
`dilCirclePath_isPinchedPathFree`, `cost_dilCirclePath`,
`not_forall_stationary_of_isPinchedPathFree`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPathMoving

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathCurvBoundC2 SelInvPathPerimC2 SelInvTubePathDist
  PinchedPath SelInvPathTurningCircle

variable {r a : ℝ}

/-! ### The dilating radius -/

/-- The radius of the dilating circle: it increases smoothly from `r` to
`r + a`, and is constant outside the window `[1/4, 3/4]`. -/
def dilRadius (r a : ℝ) : ℝ → ℝ := fun t => r + a * flatTime 1 t

/-- The rate at which the radius grows. -/
def dilRate (a : ℝ) : ℝ → ℝ := fun t => a * flatSpeed 1 t

theorem contDiff_dilRadius {n : ℕ} : ContDiff ℝ (n : ℕ) (dilRadius r a) :=
  contDiff_const.add (contDiff_const.mul (contDiff_flatTime (n := n) 1))

theorem hasDerivAt_dilRadius (t : ℝ) : HasDerivAt (dilRadius r a) (dilRate a t) t :=
  ((hasDerivAt_flatTime 1 t).const_mul a).const_add r

theorem continuous_dilRate : Continuous (dilRate a) :=
  continuous_const.mul (continuous_flatSpeed 1)

theorem dilRate_nonneg (ha : 0 ≤ a) (t : ℝ) : 0 ≤ dilRate a t :=
  mul_nonneg ha (flatSpeed_nonneg one_pos t)

theorem dilRate_eq_zero_outside {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) : dilRate a t = 0 := by
  rw [dilRate, flatSpeed_eq_zero_outside one_pos ht, mul_zero]

theorem dilRadius_zero : dilRadius r a 0 = r := by
  rw [dilRadius, flatTime_zero one_pos, mul_zero, add_zero]

theorem dilRadius_one : dilRadius r a 1 = r + a := by
  rw [dilRadius, flatTime_final one_pos, mul_one]

theorem flatTime_one_nonneg (t : ℝ) : 0 ≤ flatTime 1 t := by
  rw [flatTime, one_mul]
  exact Real.smoothTransition.nonneg _

theorem flatTime_one_le_one (t : ℝ) : flatTime 1 t ≤ 1 := by
  rw [flatTime, one_mul]
  exact Real.smoothTransition.le_one _

theorem le_dilRadius (ha : 0 ≤ a) (t : ℝ) : r ≤ dilRadius r a t := by
  rw [dilRadius]
  nlinarith [mul_nonneg ha (flatTime_one_nonneg t)]

theorem dilRadius_le (ha : 0 ≤ a) (t : ℝ) : dilRadius r a t ≤ r + a := by
  rw [dilRadius]
  nlinarith [flatTime_one_le_one t, ha]

theorem dilRadius_pos (hr : 0 < r) (ha : 0 ≤ a) (t : ℝ) : 0 < dilRadius r a t :=
  lt_of_lt_of_le hr (le_dilRadius ha t)

/-! ### The dilating family of circles -/

/-- **The dilating circle**: the family of circles of radius `dilRadius r a t`,
in the normalized parameter. -/
def dilX (r a : ℝ) : ℝ → ℝ → ℂ := fun t u => (dilRadius r a t : ℂ) * normExp u

theorem contDiff_uncurry_dilX {n : ℕ} : ContDiff ℝ (n : ℕ) (uncurry (dilX r a)) := by
  have h : uncurry (dilX r a)
      = fun z : ℝ × ℝ => ((dilRadius r a z.1 : ℝ) : ℂ) * normExp z.2 := rfl
  rw [h]
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_dilRadius.comp contDiff_fst)).mul
    (contDiff_normExp.comp contDiff_snd)

theorem differentiable_uncurry_dilX : Differentiable ℝ (uncurry (dilX r a)) :=
  (contDiff_uncurry_dilX (n := 1)).differentiable (by norm_num)

theorem dilX_slice (t : ℝ) : dilX r a t = fun u => (circleData (dilRadius r a t)).1 u := rfl

theorem pathVel_dilX (hr : 0 < r) (ha : 0 ≤ a) (t u : ℝ) :
    pathVel (dilX r a) t u = (circleData (dilRadius r a t)).2.1 u :=
  pathVel_eq_of_slice differentiable_uncurry_dilX (fun _ => rfl)
    (circleData_mem_tube (dilRadius_pos hr ha t)).hasDerivAt_curve u

theorem pathVel_dilX_eq (hr : 0 < r) (ha : 0 ≤ a) :
    pathVel (dilX r a)
      = fun t u => ((2 * Real.pi * dilRadius r a t : ℝ) : ℂ) * Complex.I * normExp u := by
  funext t u
  rw [pathVel_dilX hr ha, circleData_vel]

theorem contDiff_uncurry_pathVel_dilX (hr : 0 < r) (ha : 0 ≤ a) {n : ℕ} :
    ContDiff ℝ (n : ℕ) (uncurry (pathVel (dilX r a))) := by
  rw [pathVel_dilX_eq hr ha]
  have h : (uncurry fun t u => ((2 * Real.pi * dilRadius r a t : ℝ) : ℂ) * Complex.I * normExp u)
      = fun z : ℝ × ℝ =>
        (((2 * Real.pi * dilRadius r a z.1 : ℝ) : ℂ) * Complex.I) * normExp z.2 := rfl
  rw [h]
  refine ContDiff.mul ?_ (contDiff_normExp.comp contDiff_snd)
  exact (Complex.ofRealCLM.contDiff.comp
    ((contDiff_const.mul contDiff_dilRadius).comp contDiff_fst)).mul contDiff_const

theorem pathAcc_dilX (hr : 0 < r) (ha : 0 ≤ a) (t u : ℝ) :
    pathAcc (dilX r a) t u = (circleData (dilRadius r a t)).2.2 u := by
  have hVdiff : Differentiable ℝ (uncurry (pathVel (dilX r a))) :=
    (contDiff_uncurry_pathVel_dilX (r := r) (a := a) hr ha (n := 1)).differentiable (by norm_num)
  have h1 : HasDerivAt (pathVel (dilX r a) t) ((circleData (dilRadius r a t)).2.2 u) u := by
    have hfun : pathVel (dilX r a) t = ⇑(circleData (dilRadius r a t)).2.1 :=
      funext fun v => pathVel_dilX hr ha t v
    rw [hfun]
    exact (circleData_mem_tube (dilRadius_pos hr ha t)).hasDerivAt_vel u
  exact (hasDerivAt_partialArc hVdiff t u).unique h1

theorem pathPerim_dilX (hr : 0 < r) (ha : 0 ≤ a) (t : ℝ) :
    pathPerim (dilX r a) t = 2 * Real.pi * dilRadius r a t := by
  show ‖pathVel (dilX r a) t 0‖ = _
  rw [pathVel_dilX hr ha, norm_vel_circleData (dilRadius_pos hr ha t)]

theorem pathKn_dilX (hr : 0 < r) (ha : 0 ≤ a) (t σ : ℝ) :
    pathKn (dilX r a) (pathPerim (dilX r a)) t σ = 1 / dilRadius r a t := by
  have hR : 0 < dilRadius r a t := dilRadius_pos hr ha t
  have hne : (2 : ℝ) * Real.pi * dilRadius r a t ≠ 0 := by positivity
  rw [pathKn, curvOfPath, pathPerim_dilX hr ha]
  have hcancel : σ * (2 * Real.pi * dilRadius r a t) / (2 * Real.pi * dilRadius r a t) = σ := by
    field_simp
  rw [hcancel, pathVel_dilX hr ha, pathAcc_dilX hr ha, im_conj_vel_mul_acc]
  field_simp
  ring

/-! ### The dilating circle as a normal path -/

/-- **The dilating circle as a normal path** from the marked circle of radius
`r` to the marked circle of radius `r + a`. -/
def dilCirclePath (r a : ℝ) (ha : 0 ≤ a) :
    NormalPath (circleData r) (circleData (r + a)) where
  T := 1
  T_pos := one_pos
  X := dilX r a
  eta := fun t _ => -dilRate a t
  nu := fun _ u => -normExp u
  m := fun t => dilRate a t
  start := fun u => by
    show (dilRadius r a 0 : ℂ) * normExp u = _
    rw [dilRadius_zero]; rfl
  finish := fun u => by
    show (dilRadius r a 1 : ℂ) * normExp u = _
    rw [dilRadius_one]; rfl
  hasDerivAt_time := fun t u => by
    have h := ((hasDerivAt_dilRadius (r := r) (a := a) t).ofReal_comp).mul_const (normExp u)
    have hval : ((dilRate a t : ℝ) : ℂ) * normExp u
        = ((-dilRate a t : ℝ) : ℂ) * -normExp u := by push_cast; ring
    rw [hval] at h
    exact h
  cont_vel := fun u => by
    have h : (fun t => ((-dilRate a t : ℝ) : ℂ) * -normExp u)
        = fun t => ((dilRate a t : ℝ) : ℂ) * normExp u := by
      funext t; push_cast; ring
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_dilRate).mul continuous_const
  norm_nu := fun _ u => by simp
  cont_m := continuous_dilRate
  m_nonneg := dilRate_nonneg ha
  m_stop := fun _ ht => dilRate_eq_zero_outside ht
  abs_eta_le := fun t _ => by
    rw [abs_neg, abs_of_nonneg (dilRate_nonneg ha t)]
  le_m_L1 := fun t => by
    rw [abs_neg, abs_of_nonneg (dilRate_nonneg ha t)]
    simp
  le_m_sup := fun t j hj => by
    interval_cases j
    · have h : iteratedDeriv 0 (fun _ : ℝ => -dilRate a t) = fun _ : ℝ => -dilRate a t := rfl
      rw [h, supNorm, ciSup_const, abs_neg, abs_of_nonneg (dilRate_nonneg ha t)]
    · have h : iteratedDeriv 1 (fun _ : ℝ => -dilRate a t) = fun _ : ℝ => (0 : ℝ) := by
        simp [iteratedDeriv_succ]
      rw [h, supNorm]
      simpa using dilRate_nonneg ha t
    · have h : iteratedDeriv 2 (fun _ : ℝ => -dilRate a t) = fun _ : ℝ => (0 : ℝ) := by
        simp [iteratedDeriv_succ]
      rw [h, supNorm]
      simpa using dilRate_nonneg ha t

@[simp] theorem dilCirclePath_X (ha : 0 ≤ a) : (dilCirclePath r a ha).X = dilX r a := rfl

@[simp] theorem dilCirclePath_eta (ha : 0 ≤ a) (t u : ℝ) :
    (dilCirclePath r a ha).eta t u = -dilRate a t := rfl

/-- **The cost of the dilating circle is the increment of the radius.** -/
theorem cost_dilCirclePath (ha : 0 ≤ a) : cost (dilCirclePath r a ha) = a := by
  have hsub : (∫ t in (0:ℝ)..1, dilRate a t) = dilRadius r a 1 - dilRadius r a 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_dilRadius t)
      (continuous_dilRate.intervalIntegrable 0 1)
  rw [cost]
  show (∫ t in (0:ℝ)..(1:ℝ), dilRate a t) = a
  rw [hsub, dilRadius_one, dilRadius_zero]
  ring

/-! ### Admissibility without the resting marked point -/

/-- **An admissible path with the resting marked point dropped**: every
condition of `SelInvTubePathDist.IsPinchedPath` except `rest`. -/
structure IsPinchedPathFree {p q : Data} (kminP kh : ℝ) (Γ : NormalPath p q) : Prop where
  /-- the family of slices is `C⁶` -/
  smooth : ContDiff ℝ (6 : ℕ) (uncurry Γ.X)
  /-- each slice has constant speed -/
  speed : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖
  /-- each slice is a closed curve -/
  per : ∀ t, Periodic (Γ.X t) 1
  /-- the path moves along the unit normal of its slices -/
  normal : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ))
  /-- the curvature of the slices is at least `kminP` -/
  kmin : ∀ t σ, kminP ≤ pathKn Γ.X (pathPerim Γ.X) t σ
  /-- the curvature of the slices is at most `κ̂` -/
  kmax : ∀ t σ, pathKn Γ.X (pathPerim Γ.X) t σ ≤ kh
  /-- the slices are short -/
  short : ∀ t, kh * pathPerim Γ.X t < 4 * Real.pi
  /-- the velocity at the marked point avoids the slit -/
  slit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane

/-- An admissible path is admissible in the weaker sense. -/
theorem isPinchedPathFree_of_isPinchedPath {p q : Data} {kminP kh : ℝ} {Γ : NormalPath p q}
    (hΓ : IsPinchedPath kminP kh Γ) : IsPinchedPathFree kminP kh Γ :=
  { smooth := hΓ.smooth, speed := hΓ.speed, per := hΓ.per, normal := hΓ.normal,
    kmin := hΓ.kmin, kmax := hΓ.kmax, short := hΓ.short, slit := hΓ.slit }

/-- **The dilating circle satisfies every condition of the admissible class but
the resting marked point**, with the curvature pinching
`kminP = 1/(r+a) ≤ κ ≤ 1/r = κ̂`. -/
theorem dilCirclePath_isPinchedPathFree (hr : 0 < r) (ha : 0 ≤ a) (har : a < r) :
    IsPinchedPathFree (1 / (r + a)) (1 / r) (dilCirclePath r a ha) := by
  have hRpos : ∀ t, 0 < dilRadius r a t := dilRadius_pos hr ha
  refine
    { smooth := contDiff_uncurry_dilX
      speed := fun t u => ?_
      per := fun t u => ?_
      normal := fun t u => ?_
      kmin := fun t σ => ?_
      kmax := fun t σ => ?_
      short := fun t => ?_
      slit := fun t => ?_ }
  · show ‖pathVel (dilX r a) t u‖ = ‖pathVel (dilX r a) t 0‖
    rw [pathVel_dilX hr ha, pathVel_dilX hr ha, norm_vel_circleData (hRpos t),
      norm_vel_circleData (hRpos t)]
  · show (dilRadius r a t : ℂ) * normExp (u + 1) = (dilRadius r a t : ℂ) * normExp u
    rw [periodic_normExp u]
  · show -normExp u = _
    have hc : 0 < 2 * Real.pi * dilRadius r a t :=
      mul_pos (by positivity) (hRpos t)
    have hne : ((2 * Real.pi * dilRadius r a t : ℝ) : ℂ) ≠ 0 := by simpa using (ne_of_gt hc)
    rw [show (dilCirclePath r a ha).X = dilX r a from rfl, pathVel_dilX hr ha,
      pathPerim_dilX hr ha, circleData_vel]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  · rw [show (dilCirclePath r a ha).X = dilX r a from rfl, pathKn_dilX hr ha]
    exact one_div_le_one_div_of_le (hRpos t) (dilRadius_le ha t)
  · rw [show (dilCirclePath r a ha).X = dilX r a from rfl, pathKn_dilX hr ha]
    exact one_div_le_one_div_of_le hr (le_dilRadius ha t)
  · rw [show (dilCirclePath r a ha).X = dilX r a from rfl, pathPerim_dilX hr ha]
    have h : 1 / r * (2 * Real.pi * dilRadius r a t) = 2 * Real.pi * (dilRadius r a t / r) := by
      field_simp
    rw [h]
    have hlt : dilRadius r a t / r < 2 := by
      rw [div_lt_iff₀ hr]
      have := dilRadius_le (r := r) ha t
      linarith
    nlinarith [Real.pi_pos]
  · rw [show (dilCirclePath r a ha).X = dilX r a from rfl, pathVel_dilX hr ha, circleData_vel]
    right
    have h0 : normExp 0 = 1 := by simp [normExp]
    rw [h0, mul_one]
    simp only [Complex.mul_I_im, Complex.ofReal_re, ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨two_ne_zero, ne_of_gt Real.pi_pos⟩, ne_of_gt (hRpos t)⟩

/-! ### The weaker class is not rigid -/

/-- **The dilating circle really moves**: its two ends are different curves. -/
theorem circleData_ne_of_lt (ha : 0 < a) :
    ((circleData r).1 : ℝ → ℂ) ≠ (circleData (r + a)).1 := by
  intro h
  have h0 := congrFun h 0
  rw [circleData_fst, circleData_fst] at h0
  have hE : normExp 0 = 1 := by simp [normExp]
  rw [hE, mul_one, mul_one] at h0
  have : r = r + a := by exact_mod_cast h0
  linarith

/-- **The rigidity of the admissible paths is sharp.**  Dropping the condition
that the marked point is at rest, and keeping every other one, there are
positive curvature bounds and a path in the class whose two ends carry different
curves — indeed the dilating circle, of cost `a > 0`. -/
theorem not_forall_stationary_of_isPinchedPathFree :
    ∃ (kminP kh : ℝ) (p q : Data) (Γ : NormalPath p q),
      0 < kminP ∧ IsPinchedPathFree kminP kh Γ ∧ (p.1 : ℝ → ℂ) ≠ q.1 ∧ 0 < cost Γ := by
  refine ⟨1 / (2 + 1), 1 / 2, circleData 2, circleData (2 + 1),
    dilCirclePath 2 1 zero_le_one, by norm_num, ?_, ?_, ?_⟩
  · exact dilCirclePath_isPinchedPathFree (by norm_num) zero_le_one (by norm_num)
  · exact circleData_ne_of_lt one_pos
  · rw [cost_dilCirclePath]; norm_num

/-- **The culprit is the conjunction.**  For a constant-speed normal path of
positively curved slices, the family is stationary exactly when its marked point
is at rest. -/
theorem eta_eq_zero_iff_rest {p q : Data} {kminP kh : ℝ} {Γ : NormalPath p q}
    (hΓ : IsPinchedPathFree kminP kh Γ) (hkminP : 0 < kminP) :
    (∀ t u, Γ.eta t u = 0) ↔ (∀ t, Γ.eta t 0 = 0) := by
  refine ⟨fun h t => h t 0, fun h t u => ?_⟩
  exact PinchedPathRigidity.eta_eq_zero_of_speed_rest (hΓ.smooth.of_le (by norm_num))
    hΓ.speed hΓ.normal hkminP hΓ.kmin
    (fun t => Complex.slitPlane_ne_zero (hΓ.slit t)) h t u

end PinchedPathMoving
