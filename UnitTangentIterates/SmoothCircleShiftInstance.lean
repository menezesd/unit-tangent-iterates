import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnShiftSteering
import UnitTangentIterates.SelectedInverseTubeCircle
import UnitTangentIterates.MovingCircleNormalized

/-!
# The shift bound for the marked selected inverses is not vacuous

`SelectedInverseRearOwnShiftSteering.exists_steering_pathDistShift_selInv_le`
bounds the distance modulo the marking of the two marked selected inverses of
the ends of a normal path of fronts, with the steering data produced from the
curvature alone.  Its hypotheses are strong: both ends must be members of the
tube, their rear tracks must be embedded, and the period and the curvature
family must be `C⁴`-regular in the path parameter with a two-sided pinching
`0 ≤ K̂ ≤ κ̂ < 1`.

This file checks that they are consistent.  The witness is the *smooth*
dilation of a circle: the circles of radius `1 / sin A(t)`, with the smooth
profile `A` of `MovingCircleProfile.lean`, which rests at both ends of the time
interval, so that

* the two ends of the path are the marked circles of radius `√2` and `2`, both
  members of the tube (`MarkedSpace.circleData_mem_tube`) of curvature at most
  `κ̂ = sin(π/4)`;
* their rear tracks are embedded, by a version of
  `SelectedInverseTubeCircle.injOn_rearTrack_evCircleData` proved here for a
  steering angle confined to any strip `0 ≤ δ ≤ arcsin κ̂` rather than to the
  strip of the circle's own curvature (`injOn_rearTrack_evCircleData_strip`);
* the period `P(t) = 2π / sin A(t)` and the curvature `K̂(t, σ) = sin A(t)` are
  smooth in `t`, with the bounds already established for the moving circle.

Main definitions and results:

* `rad`, `circlePath` — the radius profile and the resulting normal path from
  the circle of radius `1 / sin A(0)` to the circle of radius `1 / sin A(1)`;
* `injOn_rearTrack_evCircleData_strip` — embeddedness of the rear tracks of a
  circle for a steering angle in an arbitrary selected strip;
* `circlePath_shift_instance` — the instance.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SmoothCircleShiftInstance

open MovingCircleProfile MovingCircleCurvature MovingCircle MovingCircleNormalized
  FrontFromPath SelectedInverseCircle SelectedInverseTubeCircle

/-! ### Embeddedness of the rear tracks of a circle, on an arbitrary strip -/

/-- **Every rear track of the marked circle of radius `r > 1` built from a
steering angle in the strip `0 ≤ δ ≤ arcsin κ` is embedded.**  The same
statement as `SelectedInverseTubeCircle.injOn_rearTrack_evCircleData`, except
that the steering angle is only required to lie in the selected strip of some
`κ`, not in that of the circle's own curvature `1/r`: the uniqueness of the
periodic steering angle only uses that it stays in `[-π/2, π/2]`. -/
theorem injOn_rearTrack_evCircleData_strip {r kap : ℝ} (hr : 1 < r) (Θ K dl : ℝ → ℝ)
    (hX : ∀ s, HasDerivAt (ev (circleData r)) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hdlper : Function.Periodic dl (perim (circleData r)))
    (hdlmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap))
    (hdlode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) :
    InjOn (rearTrack (ev (circleData r)) Θ dl) (Ico 0 (perim (circleData r))) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hev := SelectedInverseTubeCircle.ev_circleData hr0
  have hperim := perim_circleData hr0
  have hppos : 0 < 2 * Real.pi * r := by positivity
  have hkap1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have hkmin : 0 < 1 / r := by positivity
  rw [hev] at hX ⊢
  rw [hperim] at hdlper ⊢
  have hXc : ∀ s, HasDerivAt (circleFront r)
      (Complex.exp (Complex.I * ((circleAngle r s : ℝ) : ℂ))) s := hasDerivAt_circleFront hr0
  have hKeq : ∀ s, K s = 1 / r := fun s =>
    SelectedInverseTube.curvature_unique hX hXc hΘ (fun t => hasDerivAt_circleAngle t) s
  set d0 : ℝ := Real.arcsin (1 / r) with hd0
  have hsin : Real.sin d0 = 1 / r := Real.sin_arcsin (by linarith) hkap1.le
  have hd0nonneg : 0 ≤ d0 := Real.arcsin_nonneg.mpr hkmin.le
  have hd0le : d0 ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hdlconst : dl = fun _ => d0 := by
    refine Shadowing.steering_unique (K := K) hppos hdlode ?_ hdlper (fun s => by simp) ?_ ?_
    · intro s
      have : K s - Real.sin d0 = 0 := by rw [hKeq s, hsin]; ring
      rw [this]
      exact hasDerivAt_const s d0
    · intro s
      exact ⟨by linarith [(hdlmem s).1],
        le_trans (hdlmem s).2 (Real.arcsin_le_pi_div_two kap)⟩
    · exact fun s => ⟨by linarith, hd0le⟩
  rw [hdlconst]
  have hexp : ∀ s, Complex.exp (Complex.I * (Θ s : ℂ))
      = Complex.exp (Complex.I * ((circleAngle r s : ℝ) : ℂ)) := fun s => (hX s).unique (hXc s)
  have hrear : rearTrack (circleFront r) Θ (fun _ => d0)
      = rearTrack (circleFront r) (circleAngle r) (fun _ => d0) := by
    funext s
    simp only [rearTrack, rearAngle]
    congr 1
    have hsplitΘ : ((Θ s - d0 : ℝ) : ℂ) = (Θ s : ℂ) + ((-d0 : ℝ) : ℂ) := by push_cast; ring
    have hsplitA : ((circleAngle r s - d0 : ℝ) : ℂ)
        = ((circleAngle r s : ℝ) : ℂ) + ((-d0 : ℝ) : ℂ) := by push_cast; ring
    rw [hsplitΘ, hsplitA, mul_add, mul_add, Complex.exp_add, Complex.exp_add, hexp s]
  rw [hrear]
  exact SelectedInverseCircle.injOn_rearTrack_circle hr d0

/-! ### The smooth dilation of a circle -/

/-- The radius of the circle at time `t`: `1 / sin A(t)`. -/
def rad (t : ℝ) : ℝ := 1 / sA t

/-- Its time derivative. -/
def radD (t : ℝ) : ℝ := -sAd t / sA t ^ 2

theorem rad_pos (t : ℝ) : 0 < rad t := by
  rw [rad]
  exact div_pos one_pos (sA_pos t)

theorem one_lt_rad (t : ℝ) : 1 < rad t := by
  have h1 : sA t ≤ Real.sin (Real.pi / 4) := sA_le t
  have h2 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_nonneg 2]
  rw [rad, lt_div_iff₀ (sA_pos t)]
  linarith

/-- The path starts at the circle of radius `√2`. -/
theorem rad_zero : rad 0 = Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  rw [rad, sA_zero]
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- and ends at the circle of radius `2`: the two ends are genuinely different
circles. -/
theorem rad_one : rad 1 = 2 := by
  rw [rad, sA_one]; norm_num

theorem hasDerivAt_rad (t : ℝ) : HasDerivAt rad (radD t) t := by
  have h := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_sAd t) (sA_ne t)
  refine h.congr_deriv ?_
  rw [radD]
  field_simp
  ring

theorem contDiff_rad {n : ℕ} : ContDiff ℝ n rad := by
  have h : ContDiff ℝ (n : WithTop ℕ∞) sA := contDiff_sA.of_le (by exact ENat.LEInfty.out)
  exact contDiff_const.div h (fun t => sA_ne t)

theorem continuous_radD : Continuous radD := by
  rw [show radD = fun t => -sAd t / sA t ^ 2 from rfl]
  exact (contDiff_sAd.continuous.neg).div (contDiff_sA.continuous.pow 2)
    (fun t => pow_ne_zero 2 (sA_ne t))

theorem radD_eq_zero_outside {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) : radD t = 0 := by
  rw [radD, sAd, profD_eq_zero_outside ht]
  simp

/-- The front period of the circle of radius `rad t` is `Pp t = 2π / sin A(t)`. -/
theorem Pp_eq_two_pi_mul_rad (t : ℝ) : Pp t = 2 * Real.pi * rad t := by
  rw [Pp, rad]; ring

theorem Pp_pos (t : ℝ) : 0 < Pp t := by
  rw [Pp]
  exact div_pos (by positivity) (sA_pos t)

/-- **The smooth dilation of a circle.**  The circles of radius `1 / sin A(t)`,
moving along their inward unit normal `−e^{2πiu}`; at rest outside `(0,1)`
because the profile is, and joining the marked circle of radius `1 / sin A(0)`
to the marked circle of radius `1 / sin A(1)`. -/
def circlePath : NormalPath (circleData (rad 0)) (circleData (rad 1)) where
  T := 1
  T_pos := one_pos
  X := fun t u => ((rad t : ℝ) : ℂ) * normExp u
  eta := fun t _ => -radD t
  nu := fun _ u => -normExp u
  m := fun t => |radD t|
  start := fun _ => rfl
  finish := fun _ => rfl
  hasDerivAt_time := by
    intro t u
    have h := ((hasDerivAt_rad t).ofReal_comp.mul_const (normExp u))
    refine h.congr_deriv ?_
    push_cast
    ring
  cont_vel := fun u => by
    have h : Continuous fun t : ℝ => ((-radD t : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_radD.neg
    exact h.mul continuous_const
  norm_nu := fun _ u => by simp
  cont_m := continuous_radD.abs
  m_nonneg := fun _ => abs_nonneg _
  m_stop := fun t ht => by rw [radD_eq_zero_outside ht, abs_zero]
  abs_eta_le := fun t _ => by rw [abs_neg]
  le_m_L1 := fun t => by simp
  le_m_sup := fun t j hj => by
    match j, hj with
    | 0, _ => simp [MarkedTopology.supNorm]
    | 1, _ =>
      rw [show (1 : ℕ) = 0 + 1 from rfl, MovingCirclePath.iteratedDeriv_const_succ,
        MovingCirclePath.supNorm_const, abs_zero]
      exact abs_nonneg _
    | 2, _ =>
      rw [show (2 : ℕ) = 1 + 1 from rfl, MovingCirclePath.iteratedDeriv_const_succ,
        MovingCirclePath.supNorm_const, abs_zero]
      exact abs_nonneg _

@[simp] theorem circlePath_T : circlePath.T = 1 := rfl

/-! ### The path genuinely moves -/

theorem profD_nonpos (t : ℝ) : profD t ≤ 0 := by
  have hanti : Antitone prof := by
    intro a b hab
    have h : Real.smoothTransition (2 * a - 1 / 2) ≤ Real.smoothTransition (2 * b - 1 / 2) :=
      Real.smoothTransition.monotone (by linarith)
    have hpi := Real.pi_pos
    simp only [prof]
    nlinarith
  exact hanti.deriv_nonpos

theorem radD_nonneg (t : ℝ) : 0 ≤ radD t := by
  have h : 0 ≤ -(cA t * profD t) :=
    neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (cA_pos t).le (profD_nonpos t))
  rw [radD, sAd]
  exact div_nonneg h (by positivity)

/-- **The cost of the path is `2 − √2`**: the radius really moves, so the
instance is not degenerate. -/
theorem cost_circlePath : cost circlePath = 2 - Real.sqrt 2 := by
  have hcong : cost circlePath = ∫ t in (0 : ℝ)..1, radD t := by
    rw [cost]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    exact abs_of_nonneg (radD_nonneg t)
  rw [hcong, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_rad t) (continuous_radD.intervalIntegrable 0 1), rad_zero, rad_one]

theorem cost_circlePath_pos : 0 < cost circlePath := by
  rw [cost_circlePath]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

@[simp] theorem circlePath_X (t u : ℝ) :
    circlePath.X t u = ((rad t : ℝ) : ℂ) * normExp u := rfl

@[simp] theorem circlePath_nu (t u : ℝ) : circlePath.nu t u = -normExp u := rfl

/-! ### The velocity, acceleration, curvature and tangent angle of the slices -/

/-- The velocity of the slice at time `t`, in the normalized parameter. -/
def Vc : ℝ → ℝ → ℂ := fun t u => ((Pp t : ℝ) : ℂ) * Complex.I * normExp u

/-- Its acceleration. -/
def Ac : ℝ → ℝ → ℂ := fun t u => -((2 * Real.pi * Pp t : ℝ) : ℂ) * normExp u

theorem hasDerivAt_Vc (t u : ℝ) : HasDerivAt (circlePath.X t) (Vc t u) u := by
  have h := (hasDerivAt_normExp u).const_mul ((rad t : ℝ) : ℂ)
  have hfun : circlePath.X t = fun u => ((rad t : ℝ) : ℂ) * normExp u := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  rw [Vc, Pp_eq_two_pi_mul_rad]
  push_cast
  ring

theorem hasDerivAt_Ac (t u : ℝ) : HasDerivAt (Vc t) (Ac t u) u := by
  have h := (hasDerivAt_normExp u).const_mul (((Pp t : ℝ) : ℂ) * Complex.I)
  have hfun : Vc t = fun u => ((Pp t : ℝ) : ℂ) * Complex.I * normExp u := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  rw [Ac]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_Vc (t u : ℝ) : ‖Vc t u‖ = Pp t := by
  rw [Vc]
  simp [norm_normExp, abs_of_pos (Pp_pos t)]

theorem im_conj_Vc_mul_Ac (t u : ℝ) :
    ((starRingEnd ℂ) (Vc t u) * Ac t u).im = 2 * Real.pi * Pp t ^ 2 := by
  have hconj : (starRingEnd ℂ) (Vc t u)
      = ((Pp t : ℝ) : ℂ) * (-Complex.I) * (starRingEnd ℂ) (normExp u) := by
    rw [Vc, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [hconj, Ac]
  have hmul : (((Pp t : ℝ) : ℂ) * (-Complex.I) * (starRingEnd ℂ) (normExp u))
      * (-((2 * Real.pi * Pp t : ℝ) : ℂ) * normExp u)
      = ((2 * Real.pi * Pp t ^ 2 : ℝ) : ℂ) * Complex.I
        * ((starRingEnd ℂ) (normExp u) * normExp u) := by
    push_cast
    ring
  rw [hmul, conj_mul_normExp, mul_one]
  simp only [Complex.mul_I_im, Complex.ofReal_re]

theorem curvOfPath_circlePath (t s : ℝ) : curvOfPath Vc Ac Pp t s = Kk t (s / Pp t) := by
  rw [curvOfPath, im_conj_Vc_mul_Ac, Kk, Pp_eq_two_pi_mul_rad, rad]
  have hs := sA_pos t
  have hpi := Real.pi_pos
  field_simp

theorem angleOfPath_circlePath (t s : ℝ) :
    angleOfPath Vc Ac Pp t s = Real.pi / 2 + s * sA t := by
  have hPne : ((Pp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Pp_pos t).ne'
  have htan : tangentOfPath Vc Pp t 0 = Complex.I := by
    rw [tangentOfPath, Vc, zero_div]
    have h0 : normExp 0 = 1 := by simp [normExp]
    rw [h0]
    field_simp
  have hint : (∫ x in (0 : ℝ)..s, curvOfPath Vc Ac Pp t x) = s * sA t := by
    have hcong : (∫ x in (0 : ℝ)..s, curvOfPath Vc Ac Pp t x)
        = ∫ _x in (0 : ℝ)..s, sA t := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [curvOfPath_circlePath, Kk]
    rw [hcong]
    simp
  rw [angleOfPath, htan, hint, Complex.arg_I]

/-! ### The instance -/

/-- **The hypotheses of the shift bound with the steering data produced are
consistent.**  They hold for the smooth dilation of a circle: the family of
circles of radius `1 / sin A(t)`, whose ends are the marked circles of radius
`1 / sin A(0) = √2` and `1 / sin A(1) = 2`.  The selected steering angle, its
arclength form and the change of variable from the rear to the front arclength
are produced from the curvature alone, and the two marked selected inverses of
the ends are at distance, modulo the marking, at most a constant times the cost
of the path. -/
theorem circlePath_shift_instance :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin (Real.sin (Real.pi / 4)))) ∧
      (∀ t σ, HasDerivAt (dn t) (Pp t * (Kk t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / Pp t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ (C : ℝ) (Phi : ℝ → ℝ → ℝ),
        (∀ u, Phi 0 u
          = perim (SelectedInverseMap.selInv (Real.sin (Real.pi / 4))
              (circleData (rad 0))) * u) ∧
        ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
          0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
          (∀ u, HasDerivAt (Phi 1) (dPhi u) u) →
          (∀ u, q'.1 u
            = (SelectedInverseMap.selInv (Real.sin (Real.pi / 4))
                (circleData (rad 1))).1
                (Phi 1 u / perim (SelectedInverseMap.selInv (Real.sin (Real.pi / 4))
                  (circleData (rad 1))))) →
          MarkedShift.pathDistShift
              (SelectedInverseMap.selInv (Real.sin (Real.pi / 4)) (circleData (rad 0)))
              (SelectedInverseMap.selInv (Real.sin (Real.pi / 4)) (circleData (rad 1)))
            ≤ C * cost circlePath := by
  have hpi := Real.pi_pos
  have hsin4 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hsin4pos : 0 ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  obtain ⟨Md, hMd0, hMd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAd t| ≤ M :=
    SecondOrderBounds.exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAd.continuous) (fun x hx => sAd_eq_zero_outside hx)
  obtain ⟨CKb, hCK0, hCK⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAdd t| ≤ M :=
    SecondOrderBounds.exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAdd.continuous) (fun x hx => sAdd_eq_zero_outside hx)
  -- the tube data of the two ends
  have htube : ∀ t : ℝ, IsTubeMember (2 * Real.pi * rad t) (1 / rad t) (4 * rad t)
      (circleData (rad t)) := fun t => circleData_mem_tube (rad_pos t)
  have hcurv : ∀ t u, ((starRingEnd ℂ) ((circleData (rad t)).2.1 u)
      * (circleData (rad t)).2.2 u).im
      ≤ Real.sin (Real.pi / 4) * ‖(circleData (rad t)).2.1 u‖ ^ 3 := by
    intro t u
    have h := SelectedInverseTubeCircle.circleData_curvature_le (rad_pos t) u
    have hle : 1 / rad t ≤ Real.sin (Real.pi / 4) := by
      rw [rad, one_div_one_div]
      exact sA_le t
    have hnn : (0 : ℝ) ≤ ‖(circleData (rad t)).2.1 u‖ ^ 3 := by positivity
    nlinarith
  obtain ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, hrest⟩ :=
    SelectedInverseRearOwnShiftSteering.exists_steering_pathDistShift_selInv_le
      (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
      (P := Pp) (Pd := Ppd) (V := Vc) (A := Ac)
      (Kn := Kk) (Kdn := fun t _ => sAd t)
      (Md := Md) (MP := 8 * Real.pi * Md) (Klip := Md) (Plip := 8 * Real.pi * Md)
      (CK := CKb) (CP := 16 * Real.pi * (CKb + 2 * Md ^ 2))
      (c := 2 * Real.pi * rad 0) (kmin := 1 / rad 0) (dlt := 4 * rad 0)
      (cq := 2 * Real.pi * rad 1) (kminq := 1 / rad 1) (dltq := 4 * rad 1)
      circlePath
      (by have := rad_pos 0; positivity) (by have := rad_pos 0; positivity)
      (htube 0) (hcurv 0)
      (fun Θ' K' dl hX hΘ hper hmem hode =>
        injOn_rearTrack_evCircleData_strip (one_lt_rad 0) Θ' K' dl hX hΘ hper hmem hode)
      (by have := rad_pos 1; positivity) (by have := rad_pos 1; positivity)
      (htube 1) (hcurv 1)
      (fun Θ' K' dl hX hΘ hper hmem hode =>
        injOn_rearTrack_evCircleData_strip (one_lt_rad 1) Θ' K' dl hX hΘ hper hmem hode)
      (by positivity) hsin4pos hsin4
      (fun t => by
        rw [Pp, le_div_iff₀ (sA_pos t)]
        nlinarith [sA_le t, Real.sin_le_one (prof t), sA_pos t])
      (fun t => by
        rw [Pp, div_le_iff₀ (sA_pos t)]
        nlinarith [sA_ge t])
      hasDerivAt_Vc hasDerivAt_Ac
      (fun t => (continuous_const.mul continuous_normExp))
      norm_Vc
      (fun t u => by simp [periodic_normExp u])
      (fun t u => by simp [Vc, periodic_normExp u])
      (fun t u => by simp [Ac, periodic_normExp u])
      (fun t => by
        have hval : ∀ u : ℝ, ((starRingEnd ℂ) (Vc t u) * Ac t u).im / Pp t ^ 2
            = 2 * Real.pi := by
          intro u
          rw [im_conj_Vc_mul_Ac, mul_div_assoc, div_self (pow_ne_zero 2 (Pp_pos t).ne'),
            mul_one]
        simp only [hval]
        simp)
      (fun t u => by
        have hPne : ((Pp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Pp_pos t).ne'
        rw [circlePath_nu, Vc]
        field_simp
        rw [Complex.I_sq]
        ring)
      curvOfPath_circlePath
      (fun t σ => rfl) (fun t σ => rfl)
      (fun t σ => (sA_pos t).le) (fun t σ => sA_le t)
      (fun t σ => hMd t) (abs_Ppd_le hMd)
      (fun a b σ => by
        simpa [Kk] using SecondOrderBounds.abs_sub_le_of_deriv_bound hasDerivAt_sAd hMd a b)
      (fun a b => SecondOrderBounds.abs_sub_le_of_deriv_bound hasDerivAt_Pp (abs_Ppd_le hMd) a b)
      (fun a b σ => by
        simpa [Kk] using
          SecondOrderBounds.abs_taylor_quadratic hasDerivAt_sAd hasDerivAt_sAdd hCK a b)
      (fun a b => SecondOrderBounds.abs_taylor_quadratic hasDerivAt_Pp hasDerivAt_Ppd
        (abs_Ppdd_le hMd hCK) a b)
      hCK0 (by positivity)
      (contDiff_Pp 4) (contDiff_Ppd 3)
      (by
        have h : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sA :=
          contDiff_sA.of_le (by exact ENat.LEInfty.out)
        simpa [Kk, uncurry] using h.comp contDiff_fst)
      (by
        have h : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sAd :=
          contDiff_sAd.of_le (by exact ENat.LEInfty.out)
        simpa [uncurry] using h.comp contDiff_fst)
      (by
        have hfun : uncurry (frontOfPath circlePath.X Pp)
            = fun p : ℝ × ℝ => ((rad p.1 : ℝ) : ℂ)
                * Complex.exp (((2 * Real.pi * (p.2 / Pp p.1) : ℝ) : ℂ) * Complex.I) := by
          funext p
          rw [uncurry, frontOfPath, circlePath_X, normExp_eq]
        rw [hfun]
        have hr : ContDiff ℝ (4 : ℕ) fun p : ℝ × ℝ => ((rad p.1 : ℝ) : ℂ) :=
          contDiff_ofReal.comp (contDiff_rad.comp contDiff_fst)
        have hP : ContDiff ℝ (4 : ℕ) fun p : ℝ × ℝ => Pp p.1 :=
          (contDiff_Pp 4).comp contDiff_fst
        have harg : ContDiff ℝ (4 : ℕ)
            fun p : ℝ × ℝ => ((2 * Real.pi * (p.2 / Pp p.1) : ℝ) : ℂ) * Complex.I := by
          have hq : ContDiff ℝ (4 : ℕ) fun p : ℝ × ℝ => (2 * Real.pi * (p.2 / Pp p.1) : ℝ) :=
            contDiff_const.mul (contDiff_snd.div hP (fun p => (Pp_pos p.1).ne'))
          exact (contDiff_ofReal.comp hq).mul contDiff_const
        exact hr.mul
          (((Complex.contDiff_exp (𝕜 := ℂ) (n := (4 : ℕ))).restrict_scalars ℝ).comp harg))
      (by
        have hfun : uncurry (angleOfPath Vc Ac Pp)
            = fun p : ℝ × ℝ => Real.pi / 2 + p.2 * sA p.1 := by
          funext p
          rw [uncurry, angleOfPath_circlePath]
        rw [hfun]
        have h : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) sA :=
          contDiff_sA.of_le (by exact ENat.LEInfty.out)
        exact contDiff_const.add (contDiff_snd.mul (h.comp contDiff_fst)))
  refine ⟨dn, δ, sf, hdnper, hstrip, hsol, hδ, hsf, ?_⟩
  obtain ⟨EF, -, -, Phi, hPhi0, -, hPhi⟩ := hrest
  exact ⟨_, Phi, hPhi0, fun q' dPhi {_ _ _} hcq' hkq' hdq' hq' hdiff hcomp =>
    hPhi q' dPhi hcq' hkq' hdq' hq' hdiff hcomp⟩

end SmoothCircleShiftInstance
