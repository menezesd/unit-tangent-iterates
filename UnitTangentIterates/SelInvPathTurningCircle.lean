import Mathlib
import UnitTangentIterates.SelInvPathTurningC2

/-!
# The `C²` estimate on the path of fronts is not vacuous

`SelInvPathTurningC2.dist_selInv_le_modulus_of_path_turning_C2` states the `C²`
comparison of the two marked selected inverses of the ends of a normal path with
every hypothesis on the *path*.  This file checks that the hypothesis block is
consistent, on the simplest path there is: the **resting circle** of radius
`r > 1`, which does not move at all, so that its cost is zero and its two ends
coincide.

Everything asked of the path holds: the slices are the marked circle, of
constant speed `2πr`, closed, of curvature `1/r` pinched between `1/r` and
`1/r`, with `(1/r)·2πr = 2π < 4π`; the unit normal of the path is the standard
one of the slices, `−e^{2πiu}`; and the marked point is at rest.

Main results: `restCirclePath`, `restCircle_instance`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathTurningCircle

open UniformFrameBounds RearOwnHigherRegularity FrontFromPath
  SelInvFrontCostC2 RearJacobiSourceCost SelInvFrontStripC2
  SelInvPathRegularityC2 SelInvPathCurvatureC2 SelInvPathCurvBoundC2
  SelInvPathPerimC2 SelInvPathGaugeC2 SelInvPathBoundsC2 SelInvPathTurningC2
  GaugeMarkedDataOfRearFamily SelInvFrontChangeVarC2 SelInvFrontVelocityC2

/-- The normalized exponential is smooth. -/
theorem contDiff_normExp {n : ℕ} : ContDiff ℝ (n : ℕ) normExp := by
  have h : normExp = fun u : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (u : ℂ)) := by
    funext u; rw [normExp]; ring_nf
  rw [h]
  exact ((Complex.contDiff_exp (𝕜 := ℂ) (n := (n : ℕ))).restrict_scalars ℝ).comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- **The resting circle**: the normal path whose slices are all the marked
circle of radius `r`, moving with zero normal speed along the standard unit
normal `−e^{2πiu}` of the circle. -/
def restCirclePath (r : ℝ) : NormalPath (circleData r) (circleData r) where
  T := 1
  T_pos := one_pos
  X := fun _ u => (circleData r).1 u
  eta := fun _ _ => 0
  nu := fun _ u => -normExp u
  m := fun _ => 0
  start := fun _ => rfl
  finish := fun _ => rfl
  hasDerivAt_time := fun t u => by simpa using hasDerivAt_const t ((circleData r).1 u)
  cont_vel := fun _ => by simpa using continuous_const
  norm_nu := fun _ _ => by simp
  cont_m := continuous_const
  m_nonneg := fun _ => le_rfl
  m_stop := fun _ _ => rfl
  abs_eta_le := fun _ _ => by simp
  le_m_L1 := fun _ => by simp
  le_m_sup := fun _ j _ => by
    rw [iteratedDeriv_zero_fun j]
    simp [MarkedTopology.supNorm]

variable {r : ℝ}

theorem contDiff_uncurry_restCirclePath {n : ℕ} :
    ContDiff ℝ (n : ℕ) (uncurry (restCirclePath r).X) := by
  have h : uncurry (restCirclePath r).X = fun z : ℝ × ℝ => (r : ℂ) * normExp z.2 := rfl
  rw [h]
  exact contDiff_const.mul (contDiff_normExp.comp contDiff_snd)

theorem differentiable_uncurry_restCirclePath :
    Differentiable ℝ (uncurry (restCirclePath r).X) :=
  (contDiff_uncurry_restCirclePath (n := 1)).differentiable (by norm_num)

theorem pathVel_restCirclePath (hr : 0 < r) (t u : ℝ) :
    pathVel (restCirclePath r).X t u = (circleData r).2.1 u :=
  pathVel_eq_of_slice differentiable_uncurry_restCirclePath (fun _ => rfl)
    (circleData_mem_tube hr).hasDerivAt_curve u

theorem pathAcc_restCirclePath (hr : 0 < r) (t u : ℝ) :
    pathAcc (restCirclePath r).X t u = (circleData r).2.2 u :=
  pathAcc_eq_of_slice (contDiff_uncurry_restCirclePath (n := 2)) (fun _ => rfl)
    (circleData_mem_tube hr).hasDerivAt_curve (circleData_mem_tube hr).hasDerivAt_vel u

theorem norm_vel_circleData (hr : 0 < r) (u : ℝ) :
    ‖(circleData r).2.1 u‖ = 2 * Real.pi * r := by
  rw [circleData_vel]
  simp [abs_of_pos Real.pi_pos, abs_of_pos hr]

theorem pathPerim_restCirclePath (hr : 0 < r) (t : ℝ) :
    pathPerim (restCirclePath r).X t = 2 * Real.pi * r := by
  show ‖pathVel (restCirclePath r).X t 0‖ = 2 * Real.pi * r
  rw [pathVel_restCirclePath hr, norm_vel_circleData hr]

/-- The numerator of the curvature of the circle. -/
theorem im_conj_vel_mul_acc (u : ℝ) :
    ((starRingEnd ℂ) ((circleData r).2.1 u) * (circleData r).2.2 u).im
      = 8 * Real.pi ^ 3 * r ^ 2 := by
  have he : (starRingEnd ℂ) (normExp u) * normExp u = 1 := conj_mul_normExp u
  have hprod : (starRingEnd ℂ) ((circleData r).2.1 u) * (circleData r).2.2 u
      = ((8 * Real.pi ^ 3 * r ^ 2 : ℝ) : ℂ) * Complex.I := by
    rw [circleData_vel, circleData_acc, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
    calc ((2 * Real.pi * r : ℝ) : ℂ) * -Complex.I * (starRingEnd ℂ) (normExp u) *
          (-((4 * Real.pi ^ 2 * r : ℝ) : ℂ) * normExp u)
        = (((2 * Real.pi * r : ℝ) : ℂ) * ((4 * Real.pi ^ 2 * r : ℝ) : ℂ)) * Complex.I *
            ((starRingEnd ℂ) (normExp u) * normExp u) := by ring
      _ = ((8 * Real.pi ^ 3 * r ^ 2 : ℝ) : ℂ) * Complex.I := by
          rw [he, mul_one]; push_cast; ring
  rw [hprod, Complex.mul_I_im, Complex.ofReal_re]

theorem pathKn_restCirclePath (hr : 0 < r) (t σ : ℝ) :
    pathKn (restCirclePath r).X (pathPerim (restCirclePath r).X) t σ = 1 / r := by
  have hne : (2 : ℝ) * Real.pi * r ≠ 0 := by positivity
  rw [pathKn, curvOfPath, pathPerim_restCirclePath hr]
  have hcancel : σ * (2 * Real.pi * r) / (2 * Real.pi * r) = σ := by field_simp
  rw [hcancel, pathVel_restCirclePath hr, pathAcc_restCirclePath hr, im_conj_vel_mul_acc]
  field_simp
  ring

/-- **The hypothesis block of the `C²` estimate on the path is consistent.**
Every hypothesis of `dist_selInv_le_modulus_of_path_turning_C2` holds for the
resting circle of radius `r > 1`. -/
theorem restCircle_instance (hr : 1 < r) :
    ∃ P0 P1 : ℝ, 0 < P0 ∧ (∀ t, P0 ≤ pathPerim (restCirclePath r).X t) ∧
      (∀ t, pathPerim (restCirclePath r).X t ≤ P1) ∧
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin (1 / r))) ∧
      (∀ t σ, HasDerivAt (dn t) ((pathPerim (restCirclePath r).X) t * (pathKn (restCirclePath r).X (pathPerim (restCirclePath r).X) t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / (pathPerim (restCirclePath r).X) t)) ∧
      ∀ (Rb : ℝ → ℝ) (khat rr : ℝ),
        rearKappa1 (1 / r) ≤ khat →
        (∀ t x,
          |frameTangential (rearOwnVelocity (restCirclePath r).X (pathVel (restCirclePath r).X) (pathAcc (restCirclePath r).X) (pathPerim (restCirclePath r).X) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel (restCirclePath r).X) (pathAcc (restCirclePath r).X) (pathPerim (restCirclePath r).X)) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t x| ≤ Rb t) →
        (∀ t, Rb t ≤ rr * (restCirclePath r).m t) → 0 ≤ rr →
        RearCostDensity.rearCostConst (1 / r) khat (rearKappa2 (1 / r))
            (rearArclength (δ 0) ((pathPerim (restCirclePath r).X) 0)) (jacobiSourceConst (1 / r) P0) * cost (restCirclePath r) ≤ 1 →
      dist (SelectedInverseMap.selInv (1 / r) (circleData r)) (SelectedInverseMap.selInv (1 / r) (circleData r))
        ≤ selInvFrontModulus P1 (1 / r) (perim (SelectedInverseMap.selInv (1 / r) (circleData r)))
            (perim (SelectedInverseMap.selInv (1 / r) (circleData r))) ((1 / r) / Real.sqrt (1 - (1 / r) ^ 2))
            (2 * (1 / r) / Real.sqrt (1 - (1 / r) ^ 2) ^ 3) (pathPv0 (1 / r) P0 khat rr) khat (jacobiSourceConst (1 / r) P0)
            (cost (restCirclePath r)) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hpi := Real.pi_pos
  have hp := circleData_mem_tube hr0
  have hc : 0 < 2 * Real.pi * r := by positivity
  have hkmin : 0 < 1 / r := by positivity
  have hkh1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have hXC6 : ContDiff ℝ (6 : ℕ) (uncurry (restCirclePath r).X) :=
    contDiff_uncurry_restCirclePath
  have hconst : ∀ t u, ‖pathVel (restCirclePath r).X t u‖
      = ‖pathVel (restCirclePath r).X t 0‖ := by
    intro t u
    rw [pathVel_restCirclePath hr0, pathVel_restCirclePath hr0,
      norm_vel_circleData hr0, norm_vel_circleData hr0]
  have hXper : ∀ t, Periodic ((restCirclePath r).X t) 1 := by
    intro t u
    show (r : ℂ) * normExp (u + 1) = (r : ℂ) * normExp u
    rw [periodic_normExp u]
  have hnu : ∀ t u, (restCirclePath r).nu t u
      = Complex.I * (pathVel (restCirclePath r).X t u
          / ((pathPerim (restCirclePath r).X t : ℝ) : ℂ)) := by
    intro t u
    rw [pathVel_restCirclePath hr0, pathPerim_restCirclePath hr0, circleData_vel]
    have hne : ((2 * Real.pi * r : ℝ) : ℂ) ≠ 0 := by
      simpa using (ne_of_gt hc)
    show -normExp u = _
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hKn := pathKn_restCirclePath (r := r) hr0
  have hkminP : (0 : ℝ) < 1 / r := hkmin
  have hKnmin : ∀ t σ, 1 / r
      ≤ pathKn (restCirclePath r).X (pathPerim (restCirclePath r).X) t σ :=
    fun t σ => le_of_eq (hKn t σ).symm
  have hKnk : ∀ t σ, pathKn (restCirclePath r).X (pathPerim (restCirclePath r).X) t σ
      ≤ 1 / r := fun t σ => le_of_eq (hKn t σ)
  have hshort : ∀ t, 1 / r * pathPerim (restCirclePath r).X t < 4 * Real.pi := by
    intro t
    rw [pathPerim_restCirclePath hr0]
    have h : 1 / r * (2 * Real.pi * r) = 2 * Real.pi := by field_simp
    rw [h]
    linarith
  have hslit : ∀ t, pathVel (restCirclePath r).X t 0 ∈ Complex.slitPlane := by
    intro t
    rw [pathVel_restCirclePath hr0, circleData_vel]
    right
    have h0 : normExp 0 = 1 := by simp [normExp]
    rw [h0, mul_one]
    simp
    positivity
  have hmark : ∀ t, (restCirclePath r).eta t 0 = 0 := fun _ => rfl
  exact dist_selInv_le_modulus_of_path_turning_C2 (restCirclePath r) hc hkmin hp hc hkmin hp
    hkh1 hXC6 hconst hXper hnu hkminP hKnmin hKnk hshort hslit hmark

end SelInvPathTurningCircle
