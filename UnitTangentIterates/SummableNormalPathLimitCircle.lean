import Mathlib
import UnitTangentIterates.SummableNormalPathLimit
import UnitTangentIterates.MarkedSpaceCircle
import UnitTangentIterates.MovingCirclePath

/-!
# A sequence of circles: the completeness lemma is not vacuous

The hypotheses of `SummableNormalPathLimit.exists_limit_of_summable_costs` — a
sequence of marked curves of one tube, joined by normal paths with
constant-speed slices in the normal gauge, of summable cost — are checked here
on a genuinely moving sequence: the circles of radii `rₙ = 1 + 2^{-n}`, joined
by the dilations that interpolate between two consecutive radii along the
smooth time profile of `MovingCircleProfile.lean`.

A dilation of a circle *is* a normal motion: the radial direction is the normal
one, so the slice `X(t,u) = R(t)e^{2πiu}` moves with velocity `R'(t)e^{2πiu}`,
purely normal and constant in the arclength; its cost density is `|R'(t)|`, and
the cost of the `n`-th path is `2^{-(n+1)}∫₀¹|w'|`, a geometric sequence.

Main results:

* `isConstantSpeedNormalPath_circlePath` — the geometric hypotheses of the
  increment bound hold for the dilation, with `P₀ = 2π`, `P₁ = 4π`, `κ̂ = 1`;
* `summable_cost_circlePath` — the costs are summable;
* `circle_sequence_limit` — the conclusion: the sequence of circles converges
  to a marked curve of the tube;
* `circle_sequence_limit_eq` — the limit is the circle of radius one.
-/

noncomputable section

open Set Function Complex Filter Topology MarkedSpace PathMetric PathMetric.NormalPath
open MovingCircleProfile NormalPathC2Increment

namespace SummableNormalPathLimitCircle

/-! ### The time profile -/

/-- The time profile of the dilation: `0` up to `1/4`, `1` from `3/4` on,
smooth, obtained from the profile of `MovingCircleProfile.lean` by an affine
change. -/
def w (t : ℝ) : ℝ := (Real.pi / 4 - prof t) * (12 / Real.pi)

/-- The derivative of the time profile. -/
def wD (t : ℝ) : ℝ := -profD t * (12 / Real.pi)

theorem hasDerivAt_w (t : ℝ) : HasDerivAt w (wD t) t := by
  have h := ((hasDerivAt_prof t).const_sub (Real.pi / 4)).mul_const (12 / Real.pi)
  exact h

theorem continuous_wD : Continuous wD :=
  (contDiff_profD.continuous.neg).mul continuous_const

theorem wD_eq_zero_outside {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) : wD t = 0 := by
  simp [wD, profD_eq_zero_outside ht]

@[simp] theorem w_zero : w 0 = 0 := by simp [w, prof_zero]

@[simp] theorem w_one : w 1 = 1 := by
  have hpi := Real.pi_pos
  rw [w, prof_one]
  field_simp
  ring

theorem w_nonneg (t : ℝ) : 0 ≤ w t := by
  have hpi := Real.pi_pos
  have h := prof_le t
  have h12 : 0 < 12 / Real.pi := by positivity
  exact mul_nonneg (by linarith) h12.le

theorem w_le_one (t : ℝ) : w t ≤ 1 := by
  have hpi := Real.pi_pos
  have h := prof_ge t
  have h12 : (0:ℝ) < 12 / Real.pi := by positivity
  rw [w, ← sub_nonneg,
    show 1 - (Real.pi / 4 - prof t) * (12 / Real.pi)
      = (prof t - Real.pi / 6) * (12 / Real.pi) by field_simp; ring]
  exact mul_nonneg (by linarith) h12.le

/-! ### The radii and the dilations -/

/-- The radii of the sequence of circles: `rₙ = 1 + 2^{-n}`. -/
def rad (n : ℕ) : ℝ := 1 + (1 / 2 : ℝ) ^ n

theorem rad_ge (n : ℕ) : 1 ≤ rad n := by
  have : (0:ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  unfold rad; linarith

theorem rad_le (n : ℕ) : rad n ≤ 2 := by
  have h : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold rad; linarith

theorem rad_pos (n : ℕ) : 0 < rad n := lt_of_lt_of_le one_pos (rad_ge n)

theorem rad_sub (n : ℕ) : rad (n + 1) - rad n = -(1 / 2 : ℝ) ^ (n + 1) := by
  simp [rad, pow_succ]
  ring

theorem abs_rad_sub (n : ℕ) : |rad (n + 1) - rad n| = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [rad_sub, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 / 2 : ℝ) ^ (n + 1))]

/-- The radius of the `n`-th dilation at time `t`. -/
def R (n : ℕ) (t : ℝ) : ℝ := rad n + (rad (n + 1) - rad n) * w t

/-- Its time derivative. -/
def Rd (n : ℕ) (t : ℝ) : ℝ := (rad (n + 1) - rad n) * wD t

theorem hasDerivAt_R (n : ℕ) (t : ℝ) : HasDerivAt (R n) (Rd n t) t := by
  have h := ((hasDerivAt_w t).const_mul (rad (n + 1) - rad n)).const_add (rad n)
  exact h

theorem continuous_Rd (n : ℕ) : Continuous (Rd n) := continuous_const.mul continuous_wD

theorem Rd_eq_zero_outside {n : ℕ} {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) : Rd n t = 0 := by
  simp [Rd, wD_eq_zero_outside ht]

@[simp] theorem R_zero (n : ℕ) : R n 0 = rad n := by simp [R]

@[simp] theorem R_one (n : ℕ) : R n 1 = rad (n + 1) := by simp [R]

theorem R_ge (n : ℕ) (t : ℝ) : 1 ≤ R n t := by
  have h0 := w_nonneg t
  have h1 := w_le_one t
  have hn := rad_ge n
  have hn1 := rad_ge (n + 1)
  have hR : R n t = rad n * (1 - w t) + rad (n + 1) * w t := by rw [R]; ring
  rw [hR]
  nlinarith

theorem R_le (n : ℕ) (t : ℝ) : R n t ≤ 2 := by
  have h0 := w_nonneg t
  have h1 := w_le_one t
  have hn := rad_le n
  have hn1 := rad_le (n + 1)
  have hR : R n t = rad n * (1 - w t) + rad (n + 1) * w t := by rw [R]; ring
  rw [hR]
  nlinarith

theorem R_pos (n : ℕ) (t : ℝ) : 0 < R n t := lt_of_lt_of_le one_pos (R_ge n t)

theorem R_ne (n : ℕ) (t : ℝ) : R n t ≠ 0 := (R_pos n t).ne'

/-! ### The dilation as a normal path -/

theorem hasDerivAt_dilation (n : ℕ) (t u : ℝ) :
    HasDerivAt (fun r => ((R n r : ℝ) : ℂ) * normExp u)
      ((Rd n t : ℂ) * normExp u) t :=
  ((hasDerivAt_R n t).ofReal_comp).mul_const (normExp u)

/-- **The dilation of a circle is a normal path.**  The radial direction is the
normal direction, so the circle of radius `R(t)` moves with the purely normal
velocity `R'(t)e^{2πiu}`; the cost density `|R'(t)|` does not depend on the
arclength, so it dominates every density of the path metric. -/
def circlePath (n : ℕ) : NormalPath (circleData (rad n)) (circleData (rad (n + 1))) where
  T := 1
  T_pos := one_pos
  X := fun t u => ((R n t : ℝ) : ℂ) * normExp u
  eta := fun t _ => Rd n t
  nu := fun _ u => normExp u
  m := fun t => |Rd n t|
  start := fun u => by rw [circleData_fst, R_zero]
  finish := fun u => by rw [circleData_fst, R_one]
  hasDerivAt_time := fun t u => by
    simpa using hasDerivAt_dilation n t u
  cont_vel := fun u => by
    have : Continuous fun t : ℝ => ((Rd n t : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_Rd n)
    exact this.mul continuous_const
  norm_nu := fun _ u => by simp
  cont_m := (continuous_Rd n).abs
  m_nonneg := fun _ => abs_nonneg _
  m_stop := fun t ht => by rw [Rd_eq_zero_outside ht, abs_zero]
  abs_eta_le := fun _ _ => le_rfl
  le_m_L1 := fun t => by simp
  le_m_sup := fun t j hj => by
    match j, hj with
    | 0, _ => simp [MarkedTopology.supNorm]
    | 1, _ => simp [MovingCirclePath.iteratedDeriv_const_succ 0 (Rd n t), MarkedTopology.supNorm]
    | 2, _ => simp [MovingCirclePath.iteratedDeriv_const_succ 1 (Rd n t), MarkedTopology.supNorm]

@[simp] theorem circlePath_T (n : ℕ) : (circlePath n).T = 1 := rfl

@[simp] theorem circlePath_m (n : ℕ) (t : ℝ) : (circlePath n).m t = |Rd n t| := rfl

@[simp] theorem circlePath_X (n : ℕ) (t u : ℝ) :
    (circlePath n).X t u = ((R n t : ℝ) : ℂ) * normExp u := rfl

/-! ### The geometric data of the dilation -/

/-- The tangent angle of the circle in the normalized parameter. -/
def ang (u : ℝ) : ℝ := 2 * Real.pi * u + Real.pi / 2

theorem exp_ang (u : ℝ) :
    Complex.exp (Complex.I * ((ang u : ℝ) : ℂ)) = Complex.I * normExp u := by
  have hsplit : Complex.I * ((ang u : ℝ) : ℂ)
      = 2 * (Real.pi : ℂ) * (u : ℂ) * Complex.I + Complex.I * ((Real.pi / 2 : ℝ) : ℂ) := by
    rw [ang]; push_cast; ring
  rw [hsplit, Complex.exp_add]
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * (u : ℂ) * Complex.I) = normExp u := rfl
  have h2 : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_mul_I]
    push_cast
    simp
  rw [h1, h2]
  ring

/-- **The dilation satisfies the geometric hypotheses of the increment
bound.**  The slices are circles: their arclength period is `2πR(t)`, their
tangent angle `2πu + π/2` does not move, and their curvature is `1/R(t)`. -/
theorem isConstantSpeedNormalPath_circlePath (n : ℕ) :
    IsConstantSpeedNormalPath (2 * Real.pi) (4 * Real.pi) 1 (circlePath n) := by
  have hpi := Real.pi_pos
  refine ⟨fun t => 2 * Real.pi * R n t, fun t => 2 * Real.pi * Rd n t,
    fun _ u => ang u, fun t _ => (R n t)⁻¹, fun _ _ => 0,
    fun t _ => -(Rd n t) / R n t ^ 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t => mul_nonneg (by positivity) (R_pos n t).le
  · intro t
    have := R_le n t
    nlinarith
  · intro t u
    rw [abs_of_nonneg (inv_nonneg.2 (R_pos n t).le)]
    rw [inv_le_one_iff₀]
    exact Or.inr (R_ge n t)
  · intro t u
    have h := ((hasDerivAt_normExp u).const_mul ((R n t : ℝ) : ℂ))
    have hfun : (circlePath n).X t = fun u : ℝ => ((R n t : ℝ) : ℂ) * normExp u := rfl
    rw [hfun]
    refine h.congr_deriv ?_
    rw [exp_ang]
    push_cast
    ring
  · intro t u
    have h : HasDerivAt (fun v : ℝ => 2 * Real.pi * v + Real.pi / 2) (2 * Real.pi) u := by
      simpa using ((hasDerivAt_id u).const_mul (2 * Real.pi)).add_const (Real.pi / 2)
    refine h.congr_deriv ?_
    have hR := R_ne n t
    field_simp
  · exact fun t => ((hasDerivAt_R n t).const_mul (2 * Real.pi))
  · exact continuous_const.mul (continuous_Rd n)
  · intro t
    rw [circlePath_m, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    nlinarith [abs_nonneg (Rd n t)]
  · exact fun t u => hasDerivAt_const t (ang u)
  · exact fun u => continuous_const
  · intro t u
    rw [abs_zero, circlePath_m]
    positivity
  · intro t u
    exact (hasDerivAt_R n t).inv (R_ne n t)
  · exact fun u => ((continuous_Rd n).neg).div (continuous_id.pow 2 |>.comp
      (continuous_iff_continuousAt.2 fun t => (hasDerivAt_R n t).continuousAt))
      (fun t => pow_ne_zero 2 (R_ne n t))
  · intro t u
    rw [circlePath_m, abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ R n t ^ 2)]
    have h1 : (1:ℝ) ≤ R n t ^ 2 := by nlinarith [R_ge n t]
    have h2 : |Rd n t| / R n t ^ 2 ≤ |Rd n t| := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg (Rd n t)]
    have h4 : (0:ℝ) ≤ 1 / (2 * Real.pi) ^ 2 * |Rd n t| := by positivity
    have h3 : |Rd n t| ≤ (1 / (2 * Real.pi) ^ 2 + 1 ^ 2) * |Rd n t| := by nlinarith [h4]
    linarith

/-! ### The costs are summable -/

theorem cost_circlePath (n : ℕ) :
    cost (circlePath n) = (1 / 2 : ℝ) ^ (n + 1) * ∫ t in (0:ℝ)..1, |wD t| := by
  have h : cost (circlePath n) = ∫ t in (0:ℝ)..1, |Rd n t| := by
    rw [cost, circlePath_T]
    rfl
  rw [h]
  have habs : ∀ t, |Rd n t| = (1 / 2 : ℝ) ^ (n + 1) * |wD t| := by
    intro t
    rw [Rd, abs_mul, abs_rad_sub]
  simp_rw [habs]
  exact intervalIntegral.integral_const_mul _ _

theorem summable_cost_circlePath : Summable fun n => cost (circlePath n) := by
  have hgeo : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) := by
    have := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    simpa [pow_succ, mul_comm] using this.mul_right (1 / 2 : ℝ)
  simpa [cost_circlePath] using hgeo.mul_right (∫ t in (0:ℝ)..1, |wD t|)

/-! ### The circles all lie in one tube -/

/-- Tube membership only improves when the three constants are lowered. -/
theorem tube_mono {c c' kmin kmin' dlt dlt' : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) (hc : c' ≤ c) (hk : kmin' ≤ kmin) (hd : dlt' ≤ dlt) :
    IsTubeMember c' kmin' dlt' p := by
  refine ⟨hp.hasDerivAt_curve, hp.hasDerivAt_vel, hp.periodic, hp.speed_const,
    fun u => le_trans hc (hp.speed_lb u), fun u => ?_, fun u hu v hv => ?_⟩
  · exact le_trans (by nlinarith [norm_nonneg (p.2.1 u), pow_nonneg (norm_nonneg (p.2.1 u)) 3])
      (hp.curv_lb u)
  · have hcyc : 0 ≤ cyc u v := by
      rcases hu with ⟨hu0, hu1⟩
      rcases hv with ⟨hv0, hv1⟩
      have h : |u - v| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      exact le_min (abs_nonneg _) (by linarith)
    exact le_trans (mul_le_mul_of_nonneg_right hd hcyc) (hp.chord u hu v hv)

theorem circleData_rad_mem (n : ℕ) :
    IsTubeMember (2 * Real.pi) (1 / 2) 4 (circleData (rad n)) := by
  have hpi := Real.pi_pos
  have h := circleData_mem_tube (rad_pos n)
  refine tube_mono h ?_ ?_ ?_
  · nlinarith [rad_ge n]
  · rw [div_le_div_iff₀ (by norm_num) (rad_pos n)]
    nlinarith [rad_le n]
  · nlinarith [rad_ge n]

/-! ### The limit -/

/-- **The completeness lemma applied to the circles of radii `1 + 2^{-n}`.**
The sequence converges in the space of marked curves. -/
theorem circle_sequence_limit :
    ∃ plim : Data, IsTubeMember (2 * Real.pi) (1 / 2) 4 plim ∧
      Tendsto (fun n => circleData (rad n)) atTop (𝓝 plim) :=
  SummableNormalPathLimit.exists_limit_of_summable_costs circlePath circleData_rad_mem
    isConstantSpeedNormalPath_circlePath summable_cost_circlePath

/-- The marked distance of two circles is controlled by the difference of their
radii. -/
theorem dist_circleData_le (a b : ℝ) :
    dist (circleData a) (circleData b) ≤ 4 * Real.pi ^ 2 * |a - b| := by
  have hpi := Real.pi_pos
  have hb : (0:ℝ) ≤ 4 * Real.pi ^ 2 * |a - b| := by positivity
  have hpi1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpisq : (1:ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have h1 : dist (circleData a).1 (circleData b).1 ≤ 4 * Real.pi ^ 2 * |a - b| := by
    refine (BoundedContinuousFunction.dist_le hb).2 fun u => ?_
    rw [dist_eq_norm, circleData_fst, circleData_fst,
      show (a : ℂ) * normExp u - (b : ℂ) * normExp u = ((a - b : ℝ) : ℂ) * normExp u by
        push_cast; ring,
      norm_mul, norm_normExp, mul_one, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg (a - b), hpisq]
  have h2 : dist (circleData a).2.1 (circleData b).2.1 ≤ 4 * Real.pi ^ 2 * |a - b| := by
    refine (BoundedContinuousFunction.dist_le hb).2 fun u => ?_
    rw [dist_eq_norm, circleData_vel, circleData_vel,
      show ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I * normExp u
          - ((2 * Real.pi * b : ℝ) : ℂ) * Complex.I * normExp u
        = ((2 * Real.pi * (a - b) : ℝ) : ℂ) * (Complex.I * normExp u) by push_cast; ring,
      norm_mul, norm_mul, Complex.norm_I, one_mul, norm_normExp, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    nlinarith [abs_nonneg (a - b), hpisq, hpi1]
  have h3 : dist (circleData a).2.2 (circleData b).2.2 ≤ 4 * Real.pi ^ 2 * |a - b| := by
    refine (BoundedContinuousFunction.dist_le hb).2 fun u => ?_
    rw [dist_eq_norm, circleData_acc, circleData_acc,
      show -((4 * Real.pi ^ 2 * a : ℝ) : ℂ) * normExp u
          - -((4 * Real.pi ^ 2 * b : ℝ) : ℂ) * normExp u
        = -(((4 * Real.pi ^ 2 * (a - b) : ℝ) : ℂ) * normExp u) by push_cast; ring,
      norm_neg, norm_mul, norm_normExp, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2)]
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le h1 (max_le h2 h3)

/-- The circles of radii `1 + 2^{-n}` converge to the circle of radius one. -/
theorem tendsto_circleData_rad :
    Tendsto (fun n => circleData (rad n)) atTop (𝓝 (circleData 1)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => dist_circleData_le (rad n) 1) ?_
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heq : (fun n : ℕ => 4 * Real.pi ^ 2 * |rad n - 1|)
      = fun n : ℕ => 4 * Real.pi ^ 2 * (1 / 2 : ℝ) ^ n := by
    funext n
    rw [show rad n - 1 = (1 / 2 : ℝ) ^ n by rw [rad]; ring,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 / 2 : ℝ) ^ n)]
  rw [heq]
  simpa using hlim.const_mul (4 * Real.pi ^ 2)

/-- **The limit is the circle of radius one.** -/
theorem circle_sequence_limit_eq {plim : Data}
    (h : Tendsto (fun n => circleData (rad n)) atTop (𝓝 plim)) : plim = circleData 1 :=
  tendsto_nhds_unique h tendsto_circleData_rad

end SummableNormalPathLimitCircle
