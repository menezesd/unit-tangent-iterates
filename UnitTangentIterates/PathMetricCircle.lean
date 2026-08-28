import Mathlib
import UnitTangentIterates.PathMetric
import UnitTangentIterates.PathMetricJacobi
import UnitTangentIterates.MarkedSpaceCircle

/-!
# The path pseudodistance of two concentric circles

This file exhibits a nontrivial normal path — so that the pseudodistance
`PathMetric.pathDist` of the file `PathMetric.lean` is not the trivial
pseudodistance — and computes it in the model case of the paper *A Noncircular
Oval with Convex Unit-Tangent Iterates*: the radial dilation joining two
concentric circles.

The dilation is run with the time profile `B` whose derivative
`w t = max 0 (6t(1-t))` vanishes at both ends of the time interval, as required
of a normal path, and satisfies `∫₀¹ w = 1`.  Its cost density is
`|R - r| · w`, so its cost is exactly `|R - r|`, and since the path
pseudodistance dominates the pointwise distance of the curves this is exactly
the pseudodistance:

* `PathMetricCircle.pathDist_circleData` :
  `pathDist (circleData r) (circleData R) = |R - r|`.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric

namespace PathMetricCircle

/-! ### The time profile -/

/-- The speed profile of the dilation: a nonnegative continuous bump vanishing
outside the time interval `(0,1)` and of total mass one. -/
def w (t : ℝ) : ℝ := max 0 (6 * t * (1 - t))

theorem w_nonneg (t : ℝ) : 0 ≤ w t := le_max_left _ _

theorem continuous_w : Continuous w := by unfold w; fun_prop

private def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

private theorem clamp01_mem (t : ℝ) : clamp01 t ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

private theorem w_eq_clamp01 (t : ℝ) :
    w t = 6 * clamp01 t * (1 - clamp01 t) := by
  rcases le_total t 0 with ht | ht
  · unfold w clamp01
    rw [max_eq_left (by nlinarith), min_eq_left (by linarith : t ≤ 1), max_eq_left ht]
    ring
  · rcases le_total t 1 with ht1 | ht1
    · unfold w clamp01
      rw [max_eq_right (by nlinarith), min_eq_left ht1, max_eq_right ht]
    · unfold w clamp01
      rw [max_eq_left (by nlinarith), min_eq_right ht1,
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      ring

/-- The stopped polynomial speed is globally Lipschitz. -/
theorem lipschitzWith_w : LipschitzWith 6 w := by
  have hc : LipschitzWith 1 clamp01 := by
    have hmin : LipschitzWith 1 (fun x : ℝ => min x 1) := LipschitzWith.id.min_const _
    simpa [clamp01] using hmin.const_max 0
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hx := clamp01_mem x
  have hy := clamp01_mem y
  have hfac : |1 - clamp01 x - clamp01 y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hcxy : |clamp01 x - clamp01 y| ≤ |x - y| := by
    simpa [Real.dist_eq] using hc.dist_le_mul x y
  rw [Real.dist_eq, w_eq_clamp01, w_eq_clamp01]
  norm_num
  have heq :
      6 * clamp01 x * (1 - clamp01 x) - 6 * clamp01 y * (1 - clamp01 y) =
        6 * (clamp01 x - clamp01 y) * (1 - clamp01 x - clamp01 y) := by ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  calc
    6 * |clamp01 x - clamp01 y| * |1 - clamp01 x - clamp01 y|
        ≤ 6 * |clamp01 x - clamp01 y| * 1 :=
      mul_le_mul_of_nonneg_left hfac (mul_nonneg (by norm_num) (abs_nonneg _))
    _ ≤ 6 * |x - y| := by nlinarith

/-- The stopped polynomial speed has its sharp global maximum at `1 / 2`. -/
theorem w_le_three_halves (t : ℝ) : w t ≤ 3 / 2 := by
  rw [w_eq_clamp01]
  nlinarith [sq_nonneg (clamp01 t - 1 / 2)]

theorem w_eq_zero {t : ℝ} (ht : t ∉ Ioo (0:ℝ) 1) : w t = 0 := by
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
  refine max_eq_left ?_
  rcases ht with ht | ht
  · nlinarith
  · nlinarith

theorem w_eq_of_mem {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : w t = 6 * t * (1 - t) := by
  refine max_eq_right ?_
  nlinarith [ht.1, ht.2]

theorem integral_w : (∫ t in (0:ℝ)..1, w t) = 1 := by
  have hcongr : (∫ t in (0:ℝ)..1, w t) = ∫ t in (0:ℝ)..1, (6 * t - 6 * t ^ 2) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    rw [w_eq_of_mem ht]; ring
  rw [hcongr]
  have h : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3)
      (6 * t - 6 * t ^ 2) t := by
    intro t _
    have h2 : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3) (3 * (2 * t ^ 1) - 2 * (3 * t ^ 2)) t :=
      ((hasDerivAt_pow 2 t).const_mul 3).sub ((hasDerivAt_pow 3 t).const_mul 2)
    convert h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (((continuous_const.mul continuous_id).sub
      (continuous_const.mul (continuous_pow 2))).intervalIntegrable _ _)]
  norm_num

/-- The time profile of the dilation: the primitive of `w`, running from `0` to
`1` over the time interval. -/
def B (t : ℝ) : ℝ := ∫ x in (0:ℝ)..t, w x

theorem hasDerivAt_B (t : ℝ) : HasDerivAt B (w t) t :=
  intervalIntegral.integral_hasDerivAt_right (continuous_w.intervalIntegrable 0 t)
    (continuous_w.stronglyMeasurableAtFilter _ _) continuous_w.continuousAt

@[simp] theorem B_zero : B 0 = 0 := by simp [B]

@[simp] theorem B_one : B 1 = 1 := integral_w

/-! ### Bounds on the primitive of the bump -/

theorem B_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : B t = 0 := by
  have hz : (∫ x in (0 : ℝ)..t, w x) = ∫ _x in (0 : ℝ)..t, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 : x ≤ 0 := by
      rcases le_total (0 : ℝ) t with h | h
      · have : t = 0 := le_antisymm ht h
        rw [this] at hx
        simpa using hx.2
      · rw [Set.uIcc_of_ge ht] at hx
        exact hx.2
    exact w_eq_zero (by
      intro hmem
      exact absurd hmem.1 (not_lt.2 hx0))
  simpa [B] using hz

theorem continuous_B : Continuous B :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_B t).continuousAt

theorem B_nonneg (t : ℝ) : 0 ≤ B t := by
  rcases le_total t 0 with ht | ht
  · rw [B_eq_zero_of_nonpos ht]
  · exact intervalIntegral.integral_nonneg ht fun x _ => w_nonneg x

theorem B_le_one (t : ℝ) : B t ≤ 1 := by
  rcases le_total t 1 with ht | ht
  · have h : (∫ x in (0 : ℝ)..t, w x) ≤ ∫ x in (0 : ℝ)..1, w x := by
      rcases le_total (0 : ℝ) t with ht0 | ht0
      · exact intervalIntegral.integral_mono_interval le_rfl ht0 ht
          (Filter.Eventually.of_forall fun x => w_nonneg x)
          (continuous_w.intervalIntegrable 0 1)
      · rw [show (∫ x in (0 : ℝ)..t, w x) = B t from rfl, B_eq_zero_of_nonpos ht0]
        rw [show (∫ x in (0 : ℝ)..1, w x) = B 1 from rfl, B_one]
        exact zero_le_one
    exact le_trans h (le_of_eq B_one)
  · have hsplit : B t = B 1 + ∫ x in (1 : ℝ)..t, w x := by
      rw [B, B]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (continuous_w.intervalIntegrable 0 1) (continuous_w.intervalIntegrable 1 t)).symm
    have hz : (∫ x in (1 : ℝ)..t, w x) = 0 := by
      have : (∫ x in (1 : ℝ)..t, w x) = ∫ _x in (1 : ℝ)..t, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        have hx1 : 1 ≤ x := by
          rw [Set.uIcc_of_le ht] at hx
          exact hx.1
        exact w_eq_zero (by
          intro hmem
          exact absurd hmem.2 (not_lt.2 hx1))
      simpa using this
    rw [hsplit, hz, B_one, add_zero]

/-! ### Iterated derivatives of a constant -/

theorem iteratedDeriv_succ_const (c : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (fun _ : ℝ => c) = fun _ => 0 := by
  rw [iteratedDeriv_succ']
  simpa using PathMetric.iteratedDeriv_zero_fun n

theorem supNorm_const (c : ℝ) : MarkedTopology.supNorm (fun _ : ℝ => c) = |c| := by
  simp [MarkedTopology.supNorm]

/-! ### The dilation as a normal path -/

/-- **The radial dilation** from the circle of radius `r` to the circle of
radius `R`, as a normal path: the circles move with purely radial — hence
normal — velocity `(R - r) w(t)`. -/
def dilation (r R : ℝ) : NormalPath (circleData r)
    (circleData R) where
  T := 1
  T_pos := one_pos
  X := fun t u => ((r + (R - r) * B t : ℝ) : ℂ) * normExp u
  eta := fun t _ => (R - r) * w t
  nu := fun _ u => normExp u
  m := fun t => |R - r| * w t
  start := fun u => by simp
  finish := fun u => by simp
  hasDerivAt_time := by
    intro t u
    have hB : HasDerivAt (fun s => r + (R - r) * B s) ((R - r) * w t) t :=
      (((hasDerivAt_B t).const_mul (R - r)).const_add r)
    simpa using (hB.ofReal_comp.mul_const (normExp u))
  cont_vel := fun u => by
    have h : Continuous fun t : ℝ => ((R - r) * w t : ℝ) := continuous_const.mul continuous_w
    exact (Complex.continuous_ofReal.comp h).mul continuous_const
  norm_nu := fun _ u => norm_normExp u
  cont_m := continuous_const.mul continuous_w
  m_nonneg := fun t => mul_nonneg (abs_nonneg _) (w_nonneg t)
  m_stop := fun t ht => by rw [w_eq_zero ht, mul_zero]
  abs_eta_le := fun t _ => by
    rw [abs_mul, abs_of_nonneg (w_nonneg t)]
  le_m_L1 := fun t => by
    have : (∫ _u in (0:ℝ)..1, |(R - r) * w t|) = |(R - r) * w t| := by simp
    rw [this, abs_mul, abs_of_nonneg (w_nonneg t)]
  le_m_sup := fun t j _ => by
    match j with
    | 0 =>
      rw [iteratedDeriv_zero, supNorm_const, abs_mul, abs_of_nonneg (w_nonneg t)]
    | (n + 1) =>
      rw [iteratedDeriv_succ_const, supNorm_const]
      simpa using mul_nonneg (abs_nonneg (R - r)) (w_nonneg t)

theorem cost_dilation (r R : ℝ) : NormalPath.cost (dilation r R) = |R - r| := by
  have : NormalPath.cost (dilation r R) = ∫ t in (0:ℝ)..1, |R - r| * w t := rfl
  rw [this, intervalIntegral.integral_const_mul, integral_w, mul_one]

/-- **The path pseudodistance of two concentric circles is the difference of
their radii.**  In particular the pseudodistance is not identically zero. -/
theorem pathDist_circleData (r R : ℝ) :
    pathDist (circleData r) (circleData R) = |R - r| := by
  refine le_antisymm ?_ ?_
  · simpa [cost_dilation r R] using pathDist_le_cost (dilation r R)
  · have h := norm_sub_le_pathDist (p := circleData r)
      (q := circleData R) ⟨dilation r R⟩ 0
    have hval : ‖(circleData R).1 0 - (circleData r).1 0‖
        = |R - r| := by
      rw [circleData_fst, circleData_fst,
        ← sub_mul, norm_mul, norm_normExp, mul_one]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rwa [hval] at h

/-! ### The hypotheses of the Jacobi bridge are satisfiable -/

/-- **Non-vacuity of `PathMetricJacobi.exists_normalPath_of_jacobi`.**  The
dilation of the previous section satisfies the four estimates against itself,
with constants `C_W = C₀ = 1`, `C₁ = C₂ = 0` (its normal velocity is constant along
the curve), so the bridge from the inverse Jacobi estimates to the path metric
applies to it and returns a normal path of the predicted cost. -/
theorem exists_normalPath_of_jacobi_dilation (r R : ℝ) :
    ∃ Δ : NormalPath (circleData r) (circleData R),
      Δ.T = (dilation r R).T ∧
        NormalPath.cost Δ
          = PathMetricJacobi.jacobiConst 1 1 0 0 * NormalPath.cost (dilation r R) := by
  have habs : ∀ t : ℝ, |(R - r) * w t| = |R - r| * w t := fun t => by
    rw [abs_mul, abs_of_nonneg (w_nonneg t)]
  have hint : ∀ t : ℝ, (∫ _u in (0:ℝ)..1, |(R - r) * w t|) = |R - r| * w t := by
    intro t; rw [← habs t]; simp
  refine PathMetricJacobi.exists_normalPath_of_jacobi (dilation r R) zero_le_one zero_le_one
    le_rfl le_rfl
    (XR := (dilation r R).X) (nuR := (dilation r R).nu) (etaR := (dilation r R).eta)
    (dilation r R).start (dilation r R).finish (dilation r R).hasDerivAt_time
    (dilation r R).cont_vel (dilation r R).norm_nu (fun t u => ?_) (fun t => by rw [one_mul])
    (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · rw [show (dilation r R).eta t = fun _ : ℝ => (R - r) * w t from rfl, supNorm_const]
  · rw [show (dilation r R).eta t = fun _ : ℝ => (R - r) * w t from rfl, supNorm_const,
      one_mul, hint t, habs t]
  · rw [show (dilation r R).eta t = fun _ : ℝ => (R - r) * w t from rfl,
      show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ_const, supNorm_const]
    simp
  · rw [show (dilation r R).eta t = fun _ : ℝ => (R - r) * w t from rfl,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ_const, supNorm_const]
    simp

end PathMetricCircle
