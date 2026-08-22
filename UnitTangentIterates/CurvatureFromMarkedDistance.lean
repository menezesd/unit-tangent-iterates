import Mathlib
import UnitTangentIterates.MarkedSpace
import UnitTangentIterates.MarkedSpaceCircle

/-!
# The marked metric controls the curvature

`MarkedDistanceCurvature.dist_le_of_curvature_close` converts a uniform bound
on the difference of the curvatures of two members of the tube into a bound for
their distance in the space of marked curves.  This file proves the **converse**
comparison, which the estimates of the shadowing scheme need in order to feed a
`C²` bound back into a curvature-based comparison: the curvature of a marked
curve is a Lipschitz function of the marked datum.

For a marked curve the curvature in the normalized parameter is

`dataCurv p u = Im(conj V(u) · A(u)) / ‖V(u)‖³` ,

the parametrization-invariant expression of the curvature of a regular plane
curve.  If two marked curves have speed at least `c > 0`, speed at most `Vb`
and acceleration at most `Ab`, then

`|dataCurv p u − dataCurv q u| ≤ ((Vb + Ab)/c³ + 3 Vb³ Ab / c⁶) · dist p q` ,

since the numerator is bilinear in the velocity and the acceleration, both of
which are `1`-Lipschitz in the marked datum, and the denominator is bounded
below.

For members of the tube the three bounds are read off the tube data — the speed
is the perimeter `L` and the acceleration is `L²` times the curvature — so the
comparison takes the form `|k_p − k_q| ≤ curvLipTube L kb · dist p q`.

Main results: `abs_dataCurv_sub_le`, `abs_dataCurv_sub_le_of_tube`.
-/

noncomputable section

open Set Function Complex

namespace CurvatureFromMarkedDistance

open MarkedSpace

/-- **The curvature of a marked curve in the normalized parameter.** -/
def dataCurv (p : Data) (u : ℝ) : ℝ :=
  ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im / ‖p.2.1 u‖ ^ 3

/-- The numerator of the curvature is bilinear in the velocity and the
acceleration, so it is Lipschitz in the marked datum. -/
theorem abs_num_sub_le {p q : Data} {u Vb Ab : ℝ}
    (hVp : ‖p.2.1 u‖ ≤ Vb) (hAq : ‖q.2.2 u‖ ≤ Ab) :
    |((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im
        - ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im|
      ≤ (Vb + Ab) * dist p q := by
  set vp := p.2.1 u
  set ap := p.2.2 u
  set vq := q.2.1 u
  set aq := q.2.2 u
  have hsplit : (starRingEnd ℂ) vp * ap - (starRingEnd ℂ) vq * aq
      = (starRingEnd ℂ) vp * (ap - aq) + (starRingEnd ℂ) (vp - vq) * aq := by
    simp [map_sub]; ring
  have him : |(((starRingEnd ℂ) vp * ap).im - ((starRingEnd ℂ) vq * aq).im)|
      ≤ ‖(starRingEnd ℂ) vp * ap - (starRingEnd ℂ) vq * aq‖ := by
    have := Complex.abs_im_le_norm ((starRingEnd ℂ) vp * ap - (starRingEnd ℂ) vq * aq)
    simpa [Complex.sub_im] using this
  have hnorm : ‖(starRingEnd ℂ) vp * ap - (starRingEnd ℂ) vq * aq‖
      ≤ ‖vp‖ * ‖ap - aq‖ + ‖vp - vq‖ * ‖aq‖ := by
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
  have hda : ‖ap - aq‖ ≤ dist p q := by
    have h1 : dist (p.2.2 u) (q.2.2 u) ≤ dist p.2.2 q.2.2 :=
      BoundedContinuousFunction.dist_coe_le_dist u
    have h2 : dist p.2.2 q.2.2 ≤ dist p.2 q.2 := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    have h3 : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
    rw [show ‖ap - aq‖ = dist (p.2.2 u) (q.2.2 u) from (dist_eq_norm _ _).symm]
    linarith
  have hdv : ‖vp - vq‖ ≤ dist p q := dist_vel_apply_le p q u
  have hd0 : 0 ≤ dist p q := dist_nonneg
  have hVp0 : 0 ≤ ‖vp‖ := norm_nonneg _
  have hAq0 : 0 ≤ ‖aq‖ := norm_nonneg _
  have hb1 : ‖vp‖ * ‖ap - aq‖ ≤ Vb * dist p q :=
    mul_le_mul hVp hda (norm_nonneg _) (le_trans hVp0 hVp)
  have hb2 : ‖vp - vq‖ * ‖aq‖ ≤ dist p q * Ab :=
    mul_le_mul hdv hAq (norm_nonneg _) hd0
  calc |(((starRingEnd ℂ) vp * ap).im - ((starRingEnd ℂ) vq * aq).im)|
      ≤ ‖vp‖ * ‖ap - aq‖ + ‖vp - vq‖ * ‖aq‖ := le_trans him hnorm
    _ ≤ Vb * dist p q + dist p q * Ab := add_le_add hb1 hb2
    _ = (Vb + Ab) * dist p q := by ring

/-- The cube of the speed is Lipschitz in the marked datum, with constant
`3 Vb²`. -/
theorem abs_den_sub_le {p q : Data} {u Vb : ℝ}
    (hVp : ‖p.2.1 u‖ ≤ Vb) (hVq : ‖q.2.1 u‖ ≤ Vb) :
    |‖p.2.1 u‖ ^ 3 - ‖q.2.1 u‖ ^ 3| ≤ 3 * Vb ^ 2 * dist p q := by
  set a := ‖p.2.1 u‖
  set b := ‖q.2.1 u‖
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hab : |a - b| ≤ dist p q := by
    have := abs_norm_sub_norm_le (p.2.1 u) (q.2.1 u)
    exact le_trans this (dist_vel_apply_le p q u)
  have hfac : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
  have hsum : a ^ 2 + a * b + b ^ 2 ≤ 3 * Vb ^ 2 := by nlinarith
  have hsum0 : 0 ≤ a ^ 2 + a * b + b ^ 2 := by positivity
  rw [hfac, abs_mul, abs_of_nonneg hsum0]
  calc |a - b| * (a ^ 2 + a * b + b ^ 2) ≤ dist p q * (3 * Vb ^ 2) :=
        mul_le_mul hab hsum hsum0 dist_nonneg
    _ = 3 * Vb ^ 2 * dist p q := by ring

/-- The Lipschitz constant of the curvature for the marked metric. -/
def curvLip (c Vb Ab : ℝ) : ℝ := (Vb + Ab) / c ^ 3 + 3 * Vb ^ 3 * Ab / c ^ 6

/-- **The curvature is Lipschitz for the marked metric.**  For two marked curves
of speed between `c > 0` and `Vb` and acceleration at most `Ab`, the curvatures
in the normalized parameter differ by at most `curvLip c Vb Ab` times the marked
distance. -/
theorem abs_dataCurv_sub_le {p q : Data} {u c Vb Ab : ℝ} (hc : 0 < c)
    (hcp : c ≤ ‖p.2.1 u‖) (hcq : c ≤ ‖q.2.1 u‖)
    (hVp : ‖p.2.1 u‖ ≤ Vb) (hVq : ‖q.2.1 u‖ ≤ Vb)
    (hAp : ‖p.2.2 u‖ ≤ Ab) (hAq : ‖q.2.2 u‖ ≤ Ab) :
    |dataCurv p u - dataCurv q u| ≤ curvLip c Vb Ab * dist p q := by
  set Np := ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im with hNp
  set Nq := ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im with hNq
  set Dp := ‖p.2.1 u‖ ^ 3 with hDp
  set Dq := ‖q.2.1 u‖ ^ 3 with hDq
  have hd0 : 0 ≤ dist p q := dist_nonneg
  have hVb0 : 0 ≤ Vb := le_trans (norm_nonneg _) hVp
  have hAb0 : 0 ≤ Ab := le_trans (norm_nonneg _) hAp
  have hDp0 : c ^ 3 ≤ Dp := by
    rw [hDp]; exact pow_le_pow_left₀ hc.le hcp 3
  have hDq0 : c ^ 3 ≤ Dq := by
    rw [hDq]; exact pow_le_pow_left₀ hc.le hcq 3
  have hc3 : (0 : ℝ) < c ^ 3 := by positivity
  have hDppos : 0 < Dp := lt_of_lt_of_le hc3 hDp0
  have hDqpos : 0 < Dq := lt_of_lt_of_le hc3 hDq0
  -- the numerator and the denominator
  have hnum : |Np - Nq| ≤ (Vb + Ab) * dist p q := abs_num_sub_le hVp hAq
  have hden : |Dp - Dq| ≤ 3 * Vb ^ 2 * dist p q := abs_den_sub_le hVp hVq
  have hNq_le : |Nq| ≤ Vb * Ab := by
    have h1 : |Nq| ≤ ‖(starRingEnd ℂ) (q.2.1 u) * q.2.2 u‖ := Complex.abs_im_le_norm _
    have h2 : ‖(starRingEnd ℂ) (q.2.1 u) * q.2.2 u‖ = ‖q.2.1 u‖ * ‖q.2.2 u‖ := by
      rw [norm_mul, RCLike.norm_conj]
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul hVq hAq (norm_nonneg _) hVb0)
  -- the algebraic splitting
  have hsplit : Np / Dp - Nq / Dq = (Np - Nq) / Dp + Nq * (Dq - Dp) / (Dp * Dq) := by
    field_simp
    ring
  have hterm1 : |(Np - Nq) / Dp| ≤ (Vb + Ab) * dist p q / c ^ 3 := by
    rw [abs_div, abs_of_pos hDppos]
    have hnn : (0 : ℝ) ≤ (Vb + Ab) * dist p q := by positivity
    calc |Np - Nq| / Dp ≤ ((Vb + Ab) * dist p q) / Dp := by gcongr
      _ ≤ ((Vb + Ab) * dist p q) / c ^ 3 := by gcongr
  have hterm2 : |Nq * (Dq - Dp) / (Dp * Dq)| ≤ Vb * Ab * (3 * Vb ^ 2 * dist p q) / (c ^ 3 * c ^ 3) := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hDppos hDqpos)]
    have hnum2 : |Nq| * |Dq - Dp| ≤ Vb * Ab * (3 * Vb ^ 2 * dist p q) := by
      have h : |Dq - Dp| ≤ 3 * Vb ^ 2 * dist p q := by rw [abs_sub_comm]; exact hden
      exact mul_le_mul hNq_le h (abs_nonneg _) (by positivity)
    have hden2 : c ^ 3 * c ^ 3 ≤ Dp * Dq :=
      mul_le_mul hDp0 hDq0 hc3.le (le_trans hc3.le hDp0)
    have hnn : (0 : ℝ) ≤ Vb * Ab * (3 * Vb ^ 2 * dist p q) := by positivity
    have hcc : (0 : ℝ) < c ^ 3 * c ^ 3 := by positivity
    calc |Nq| * |Dq - Dp| / (Dp * Dq)
        ≤ (Vb * Ab * (3 * Vb ^ 2 * dist p q)) / (Dp * Dq) := by gcongr
      _ ≤ (Vb * Ab * (3 * Vb ^ 2 * dist p q)) / (c ^ 3 * c ^ 3) := by gcongr
  have hfinal : |Np / Dp - Nq / Dq|
      ≤ (Vb + Ab) * dist p q / c ^ 3
        + Vb * Ab * (3 * Vb ^ 2 * dist p q) / (c ^ 3 * c ^ 3) := by
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (add_le_add hterm1 hterm2)
  have hrw : (Vb + Ab) * dist p q / c ^ 3
      + Vb * Ab * (3 * Vb ^ 2 * dist p q) / (c ^ 3 * c ^ 3)
      = curvLip c Vb Ab * dist p q := by
    unfold curvLip
    field_simp
  rw [hrw] at hfinal
  simpa [dataCurv, hNp, hNq, hDp, hDq] using hfinal

/-! ### The acceleration of a member of the tube -/

/-- The derivative of the squared speed is twice the real part of
`conj V · A`. -/
theorem hasDerivAt_normSq_vel {p : Data} {c kmin dlt : ℝ} (hp : IsTubeMember c kmin dlt p)
    (u : ℝ) :
    HasDerivAt (fun t => Complex.normSq (p.2.1 t))
      (2 * ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).re) u := by
  have h := hp.hasDerivAt_vel u
  have hre : HasDerivAt (fun t => (p.2.1 t).re) (p.2.2 u).re u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h
  have him : HasDerivAt (fun t => (p.2.1 t).im) (p.2.2 u).im u :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt u h
  have hsum := (hre.mul hre).add (him.mul him)
  have heq : (fun t => Complex.normSq (p.2.1 t))
      = fun t => (p.2.1 t).re * (p.2.1 t).re + (p.2.1 t).im * (p.2.1 t).im := by
    funext t; simp [Complex.normSq_apply]
  rw [heq]
  convert hsum using 1
  simp [Complex.mul_re]
  ring

/-- **The acceleration of a member of the tube is orthogonal to its velocity**:
the speed is constant. -/
theorem re_conj_vel_acc_eq_zero {p : Data} {c kmin dlt : ℝ} (hp : IsTubeMember c kmin dlt p)
    (u : ℝ) : ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).re = 0 := by
  have hconst : (fun t => Complex.normSq (p.2.1 t)) = fun _ : ℝ => perim p ^ 2 := by
    funext t
    rw [Complex.normSq_eq_norm_sq, norm_vel_eq_perim hp t]
  have h1 := hasDerivAt_normSq_vel hp u
  rw [hconst] at h1
  have h2 : HasDerivAt (fun _ : ℝ => perim p ^ 2) 0 u := hasDerivAt_const u _
  have := h1.unique h2
  linarith

/-- **The acceleration of a member of the tube is the curvature times the square
of the speed.** -/
theorem norm_acc_eq {p : Data} {c kmin dlt : ℝ} (hp : IsTubeMember c kmin dlt p) {u : ℝ}
    (hu : 0 < ‖p.2.1 u‖) : ‖p.2.2 u‖ = |dataCurv p u| * ‖p.2.1 u‖ ^ 2 := by
  have hre := re_conj_vel_acc_eq_zero hp u
  have hnorm : ‖(starRingEnd ℂ) (p.2.1 u) * p.2.2 u‖ = ‖p.2.1 u‖ * ‖p.2.2 u‖ := by
    rw [norm_mul, RCLike.norm_conj]
  have him : ‖(starRingEnd ℂ) (p.2.1 u) * p.2.2 u‖
      = |((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im| := by
    set z := (starRingEnd ℂ) (p.2.1 u) * p.2.2 u
    rw [Complex.norm_def, Complex.normSq_apply, hre,
      show (0:ℝ) * 0 + z.im * z.im = z.im ^ 2 by ring, Real.sqrt_sq_eq_abs]
  have hcurv : ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im = dataCurv p u * ‖p.2.1 u‖ ^ 3 := by
    unfold dataCurv
    field_simp
  rw [hnorm] at him
  rw [hcurv, abs_mul, abs_of_pos (by positivity : (0:ℝ) < ‖p.2.1 u‖ ^ 3)] at him
  have hne : ‖p.2.1 u‖ ≠ 0 := ne_of_gt hu
  field_simp at him ⊢
  nlinarith [him, hu]

/-! ### The comparison for two members of the tube -/

/-- The Lipschitz constant of the curvature on the tube of perimeter `L` and
curvature at most `kb`: the speed is `L` and the acceleration is at most
`L² k_b`. -/
def curvLipTube (L kb : ℝ) : ℝ := curvLip L L (L ^ 2 * kb)

/-- **The curvature is Lipschitz for the marked metric, on the tube.**  Two
members of the tube of the same perimeter `L > 0` whose accelerations are
bounded by `L² k_b` — that is, whose curvatures are bounded by `k_b` — have
curvatures differing by at most `curvLipTube L kb` times their marked
distance. -/
theorem abs_dataCurv_sub_le_of_tube {p q : Data} {u L kb : ℝ} (hL : 0 < L)
    (hperp : ∀ v, ‖p.2.1 v‖ = L) (hperq : ∀ v, ‖q.2.1 v‖ = L)
    (hAp : ‖p.2.2 u‖ ≤ L ^ 2 * kb) (hAq : ‖q.2.2 u‖ ≤ L ^ 2 * kb) :
    |dataCurv p u - dataCurv q u| ≤ curvLipTube L kb * dist p q :=
  abs_dataCurv_sub_le hL (le_of_eq (hperp u).symm) (le_of_eq (hperq u).symm)
    (le_of_eq (hperp u)) (le_of_eq (hperq u)) hAp hAq

/-- **The curvature comparison for two members of the tube.**  Two members of
the tube of the same perimeter `L > 0` whose curvatures at the parameter `u` are
bounded by `k_b` have curvatures differing there by at most `curvLipTube L kb`
times their marked distance. -/
theorem abs_dataCurv_sub_le_of_tube_curv {p q : Data} {cp kminp dltp cq kminq dltq L kb u : ℝ}
    (hL : 0 < L) (hp : IsTubeMember cp kminp dltp p) (hq : IsTubeMember cq kminq dltq q)
    (hLp : perim p = L) (hLq : perim q = L)
    (hkp : |dataCurv p u| ≤ kb) (hkq : |dataCurv q u| ≤ kb) :
    |dataCurv p u - dataCurv q u| ≤ curvLipTube L kb * dist p q := by
  have hvp : ∀ v, ‖p.2.1 v‖ = L := fun v => by rw [norm_vel_eq_perim hp v, hLp]
  have hvq : ∀ v, ‖q.2.1 v‖ = L := fun v => by rw [norm_vel_eq_perim hq v, hLq]
  have hap : ‖p.2.2 u‖ ≤ L ^ 2 * kb := by
    rw [norm_acc_eq hp (by rw [hvp u]; exact hL), hvp u]
    nlinarith [abs_nonneg (dataCurv p u)]
  have haq : ‖q.2.2 u‖ ≤ L ^ 2 * kb := by
    rw [norm_acc_eq hq (by rw [hvq u]; exact hL), hvq u]
    nlinarith [abs_nonneg (dataCurv q u)]
  exact abs_dataCurv_sub_le_of_tube hL hvp hvq hap haq

/-! ### Non-vacuity: the circle -/

/-- The curvature of the circle of radius `r` is `1/r`, as computed from its
marked datum. -/
theorem dataCurv_circleData {r : ℝ} (hr : 0 < r) (u : ℝ) :
    dataCurv (circleData r) u = 1 / r := by
  have hpi := Real.pi_pos
  have hspeed : ‖(circleData r).2.1 u‖ = 2 * Real.pi * r := by
    rw [circleData_vel]
    simp [abs_of_pos hpi, abs_of_pos hr]
  have hconj : (starRingEnd ℂ) ((circleData r).2.1 u) * (circleData r).2.2 u
      = ((8 * Real.pi ^ 3 * r ^ 2 : ℝ) : ℂ) * Complex.I := by
    rw [circleData_vel, circleData_acc]
    have hEE := conj_mul_normExp u
    have hstep : (starRingEnd ℂ) (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I * normExp u)
        * (-((4 * Real.pi ^ 2 * r : ℝ) : ℂ) * normExp u)
        = ((starRingEnd ℂ) (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I)
            * -((4 * Real.pi ^ 2 * r : ℝ) : ℂ)) * ((starRingEnd ℂ) (normExp u) * normExp u) := by
      rw [map_mul]
      ring
    rw [hstep, hEE, mul_one, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [dataCurv, hconj, hspeed]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  field_simp
  ring

/-- **The comparison is not vacuous.**  For two circles the bound reads
`|1/r₁ − 1/r₂| ≤ curvLip c Vb Ab · dist`, with the three constants of the two
circles. -/
theorem abs_dataCurv_sub_circleData {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (u : ℝ) :
    |1 / r₁ - 1 / r₂|
      ≤ curvLip (2 * Real.pi * min r₁ r₂) (2 * Real.pi * max r₁ r₂)
          (4 * Real.pi ^ 2 * max r₁ r₂) * dist (circleData r₁) (circleData r₂) := by
  have hpi := Real.pi_pos
  have hspeed : ∀ r : ℝ, 0 < r → ∀ v : ℝ, ‖(circleData r).2.1 v‖ = 2 * Real.pi * r := by
    intro r hr v
    rw [circleData_vel]
    simp [abs_of_pos hpi, abs_of_pos hr]
  have hacc : ∀ r : ℝ, 0 < r → ∀ v : ℝ, ‖(circleData r).2.2 v‖ = 4 * Real.pi ^ 2 * r := by
    intro r hr v
    rw [circleData_acc]
    simp [abs_of_pos hpi, abs_of_pos hr]
  have hmin : 0 < 2 * Real.pi * min r₁ r₂ := by
    have : 0 < min r₁ r₂ := lt_min hr₁ hr₂
    positivity
  have key := abs_dataCurv_sub_le (p := circleData r₁) (q := circleData r₂) (u := u)
    (c := 2 * Real.pi * min r₁ r₂) (Vb := 2 * Real.pi * max r₁ r₂)
    (Ab := 4 * Real.pi ^ 2 * max r₁ r₂) hmin
    (by rw [hspeed r₁ hr₁]; have := min_le_left r₁ r₂; nlinarith)
    (by rw [hspeed r₂ hr₂]; have := min_le_right r₁ r₂; nlinarith)
    (by rw [hspeed r₁ hr₁]; have := le_max_left r₁ r₂; nlinarith)
    (by rw [hspeed r₂ hr₂]; have := le_max_right r₁ r₂; nlinarith)
    (by rw [hacc r₁ hr₁]; have := le_max_left r₁ r₂; nlinarith)
    (by rw [hacc r₂ hr₂]; have := le_max_right r₁ r₂; nlinarith)
  rwa [dataCurv_circleData hr₁, dataCurv_circleData hr₂] at key

end CurvatureFromMarkedDistance
