import Mathlib
import UnitTangentIterates.MarkedDistanceCurvature

/-!
# The marked distance from a bound on the curvatures, with moving perimeter

`MarkedDistanceCurvature.dist_le_of_curvature_close` bounds the marked distance
of two members of the tube whose curvatures are uniformly `ε`-close, but only
when the two **perimeters agree**.  In the model pseudo-orbit of
*A Noncircular Oval with Convex Unit-Tangent Iterates* they agree only up to the
defect, so this file removes the restriction.

For two members of the tube of perimeters at most `Lm` differing by at most
`D`, whose arclength parametrizations are aligned at the marked point, whose
curvatures are bounded by `kb` and `ε`-close, the second curvature being
`kL`-Lipschitz,

```
  dist p q ≤ max (εLm² + D)
              (max (D + Lm(εLm + kbD))
                   (2DLmkb + Lm²(ε + kLD + kb(εLm + kbD)))).
```

The three entries are the position, the velocity and the acceleration bounds;
each is a triangle inequality between the curvature comparison of
`CurvatureStability.lean` at a common arclength and the motion of the second
curve over the arclength interval of length `D|u|` by which the two normalized
parameters differ.  With `D = 0` the bound is the previous one up to the shape
of the constant.
-/

noncomputable section

open Set Function

namespace MarkedSpace

/-- The bound of `dist_le_of_curvature_close_perim`: the largest of the
position, velocity and acceleration errors. -/
def defectBound (eps D Lm kb kL : ℝ) : ℝ :=
  max (eps * Lm ^ 2 + D)
    (max (D + Lm * (eps * Lm + kb * D))
      (2 * D * Lm * kb + Lm ^ 2 * (eps + kL * D + kb * (eps * Lm + kb * D))))

/-- **The marked distance from a uniform bound on the curvatures, the two
perimeters being allowed to differ.** -/
theorem dist_le_of_curvature_close_perim {c kmin delta : ℝ} (hc : 0 < c) {p q : Data}
    (hp : IsTubeMember c kmin delta p) (hq : IsTubeMember c kmin delta q)
    {Θ₁ Θ₂ k₁ k₂ : ℝ → ℝ} {eps kb kL Lm D : ℝ}
    (hLp : perim p ≤ Lm) (hLq : perim q ≤ Lm)
    (hD : |perim p - perim q| ≤ D)
    (hevp : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s)
    (hevq : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ₂ s : ℂ))) s)
    (hΘ1 : ∀ s, HasDerivAt Θ₁ (k₁ s) s) (hΘ2 : ∀ s, HasDerivAt Θ₂ (k₂ s) s)
    (hF0 : ev p 0 = ev q 0) (hΘ0 : Θ₁ 0 = Θ₂ 0)
    (heps : 0 ≤ eps) (hk : ∀ s, |k₁ s - k₂ s| ≤ eps)
    (hkb1 : ∀ s, |k₁ s| ≤ kb) (hkb2 : ∀ s, |k₂ s| ≤ kb)
    (hkL : ∀ a b, |k₂ a - k₂ b| ≤ kL * |a - b|) :
    dist p q ≤ defectBound eps D Lm kb kL := by
  rw [defectBound]
  set L₁ : ℝ := perim p with hL1def
  set L₂ : ℝ := perim q with hL2def
  have hL1pos : 0 < L₁ := perim_pos hc hp
  have hL2pos : 0 < L₂ := perim_pos hc hq
  have hLmpos : 0 < Lm := lt_of_lt_of_le hL1pos hLp
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hD
  have hkb0 : 0 ≤ kb := le_trans (abs_nonneg _) (hkb2 0)
  have hkL0 : 0 ≤ kL := by
    have h := hkL 1 0
    have h1 : |k₂ 1 - k₂ 0| ≤ kL * |(1 : ℝ) - 0| := h
    simp only [sub_zero, abs_one, mul_one] at h1
    exact le_trans (abs_nonneg _) h1
  -- the angle comparison
  have hang : ∀ s, |Θ₁ s - Θ₂ s| ≤ eps * |s| :=
    CurvatureStability.abs_angle_sub_le hΘ1 hΘ2 hΘ0 hk
  -- the three bounds on one period
  have hu1 : ∀ u ∈ Icc (0:ℝ) 1, |L₁ * u| ≤ Lm := by
    intro u hu
    rw [abs_of_nonneg (by nlinarith [hu.1] : (0:ℝ) ≤ L₁ * u)]
    nlinarith [hu.2, hu.1]
  have hshift : ∀ u ∈ Icc (0:ℝ) 1, |L₁ * u - L₂ * u| ≤ D := by
    intro u hu
    have hfac : L₁ * u - L₂ * u = (L₁ - L₂) * u := by ring
    rw [hfac, abs_mul, abs_of_nonneg hu.1]
    calc |L₁ - L₂| * u ≤ D * u := mul_le_mul_of_nonneg_right hD hu.1
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left hu.2 hD0
      _ = D := by ring
  have hmem : ∀ u ∈ Icc (0:ℝ) 1, L₁ * u ∈ Icc (-Lm) Lm := by
    intro u hu
    have h := hu1 u hu
    rw [abs_le] at h
    exact ⟨h.1, h.2⟩
  -- the position bound
  have hbound1 : ∀ u, ‖p.1 u - q.1 u‖ ≤ eps * Lm ^ 2 + D := by
    refine forall_of_forall_Icc (f := fun u => p.1 u - q.1 u)
      (fun u => by simp [hp.periodic u, hq.periodic u]) ?_
    intro u hu
    show ‖p.1 u - q.1 u‖ ≤ eps * Lm ^ 2 + D
    have hpe : p.1 u = ev p (L₁ * u) := curve_eq_ev p u (ne_of_gt hL1pos)
    have hqe : q.1 u = ev q (L₂ * u) := curve_eq_ev q u (ne_of_gt hL2pos)
    have h1 : ‖ev p (L₁ * u) - ev q (L₁ * u)‖ ≤ eps * Lm ^ 2 := by
      have h := CurvatureStability.norm_curve_sub_le hevp hevq hF0 heps hLmpos.le hang
        (hmem u hu)
      refine le_trans h ?_
      have : eps * Lm * |L₁ * u| ≤ eps * Lm * Lm :=
        mul_le_mul_of_nonneg_left (hu1 u hu) (by positivity)
      nlinarith [this]
    have h2 : ‖ev q (L₁ * u) - ev q (L₂ * u)‖ ≤ D :=
      le_trans (CurvatureStability.norm_curve_sub_le_dist hevq _ _) (hshift u hu)
    calc ‖p.1 u - q.1 u‖ = ‖(ev p (L₁ * u) - ev q (L₁ * u)) + (ev q (L₁ * u) - ev q (L₂ * u))‖ := by
          rw [hpe, hqe]; ring_nf
      _ ≤ ‖ev p (L₁ * u) - ev q (L₁ * u)‖ + ‖ev q (L₁ * u) - ev q (L₂ * u)‖ := norm_add_le _ _
      _ ≤ eps * Lm ^ 2 + D := add_le_add h1 h2
  -- the tangent comparison at a common arclength, and the shift of the second angle
  have htan : ∀ u ∈ Icc (0:ℝ) 1,
      ‖Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
        - Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))‖ ≤ eps * Lm + kb * D := by
    intro u hu
    have h1 : ‖Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
        - Complex.exp (Complex.I * (Θ₂ (L₁ * u) : ℂ))‖ ≤ eps * Lm := by
      refine le_trans (CurvatureStability.norm_tangent_sub_le _ _) ?_
      refine le_trans (hang (L₁ * u)) ?_
      exact mul_le_mul_of_nonneg_left (hu1 u hu) heps
    have h2 : ‖Complex.exp (Complex.I * (Θ₂ (L₁ * u) : ℂ))
        - Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))‖ ≤ kb * D := by
      refine le_trans (CurvatureStability.norm_tangent_sub_le _ _) ?_
      refine le_trans (CurvatureStability.abs_angle_sub_le_dist hΘ2 hkb2 _ _) ?_
      exact mul_le_mul_of_nonneg_left (hshift u hu) hkb0
    calc ‖Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
            - Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))‖
        ≤ ‖Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
            - Complex.exp (Complex.I * (Θ₂ (L₁ * u) : ℂ))‖
          + ‖Complex.exp (Complex.I * (Θ₂ (L₁ * u) : ℂ))
            - Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub
            (Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ)))
            (Complex.exp (Complex.I * (Θ₂ (L₁ * u) : ℂ)))
            (Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ)))
      _ ≤ eps * Lm + kb * D := add_le_add h1 h2
  -- the velocity bound
  have hbound2 : ∀ u, ‖p.2.1 u - q.2.1 u‖ ≤ D + Lm * (eps * Lm + kb * D) := by
    refine forall_of_forall_Icc (f := fun u => p.2.1 u - q.2.1 u)
      (fun u => by simp [periodic_vel hp u, periodic_vel hq u]) ?_
    intro u hu
    show ‖p.2.1 u - q.2.1 u‖ ≤ D + Lm * (eps * Lm + kb * D)
    rw [vel_eq hc hp hevp u, vel_eq hc hq hevq u, ← hL1def, ← hL2def]
    have hsplit : ((L₁ : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
        - ((L₂ : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))
        = ((L₁ - L₂ : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
          + ((L₂ : ℝ) : ℂ) * (Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
            - Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))) := by
      push_cast; ring
    rw [hsplit]
    have ha : ‖((L₁ - L₂ : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))‖ ≤ D := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Real.exp_zero, mul_one, mul_zero]
      exact hD
    have hb : ‖((L₂ : ℝ) : ℂ) * (Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
        - Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ)))‖ ≤ Lm * (eps * Lm + kb * D) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL2pos]
      have hnn : (0:ℝ) ≤ eps * Lm + kb * D := by positivity
      calc L₂ * ‖Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
              - Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))‖
          ≤ L₂ * (eps * Lm + kb * D) := mul_le_mul_of_nonneg_left (htan u hu) hL2pos.le
        _ ≤ Lm * (eps * Lm + kb * D) := mul_le_mul_of_nonneg_right hLq hnn
    exact le_trans (norm_add_le _ _) (add_le_add ha hb)
  -- the acceleration bound
  have hbound3 : ∀ u, ‖p.2.2 u - q.2.2 u‖
      ≤ 2 * D * Lm * kb + Lm ^ 2 * (eps + kL * D + kb * (eps * Lm + kb * D)) := by
    refine forall_of_forall_Icc (f := fun u => p.2.2 u - q.2.2 u)
      (fun u => by simp [periodic_acc hp u, periodic_acc hq u]) ?_
    intro u hu
    show ‖p.2.2 u - q.2.2 u‖
      ≤ 2 * D * Lm * kb + Lm ^ 2 * (eps + kL * D + kb * (eps * Lm + kb * D))
    rw [acc_eq hc hp hevp hΘ1 u, acc_eq hc hq hevq hΘ2 u, ← hL1def, ← hL2def]
    have hsplit : ((L₁ ^ 2 : ℝ) : ℂ) *
          (Complex.I * (k₁ (L₁ * u) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ)))
        - ((L₂ ^ 2 : ℝ) : ℂ) *
          (Complex.I * (k₂ (L₂ * u) : ℂ) * Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ)))
        = ((L₁ ^ 2 - L₂ ^ 2 : ℝ) : ℂ) *
            (Complex.I * (k₁ (L₁ * u) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ)))
          + ((L₂ ^ 2 : ℝ) : ℂ) *
            (Complex.I * (k₁ (L₁ * u) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
              - Complex.I * (k₂ (L₂ * u) : ℂ)
                * Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))) := by
      push_cast; ring
    rw [hsplit]
    have hnormI : ∀ (a x : ℝ),
        ‖Complex.I * (a : ℂ) * Complex.exp (Complex.I * (x : ℂ))‖ = |a| := by
      intro a x
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp]
      simp [Complex.mul_re]
    have ha : ‖((L₁ ^ 2 - L₂ ^ 2 : ℝ) : ℂ) *
        (Complex.I * (k₁ (L₁ * u) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ)))‖
        ≤ 2 * D * Lm * kb := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormI]
      have hfac : |L₁ ^ 2 - L₂ ^ 2| = |L₁ - L₂| * (L₁ + L₂) := by
        have : L₁ ^ 2 - L₂ ^ 2 = (L₁ - L₂) * (L₁ + L₂) := by ring
        rw [this, abs_mul, abs_of_pos (by linarith : (0:ℝ) < L₁ + L₂)]
      rw [hfac]
      have h1 : |L₁ - L₂| * (L₁ + L₂) ≤ D * (2 * Lm) := by
        refine mul_le_mul hD (by linarith) (by linarith) hD0
      calc |L₁ - L₂| * (L₁ + L₂) * |k₁ (L₁ * u)|
          ≤ (D * (2 * Lm)) * kb := by
            refine mul_le_mul h1 (hkb1 _) (abs_nonneg _) (by positivity)
        _ = 2 * D * Lm * kb := by ring
    have hcurv : |k₁ (L₁ * u) - k₂ (L₂ * u)| ≤ eps + kL * D := by
      have h1 : |k₁ (L₁ * u) - k₂ (L₁ * u)| ≤ eps := hk _
      have h2 : |k₂ (L₁ * u) - k₂ (L₂ * u)| ≤ kL * D := by
        refine le_trans (hkL _ _) (mul_le_mul_of_nonneg_left (hshift u hu) hkL0)
      calc |k₁ (L₁ * u) - k₂ (L₂ * u)|
          ≤ |k₁ (L₁ * u) - k₂ (L₁ * u)| + |k₂ (L₁ * u) - k₂ (L₂ * u)| := by
            simpa using abs_sub_le (k₁ (L₁ * u)) (k₂ (L₁ * u)) (k₂ (L₂ * u))
        _ ≤ eps + kL * D := add_le_add h1 h2
    have hb : ‖((L₂ ^ 2 : ℝ) : ℂ) *
        (Complex.I * (k₁ (L₁ * u) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
          - Complex.I * (k₂ (L₂ * u) : ℂ) * Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ)))‖
        ≤ Lm ^ 2 * (eps + kL * D + kb * (eps * Lm + kb * D)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < L₂ ^ 2)]
      have hinner : ‖Complex.I * (k₁ (L₁ * u) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
          - Complex.I * (k₂ (L₂ * u) : ℂ) * Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))‖
          ≤ eps + kL * D + kb * (eps * Lm + kb * D) := by
        have hsplit2 : Complex.I * (k₁ (L₁ * u) : ℂ)
              * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
            - Complex.I * (k₂ (L₂ * u) : ℂ) * Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))
            = Complex.I * ((k₁ (L₁ * u) - k₂ (L₂ * u) : ℝ) : ℂ)
                * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
              + Complex.I * (k₂ (L₂ * u) : ℂ)
                * (Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
                  - Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))) := by
          push_cast; ring
        rw [hsplit2]
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · rw [hnormI]
          exact hcurv
        · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs]
          refine mul_le_mul (hkb2 _) (htan u hu) (norm_nonneg _) hkb0
      have hnn : (0:ℝ) ≤ eps + kL * D + kb * (eps * Lm + kb * D) := by positivity
      calc L₂ ^ 2 * ‖Complex.I * (k₁ (L₁ * u) : ℂ)
                * Complex.exp (Complex.I * (Θ₁ (L₁ * u) : ℂ))
              - Complex.I * (k₂ (L₂ * u) : ℂ)
                * Complex.exp (Complex.I * (Θ₂ (L₂ * u) : ℂ))‖
          ≤ L₂ ^ 2 * (eps + kL * D + kb * (eps * Lm + kb * D)) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ Lm ^ 2 * (eps + kL * D + kb * (eps * Lm + kb * D)) := by
            refine mul_le_mul_of_nonneg_right ?_ hnn
            nlinarith [hL2pos.le, hLq]
    exact le_trans (norm_add_le _ _) (add_le_add ha hb)
  -- assemble
  set M : ℝ := max (eps * Lm ^ 2 + D)
      (max (D + Lm * (eps * Lm + kb * D))
        (2 * D * Lm * kb + Lm ^ 2 * (eps + kL * D + kb * (eps * Lm + kb * D)))) with hM
  have hM1 : eps * Lm ^ 2 + D ≤ M := le_max_left _ _
  have hM2 : D + Lm * (eps * Lm + kb * D) ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM3 : 2 * D * Lm * kb + Lm ^ 2 * (eps + kL * D + kb * (eps * Lm + kb * D)) ≤ M :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hM0 : 0 ≤ M := le_trans (by positivity) hM1
  have hd1 : dist p.1 q.1 ≤ M :=
    (BoundedContinuousFunction.dist_le hM0).2 fun u => by
      rw [dist_eq_norm]; exact le_trans (hbound1 u) hM1
  have hd2 : dist p.2.1 q.2.1 ≤ M :=
    (BoundedContinuousFunction.dist_le hM0).2 fun u => by
      rw [dist_eq_norm]; exact le_trans (hbound2 u) hM2
  have hd3 : dist p.2.2 q.2.2 ≤ M :=
    (BoundedContinuousFunction.dist_le hM0).2 fun u => by
      rw [dist_eq_norm]; exact le_trans (hbound3 u) hM3
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le hd1 (max_le hd2 hd3)

end MarkedSpace
