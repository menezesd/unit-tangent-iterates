import Mathlib

/-!
# Joint `C¹` regularity from continuous partial derivatives

Throughout the formalization of *A Noncircular Oval with Convex Unit-Tangent
Iterates* the objects are *families* `f : ℝ → ℝ → E`, a time and an arclength,
and the assembly of the path metric asks for the joint regularity
`ContDiff ℝ 1 (uncurry f)`, while what the geometry produces are the two
partial derivatives, each of them jointly continuous.

This file supplies the classical bridge between the two: **a function of two
real variables whose partial derivatives exist everywhere and are jointly
continuous is jointly `C¹`**, with the expected differential

`Df(t,x)(u,v) = u · ∂_t f(t,x) + v · ∂_x f(t,x)`.

* `partialCLM a b` — the continuous linear map `(u,v) ↦ u • a + v • b`;
* `hasFDerivAt_of_continuous_partials` — the differential of `f` at a point;
* `contDiff_one_of_continuous_partials` — the resulting joint `C¹` regularity.
-/

noncomputable section

open Function Set Filter Topology

namespace JointC1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous linear map `(u, v) ↦ u • a + v • b` on `ℝ × ℝ`: the
differential of a function of two variables with partial derivatives `a`
and `b`. -/
def partialCLM (a b : E) : (ℝ × ℝ) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b

@[simp] theorem partialCLM_apply (a b : E) (p : ℝ × ℝ) :
    partialCLM a b p = p.1 • a + p.2 • b := rfl

/-- `a ↦ partialCLM a b` and `b ↦ partialCLM a b` are continuous, jointly. -/
theorem continuous_partialCLM {g1 g2 : ℝ × ℝ → E} (h1 : Continuous g1) (h2 : Continuous g2) :
    Continuous fun p : ℝ × ℝ => partialCLM (g1 p) (g2 p) := by
  have c1 := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous
  have c2 := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous
  exact (c1.comp h1).add (c2.comp h2)

/-- A point of the interval `[t, r]` is no further from `t` than `r` is. -/
theorem abs_sub_le_of_mem_uIcc {t r u : ℝ} (hu : u ∈ Set.uIcc t r) : |u - t| ≤ |r - t| := by
  rcases le_total t r with h | h
  · rw [Set.uIcc_of_le h] at hu
    rw [abs_of_nonneg (by linarith [hu.1]), abs_of_nonneg (by linarith)]
    linarith [hu.2]
  · rw [Set.uIcc_of_ge h] at hu
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith)]
    linarith [hu.1]

/-- **Differentiability from continuous partial derivatives.**  If the two
partial derivatives of `f : ℝ → ℝ → E` exist everywhere and are jointly
continuous, then `f` is (totally) differentiable at every point, with
differential `(u,v) ↦ u · ∂_t f + v · ∂_x f`. -/
theorem hasFDerivAt_of_continuous_partials {f f1 f2 : ℝ → ℝ → E}
    (h1 : ∀ t x, HasDerivAt (fun r => f r x) (f1 t x) t)
    (h2 : ∀ t x, HasDerivAt (f t) (f2 t x) x)
    (hc1 : Continuous (uncurry f1)) (hc2 : Continuous (uncurry f2)) (t x : ℝ) :
    HasFDerivAt (uncurry f) (partialCLM (f1 t x) (f2 t x)) (t, x) := by
  apply HasFDerivAtFilter.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨d1, hd1pos, hd1⟩ := Metric.continuousAt_iff.1 (hc1.continuousAt (x := (t, x))) (ε/2) hε2
  obtain ⟨d2, hd2pos, hd2⟩ := Metric.continuousAt_iff.1 (hc2.continuousAt (x := (t, x))) (ε/2) hε2
  set d := min d1 d2 with hd
  have hdpos : 0 < d := lt_min hd1pos hd2pos
  rw [Metric.eventually_nhds_iff]
  refine ⟨d, hdpos, ?_⟩
  rintro ⟨r, y⟩ hq
  have hqd : max |r - t| |y - x| < d := by
    have h := hq
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
    exact h
  have hyx : |y - x| < d := lt_of_le_of_lt (le_max_right _ _) hqd
  -- the increment in the time, at the second point
  have hA : ‖f r y - f t y - (r - t) • f1 t x‖ ≤ (ε/2) * |r - t| := by
    have hderiv : ∀ u ∈ Set.uIcc t r, HasDerivWithinAt
        (fun u' => f u' y - (u' - t) • f1 t x) (f1 u y - f1 t x) (Set.uIcc t r) u := by
      intro u _
      have h := (h1 u y).sub (((hasDerivAt_id u).sub_const t).smul_const (f1 t x))
      simpa using h.hasDerivWithinAt
    have hbd : ∀ u ∈ Set.uIcc t r, ‖f1 u y - f1 t x‖ ≤ ε/2 := by
      intro u hu
      have hu' : |u - t| ≤ |r - t| := abs_sub_le_of_mem_uIcc hu
      have hdlt : dist ((u, y) : ℝ × ℝ) (t, x) < d1 := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact lt_of_lt_of_le (lt_of_le_of_lt (max_le_max hu' le_rfl) hqd) (min_le_left _ _)
      simpa [dist_eq_norm] using (hd1 hdlt).le
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd (convex_uIcc t r)
      Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [Real.norm_eq_abs, sub_right_comm] using hmvt
  -- the increment in the arclength, at the first time
  have hB : ‖f t y - f t x - (y - x) • f2 t x‖ ≤ (ε/2) * |y - x| := by
    have hderiv : ∀ u ∈ Set.uIcc x y, HasDerivWithinAt
        (fun u' => f t u' - (u' - x) • f2 t x) (f2 t u - f2 t x) (Set.uIcc x y) u := by
      intro u _
      have h := (h2 t u).sub (((hasDerivAt_id u).sub_const x).smul_const (f2 t x))
      simpa using h.hasDerivWithinAt
    have hbd : ∀ u ∈ Set.uIcc x y, ‖f2 t u - f2 t x‖ ≤ ε/2 := by
      intro u hu
      have hu' : |u - x| ≤ |y - x| := abs_sub_le_of_mem_uIcc hu
      have hlt : |u - x| < d2 := lt_of_lt_of_le (lt_of_le_of_lt hu' hyx) (min_le_right _ _)
      have hdlt : dist ((t, u) : ℝ × ℝ) (t, x) < d2 := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
          max_eq_right (abs_nonneg _)]
        exact hlt
      simpa [dist_eq_norm] using (hd2 hdlt).le
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd (convex_uIcc x y)
      Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [Real.norm_eq_abs, sub_right_comm] using hmvt
  have hsum : ‖f r y - f t x - ((r - t) • f1 t x + (y - x) • f2 t x)‖
      ≤ (ε/2) * |r - t| + (ε/2) * |y - x| := by
    have heq : f r y - f t x - ((r - t) • f1 t x + (y - x) • f2 t x)
        = (f r y - f t y - (r - t) • f1 t x) + (f t y - f t x - (y - x) • f2 t x) := by
      abel
    rw [heq]
    exact le_trans (norm_add_le _ _) (add_le_add hA hB)
  calc ‖uncurry f (r, y) - uncurry f (t, x) - (partialCLM (f1 t x) (f2 t x)) ((r, y) - (t, x))‖
      = ‖f r y - f t x - ((r - t) • f1 t x + (y - x) • f2 t x)‖ := by simp [uncurry]
    _ ≤ (ε/2) * |r - t| + (ε/2) * |y - x| := hsum
    _ ≤ ε * ‖((r, y) : ℝ × ℝ) - (t, x)‖ := by
        rw [Prod.norm_def]
        simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
        have hm1 : |r - t| ≤ max |r - t| |y - x| := le_max_left _ _
        have hm2 : |y - x| ≤ max |r - t| |y - x| := le_max_right _ _
        nlinarith [abs_nonneg (r - t), abs_nonneg (y - x)]

/-- **Joint `C¹` regularity from continuous partial derivatives.**  A family
`f : ℝ → ℝ → E` whose two partial derivatives exist everywhere and are jointly
continuous is jointly `C¹`. -/
theorem contDiff_one_of_continuous_partials {f f1 f2 : ℝ → ℝ → E}
    (h1 : ∀ t x, HasDerivAt (fun r => f r x) (f1 t x) t)
    (h2 : ∀ t x, HasDerivAt (f t) (f2 t x) x)
    (hc1 : Continuous (uncurry f1)) (hc2 : Continuous (uncurry f2)) :
    ContDiff ℝ 1 (uncurry f) := by
  have hfd : ∀ p : ℝ × ℝ,
      HasFDerivAt (uncurry f) (partialCLM (f1 p.1 p.2) (f2 p.1 p.2)) p := by
    rintro ⟨t, x⟩
    exact hasFDerivAt_of_continuous_partials h1 h2 hc1 hc2 t x
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun p => (hfd p).differentiableAt, ?_⟩
  have heq : fderiv ℝ (uncurry f)
      = fun p : ℝ × ℝ => partialCLM (f1 p.1 p.2) (f2 p.1 p.2) :=
    funext fun p => (hfd p).fderiv
  rw [heq]
  exact continuous_partialCLM hc1 hc2

end JointC1
