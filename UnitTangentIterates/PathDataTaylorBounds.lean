import Mathlib
import UnitTangentIterates.UniformFrameBounds
import UnitTangentIterates.PathMetric
import UnitTangentIterates.FrontFromPath

/-!
# Lipschitz and Taylor bounds for the data of a normal path

The rear path-distance bounds of this project (`SelectedInverseRearOwn*`) carry,
besides the regularity of the front data, a block of *quantitative* hypotheses
on the way that data moves in the time of the path:

* sup bounds `|∂_t Kn| ≤ Md`, `|P'| ≤ MP` for the first time derivatives;
* Lipschitz bounds `|Kn a σ − Kn b σ| ≤ Klip|a−b|`, `|P a − P b| ≤ Plip|a−b|`;
* first-order Taylor bounds
  `|Kn a σ − Kn b σ − (a−b)∂_tKn b σ| ≤ CK(a−b)²`,
  `|P a − P b − (a−b)P' b| ≤ CP(a−b)²`.

None of the six constants appears in the conclusion of those bounds, and none of
them is an independent assumption: a normal path is *at rest outside its time
window* (its cost density, hence its normal velocity, vanishes there), so all
this data is constant in the time outside a compact window and, being periodic
in the space variable, is bounded together with its time derivatives.  This
file proves that.

Contents:

* `abs_sub_le_of_deriv_bound`, `abs_taylor_le_of_deriv2_bound` — the two
  one-dimensional mean value bounds, the Taylor one with the (non-sharp, but
  global) constant `B` in place of `B/2`;
* `exists_bound_of_rest`, `exists_bound_of_periodic_rest` — boundedness on the
  whole line of data that is constant in the time outside `[0,T]` (and periodic
  in the space variable);
* `exists_lip_taylor_of_rest`, `exists_lip_taylor_of_rest_periodic` — the three
  constants produced at once, for a function of the time alone and for a family;
* `path_X_rest` and its consequences `path_V_rest`, `path_A_rest`, `path_P_rest`,
  `path_Kn_rest`: the front data of a normal path is indeed at rest outside the time
  window of the path.
-/

noncomputable section

open Set Function UniformFrameBounds

namespace PathDataTaylorBounds

/-! ### One-dimensional mean value bounds -/

/-- **The mean value inequality.**  A function whose derivative is bounded by
`B` everywhere is `B`-Lipschitz. -/
theorem abs_sub_le_of_deriv_bound {g g' : ℝ → ℝ} {B : ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hB : ∀ t, |g' t| ≤ B) (a b : ℝ) :
    |g a - g b| ≤ B * |a - b| := by
  have hdiff : ∀ t ∈ (univ : Set ℝ), DifferentiableAt ℝ g t := fun t _ => (hg t).differentiableAt
  have hbound : ∀ t ∈ (univ : Set ℝ), ‖deriv g t‖ ≤ B := by
    intro t _
    rw [(hg t).deriv, Real.norm_eq_abs]
    exact hB t
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
    (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using h

/-- **The first-order Taylor bound.**  If the second derivative is bounded by
`B` then the first-order Taylor remainder at `b` is at most `B(a−b)²`.  (The
sharp constant is `B/2`; the weaker one suffices here and is proved by applying
the mean value inequality twice.) -/
theorem abs_taylor_le_of_deriv2_bound {g g' g'' : ℝ → ℝ} {B : ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (hB : ∀ t, |g'' t| ≤ B) (a b : ℝ) :
    |g a - g b - (a - b) * g' b| ≤ B * (a - b) ^ 2 := by
  set h : ℝ → ℝ := fun t => g t - g b - (t - b) * g' b with hh
  have hderiv : ∀ t, HasDerivAt h (g' t - g' b) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => g t - g b) (g' t) t := (hg t).sub_const _
    have h2 : HasDerivAt (fun t : ℝ => (t - b) * g' b) (g' b) t := by
      simpa using ((hasDerivAt_id t).sub_const b).mul_const (g' b)
    simpa [hh] using h1.sub h2
  have hlip : ∀ t, |g' t - g' b| ≤ B * |t - b| := fun t =>
    abs_sub_le_of_deriv_bound hg' hB t b
  have hseg : ∀ t ∈ uIcc b a, ‖deriv h t‖ ≤ B * |a - b| := by
    intro t ht
    have htb : |t - b| ≤ |a - b| := by
      rcases mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - b)]
        exact le_trans (by linarith) (le_abs_self _)
      · rw [abs_of_nonpos (by linarith : t - b ≤ 0), abs_of_nonpos (by linarith : a - b ≤ 0)]
        linarith
    calc ‖deriv h t‖ = |g' t - g' b| := by rw [(hderiv t).deriv, Real.norm_eq_abs]
      _ ≤ B * |t - b| := hlip t
      _ ≤ B * |a - b| := by
          have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB b)
          exact mul_le_mul_of_nonneg_left htb hB0
  have hdiff : ∀ t ∈ uIcc b a, DifferentiableAt ℝ h t := fun t _ => (hderiv t).differentiableAt
  have hres := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hseg (convex_uIcc b a)
    (left_mem_uIcc) (right_mem_uIcc)
  have hb : h b = 0 := by simp [hh]
  have ha : h a = g a - g b - (a - b) * g' b := rfl
  rw [ha, hb] at hres
  simpa [Real.norm_eq_abs, sq_abs, pow_two, mul_assoc, abs_mul] using
    (by simpa [Real.norm_eq_abs, abs_mul] using hres :
      |g a - g b - (a - b) * g' b| ≤ B * |a - b| * |a - b|)

/-! ### Boundedness from rest outside the time window -/

/-- **A continuous function that is constant in the time outside a compact
window is bounded.** -/
theorem exists_bound_of_rest {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hc : Continuous f)
    (hrest : ∀ t, f t = f (clampT 0 T t)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |f t| ≤ B := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_isMaxOn
    ⟨0, left_mem_Icc.mpr hT⟩ hc.abs.continuousOn
  refine ⟨|f p|, abs_nonneg _, fun t => ?_⟩
  rw [hrest t]
  exact hmax (clampT_mem hT t)

/-- **A jointly continuous family, periodic in the space variable and constant
in the time outside a compact window, is bounded on the whole plane.** -/
theorem exists_bound_of_periodic_rest {f : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hc : Continuous (uncurry f)) (hper : ∀ t, Periodic (f t) 1)
    (hrest : ∀ t σ, f t σ = f (clampT 0 T t) σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t σ, |f t σ| ≤ B := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_periodic (t0 := 0) (t1 := T) one_pos hc hper
  exact ⟨M, hM0, fun t σ => by rw [hrest t σ]; exact hM _ (clampT_mem hT t) σ⟩

/-! ### The three constants, produced -/

/-- **The sup, Lipschitz and Taylor constants of a function of the time alone.**
If `f` is twice differentiable with continuous derivatives and is constant
outside the window `[0,T]`, then its derivative is bounded, it is Lipschitz, and
its first-order Taylor remainder is quadratic — all three globally in the
time. -/
theorem exists_lip_taylor_of_rest {f f1 f2 : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf1 : ∀ t, HasDerivAt f (f1 t) t) (hf2 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hc1 : Continuous f1) (hc2 : Continuous f2)
    (hrest1 : ∀ t, f1 t = f1 (clampT 0 T t)) (hrest2 : ∀ t, f2 t = f2 (clampT 0 T t)) :
    ∃ M L C : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ 0 ≤ C ∧ (∀ t, |f1 t| ≤ M) ∧
      (∀ a b, |f a - f b| ≤ L * |a - b|) ∧
      (∀ a b, |f a - f b - (a - b) * f1 b| ≤ C * (a - b) ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_rest hT hc1 hrest1
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_rest hT hc2 hrest2
  exact ⟨M, M, C, hM0, hM0, hC0, hM, fun a b => abs_sub_le_of_deriv_bound hf1 hM a b,
    fun a b => abs_taylor_le_of_deriv2_bound hf1 hf2 hC a b⟩

/-- **The three constants of a family, uniformly in the space variable.**  The
same for a family that is periodic in the space variable, its time derivatives
being taken slicewise. -/
theorem exists_lip_taylor_of_rest_periodic {f f1 f2 : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf1 : ∀ t σ, HasDerivAt (fun a => f a σ) (f1 t σ) t)
    (hf2 : ∀ t σ, HasDerivAt (fun a => f1 a σ) (f2 t σ) t)
    (hc1 : Continuous (uncurry f1)) (hc2 : Continuous (uncurry f2))
    (hper1 : ∀ t, Periodic (f1 t) 1) (hper2 : ∀ t, Periodic (f2 t) 1)
    (hrest1 : ∀ t σ, f1 t σ = f1 (clampT 0 T t) σ)
    (hrest2 : ∀ t σ, f2 t σ = f2 (clampT 0 T t) σ) :
    ∃ M L C : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ 0 ≤ C ∧ (∀ t σ, |f1 t σ| ≤ M) ∧
      (∀ a b σ, |f a σ - f b σ| ≤ L * |a - b|) ∧
      (∀ a b σ, |f a σ - f b σ - (a - b) * f1 b σ| ≤ C * (a - b) ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_periodic_rest hT hc1 hper1 hrest1
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_periodic_rest hT hc2 hper2 hrest2
  refine ⟨M, M, C, hM0, hM0, hC0, hM, fun a b σ => ?_, fun a b σ => ?_⟩
  · exact abs_sub_le_of_deriv_bound (fun t => hf1 t σ) (fun t => hM t σ) a b
  · exact abs_taylor_le_of_deriv2_bound (fun t => hf1 t σ) (fun t => hf2 t σ)
      (fun t => hC t σ) a b

/-! ### The partial derivative in the time variable -/

/-- The partial derivative of a family in its **time** variable, as a function
of the pair.  (`UniformFrameBounds.partialX` is the derivative in the space
variable.) -/
def partialT (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun a x => fderiv ℝ (uncurry f) (a, x) (1, 0)

/-- `partialT f · x` is the derivative of the time slice `fun a => f a x`. -/
theorem hasDerivAt_partialT {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (uncurry f)) (a x : ℝ) :
    HasDerivAt (fun r => f r x) (partialT f a x) a := by
  have h1 : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (a, x)) (a, x) :=
    (hf.differentiable one_ne_zero _).hasFDerivAt
  have h2 : HasDerivAt (fun r : ℝ => (r, (x : ℝ))) (1, 0) a := by
    simpa using (hasDerivAt_id a).prodMk (hasDerivAt_const a x)
  exact h1.comp_hasDerivAt a h2

/-- The time derivative is one degree less smooth than the family. -/
theorem contDiff_partialT {f : ℝ → ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ ((n : ℕ) + 1) (uncurry f)) :
    ContDiff ℝ (n : ℕ) (uncurry (partialT f)) := by
  have hd : ContDiff ℝ (n : ℕ) (fderiv ℝ (uncurry f)) := by
    refine hf.fderiv_right ?_
    exact_mod_cast le_rfl
  have := (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff.comp hd
  simpa [Function.uncurry, partialT] using this

/-- The time derivative of a space-periodic family is space-periodic. -/
theorem periodic_partialT {f : ℝ → ℝ → ℝ} {Q : ℝ} (hf : ContDiff ℝ 1 (uncurry f))
    (hper : ∀ a, Function.Periodic (f a) Q) (a : ℝ) :
    Function.Periodic (partialT f a) Q := by
  intro x
  have h1 : HasDerivAt (fun r => f r (x + Q)) (partialT f a (x + Q)) a :=
    hasDerivAt_partialT hf a (x + Q)
  have hfun : (fun r => f r (x + Q)) = fun r => f r x := funext fun r => hper r x
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_partialT hf a x)

/-- **A family that does not move in time on an open set has vanishing time
derivative there.** -/
theorem partialT_eq_zero_of_const_on {f : ℝ → ℝ → ℝ} {s : Set ℝ} {t x : ℝ}
    (hf : ContDiff ℝ 1 (uncurry f)) (hs : IsOpen s) (ht : t ∈ s)
    (hconst : ∀ r ∈ s, f r x = f t x) : partialT f t x = 0 := by
  have hev : (fun r => f r x) =ᶠ[nhds t] fun _ => f t x :=
    Filter.eventuallyEq_of_mem (hs.mem_nhds ht) hconst
  have h0 : HasDerivAt (fun r => f r x) 0 t :=
    (hasDerivAt_const t (f t x)).congr_of_eventuallyEq hev
  exact (hasDerivAt_partialT hf t x).unique h0

/-- **A function that is constant on an open set has vanishing derivative
there.** -/
theorem deriv_eq_zero_of_const_on {g : ℝ → ℝ} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s) (hconst : ∀ r ∈ s, g r = g t) : deriv g t = 0 := by
  have hev : g =ᶠ[nhds t] fun _ => g t :=
    Filter.eventuallyEq_of_mem (hs.mem_nhds ht) hconst
  rw [hev.deriv_eq, deriv_const]

/-! ### Rest outside the window makes the time derivatives vanish -/

theorem clampT_of_le_zero {T t : ℝ} (ht : t ≤ 0) : clampT 0 T t = 0 := by
  have h : min t T ≤ 0 := le_trans (min_le_left _ _) ht
  simp [clampT, max_eq_left h]

theorem clampT_of_ge {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ t) : clampT 0 T t = T := by
  simp [clampT, min_eq_right ht, max_eq_right hT]

theorem not_mem_Icc_cases {T t : ℝ} (ht : t ∉ Icc (0:ℝ) T) : t < 0 ∨ T < t := by
  by_contra hcon
  push_neg at hcon
  exact ht ⟨hcon.1, hcon.2⟩

/-- **The time derivative of a family at rest outside the window vanishes
there.** -/
theorem partialT_vanishing_of_rest {f : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContDiff ℝ 1 (uncurry f)) (hrest : ∀ t σ, f t σ = f (clampT 0 T t) σ) :
    ∀ t σ, t ∉ Icc (0:ℝ) T → partialT f t σ = 0 := by
  intro t σ ht
  rcases not_mem_Icc_cases ht with h | h
  · refine partialT_eq_zero_of_const_on hf isOpen_Iio (mem_Iio.mpr h) fun r hr => ?_
    rw [hrest r σ, hrest t σ, clampT_of_le_zero (le_of_lt (mem_Iio.mp hr)),
      clampT_of_le_zero h.le]
  · refine partialT_eq_zero_of_const_on hf isOpen_Ioi (mem_Ioi.mpr h) fun r hr => ?_
    rw [hrest r σ, hrest t σ, clampT_of_ge hT (le_of_lt (mem_Ioi.mp hr)), clampT_of_ge hT h.le]

/-- **The time derivative of a family vanishing outside the window vanishes
there too.** -/
theorem partialT_vanishing_of_vanishing {f : ℝ → ℝ → ℝ} {T : ℝ}
    (hf : ContDiff ℝ 1 (uncurry f)) (hvan : ∀ t σ, t ∉ Icc (0:ℝ) T → f t σ = 0) :
    ∀ t σ, t ∉ Icc (0:ℝ) T → partialT f t σ = 0 := by
  intro t σ ht
  rcases not_mem_Icc_cases ht with h | h
  · refine partialT_eq_zero_of_const_on hf isOpen_Iio (mem_Iio.mpr h) fun r hr => ?_
    rw [hvan r σ (fun hc => absurd hc.1 (not_le.mpr (mem_Iio.mp hr))), hvan t σ ht]
  · refine partialT_eq_zero_of_const_on hf isOpen_Ioi (mem_Ioi.mpr h) fun r hr => ?_
    rw [hvan r σ (fun hc => absurd hc.2 (not_le.mpr (mem_Ioi.mp hr))), hvan t σ ht]

/-- **The derivative of a function at rest outside the window vanishes
there.** -/
theorem deriv_vanishing_of_rest {g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hrest : ∀ t, g t = g (clampT 0 T t)) : ∀ t, t ∉ Icc (0:ℝ) T → deriv g t = 0 := by
  intro t ht
  rcases not_mem_Icc_cases ht with h | h
  · refine deriv_eq_zero_of_const_on isOpen_Iio (mem_Iio.mpr h) fun r hr => ?_
    rw [hrest r, hrest t, clampT_of_le_zero (le_of_lt (mem_Iio.mp hr)), clampT_of_le_zero h.le]
  · refine deriv_eq_zero_of_const_on isOpen_Ioi (mem_Ioi.mpr h) fun r hr => ?_
    rw [hrest r, hrest t, clampT_of_ge hT (le_of_lt (mem_Ioi.mp hr)), clampT_of_ge hT h.le]

/-- **The derivative of a function vanishing outside the window vanishes
there too.** -/
theorem deriv_vanishing_of_vanishing {g : ℝ → ℝ} {T : ℝ}
    (hvan : ∀ t, t ∉ Icc (0:ℝ) T → g t = 0) : ∀ t, t ∉ Icc (0:ℝ) T → deriv g t = 0 := by
  intro t ht
  rcases not_mem_Icc_cases ht with h | h
  · refine deriv_eq_zero_of_const_on isOpen_Iio (mem_Iio.mpr h) fun r hr => ?_
    rw [hvan r (fun hc => absurd hc.1 (not_le.mpr (mem_Iio.mp hr))), hvan t ht]
  · refine deriv_eq_zero_of_const_on isOpen_Ioi (mem_Ioi.mpr h) fun r hr => ?_
    rw [hvan r (fun hc => absurd hc.2 (not_le.mpr (mem_Ioi.mp hr))), hvan t ht]

/-! ### Boundedness from vanishing outside the time window -/

/-- **A jointly continuous family, periodic in space and vanishing outside a
compact window of times, is bounded.** -/
theorem exists_bound_of_periodic_vanishing {f : ℝ → ℝ → ℝ} {T : ℝ}
    (hc : Continuous (uncurry f)) (hper : ∀ t, Periodic (f t) 1)
    (hvan : ∀ t σ, t ∉ Icc (0:ℝ) T → f t σ = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t σ, |f t σ| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_of_periodic (t0 := 0) (t1 := T) one_pos hc hper
  refine ⟨B, hB0, fun t σ => ?_⟩
  by_cases ht : t ∈ Icc (0:ℝ) T
  · exact hB t ht σ
  · rw [hvan t σ ht]; simpa using hB0

/-- **A continuous function vanishing outside a compact window is bounded.** -/
theorem exists_bound_of_vanishing {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hc : Continuous f)
    (hvan : ∀ t, t ∉ Icc (0:ℝ) T → f t = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |f t| ≤ B := by
  obtain ⟨y, hy, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_isMaxOn
    ⟨0, left_mem_Icc.mpr hT⟩ hc.abs.continuousOn
  refine ⟨|f y|, abs_nonneg _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0:ℝ) T
  · exact hmax ht
  · rw [hvan t ht]; simp [abs_nonneg (f y)]

/-- **The three constants of a function of the time whose derivatives vanish
outside a compact window.** -/
theorem exists_lip_taylor_of_vanishing {f f1 f2 : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf1 : ∀ t, HasDerivAt f (f1 t) t) (hf2 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hc1 : Continuous f1) (hc2 : Continuous f2)
    (hvan1 : ∀ t, t ∉ Icc (0:ℝ) T → f1 t = 0) (hvan2 : ∀ t, t ∉ Icc (0:ℝ) T → f2 t = 0) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ (∀ t, |f1 t| ≤ M) ∧
      (∀ a b, |f a - f b| ≤ M * |a - b|) ∧
      (∀ a b, |f a - f b - (a - b) * f1 b| ≤ C * (a - b) ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_vanishing hT hc1 hvan1
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_vanishing hT hc2 hvan2
  exact ⟨M, C, hM0, hC0, hM, fun a b => abs_sub_le_of_deriv_bound hf1 hM a b,
    fun a b => abs_taylor_le_of_deriv2_bound hf1 hf2 hC a b⟩

/-- **The three constants of a family whose time derivatives vanish outside a
compact window.** -/
theorem exists_lip_taylor_of_vanishing_periodic {f f1 f2 : ℝ → ℝ → ℝ} {T : ℝ}
    (hf1 : ∀ t σ, HasDerivAt (fun a => f a σ) (f1 t σ) t)
    (hf2 : ∀ t σ, HasDerivAt (fun a => f1 a σ) (f2 t σ) t)
    (hc1 : Continuous (uncurry f1)) (hc2 : Continuous (uncurry f2))
    (hper1 : ∀ t, Periodic (f1 t) 1) (hper2 : ∀ t, Periodic (f2 t) 1)
    (hvan1 : ∀ t σ, t ∉ Icc (0:ℝ) T → f1 t σ = 0)
    (hvan2 : ∀ t σ, t ∉ Icc (0:ℝ) T → f2 t σ = 0) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ (∀ t σ, |f1 t σ| ≤ M) ∧
      (∀ a b σ, |f a σ - f b σ| ≤ M * |a - b|) ∧
      (∀ a b σ, |f a σ - f b σ - (a - b) * f1 b σ| ≤ C * (a - b) ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_periodic_vanishing hc1 hper1 hvan1
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_periodic_vanishing hc2 hper2 hvan2
  refine ⟨M, C, hM0, hC0, hM, fun a b σ => ?_, fun a b σ => ?_⟩
  · exact abs_sub_le_of_deriv_bound (fun t => hf1 t σ) (fun t => hM t σ) a b
  · exact abs_taylor_le_of_deriv2_bound (fun t => hf1 t σ) (fun t => hf2 t σ)
      (fun t => hC t σ) a b

/-! ### The front data of a normal path is at rest outside the window -/

open PathMetric MarkedSpace

variable {p q : Data}

/-- **A normal path stands still outside its time window.**  Its normal
velocity vanishes there, so each point of the curve is where it was at the
nearest end of the window. -/
theorem path_X_rest (Γ : NormalPath p q) (t u : ℝ) :
    Γ.X t u = Γ.X (clampT 0 Γ.T t) u := by
  have hzero : ∀ s : Set ℝ, Convex ℝ s → (∀ r ∈ s, r ∉ Ioo (0:ℝ) Γ.T) →
      ∀ x ∈ s, ∀ y ∈ s, Γ.X x u = Γ.X y u := by
    intro s hs hout x hx y hy
    have hdiff : ∀ r ∈ s, DifferentiableAt ℝ (fun r => Γ.X r u) r :=
      fun r _ => (Γ.hasDerivAt_time r u).differentiableAt
    have hbound : ∀ r ∈ s, ‖deriv (fun r => Γ.X r u) r‖ ≤ 0 := by
      intro r hr
      rw [(Γ.hasDerivAt_time r u).deriv, Γ.vel_stop (hout r hr) u]
      simp
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hs hy hx
    have : ‖Γ.X x u - Γ.X y u‖ ≤ 0 := by simpa using h
    have := le_antisymm this (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  rcases le_or_gt t 0 with ht | ht
  · have hc : clampT 0 Γ.T t = 0 := by
      have : min t Γ.T ≤ 0 := le_trans (min_le_left _ _) ht
      simp [clampT, max_eq_left this]
    rw [hc]
    exact hzero (Iic 0) (convex_Iic 0)
      (fun r hr hmem => absurd hmem.1 (not_lt.mpr (mem_Iic.mp hr)))
      t (mem_Iic.mpr ht) 0 (mem_Iic.mpr (le_refl 0))
  · rcases le_or_gt t Γ.T with ht2 | ht2
    · rw [clampT_of_mem ⟨ht.le, ht2⟩]
    · have hc : clampT 0 Γ.T t = Γ.T := by
        have h1 : min t Γ.T = Γ.T := min_eq_right ht2.le
        simp [clampT, h1, max_eq_right Γ.T_pos.le]
      rw [hc]
      exact hzero (Ici Γ.T) (convex_Ici _)
        (fun r hr hmem => absurd hmem.2 (not_lt.mpr (mem_Ici.mp hr)))
        t (mem_Ici.mpr ht2.le) Γ.T (mem_Ici.mpr (le_refl Γ.T))

/-- The velocity of the slices of a normal path is at rest outside the time
window. -/
theorem path_V_rest (Γ : NormalPath p q) {V : ℝ → ℝ → ℂ}
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u) (t u : ℝ) :
    V t u = V (clampT 0 Γ.T t) u := by
  have hfun : Γ.X t = Γ.X (clampT 0 Γ.T t) := funext fun y => path_X_rest Γ t y
  have h1 : HasDerivAt (Γ.X (clampT 0 Γ.T t)) (V t u) u := by rw [← hfun]; exact hV t u
  exact h1.unique (hV _ u)

/-- The acceleration of the slices of a normal path is at rest outside the time
window. -/
theorem path_A_rest (Γ : NormalPath p q) {V A : ℝ → ℝ → ℂ}
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u) (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (t u : ℝ) : A t u = A (clampT 0 Γ.T t) u := by
  have hfun : V t = V (clampT 0 Γ.T t) := funext fun y => path_V_rest Γ hV t y
  have h1 : HasDerivAt (V (clampT 0 Γ.T t)) (A t u) u := by rw [← hfun]; exact hA t u
  exact h1.unique (hA _ u)

/-- The speed of the slices of a normal path is at rest outside the time
window. -/
theorem path_P_rest (Γ : NormalPath p q) {V : ℝ → ℝ → ℂ} {P : ℝ → ℝ}
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u) (hspeed : ∀ t u, ‖V t u‖ = P t) (t : ℝ) :
    P t = P (clampT 0 Γ.T t) := by
  rw [← hspeed t 0, ← hspeed (clampT 0 Γ.T t) 0, path_V_rest Γ hV t 0]

/-- The curvature of the slices of a normal path, read in the normalized
parameter, is at rest outside the time window. -/
theorem path_Kn_rest (Γ : NormalPath p q) {V A : ℝ → ℝ → ℂ} {P : ℝ → ℝ}
    {Kn : ℝ → ℝ → ℝ} (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u) (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hPpos : ∀ t, 0 < P t)
    (hKeq : ∀ t s, FrontFromPath.curvOfPath V A P t s = Kn t (s / P t)) (t σ : ℝ) :
    Kn t σ = Kn (clampT 0 Γ.T t) σ := by
  have hPeq : P t = P (clampT 0 Γ.T t) := path_P_rest Γ hV hspeed t
  have hVeq : ∀ u, V t u = V (clampT 0 Γ.T t) u := fun u => path_V_rest Γ hV t u
  have hAeq : ∀ u, A t u = A (clampT 0 Γ.T t) u := fun u => path_A_rest Γ hV hA t u
  have h1 := hKeq t (σ * P t)
  have h2 := hKeq (clampT 0 Γ.T t) (σ * P (clampT 0 Γ.T t))
  have hne : P t ≠ 0 := (hPpos t).ne'
  have hne2 : P (clampT 0 Γ.T t) ≠ 0 := (hPpos _).ne'
  have hdiv : σ * P t / P t = σ := by field_simp
  have hdiv2 : σ * P (clampT 0 Γ.T t) / P (clampT 0 Γ.T t) = σ := by field_simp
  rw [hdiv] at h1
  rw [hdiv2] at h2
  rw [← h1, ← h2, FrontFromPath.curvOfPath, FrontFromPath.curvOfPath, hdiv, hdiv2,
    hVeq, hAeq, hPeq]

end PathDataTaylorBounds
