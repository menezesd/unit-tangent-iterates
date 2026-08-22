import Mathlib

/-!
# Stability of a unit-speed curve under a perturbation of its curvature

The defect estimate of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates* compares two curves through their **curvatures**, while the space of
marked curves is metrized by the `C²` distance of the curves themselves.  This
file supplies the elementary bridge between the two: two unit-speed plane
curves whose curvatures are uniformly `ε`-close, and which agree in position
and direction at the marked point, stay `C²`-close on a window of length `S`,
with the explicit bounds

* `|Θ₁ − Θ₂| ≤ ε|s|` for the tangent angles (`abs_angle_sub_le`);
* `‖F₁' − F₂'‖ ≤ ε|s|` for the unit tangents (`norm_tangent_sub_le`);
* `‖F₁ − F₂‖ ≤ εS|s|` for the curves (`norm_curve_sub_le`);
* `‖F₁'' − F₂''‖ ≤ ε(1 + kb·S)` for the accelerations, `kb` a bound for the
  second curvature (`norm_accel_sub_le'`).

`c2_close_of_curvature_close` packages the three of them.  Everything is proved
from the mean value inequality; no periodicity or closedness is used.
-/

noncomputable section

open Set

namespace CurvatureStability

/-! ### The tangent angles -/

/-- **Two tangent angles with `ε`-close curvatures separate at most linearly.**
If `Θᵢ' = kᵢ` with `|k₁ − k₂| ≤ ε` everywhere and the two angles agree at the
marked point, then `|Θ₁ s − Θ₂ s| ≤ ε|s|`. -/
theorem abs_angle_sub_le {Θ₁ Θ₂ k₁ k₂ : ℝ → ℝ} {eps : ℝ}
    (h1 : ∀ s, HasDerivAt Θ₁ (k₁ s) s) (h2 : ∀ s, HasDerivAt Θ₂ (k₂ s) s)
    (h0 : Θ₁ 0 = Θ₂ 0) (hk : ∀ s, |k₁ s - k₂ s| ≤ eps) (s : ℝ) :
    |Θ₁ s - Θ₂ s| ≤ eps * |s| := by
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) s,
      HasDerivWithinAt (fun r => Θ₁ r - Θ₂ r) (k₁ u - k₂ u) (uIcc (0 : ℝ) s) u :=
    fun u _ => ((h1 u).sub (h2 u)).hasDerivWithinAt
  have hbound : ∀ u ∈ uIcc (0 : ℝ) s, ‖k₁ u - k₂ u‖ ≤ eps := fun u _ => by
    simpa [Real.norm_eq_abs] using hk u
  have hmvt := (convex_uIcc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs, h0, sub_zero] using hmvt

/-! ### The unit tangents -/

/-- **The unit tangent is `1`-Lipschitz in the angle**: `‖e^{ia} − e^{ib}‖ ≤ |a − b|`. -/
theorem norm_tangent_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
      (Complex.I * Complex.exp (Complex.I * (x : ℂ))) x := by
    intro x
    have h0 : HasDerivAt (fun r : ℝ => Complex.I * (r : ℂ)) Complex.I x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul Complex.I
    simpa [mul_comm] using h0.cexp
  have hderiv : ∀ u ∈ uIcc b a,
      HasDerivWithinAt (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
        (Complex.I * Complex.exp (Complex.I * (u : ℂ))) (uIcc b a) u :=
    fun u _ => (hd u).hasDerivWithinAt
  have hbound : ∀ u ∈ uIcc b a, ‖Complex.I * Complex.exp (Complex.I * (u : ℂ))‖ ≤ 1 := by
    intro u _
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
    simp
  have hmvt := (convex_uIcc b a).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmvt

/-! ### The curves -/

/-- **Two unit-speed curves with `ε`-close curvatures stay `εS|s|`-close on a
window of half-length `S`.**  The curves agree in position and direction at the
marked point. -/
theorem norm_curve_sub_le {F₁ F₂ : ℝ → ℂ} {Θ₁ Θ₂ : ℝ → ℝ} {eps S : ℝ}
    (hF1 : ∀ s, HasDerivAt F₁ (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s)
    (hF2 : ∀ s, HasDerivAt F₂ (Complex.exp (Complex.I * (Θ₂ s : ℂ))) s)
    (hF0 : F₁ 0 = F₂ 0) (heps : 0 ≤ eps) (hS : 0 ≤ S)
    (hang : ∀ s, |Θ₁ s - Θ₂ s| ≤ eps * |s|)
    {s : ℝ} (hs : s ∈ Icc (-S) S) :
    ‖F₁ s - F₂ s‖ ≤ eps * S * |s| := by
  have h0mem : (0 : ℝ) ∈ Icc (-S) S := ⟨by linarith, hS⟩
  have hderiv : ∀ u ∈ Icc (-S) S,
      HasDerivWithinAt (fun r => F₁ r - F₂ r)
        (Complex.exp (Complex.I * (Θ₁ u : ℂ)) - Complex.exp (Complex.I * (Θ₂ u : ℂ)))
        (Icc (-S) S) u :=
    fun u _ => ((hF1 u).sub (hF2 u)).hasDerivWithinAt
  have hbound : ∀ u ∈ Icc (-S) S,
      ‖Complex.exp (Complex.I * (Θ₁ u : ℂ)) - Complex.exp (Complex.I * (Θ₂ u : ℂ))‖
        ≤ eps * S := by
    intro u hu
    refine le_trans (norm_tangent_sub_le _ _) (le_trans (hang u) ?_)
    have hu' : |u| ≤ S := abs_le.2 ⟨hu.1, hu.2⟩
    exact mul_le_mul_of_nonneg_left hu' heps
  have hmvt := (convex_Icc (-S) S).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound h0mem hs
  simpa [hF0, Real.norm_eq_abs] using hmvt

/-! ### Lipschitz bounds along a single curve -/

/-- A unit-speed curve is `1`-Lipschitz. -/
theorem norm_curve_sub_le_dist {F : ℝ → ℂ} {Θ : ℝ → ℝ}
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s) (a b : ℝ) :
    ‖F a - F b‖ ≤ |a - b| := by
  have hderiv : ∀ u ∈ uIcc b a,
      HasDerivWithinAt F (Complex.exp (Complex.I * (Θ u : ℂ))) (uIcc b a) u :=
    fun u _ => (hF u).hasDerivWithinAt
  have hbound : ∀ u ∈ uIcc b a, ‖Complex.exp (Complex.I * (Θ u : ℂ))‖ ≤ 1 := by
    intro u _
    rw [Complex.norm_exp]
    simp
  have hmvt := (convex_uIcc b a).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmvt

/-- The tangent angle of a curve of curvature bounded by `kb` is
`kb`-Lipschitz. -/
theorem abs_angle_sub_le_dist {Θ k : ℝ → ℝ} {kb : ℝ}
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb) (a b : ℝ) :
    |Θ a - Θ b| ≤ kb * |a - b| := by
  have hderiv : ∀ u ∈ uIcc b a, HasDerivWithinAt Θ (k u) (uIcc b a) u :=
    fun u _ => (hΘ u).hasDerivWithinAt
  have hbound : ∀ u ∈ uIcc b a, ‖k u‖ ≤ kb := fun u _ => by
    simpa [Real.norm_eq_abs] using hkb u
  have hmvt := (convex_uIcc b a).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmvt

/-! ### The accelerations -/

/-- The accelerations of two unit-speed curves differ by at most
`|k₁ − k₂| + |k₂||Θ₁ − Θ₂|`. -/
theorem norm_accel_sub_le (a b ka kb : ℝ) :
    ‖Complex.I * (ka : ℂ) * Complex.exp (Complex.I * (a : ℂ))
      - Complex.I * (kb : ℂ) * Complex.exp (Complex.I * (b : ℂ))‖
      ≤ |ka - kb| + |kb| * |a - b| := by
  have hsplit : Complex.I * (ka : ℂ) * Complex.exp (Complex.I * (a : ℂ))
      - Complex.I * (kb : ℂ) * Complex.exp (Complex.I * (b : ℂ))
      = Complex.I * ((ka - kb : ℝ) : ℂ) * Complex.exp (Complex.I * (a : ℂ))
        + Complex.I * (kb : ℂ)
          * (Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))) := by
    push_cast; ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
    simp [Complex.norm_real, Real.norm_eq_abs, Complex.mul_re, -Complex.ofReal_sub]
  · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_tangent_sub_le a b) (abs_nonneg kb)

/-- **The accelerations stay `ε(1 + kb·S)`-close on the window.** -/
theorem norm_accel_sub_le' {Θ₁ Θ₂ k₁ k₂ : ℝ → ℝ} {eps S kb : ℝ}
    (heps : 0 ≤ eps) (hkb : ∀ s, |k₂ s| ≤ kb)
    (hk : ∀ s, |k₁ s - k₂ s| ≤ eps)
    (hang : ∀ s, |Θ₁ s - Θ₂ s| ≤ eps * |s|)
    {s : ℝ} (hs : s ∈ Icc (-S) S) :
    ‖Complex.I * (k₁ s : ℂ) * Complex.exp (Complex.I * (Θ₁ s : ℂ))
      - Complex.I * (k₂ s : ℂ) * Complex.exp (Complex.I * (Θ₂ s : ℂ))‖
      ≤ eps * (1 + kb * S) := by
  have habs : |s| ≤ S := abs_le.2 ⟨hs.1, hs.2⟩
  have hkb0 : 0 ≤ kb := le_trans (abs_nonneg _) (hkb 0)
  have h1 : |k₂ s| * |Θ₁ s - Θ₂ s| ≤ kb * (eps * S) := by
    refine mul_le_mul (hkb s) (le_trans (hang s) ?_) (abs_nonneg _) hkb0
    exact mul_le_mul_of_nonneg_left habs heps
  refine le_trans (norm_accel_sub_le _ _ _ _) ?_
  have := hk s
  nlinarith [this, h1]

/-! ### The package -/

/-- **`C²` stability of a unit-speed curve under a perturbation of its
curvature.**  Two unit-speed plane curves agreeing in position and direction at
the marked point, whose curvatures differ by at most `ε` and the second of
whose curvatures is bounded by `kb`, differ on the window `[−S, S]` by at most
`εS²` in position, `εS` in velocity and `ε(1 + kbS)` in acceleration. -/
theorem c2_close_of_curvature_close {F₁ F₂ : ℝ → ℂ} {Θ₁ Θ₂ k₁ k₂ : ℝ → ℝ} {eps S kb : ℝ}
    (hF1 : ∀ s, HasDerivAt F₁ (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s)
    (hF2 : ∀ s, HasDerivAt F₂ (Complex.exp (Complex.I * (Θ₂ s : ℂ))) s)
    (h1 : ∀ s, HasDerivAt Θ₁ (k₁ s) s) (h2 : ∀ s, HasDerivAt Θ₂ (k₂ s) s)
    (hF0 : F₁ 0 = F₂ 0) (hΘ0 : Θ₁ 0 = Θ₂ 0)
    (heps : 0 ≤ eps) (hS : 0 ≤ S)
    (hk : ∀ s, |k₁ s - k₂ s| ≤ eps) (hkb : ∀ s, |k₂ s| ≤ kb)
    {s : ℝ} (hs : s ∈ Icc (-S) S) :
    ‖F₁ s - F₂ s‖ ≤ eps * S ^ 2 ∧
      ‖Complex.exp (Complex.I * (Θ₁ s : ℂ)) - Complex.exp (Complex.I * (Θ₂ s : ℂ))‖
        ≤ eps * S ∧
      ‖Complex.I * (k₁ s : ℂ) * Complex.exp (Complex.I * (Θ₁ s : ℂ))
        - Complex.I * (k₂ s : ℂ) * Complex.exp (Complex.I * (Θ₂ s : ℂ))‖
        ≤ eps * (1 + kb * S) := by
  have hang : ∀ t, |Θ₁ t - Θ₂ t| ≤ eps * |t| := abs_angle_sub_le h1 h2 hΘ0 hk
  have habs : |s| ≤ S := abs_le.2 ⟨hs.1, hs.2⟩
  refine ⟨?_, ?_, norm_accel_sub_le' heps hkb hk hang hs⟩
  · refine le_trans (norm_curve_sub_le hF1 hF2 hF0 heps hS hang hs) ?_
    have : eps * S * |s| ≤ eps * S * S :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    nlinarith [this]
  · refine le_trans (norm_tangent_sub_le _ _) (le_trans (hang s) ?_)
    exact mul_le_mul_of_nonneg_left habs heps

end CurvatureStability
