import Mathlib
import UnitTangentIterates.CurvatureStability
import UnitTangentIterates.MarkedDistanceCurvature
import UnitTangentIterates.SupFromL1

/-!
# `C²` stability of a curve under an `L¹` perturbation of its curvature

`CurvatureStability.lean` turns a **uniform** comparison of curvatures into a
`C²` comparison of the curves, and `SupFromL1.lean` turns an `L¹` comparison
into a uniform one for a function with bounded derivative.  This file composes
the two, which is the form the defect estimate of the paper *A Noncircular Oval
with Convex Unit-Tangent Iterates* needs: its theorem *Curvature-measure
matching* controls `∫_{J_H}|k₁ − k₂|` over one period of the configuration,
while the space of marked curves is metrized by the `C²` distance.

For two `P`-periodic curvatures with `|kᵢ'| ≤ M/2` the uniform bound extends
from one period to the whole line (`abs_sub_le_of_periodic`), and feeding it to
`CurvatureStability.c2_close_of_curvature_close` gives the `C²` comparison with
`ε` replaced by `max(√(2Mε), 4ε/P)`
(`CurvatureStabilityL1.c2_close_of_L1_curvature_close`).
-/

noncomputable section

open Set

namespace CurvatureStabilityL1

/-- The uniform modulus produced by an `L¹` bound `eps` over a window of length
`P`, for functions whose derivatives are bounded by `M/2`. -/
def l1Modulus (M eps P : ℝ) : ℝ := max (Real.sqrt (2 * M * eps)) (4 * eps / P)

theorem l1Modulus_nonneg (M eps P : ℝ) : 0 ≤ l1Modulus M eps P :=
  le_max_of_le_left (Real.sqrt_nonneg _)

/-- Every point of the line lies in the window `[c, c + P)` modulo `P`. -/
theorem exists_int_sub_mem_Ico {P c : ℝ} (hP : 0 < P) (s : ℝ) :
    ∃ n : ℤ, s - n * P ∈ Ico c (c + P) := by
  refine ⟨⌊(s - c) / P⌋, ?_, ?_⟩
  · have h := Int.floor_le ((s - c) / P)
    rw [le_div_iff₀ hP] at h
    linarith
  · have h := Int.lt_floor_add_one ((s - c) / P)
    rw [div_lt_iff₀ hP] at h
    nlinarith

/-- **The uniform bound on the whole line.**  Two `P`-periodic functions with
derivatives bounded by `M/2` whose difference has `L¹` norm at most `ε` over one
period differ everywhere by at most `max(√(2Mε), 4ε/P)`. -/
theorem abs_sub_le_of_periodic {k₁ k₂ k₁' k₂' : ℝ → ℝ} {c P M eps : ℝ}
    (hP : 0 < P) (hM : 0 < M)
    (hp1 : Function.Periodic k₁ P) (hp2 : Function.Periodic k₂ P)
    (h1 : ∀ x, HasDerivAt k₁ (k₁' x) x) (h2 : ∀ x, HasDerivAt k₂ (k₂' x) x)
    (hb1 : ∀ x, |k₁' x| ≤ M / 2) (hb2 : ∀ x, |k₂' x| ≤ M / 2)
    (hint : (∫ x in c..(c + P), |k₁ x - k₂ x|) ≤ eps) (s : ℝ) :
    |k₁ s - k₂ s| ≤ max (Real.sqrt (2 * M * eps)) (4 * eps / P) := by
  obtain ⟨n, hn1, hn2⟩ := exists_int_sub_mem_Ico (c := c) hP s
  have hval1 : k₁ (s - n * P) = k₁ s := hp1.sub_int_mul_eq n
  have hval2 : k₂ (s - n * P) = k₂ s := hp2.sub_int_mul_eq n
  have h := SupFromL1.abs_sub_le_of_intervalIntegral_abs_sub_le (x0 := s - n * P)
    hP hM h1 h2 hb1 hb2 hint ⟨hn1, hn2.le⟩
  rwa [hval1, hval2] at h

/-- **`C²` stability under an `L¹` perturbation of the curvature.**  Two
unit-speed plane curves whose `P`-periodic curvatures have derivatives bounded
by `M/2` and differ by at most `ε` in `L¹` over one period, and which agree in
position and direction at the marked point, are `C²`-close on the window
`[−S, S]` with the modulus `E = max(√(2Mε), 4ε/P)`. -/
theorem c2_close_of_L1_curvature_close {F₁ F₂ : ℝ → ℂ} {Θ₁ Θ₂ k₁ k₂ k₁' k₂' : ℝ → ℝ}
    {c P M eps S kb : ℝ}
    (hF1 : ∀ s, HasDerivAt F₁ (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s)
    (hF2 : ∀ s, HasDerivAt F₂ (Complex.exp (Complex.I * (Θ₂ s : ℂ))) s)
    (hΘ1 : ∀ s, HasDerivAt Θ₁ (k₁ s) s) (hΘ2 : ∀ s, HasDerivAt Θ₂ (k₂ s) s)
    (hF0 : F₁ 0 = F₂ 0) (hΘ0 : Θ₁ 0 = Θ₂ 0) (hS : 0 ≤ S)
    (hP : 0 < P) (hM : 0 < M)
    (hp1 : Function.Periodic k₁ P) (hp2 : Function.Periodic k₂ P)
    (h1 : ∀ x, HasDerivAt k₁ (k₁' x) x) (h2 : ∀ x, HasDerivAt k₂ (k₂' x) x)
    (hb1 : ∀ x, |k₁' x| ≤ M / 2) (hb2 : ∀ x, |k₂' x| ≤ M / 2)
    (hint : (∫ x in c..(c + P), |k₁ x - k₂ x|) ≤ eps)
    (hkb : ∀ s, |k₂ s| ≤ kb) {s : ℝ} (hs : s ∈ Icc (-S) S) :
    ‖F₁ s - F₂ s‖ ≤ max (Real.sqrt (2 * M * eps)) (4 * eps / P) * S ^ 2 ∧
      ‖Complex.exp (Complex.I * (Θ₁ s : ℂ)) - Complex.exp (Complex.I * (Θ₂ s : ℂ))‖
        ≤ max (Real.sqrt (2 * M * eps)) (4 * eps / P) * S ∧
      ‖Complex.I * (k₁ s : ℂ) * Complex.exp (Complex.I * (Θ₁ s : ℂ))
        - Complex.I * (k₂ s : ℂ) * Complex.exp (Complex.I * (Θ₂ s : ℂ))‖
        ≤ max (Real.sqrt (2 * M * eps)) (4 * eps / P) * (1 + kb * S) := by
  have heps : 0 ≤ eps := le_trans
    (intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)) hint
  have hE : (0:ℝ) ≤ max (Real.sqrt (2 * M * eps)) (4 * eps / P) :=
    le_max_of_le_left (Real.sqrt_nonneg _)
  exact CurvatureStability.c2_close_of_curvature_close hF1 hF2 hΘ1 hΘ2 hF0 hΘ0 hE hS
    (abs_sub_le_of_periodic hP hM hp1 hp2 h1 h2 hb1 hb2 hint) hkb hs

/-- **The marked distance from an `L¹` comparison of the curvatures.**  Two
members of the tube of the same perimeter `L`, whose arclength
parametrizations agree in position and direction at the marked point and whose
`P`-periodic curvatures have derivatives bounded by `M/2` and differ by at most
`ε` in `L¹` over one period, are at marked distance at most
`max(√(2Mε), 4ε/P)·L²(1 + kb L)`.  This is the passage from the `L¹` output of
the theorem *Curvature-measure matching* to the metric of the space of marked
curves; the comparison itself is not supplied here. -/
theorem dist_le_of_L1_curvature_close {cc kmin delta : ℝ} (hc : 0 < cc)
    {p q : MarkedSpace.Data}
    (hp : MarkedSpace.IsTubeMember cc kmin delta p)
    (hq : MarkedSpace.IsTubeMember cc kmin delta q)
    {Θ₁ Θ₂ k₁ k₂ k₁' k₂' : ℝ → ℝ} {c P M eps kb L : ℝ}
    (hLp : MarkedSpace.perim p = L) (hLq : MarkedSpace.perim q = L)
    (hevp : ∀ s, HasDerivAt (MarkedSpace.ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s)
    (hevq : ∀ s, HasDerivAt (MarkedSpace.ev q) (Complex.exp (Complex.I * (Θ₂ s : ℂ))) s)
    (hΘ1 : ∀ s, HasDerivAt Θ₁ (k₁ s) s) (hΘ2 : ∀ s, HasDerivAt Θ₂ (k₂ s) s)
    (hF0 : MarkedSpace.ev p 0 = MarkedSpace.ev q 0) (hΘ0 : Θ₁ 0 = Θ₂ 0)
    (hP : 0 < P) (hM : 0 < M)
    (hp1 : Function.Periodic k₁ P) (hp2 : Function.Periodic k₂ P)
    (h1 : ∀ x, HasDerivAt k₁ (k₁' x) x) (h2 : ∀ x, HasDerivAt k₂ (k₂' x) x)
    (hb1 : ∀ x, |k₁' x| ≤ M / 2) (hb2 : ∀ x, |k₂' x| ≤ M / 2)
    (hint : (∫ x in c..(c + P), |k₁ x - k₂ x|) ≤ eps)
    (hkb : ∀ s, |k₂ s| ≤ kb) :
    dist p q ≤ max (Real.sqrt (2 * M * eps)) (4 * eps / P) * L ^ 2 * (1 + kb * L) := by
  have hE : (0:ℝ) ≤ max (Real.sqrt (2 * M * eps)) (4 * eps / P) :=
    le_max_of_le_left (Real.sqrt_nonneg _)
  exact MarkedSpace.dist_le_of_curvature_close hc hp hq hLp hLq hevp hevq hΘ1 hΘ2 hF0 hΘ0
    hE (abs_sub_le_of_periodic hP hM hp1 hp2 h1 h2 hb1 hb2 hint) hkb

end CurvatureStabilityL1
