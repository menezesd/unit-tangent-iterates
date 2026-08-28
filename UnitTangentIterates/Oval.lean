import Mathlib
import UnitTangentIterates.UnitTangent

/-!
# The definition of an oval

This file houses the project-wide definition `MainTheoremConditional.IsOval`:
a smooth embedded closed plane curve parametrized by arclength with strictly
positive curvature.  The namespace name `MainTheoremConditional` is retained so
that every qualified reference across the project keeps working; the file
formerly carrying these declarations (`MainTheoremConditional.lean`) also
stated a conditional closing theorem whose orbit condition combined
`IsOval (X n)` with the *parametrized* identity `𝒯(X n) = X (n+1)` — a
contradictory pair of hypotheses (see
`UnitTangentSpeed.not_isOval_unitTangentMap`).  That vacuous statement has been
removed; the corrected image-based form lives in
`MarkedSchemeTheoremRange.main_theorem_on_marked_space_range`.

Main contents:

* `MainTheoremConditional.IsOval` : unit speed with tangent angle `θ`,
  curvature `θ' > 0`, `L`-periodic and injective on a period;
* `MainTheoremConditional.IsOval.continuous`,
  `MainTheoremConditional.IsOval.exists_period` : elementary consequences;
* `MainTheoremConditional.isOval_circleCurve` : circles are ovals.
-/

noncomputable section

open Set Filter Topology Function

namespace MainTheoremConditional

/-- An **oval**: a closed embedded plane curve, parametrized by arclength, with
positive curvature.  Concretely: there are a period `L > 0` and a tangent angle
`θ` with `γ' = e^{iθ}` (unit speed) and `θ' = k > 0` (strict convexity), the
curve being `L`-periodic and injective on one period. -/
def IsOval (γ : ℝ → ℂ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ Periodic γ L ∧ InjOn γ (Ico 0 L) ∧
    ∃ θ : ℝ → ℝ, (∀ s, HasDerivAt γ (Complex.exp (Complex.I * (θ s : ℂ))) s) ∧
      ∃ k : ℝ → ℝ, (∀ s, HasDerivAt θ (k s) s) ∧ ∀ s, 0 < k s

theorem IsOval.continuous {γ : ℝ → ℂ} (h : IsOval γ) : Continuous γ := by
  obtain ⟨_, _, _, _, θ, hθ, _⟩ := h
  exact (Differentiable.continuous (fun s => (hθ s).differentiableAt))

theorem IsOval.exists_period {γ : ℝ → ℂ} (h : IsOval γ) :
    ∃ L : ℝ, 0 < L ∧ Periodic γ L := by
  obtain ⟨L, hL, hper, -⟩ := h
  exact ⟨L, hL, hper⟩


/-- **Circles are ovals.**  A sanity check that the definition above is
satisfied by the standard example: the circle of centre `c` and radius `r > 0`,
parametrized by arclength, is an oval of period `2πr`, tangent angle
`s/r + π/2` and curvature `1/r`. -/
theorem isOval_circleCurve {c : ℂ} {r : ℝ} (hr : 0 < r) :
    IsOval (UnitTangent.circleCurve c r) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr'
  refine ⟨2 * Real.pi * r, by positivity, ?_, ?_, fun s => s / r + Real.pi / 2, ?_,
    fun _ => 1 / r, fun s => ?_, fun _ => by positivity⟩
  · intro s
    simp only [UnitTangent.circleCurve]
    congr 1
    have hcast : ((s + 2 * Real.pi * r : ℝ) : ℂ) / r = (s : ℂ) / r + 2 * Real.pi := by
      push_cast; field_simp
    rw [hcast, mul_add, Complex.exp_add]
    have h2pi : Complex.exp (Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
      rw [show Complex.I * (2 * (Real.pi : ℂ)) = 2 * Real.pi * Complex.I by ring]
      exact Complex.exp_two_pi_mul_I
    rw [h2pi, mul_one]
  · intro s hs t ht hst
    simp only [UnitTangent.circleCurve, add_right_inj] at hst
    have hst' : Complex.exp (Complex.I * ((s : ℂ) / r)) = Complex.exp (Complex.I * ((t : ℂ) / r)) :=
      mul_left_cancel₀ hrC hst
    rw [Complex.exp_eq_exp_iff_exists_int] at hst'
    obtain ⟨n, hn⟩ := hst'
    have hn' : Complex.I * ((s : ℂ) / r)
        = Complex.I * ((t : ℂ) / r + (n : ℂ) * (2 * Real.pi)) := by rw [hn]; ring
    have hc := mul_left_cancel₀ Complex.I_ne_zero hn'
    have hreal : s / r = t / r + (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hc
    have hdiff : s - t = (n : ℝ) * (2 * Real.pi * r) := by
      have h2 : (s / r) * r = (t / r + (n : ℝ) * (2 * Real.pi)) * r := by rw [hreal]
      field_simp at h2
      linarith
    rcases hs with ⟨hs0, hs1⟩
    rcases ht with ⟨ht0, ht1⟩
    have hn0 : n = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hne)
        exact_mod_cast this
      have hpos : 0 < 2 * Real.pi * r := by positivity
      have habs : |s - t| = |(n : ℝ)| * (2 * Real.pi * r) := by
        rw [hdiff, abs_mul, abs_of_pos hpos]
      have hlt : |s - t| < 2 * Real.pi * r := by
        rw [abs_lt]; constructor <;> linarith
      nlinarith
    rw [hn0] at hdiff
    simp at hdiff
    linarith
  · intro s
    have h := UnitTangent.hasDerivAt_circleCurve (c := c) hr' s
    convert h using 1
    rw [show Complex.I * ((s / r + Real.pi / 2 : ℝ) : ℂ)
        = Complex.I * ((s : ℂ) / r) + Complex.I * ((Real.pi : ℂ) / 2) by push_cast; ring,
      Complex.exp_add]
    have hhalf : Complex.exp (Complex.I * ((Real.pi : ℂ) / 2)) = Complex.I := by
      rw [mul_comm, Complex.exp_mul_I]
      simp
    rw [hhalf]
    ring
  · simpa using ((hasDerivAt_id s).div_const r).add_const (Real.pi / 2)

end MainTheoremConditional
