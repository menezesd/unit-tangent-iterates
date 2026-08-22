import Mathlib
import UnitTangentIterates.CurveDistance
import UnitTangentIterates.UnitTangent
import UnitTangentIterates.MainThresholds

/-!
# The closing assembly of the main theorem, as a conditional statement

The main theorem of *A Noncircular Oval with Convex Unit-Tangent Iterates*
asserts that there is a **noncircular oval** `Γ₀` such that `𝒯ⁿΓ₀` is an oval
for every `n ≥ 0`.  Its proof is a long construction whose analytic core is
distributed over the rest of this project; the final section assembles the
pieces as follows.  For every large initial separation `H₀` the shadowing
theorem produces an exact orbit `𝒯Xₙ = X_{n+1}` of ovals whose initial member
stays within distance `C_sh r(H₀)` of the model `Q₀ = F_{H₀}`, with
`Per(X₀) ≥ 2H₀ − C_sh r(H₀)`, while the model has transverse width at most
`C_W`.  Since `r(H₀) → 0` and `2H₀/π → ∞`, one large `H₀` makes `X₀` too thin
to be a circle.

This file formalizes that last assembly, **as a conditional statement**: the
shadowing input is a hypothesis, not a result proved here.  Nothing in this
file (or in this project) should be read as a proof of the main theorem.

Main contents:

* `IsOval` : a smooth embedded closed curve with positive curvature — unit
  speed with tangent angle `θ`, curvature `θ' > 0`, `L`-periodic and injective
  on a period;
* `IsOval.continuous`, `IsOval.exists_period` : the elementary consequences
  used below;
* `main_theorem_of_shadowing` : **given** the shadowing conclusion at every
  large separation, there is an orbit of ovals `𝒯Xₙ = X_{n+1}` whose initial
  member is not a circle.
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

/-- **The closing assembly of the main theorem, conditionally on the shadowing
input.**

Assume that for every initial separation `H₀` above some level `H_sh` the
construction of the paper delivers:

* an orbit `X : ℕ → (ℝ → ℂ)` of ovals with `𝒯Xₙ = X_{n+1}`;
* a closed model curve `Q` of transverse width at most `C_W` in some unit
  direction;
* the shadowing bound `dist (X₀ t) (Q t) ≤ C_sh r(H₀)` with
  `r(H₀) = C_r(1+H₀)²e^{-βH₀}`, and the perimeter bound
  `2H₀ − C_sh r(H₀) ≤ Per(X₀)`.

Then there is an orbit of ovals under the unit-tangent transform whose initial
member is **not** a circle: the width of `X₀` is at most `C_W + 2C_sh r(H₀)`,
whereas a circle of its perimeter would have width at least
`(2H₀ − C_sh r(H₀))/π`, and for `H₀` large the latter exceeds the former.

This is the paper's *Excluding a circle* step; the hypothesis packages the
results that precede it, none of which is proved here.

NOTE (see `UnitTangentIterates/UnitTangentSpeed.lean`).  The orbit condition is
stated here as the identity of *parametrized* curves
`UnitTangent.unitTangentMap (X n) = X (n+1)`.  For a unit-speed curve of
curvature `k` the transform has speed `√(1 + k²) > 1`, so by
`UnitTangentSpeed.not_isOval_unitTangentMap` no oval has an oval as its
unit-tangent image: the combination of `IsOval (X n)` with that identity is
contradictory, and hypotheses of this shape can never be met.  The
geometrically correct statement asks only for equality of the images,
`range (X (n+1)) = range (UnitTangent.unitTangentMap (X n))`, i.e. equality up
to reparametrization; the corrected form of the closing argument is
`MarkedSpace.main_theorem_on_marked_space_range` in
`UnitTangentIterates/MarkedSchemeTheoremRange.lean`.
-/
theorem main_theorem_of_shadowing {Cw Csh Cr beta Hsh : ℝ} (hbeta : 0 < beta)
    (hshadow : ∀ H0 : ℝ, Hsh ≤ H0 →
      ∃ (X : ℕ → ℝ → ℂ) (Q : ℝ → ℂ) (LX LQ : ℝ) (e : ℂ),
        (∀ n, IsOval (X n)) ∧
        (∀ n, UnitTangent.unitTangentMap (X n) = X (n + 1)) ∧
        Periodic (X 0) LX ∧ 0 < LX ∧
        Continuous Q ∧ Periodic Q LQ ∧ 0 < LQ ∧ ‖e‖ = 1 ∧
        Width.width (range Q) e ≤ Cw ∧
        0 ≤ Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta * H0))) ∧
        (∀ t, dist (X 0 t) (Q t) ≤ Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta * H0)))) ∧
        2 * H0 - Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta * H0))) ≤ LX) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ), (∀ n, IsOval (X n)) ∧
      (∀ n, UnitTangent.unitTangentMap (X n) = X (n + 1)) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  -- the shadowing defect tends to zero, so the width gap holds for large `H₀`
  set r : ℝ → ℝ := fun x => Cr * ((1 + x) ^ 2 * Real.exp (-beta * x)) with hr
  have hrzero : Tendsto r atTop (𝓝 0) := by
    have := (MainThresholds.tendsto_tail_zero (beta := beta) hbeta).const_mul Cr
    simpa [hr] using this
  have hgap : ∀ᶠ x in atTop, Cw + 2 * (Csh * r x) < (2 * x - Csh * r x) / Real.pi := by
    have h := MainThresholds.eventually_width_gap (Cw := Cw) (Csh := Csh) hrzero
    filter_upwards [h] with x hx
    calc Cw + 2 * (Csh * r x) = Cw + 2 * Csh * r x := by ring
      _ < (2 * x - Csh * r x) / Real.pi := hx
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hgap
  set H0 : ℝ := max Hsh B with hH0
  obtain ⟨X, Q, LX, LQ, e, hoval, horbit, hXper, hLX, hQc, hQper, hLQ, he, hQw, hd0,
    hdist, hLXge⟩ := hshadow H0 (le_max_left _ _)
  refine ⟨X, LX, hoval, horbit, hLX, hXper, ?_⟩
  exact CurveDistance.not_isCircleOfPerimeter_of_dist_le (H := H0)
    (hoval 0).continuous hXper hLX hQc hQper hLQ he hd0 hdist hQw hLXge
    (hB H0 (le_max_right _ _))

end MainTheoremConditional
