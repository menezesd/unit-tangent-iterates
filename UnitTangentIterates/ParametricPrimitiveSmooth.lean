import Mathlib
import UnitTangentIterates.ParametricPrimitive
import UnitTangentIterates.PathDataTaylorBounds

/-!
# The primitive of a `Cⁿ` family is a `Cⁿ` family

`ParametricPrimitive.contDiff_one_primitive` proves that the primitive
`A(t,s) = ∫₀ˢ g(t,u) du` of a jointly `C¹` family is jointly `C¹`.  The
regularity hypotheses of the path-distance bounds of this project are of order
four, so the same statement is needed to all orders.

The two ingredients are:

* `contDiff_succ_of_partials` — a function of two variables whose two partial
  derivatives exist everywhere and are jointly `Cⁿ` is jointly `C^{n+1}`
  (the differential being the map `(u,v) ↦ u ∂_t f + v ∂_x f` of
  `JointC1.partialCLM`, which depends on the point only through the two
  partials);
* the induction itself: `∂_s A = g` and `∂_t A(t,s) = ∫₀ˢ ∂_t g(t,u) du`
  (differentiation under the integral sign,
  `ParametricPrimitive.hasDerivAt_primitive_param`), and the latter is the
  primitive of a family one degree less smooth.

Main result: `contDiff_primitive`.
-/

noncomputable section

open Function Set MeasureTheory

namespace ParametricPrimitiveSmooth

open JointC1 PathDataTaylorBounds

/-- **Joint `C^{n+1}` regularity from `Cⁿ` partial derivatives.**  If the two
partial derivatives of `f : ℝ → ℝ → ℝ` exist everywhere and are jointly `Cⁿ`,
then `f` is jointly `C^{n+1}`. -/
theorem contDiff_succ_of_partials {f f1 f2 : ℝ → ℝ → ℝ} {n : ℕ}
    (h1 : ∀ t x, HasDerivAt (fun r => f r x) (f1 t x) t)
    (h2 : ∀ t x, HasDerivAt (f t) (f2 t x) x)
    (hc1 : ContDiff ℝ (n : ℕ) (uncurry f1)) (hc2 : ContDiff ℝ (n : ℕ) (uncurry f2)) :
    ContDiff ℝ ((n : ℕ) + 1) (uncurry f) := by
  have hfd : ∀ p : ℝ × ℝ, HasFDerivAt (uncurry f)
      (partialCLM (f1 p.1 p.2) (f2 p.1 p.2)) p := by
    rintro ⟨t, x⟩
    exact hasFDerivAt_of_continuous_partials h1 h2 hc1.continuous hc2.continuous t x
  have hdiff : Differentiable ℝ (uncurry f) := fun p => (hfd p).differentiableAt
  have hfderiv : fderiv ℝ (uncurry f)
      = fun p : ℝ × ℝ => partialCLM (f1 p.1 p.2) (f2 p.1 p.2) :=
    funext fun p => (hfd p).fderiv
  refine contDiff_succ_iff_fderiv.mpr ⟨hdiff, by simp, ?_⟩
  rw [hfderiv]
  have e : (fun p : ℝ × ℝ => partialCLM (f1 p.1 p.2) (f2 p.1 p.2))
      = fun p : ℝ × ℝ => (uncurry f1 p) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
          + (uncurry f2 p) • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    funext p
    refine ContinuousLinearMap.ext fun q => ?_
    simp [partialCLM, uncurry]
    ring
  rw [e]
  exact (hc1.smul contDiff_const).add (hc2.smul contDiff_const)

/-- **The primitive of a `C^{n+1}` family is a `C^{n+1}` family.**  If `g` is
jointly `C^{n+1}` then so is `A(t,s) = ∫₀ˢ g(t,u) du`. -/
theorem contDiff_primitive : ∀ (n : ℕ) {g : ℝ → ℝ → ℝ},
    ContDiff ℝ ((n : ℕ) + 1) (uncurry g) →
    ContDiff ℝ ((n : ℕ) + 1) (uncurry fun t s => ∫ u in (0:ℝ)..s, g t u) := by
  intro n
  induction n with
  | zero =>
    intro g hg
    have hg1 : ContDiff ℝ 1 (uncurry g) := by
      have : ContDiff ℝ ((0 : ℕ) + 1 : ℕ) (uncurry g) := hg
      simpa using this
    have hgt : ContDiff ℝ ((0 : ℕ)) (uncurry (partialT g)) :=
      contDiff_partialT (n := 0) (by simpa using hg1)
    have := ParametricPrimitive.contDiff_one_primitive (g := g) (gt := partialT g)
      hg1.continuous (fun t u => hasDerivAt_partialT hg1 t u) hgt.continuous
    simpa using this
  | succ n ih =>
    intro g hg
    have hgS : ContDiff ℝ (((n : ℕ) + 1 : ℕ) + 1) (uncurry g) := by
      have : ContDiff ℝ (((n + 1 : ℕ) : ℕ) + 1) (uncurry g) := hg
      simpa using this
    have hg1 : ContDiff ℝ 1 (uncurry g) := by
      refine hgS.of_le ?_
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have hgtC : ContDiff ℝ ((n : ℕ) + 1) (uncurry (partialT g)) :=
      contDiff_partialT (n := (n : ℕ) + 1) (by exact_mod_cast hgS)
    have hprim : ContDiff ℝ ((n : ℕ) + 1)
        (uncurry fun t s => ∫ u in (0:ℝ)..s, partialT g t u) := ih hgtC
    have hgn : ContDiff ℝ ((n : ℕ) + 1) (uncurry g) := by
      refine hgS.of_le ?_
      exact_mod_cast Nat.le_succ ((n : ℕ) + 1)
    have hpartial1 : ∀ t s, HasDerivAt (fun r => ∫ u in (0:ℝ)..s, g r u)
        (∫ u in (0:ℝ)..s, partialT g t u) t := fun t s =>
      ParametricPrimitive.hasDerivAt_primitive_param hg1.continuous
        (fun t u => hasDerivAt_partialT hg1 t u)
        (contDiff_partialT (n := 0) (by simpa using hg1)).continuous t s
    have hpartial2 : ∀ t s, HasDerivAt (fun y => ∫ u in (0:ℝ)..y, g t u) (g t s) s :=
      fun t s => ParametricPrimitive.hasDerivAt_primitive_space hg1.continuous t s
    have := contDiff_succ_of_partials (n := (n : ℕ) + 1)
      (f := fun t s => ∫ u in (0:ℝ)..s, g t u)
      (f1 := fun t s => ∫ u in (0:ℝ)..s, partialT g t u) (f2 := g)
      hpartial1 hpartial2 hprim hgn
    exact_mod_cast this

end ParametricPrimitiveSmooth
