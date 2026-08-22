import Mathlib
import UnitTangentIterates.PeriodicGreen

/-!
# The periodic Green operator depends continuously on its data

`PeriodicGreen.lean` builds, for a positive `ℓ`-periodic coefficient `a`, the
inverse

```
  (𝒢 f)(x) = (1 - e^{-A(ℓ)})⁻¹ ∫_{x-ℓ}^{x} e^{-(A(x)-A(t))} f(t) dt ,
            A(x) = ∫₀ˣ a ,
```

of `∂ₓ + a` on the circle of length `ℓ`.  In the paper *A Noncircular Oval with
Convex Unit-Tangent Iterates* this operator produces the derivative of the
selected steering angle with respect to the path parameter (the lemma *Smooth
dependence of the selected rear*), so what is needed of it, in order to know
that the selected steering angle is jointly regular along a path of fronts, is
that it moves continuously with its data.

This file proves exactly that: for a **family** `A(a, ·)` of coefficients and a
family `F(a, ·)` of right-hand sides, both jointly continuous, the map

```
  (a, x) ↦ (𝒢_{A(a,·)} F(a,·))(x)
```

is jointly continuous.  The proof rewrites the operator in the closed form

```
  (𝒢 f)(x) = (1 - e^{-A(ℓ)})⁻¹ e^{-A(x)} (B(x) - B(x-ℓ)) ,
            B(y) = ∫₀^y e^{A(t)} f(t) dt ,
```

and uses continuity of a parametric interval integral with a moving endpoint
for the two parametric primitives `A` and `B`.

Main results:

* `continuous_prim_param` — `(a, x) ↦ ∫₀ˣ A(a, ·)` is jointly continuous;
* `continuous_periodicGreen_param_var` — joint continuity of the Green
  operator, the length of the circle being allowed to move continuously with
  the parameter, as it does along a path of fronts of varying perimeter;
* `continuous_periodicGreen_param` — the same for a fixed period;
* `periodicGreen_eq_bigB` — the closed form the proof rests on, also the entry
  point of the higher-order regularity of `PeriodicGreenSmooth.lean`.
-/

noncomputable section

open Function

namespace PeriodicGreenJoint

open PeriodicGreen

variable {A F : ℝ → ℝ → ℝ} {l : ℝ}

/-- The primitive of a jointly continuous family of coefficients is jointly
continuous. -/
theorem continuous_prim_param (hA : Continuous (uncurry A)) :
    Continuous fun p : ℝ × ℝ => prim (A p.1) p.2 := by
  have h : Continuous (uncurry fun (p : ℝ × ℝ) (t : ℝ) => A p.1 t) := by
    have : Continuous fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2) :=
      (continuous_fst.comp continuous_fst).prodMk continuous_snd
    exact hA.comp this
  simpa [prim] using
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (0 : ℝ)) h continuous_snd

/-- The weighted primitive `B(a, y) = ∫₀^y e^{A(a,t)} F(a,t) dt`. -/
def bigB (A F : ℝ → ℝ → ℝ) (a y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..y, Real.exp (prim (A a) t) * F a t

theorem continuous_bigB (hA : Continuous (uncurry A)) (hF : Continuous (uncurry F)) :
    Continuous fun p : ℝ × ℝ => bigB A F p.1 p.2 := by
  have hprim : Continuous fun q : (ℝ × ℝ) × ℝ => prim (A q.1.1) q.2 := by
    have h : Continuous fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2) : ℝ × ℝ) :=
      (continuous_fst.comp continuous_fst).prodMk continuous_snd
    exact (continuous_prim_param hA).comp h
  have hFq : Continuous fun q : (ℝ × ℝ) × ℝ => F q.1.1 q.2 := by
    have h : Continuous fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2) : ℝ × ℝ) :=
      (continuous_fst.comp continuous_fst).prodMk continuous_snd
    exact hF.comp h
  have h : Continuous (uncurry fun (p : ℝ × ℝ) (t : ℝ) =>
      Real.exp (prim (A p.1) t) * F p.1 t) :=
    (Real.continuous_exp.comp hprim).mul hFq
  simpa [bigB] using
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (0 : ℝ)) h continuous_snd

/-- The closed form of the Green operator in terms of the weighted
primitive. -/
theorem periodicGreen_eq_bigB (ha : Continuous (A a)) (hf : Continuous (F a)) (x : ℝ) :
    periodicGreen (A a) l (F a) x
      = (1 - Real.exp (-prim (A a) l))⁻¹ * Real.exp (-prim (A a) x) *
          (bigB A F a x - bigB A F a (x - l)) := by
  have hcont : Continuous fun t : ℝ => Real.exp (prim (A a) t) * F a t :=
    (Real.continuous_exp.comp (continuous_prim ha)).mul hf
  have hsplit : (∫ t in (x - l)..x, Real.exp (prim (A a) t) * F a t)
      = bigB A F a x - bigB A F a (x - l) := by
    simp only [bigB]
    rw [← intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  have hrw : (∫ t in (x - l)..x, Real.exp (-(prim (A a) x - prim (A a) t)) * F a t)
      = Real.exp (-prim (A a) x) * ∫ t in (x - l)..x, Real.exp (prim (A a) t) * F a t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [periodicGreen, hrw, hsplit]
  ring

/-- **The periodic Green operator is jointly continuous in its data**, for a
period which moves continuously with the parameter.  For a jointly continuous
family `A` of coefficients whose primitive over one period is positive, and a
jointly continuous family `F` of right-hand sides, the solutions
`(𝒢_{A(a,·)}F(a,·))(x)` depend continuously on the pair `(a, x)`. -/
theorem continuous_periodicGreen_param_var {L : ℝ → ℝ} (hA : Continuous (uncurry A))
    (hF : Continuous (uncurry F)) (hL : Continuous L) (hApos : ∀ a, 0 < prim (A a) (L a)) :
    Continuous fun p : ℝ × ℝ => periodicGreen (A p.1) (L p.1) (F p.1) p.2 := by
  have hAslice : ∀ a, Continuous (A a) := fun a =>
    hA.comp (continuous_const.prodMk continuous_id)
  have hFslice : ∀ a, Continuous (F a) := fun a =>
    hF.comp (continuous_const.prodMk continuous_id)
  have heq : (fun p : ℝ × ℝ => periodicGreen (A p.1) (L p.1) (F p.1) p.2)
      = fun p : ℝ × ℝ => (1 - Real.exp (-prim (A p.1) (L p.1)))⁻¹ *
          Real.exp (-prim (A p.1) p.2) *
          (bigB A F p.1 p.2 - bigB A F p.1 (p.2 - L p.1)) := by
    funext p
    exact periodicGreen_eq_bigB (hAslice p.1) (hFslice p.1) p.2
  rw [heq]
  -- the normalizing constant
  have hprimx : Continuous fun p : ℝ × ℝ => prim (A p.1) p.2 := continuous_prim_param hA
  have hpriml : Continuous fun a : ℝ => prim (A a) (L a) := by
    have h : Continuous fun a : ℝ => ((a, L a) : ℝ × ℝ) := continuous_id.prodMk hL
    exact hprimx.comp h
  have hconst : Continuous fun p : ℝ × ℝ => (1 - Real.exp (-prim (A p.1) (L p.1)))⁻¹ := by
    refine Continuous.inv₀ ?_ ?_
    · exact (continuous_const.sub (Real.continuous_exp.comp (hpriml.neg))).comp continuous_fst
    · intro p
      exact ne_of_gt (one_sub_exp_pos (hApos p.1))
  have hB1 : Continuous fun p : ℝ × ℝ => bigB A F p.1 p.2 := continuous_bigB hA hF
  have hB2 : Continuous fun p : ℝ × ℝ => bigB A F p.1 (p.2 - L p.1) := by
    have h : Continuous fun p : ℝ × ℝ => ((p.1, p.2 - L p.1) : ℝ × ℝ) :=
      continuous_fst.prodMk (continuous_snd.sub (hL.comp continuous_fst))
    exact hB1.comp h
  exact (hconst.mul (Real.continuous_exp.comp hprimx.neg)).mul (hB1.sub hB2)

/-- **The periodic Green operator is jointly continuous in its data**, for a
fixed period. -/
theorem continuous_periodicGreen_param (hA : Continuous (uncurry A))
    (hF : Continuous (uncurry F)) (hApos : ∀ a, 0 < prim (A a) l) :
    Continuous fun p : ℝ × ℝ => periodicGreen (A p.1) l (F p.1) p.2 :=
  continuous_periodicGreen_param_var (L := fun _ => l) hA hF continuous_const hApos

end PeriodicGreenJoint
