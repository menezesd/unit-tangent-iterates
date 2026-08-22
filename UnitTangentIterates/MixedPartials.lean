import Mathlib

/-!
# Clairaut's theorem for a function of two real variables

`deriv_partial_comm` is the classical symmetry of the mixed partial
derivatives, in the concrete form needed for a family of curves
`R : ℝ → ℝ → ℂ` depending on a path parameter and a curve parameter:

```
  ∂_a ∂_x R = ∂_x ∂_a R .
```

It is deduced from Mathlib's `second_derivative_symmetric` by writing each
partial derivative as the total derivative of the uncurried function evaluated
on a coordinate vector.
-/

noncomputable section

open Function

namespace MixedPartials

/-- **Clairaut's theorem.**  For a `C²` function of two real variables the
mixed partial derivatives agree. -/
theorem deriv_partial_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → ℝ → F} (hf : ContDiff ℝ 2 (uncurry f)) (a x : ℝ) :
    deriv (fun a' => deriv (fun x' => f a' x') x) a
      = deriv (fun x' => deriv (fun a' => f a' x') a) x := by
  set g : ℝ × ℝ → F := uncurry f with hgdef
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hf.fderiv_right le_rfl
  have hgd : ∀ p : ℝ × ℝ, HasFDerivAt g (fderiv ℝ g p) p := fun p =>
    (hf.differentiable (by norm_num) p).hasFDerivAt
  have hg2 : ∀ p : ℝ × ℝ, HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) p) p := fun p =>
    (hg1.differentiable (by norm_num) p).hasFDerivAt
  have hpx : ∀ a' : ℝ, HasDerivAt (fun x' => f a' x') (fderiv ℝ g (a', x) ((0, 1) : ℝ × ℝ)) x := by
    intro a'
    exact (hgd (a', x)).comp_hasDerivAt x ((hasDerivAt_const x a').prodMk (hasDerivAt_id x))
  have hpa : ∀ x' : ℝ, HasDerivAt (fun a' => f a' x') (fderiv ℝ g (a, x') ((1, 0) : ℝ × ℝ)) a := by
    intro x'
    exact (hgd (a, x')).comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a x'))
  have hLfun : (fun a' => deriv (fun x' => f a' x') x)
      = fun a' => fderiv ℝ g (a', x) ((0, 1) : ℝ × ℝ) := by
    funext a'; exact (hpx a').deriv
  have hRfun : (fun x' => deriv (fun a' => f a' x') a)
      = fun x' => fderiv ℝ g (a, x') ((1, 0) : ℝ × ℝ) := by
    funext x'; exact (hpa x').deriv
  have hL : HasDerivAt (fun a' => fderiv ℝ g (a', x) ((0, 1) : ℝ × ℝ))
      ((fderiv ℝ (fderiv ℝ g) (a, x) ((1, 0) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ)) a := by
    have h3 : HasDerivAt (fun a' : ℝ => fderiv ℝ g (a', x))
        (fderiv ℝ (fderiv ℝ g) (a, x) ((1, 0) : ℝ × ℝ)) a :=
      (hg2 (a, x)).comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a x))
    exact (ContinuousLinearMap.apply ℝ F ((0, 1) : ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt a h3
  have hR : HasDerivAt (fun x' => fderiv ℝ g (a, x') ((1, 0) : ℝ × ℝ))
      ((fderiv ℝ (fderiv ℝ g) (a, x) ((0, 1) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ)) x := by
    have h3 : HasDerivAt (fun x' : ℝ => fderiv ℝ g (a, x'))
        (fderiv ℝ (fderiv ℝ g) (a, x) ((0, 1) : ℝ × ℝ)) x :=
      (hg2 (a, x)).comp_hasDerivAt x ((hasDerivAt_const x a).prodMk (hasDerivAt_id x))
    exact (ContinuousLinearMap.apply ℝ F ((1, 0) : ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt x h3
  rw [hLfun, hRfun, hL.deriv, hR.deriv]
  exact second_derivative_symmetric hgd (hg2 (a, x)) _ _

end MixedPartials
