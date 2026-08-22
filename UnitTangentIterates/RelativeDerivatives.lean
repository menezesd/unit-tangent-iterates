import Mathlib

/-!
# Relative derivative bounds along an autonomous flow

In the lemma *Hairpin pulse estimates* of the paper *A Noncircular Oval with
Convex Unit-Tangent Iterates* one needs the **relative derivative bounds**

```
  |K_*^{(j)}(u)| ≤ C_j K_*(u),      |y^{(j)}(s)| ≤ D_j y(s)
```

for the curvature `K_*` of the hairpin in its own arclength and for the
steering pulse `y = sin δ` in front arclength.  The paper proves them by an
induction using Faà di Bruno's formula together with a bounded-shift Harnack
inequality.

This file proves a clean general statement which yields both.  The point is
that in each case the quantity in question is a *smooth function of the state
of an autonomous one-dimensional flow*: if

```
  θ' = G ∘ θ        and       q = G ∘ θ,
```

with `G` smooth, then every derivative of `q` is again a function of the state,

```
  q^{(j)}(u) = G(θ(u)) · L_j(θ(u)),
```

where the coefficients `L_j` are obtained from `L_0 = 1` by the recursion
`L_{j+1} = (G · L_j)'`; the factor `G(θ(u)) = q(u)` is present in *every* term,
which is exactly the relative bound.  Bounding `L_j` on a compact set
containing the range of `θ` gives

```
  |q^{(j)}(u)| ≤ C_j q(u).
```

Main results:

* `RelativeDerivatives.coeff` : the coefficient functions `L_j`;
* `RelativeDerivatives.iteratedDeriv_flow` : `q^{(j)} = (G · L_j) ∘ θ`;
* `RelativeDerivatives.abs_iteratedDeriv_le` : the relative bound
  `|q^{(j)}| ≤ C_j q` with a constant uniform in the parameter, for a flow with
  relatively compact range along which `G ≥ 0`.
-/

noncomputable section

open Set
open scoped ContDiff

namespace RelativeDerivatives

variable {G : ℝ → ℝ}

/-- The coefficient functions of the relative-derivative expansion: `L 0 = 1`
and `L (j+1) = (G · L j)'`.  They satisfy `(G ∘ θ)^{(j)} = (G · L j) ∘ θ` for
any solution of `θ' = G ∘ θ`. -/
def coeff (G : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => fun _ => 1
  | j + 1 => deriv (fun t => G t * coeff G j t)

@[simp] theorem coeff_zero : coeff G 0 = fun _ => 1 := rfl

theorem coeff_succ (j : ℕ) : coeff G (j + 1) = deriv (fun t => G t * coeff G j t) := rfl

/-- Each coefficient function is smooth when `G` is. -/
theorem contDiff_coeff (hG : ContDiff ℝ ∞ G) : ∀ j, ContDiff ℝ ∞ (coeff G j)
  | 0 => contDiff_const
  | j + 1 => by
      have h : ContDiff ℝ ∞ (fun t => G t * coeff G j t) := hG.mul (contDiff_coeff hG j)
      rw [coeff_succ]
      exact (contDiff_infty_iff_deriv.1 h).2

/-- The derivative of the product `G · L j` is `L (j+1)`. -/
theorem hasDerivAt_coeff (hG : ContDiff ℝ ∞ G) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun x => G x * coeff G j x) (coeff G (j + 1) t) t := by
  have h : ContDiff ℝ ∞ (fun x => G x * coeff G j x) := hG.mul (contDiff_coeff hG j)
  have hd : DifferentiableAt ℝ (fun x => G x * coeff G j x) t :=
    (contDiff_infty_iff_deriv.1 h).1 t
  simpa [coeff_succ] using hd.hasDerivAt

/-- **The derivatives of a quantity carried by an autonomous flow.**  If
`θ' = G ∘ θ` then the `j`-th derivative of `q = G ∘ θ` is `(G · L_j) ∘ θ`. -/
theorem iteratedDeriv_flow (hG : ContDiff ℝ ∞ G) {θ : ℝ → ℝ}
    (hθ : ∀ u, HasDerivAt θ (G (θ u)) u) (j : ℕ) :
    iteratedDeriv j (fun u => G (θ u)) = fun u => G (θ u) * coeff G j (θ u) := by
  induction j with
  | zero => funext u; simp [iteratedDeriv_zero]
  | succ j ih =>
      have hstep : ∀ u, HasDerivAt (fun u => G (θ u) * coeff G j (θ u))
          (G (θ u) * coeff G (j + 1) (θ u)) u := by
        intro u
        have h := (hasDerivAt_coeff hG j (θ u)).comp u (hθ u)
        simpa [Function.comp, mul_comm] using h
      funext u
      rw [iteratedDeriv_succ, ih]
      exact (hstep u).deriv

/-- **Relative derivative bounds along an autonomous flow.**  If `θ' = G ∘ θ`
with `G` smooth, the range of `θ` is contained in a compact interval and
`q = G ∘ θ` is nonnegative, then for every order `j` there is a constant `C_j`,
independent of the point, with `|q^{(j)}| ≤ C_j q`. -/
theorem abs_iteratedDeriv_le (hG : ContDiff ℝ ∞ G) {θ : ℝ → ℝ}
    (hθ : ∀ u, HasDerivAt θ (G (θ u)) u) {a b : ℝ} (hrange : ∀ u, θ u ∈ Icc a b)
    (hpos : ∀ u, 0 ≤ G (θ u)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |iteratedDeriv j (fun u => G (θ u)) u| ≤ C * G (θ u) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((contDiff_coeff hG j).continuous.continuousOn)
  refine ⟨|C|, abs_nonneg C, fun u => ?_⟩
  rw [iteratedDeriv_flow hG hθ j]
  have h1 : |coeff G j (θ u)| ≤ |C| := le_trans (hC _ (hrange u)) (le_abs_self C)
  calc |G (θ u) * coeff G j (θ u)| = G (θ u) * |coeff G j (θ u)| := by
        rw [abs_mul, abs_of_nonneg (hpos u)]
    _ ≤ G (θ u) * |C| := by
        exact mul_le_mul_of_nonneg_left h1 (hpos u)
    _ = |C| * G (θ u) := by ring

/-- **The state functions of the expansion differentiate into one another.**
Along the flow, `(G · L_j) ∘ θ` has derivative `(G · L_{j+1}) ∘ θ`; this is the
inductive step of `iteratedDeriv_flow`, stated for use on its own. -/
theorem hasDerivAt_state (hG : ContDiff ℝ ∞ G) {θ : ℝ → ℝ}
    (hθ : ∀ u, HasDerivAt θ (G (θ u)) u) (j : ℕ) (u : ℝ) :
    HasDerivAt (fun v => G (θ v) * coeff G j (θ v)) (G (θ u) * coeff G (j + 1) (θ u)) u := by
  have h := (hasDerivAt_coeff hG j (θ u)).comp u (hθ u)
  simpa [Function.comp, mul_comm] using h

end RelativeDerivatives
