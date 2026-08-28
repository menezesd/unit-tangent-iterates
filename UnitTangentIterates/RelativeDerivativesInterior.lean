import UnitTangentIterates.RelativeDerivatives

/-!
# Relative derivative bounds along a flow, on an open set

`RelativeDerivatives.abs_iteratedDeriv_le` derives `|q^{(j)}| ≤ C_j q` for
`q = G ∘ θ` with `θ' = G(θ)`, by bounding the flow coefficient `L_j` over a
**closed** interval containing the range of `θ` — compactness supplies the
constant.

The hairpin's angle sweeps the *open* interval `(0, π)` and its profile is only
smooth there, so that route is unavailable: the range of `θ` is not contained in
any compact subset of the open interval.  This file redoes the machinery on an
open set, with the bound on `L_j` supplied rather than extracted.

That is the honest shape of the dependency.  The identity
`q^{(j)} = (G · L_j) ∘ θ` is structural and survives unchanged; what compactness
was providing — and what must now come from elsewhere — is exactly a bound on
`L_j` over the open interval.

Main results:

* `contDiffOn_deriv_of_isOpen`;
* `RelativeDerivatives.contDiffOn_coeff`;
* `RelativeDerivatives.iteratedDeriv_flow_of_isOpen`;
* `RelativeDerivatives.abs_iteratedDeriv_le_of_coeff_bound`.
-/

noncomputable section

open Set

open scoped ContDiff

/-- On an open set, `ContDiffOn` passes to the derivative. -/
theorem contDiffOn_deriv_of_isOpen {G : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : ContDiffOn ℝ ∞ G s) : ContDiffOn ℝ ∞ (deriv G) s := by
  have h1 : ContDiffOn ℝ ∞ (derivWithin G s) s :=
    h.derivWithin hs.uniqueDiffOn (by simp)
  refine h1.congr ?_
  intro x hx
  exact (derivWithin_of_isOpen (f := G) hs hx).symm

namespace RelativeDerivatives

variable {G : ℝ → ℝ} {s : Set ℝ}

/-- Each flow coefficient is smooth on the open set where `G` is. -/
theorem contDiffOn_coeff (hs : IsOpen s) (hG : ContDiffOn ℝ ∞ G s) :
    ∀ j, ContDiffOn ℝ ∞ (coeff G j) s
  | 0 => by simpa [coeff_zero] using (contDiffOn_const (c := (1:ℝ)) (s := s))
  | j + 1 => by
      rw [coeff_succ]
      exact contDiffOn_deriv_of_isOpen hs (hG.mul (contDiffOn_coeff hs hG j))

/-- The defining derivative of the flow coefficients, at points of the open
set. -/
theorem hasDerivAt_coeff_of_isOpen (hs : IsOpen s) (hG : ContDiffOn ℝ ∞ G s)
    (j : ℕ) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (fun t => G t * coeff G j t) (coeff G (j + 1) t) t := by
  have hGd : DifferentiableAt ℝ G t :=
    (hG.contDiffAt (hs.mem_nhds ht)).differentiableAt (by norm_num)
  have hCd : DifferentiableAt ℝ (coeff G j) t :=
    ((contDiffOn_coeff hs hG j).contDiffAt (hs.mem_nhds ht)).differentiableAt
      (by norm_num)
  have hd : DifferentiableAt ℝ (fun t => G t * coeff G j t) t := hGd.mul hCd
  rw [coeff_succ]
  exact hd.hasDerivAt

/-- **The derivatives of a quantity carried by an autonomous flow, on an open
set.**  This is `iteratedDeriv_flow` with global smoothness of `G` replaced by
smoothness on an open set that the flow never leaves. -/
theorem iteratedDeriv_flow_of_isOpen (hs : IsOpen s) (hG : ContDiffOn ℝ ∞ G s)
    {θ : ℝ → ℝ} (hrange : ∀ u, θ u ∈ s)
    (hθ : ∀ u, HasDerivAt θ (G (θ u)) u) (j : ℕ) :
    iteratedDeriv j (fun u => G (θ u)) = fun u => G (θ u) * coeff G j (θ u) := by
  induction j with
  | zero => funext u; simp [iteratedDeriv_zero]
  | succ j ih =>
      have hstep : ∀ u, HasDerivAt (fun u => G (θ u) * coeff G j (θ u))
          (G (θ u) * coeff G (j + 1) (θ u)) u := by
        intro u
        have h := (hasDerivAt_coeff_of_isOpen hs hG j (hrange u)).comp u (hθ u)
        simpa [Function.comp, mul_comm] using h
      funext u
      rw [iteratedDeriv_succ, ih]
      exact (hstep u).deriv

/-- **Relative derivative bounds along a flow, from a bound on the flow
coefficient.**  This is `abs_iteratedDeriv_le` with the compactness extraction
replaced by the hypothesis it was producing. -/
theorem abs_iteratedDeriv_le_of_coeff_bound (hs : IsOpen s)
    (hG : ContDiffOn ℝ ∞ G s) {θ : ℝ → ℝ} (hrange : ∀ u, θ u ∈ s)
    (hθ : ∀ u, HasDerivAt θ (G (θ u)) u) (hpos : ∀ u, 0 ≤ G (θ u))
    {j : ℕ} {D : ℝ} (hbd : ∀ t ∈ s, |coeff G j t| ≤ D) :
    ∀ u, |iteratedDeriv j (fun u => G (θ u)) u| ≤ D * G (θ u) := by
  intro u
  rw [iteratedDeriv_flow_of_isOpen hs hG hrange hθ j, abs_mul,
    abs_of_nonneg (hpos u), mul_comm D]
  exact mul_le_mul_of_nonneg_left (hbd _ (hrange u)) (hpos u)

end RelativeDerivatives
