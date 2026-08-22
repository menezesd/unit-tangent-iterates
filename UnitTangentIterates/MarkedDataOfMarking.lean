import Mathlib
import UnitTangentIterates.MarkedSpace

/-!
# A marked curve read in a marking is again a datum of the space

The comparison estimates of the selected inverse speak of the curve `q'` that
reads a member `b` of the tube in a marking `ψ`, that is, of the datum whose
position is `u ↦ b(ψ(u))`.  For that to be an element of the carrier
`MarkedSpace.Data = (ℝ →ᵇ ℂ)³` its three components have to be bounded and
continuous.

This file builds it: if the marking is twice differentiable with continuous and
bounded derivatives `ψ'`, `ψ''`, the three components

`b∘ψ` ,  `ψ'·(b'∘ψ)` ,  `ψ''·(b'∘ψ) + (ψ')²·(b''∘ψ)`

are bounded by `‖b‖`, `A₁‖b'‖` and `A₂‖b'‖ + A₁²‖b''‖`, and the second and third
are the first two derivatives of the first.

Main result: `exists_data_of_marking`.
-/

noncomputable section

open Function MarkedSpace

namespace MarkedDataOfMarking

/-- **The datum of a marked curve read in a marking.**  For a `C²` marking with
bounded derivatives the reparametrized curve, its velocity and its acceleration
are bounded continuous, so they form an element of `Data`, and the second and
third components are the derivatives of the first two. -/
theorem exists_data_of_marking {b : Data} {psi psi1 psi2 : ℝ → ℝ} {A1 A2 : ℝ}
    (hb1 : ∀ u, HasDerivAt (⇑b.1) (b.2.1 u) u) (hb2 : ∀ u, HasDerivAt (⇑b.2.1) (b.2.2 u) u)
    (hpsi1 : ∀ u, HasDerivAt psi (psi1 u) u) (hpsi2 : ∀ u, HasDerivAt psi1 (psi2 u) u)
    (hc1 : Continuous psi1) (hc2 : Continuous psi2)
    (hA1 : ∀ u, |psi1 u| ≤ A1) (hA2 : ∀ u, |psi2 u| ≤ A2) :
    ∃ q : Data, (∀ u, q.1 u = b.1 (psi u)) ∧
      (∀ u, q.2.1 u = (psi1 u : ℂ) * b.2.1 (psi u)) ∧
      (∀ u, q.2.2 u = (psi2 u : ℂ) * b.2.1 (psi u)
        + ((psi1 u : ℂ)) ^ 2 * b.2.2 (psi u)) ∧
      (∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u) ∧ (∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u) := by
  have hpsic : Continuous psi :=
    continuous_iff_continuousAt.2 fun u => (hpsi1 u).continuousAt
  have hA1nn : 0 ≤ A1 := le_trans (abs_nonneg _) (hA1 0)
  -- the three components
  have hcont0 : Continuous fun u => b.1 (psi u) := b.1.continuous.comp hpsic
  have hcont1 : Continuous fun u => (psi1 u : ℂ) * b.2.1 (psi u) :=
    (Complex.continuous_ofReal.comp hc1).mul (b.2.1.continuous.comp hpsic)
  have hcont2 : Continuous fun u => (psi2 u : ℂ) * b.2.1 (psi u)
      + ((psi1 u : ℂ)) ^ 2 * b.2.2 (psi u) :=
    ((Complex.continuous_ofReal.comp hc2).mul (b.2.1.continuous.comp hpsic)).add
      (((Complex.continuous_ofReal.comp hc1).pow 2).mul (b.2.2.continuous.comp hpsic))
  have hbd0 : ∀ u, ‖b.1 (psi u)‖ ≤ ‖b.1‖ := fun u => b.1.norm_coe_le_norm _
  have hbd1 : ∀ u, ‖(psi1 u : ℂ) * b.2.1 (psi u)‖ ≤ A1 * ‖b.2.1‖ := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hA1 u) (b.2.1.norm_coe_le_norm _) (norm_nonneg _) hA1nn
  have hbd2 : ∀ u, ‖(psi2 u : ℂ) * b.2.1 (psi u) + ((psi1 u : ℂ)) ^ 2 * b.2.2 (psi u)‖
      ≤ A2 * ‖b.2.1‖ + A1 ^ 2 * ‖b.2.2‖ := by
    intro u
    have hA2nn : 0 ≤ A2 := le_trans (abs_nonneg _) (hA2 0)
    have h1 : ‖(psi2 u : ℂ) * b.2.1 (psi u)‖ ≤ A2 * ‖b.2.1‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hA2 u) (b.2.1.norm_coe_le_norm _) (norm_nonneg _) hA2nn
    have h2 : ‖((psi1 u : ℂ)) ^ 2 * b.2.2 (psi u)‖ ≤ A1 ^ 2 * ‖b.2.2‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hA1 u) 2)
        (b.2.2.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    exact (norm_add_le _ _).trans (by linarith)
  refine ⟨(BoundedContinuousFunction.ofNormedAddCommGroup _ hcont0 ‖b.1‖ hbd0,
    BoundedContinuousFunction.ofNormedAddCommGroup _ hcont1 (A1 * ‖b.2.1‖) hbd1,
    BoundedContinuousFunction.ofNormedAddCommGroup _ hcont2
      (A2 * ‖b.2.1‖ + A1 ^ 2 * ‖b.2.2‖) hbd2), fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun u => ?_, fun u => ?_⟩
  · have h := (hb1 (psi u)).scomp u (hpsi1 u)
    simpa [Complex.real_smul, Function.comp_def] using h
  · have h1 : HasDerivAt (fun u' => b.2.1 (psi u')) ((psi1 u : ℂ) * b.2.2 (psi u)) u := by
      have h := (hb2 (psi u)).scomp u (hpsi1 u)
      simpa [Complex.real_smul, Function.comp_def] using h
    have h2 : HasDerivAt (fun u' => (psi1 u' : ℂ)) ((psi2 u : ℂ)) u := by
      simpa using ((hpsi2 u).ofReal_comp)
    have h := h2.mul h1
    simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    refine h.congr_deriv ?_
    ring

end MarkedDataOfMarking
