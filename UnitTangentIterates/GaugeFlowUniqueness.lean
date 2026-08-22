import Mathlib
import UnitTangentIterates.GlobalODE

/-!
# Uniqueness of the gauge marking

The gauge marking of a moving family of curves carried in its own arclength is
the flow of (minus) the tangential component `ξ` of the motion: the marking
`Φ` solves

```
  ∂_t Φ(t, u) = −ξ(t, Φ(t, u)) ,     Φ(0, u) = ℓ·u .
```

Two constructions in this project produce such a marking — the assembly of the
path-distance bound of the selected rears and the assembly of the comparison
path of the `C²` estimate — and to combine them the two markings have to be
identified.  They are: the field is globally Lipschitz in the arclength (its
space derivative is bounded), so Grönwall's inequality forces two flow lines
with the same initial condition to coincide.

Main results: `flow_unique_of_lipschitz`, `flow_unique_of_deriv_bound`.
-/

noncomputable section

open Set Function

namespace GaugeFlowUniqueness

/-- **Uniqueness of the flow of a globally Lipschitz scalar field.**  Two
families of flow lines of the same field which agree at time `0` agree at every
time. -/
theorem flow_unique_of_lipschitz {h : ℝ → ℝ → ℝ} {K : NNReal}
    (hlip : ∀ t, LipschitzWith K (h t)) {Phi Psi : ℝ → ℝ → ℝ}
    (hPhi : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPsi : ∀ u t, HasDerivAt (fun r => Psi r u) (h t (Psi t u)) t)
    (h0 : ∀ u, Phi 0 u = Psi 0 u) (t u : ℝ) : Phi t u = Psi t u := by
  have hb := GlobalODE.dist_le_of_global_solutions (E := ℝ) (K := K) (f := h)
    (α₁ := fun r => Phi r u) (α₂ := fun r => Psi r u) hlip (hPhi u) (hPsi u) 0 t
  rw [show dist (Phi 0 u) (Psi 0 u) = 0 by rw [h0 u, dist_self], zero_mul] at hb
  exact dist_le_zero.1 hb

/-- **Uniqueness of the gauge marking.**  For a tangential component `ξ` whose
arclength derivative is bounded by `K`, two markings solving
`∂_tΦ = −ξ(t, Φ)` with the same value at time `0` coincide. -/
theorem flow_unique_of_deriv_bound {xi xi1 : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hxi : ∀ t x, HasDerivAt (xi t) (xi1 t x) x) (hbd : ∀ t x, |xi1 t x| ≤ K)
    {Phi Psi : ℝ → ℝ → ℝ}
    (hPhi : ∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t)
    (hPsi : ∀ u t, HasDerivAt (fun r => Psi r u) (-xi t (Psi t u)) t)
    (h0 : ∀ u, Phi 0 u = Psi 0 u) (t u : ℝ) : Phi t u = Psi t u := by
  have hlip : ∀ s, LipschitzWith (Real.toNNReal K) (fun x => -xi s x) := by
    intro s
    refine lipschitzWith_of_nnnorm_deriv_le
      (fun x => ((hxi s x).neg).differentiableAt) (fun x => ?_)
    have hd : HasDerivAt (fun y => -xi s y) (-xi1 s x) x := (hxi s x).neg
    rw [hd.deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hK,
      Real.norm_eq_abs, abs_neg]
    exact hbd s x
  exact flow_unique_of_lipschitz (h := fun s x => -xi s x) hlip hPhi hPsi h0 t u

end GaugeFlowUniqueness
