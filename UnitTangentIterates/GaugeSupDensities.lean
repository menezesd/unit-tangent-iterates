import Mathlib
import UnitTangentIterates.JacobiArclength

/-!
# The three sup densities of a slice read in a marking

A normal path of the path metric asks its cost density `m` to dominate, at every
time, the three sup norms

`supNorm (η∘Φ)`, `supNorm ∂_u(η∘Φ)`, `supNorm ∂²_u(η∘Φ)`

of the normal velocity of the slice *read in the marking* `Φ` of the path
(`PathMetric.NormalPath.le_m_sup`).  This file provides the elementary chain
rule behind that condition: if the velocity `η` and its first two arclength
derivatives are bounded by `S₀, S₁, S₂` and the marking has
`|∂_uΦ| ≤ P₁`, `|∂²_uΦ| ≤ G₁`, then

```
  supNorm (η∘Φ)      ≤ S₀ ,
  supNorm ∂_u(η∘Φ)   ≤ S₁P₁ ,
  supNorm ∂²_u(η∘Φ)  ≤ S₂P₁² + S₁G₁ ,
```

so that a density dominating those three quantities dominates all three sup
norms at once.

Main result: `supNorm_iteratedDeriv_comp_le`.
-/

noncomputable section

open MarkedTopology

namespace GaugeSupDensities

open JacobiArclength

/-- The first derivative of a function read in a marking. -/
theorem deriv_comp_eq {phi phi1 e e1 : ℝ → ℝ}
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u) (he1 : ∀ x, HasDerivAt e (e1 x) x) :
    deriv (fun u => e (phi u)) = fun u => e1 (phi u) * phi1 u :=
  funext fun u => ((he1 (phi u)).comp u (hphi1 u)).deriv

/-- **The three sup densities of a slice read in a marking.**  Pointwise bounds
for the velocity, for its first two arclength derivatives and for the first two
derivatives of the marking bound the three sup norms of the path metric. -/
theorem supNorm_iteratedDeriv_comp_le {phi phi1 phi2 e e1 e2 : ℝ → ℝ}
    {S0 S1 S2 P1 G1 M : ℝ}
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u) (hphi2 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (he1 : ∀ x, HasDerivAt e (e1 x) x) (he2 : ∀ x, HasDerivAt e1 (e2 x) x)
    (h0 : ∀ x, |e x| ≤ S0) (h1 : ∀ x, |e1 x| ≤ S1) (h2 : ∀ x, |e2 x| ≤ S2)
    (hP1 : ∀ u, |phi1 u| ≤ P1) (hG1 : ∀ u, |phi2 u| ≤ G1)
    (hd0 : S0 ≤ M) (hd1 : S1 * P1 ≤ M) (hd2 : S2 * P1 ^ 2 + S1 * G1 ≤ M) :
    ∀ j ≤ 2, supNorm (iteratedDeriv j (fun u => e (phi u))) ≤ M := by
  have hS1 : 0 ≤ S1 := le_trans (abs_nonneg _) (h1 0)
  have hS2 : 0 ≤ S2 := le_trans (abs_nonneg _) (h2 0)
  have hP1nn : 0 ≤ P1 := le_trans (abs_nonneg _) (hP1 0)
  have hG1nn : 0 ≤ G1 := le_trans (abs_nonneg _) (hG1 0)
  -- the first derivative
  have hderiv1 : deriv (fun u => e (phi u)) = fun u => e1 (phi u) * phi1 u :=
    deriv_comp_eq hphi1 he1
  -- the second derivative
  have hderiv2 : ∀ u, HasDerivAt (fun u' => e1 (phi u') * phi1 u')
      (e2 (phi u) * phi1 u * phi1 u + e1 (phi u) * phi2 u) u := by
    intro u
    exact (((he2 (phi u)).comp u (hphi1 u)).mul (hphi2 u))
  intro j hj
  interval_cases j
  · simpa [iteratedDeriv_zero] using
      supNorm_le_of_forall (fun u => (h0 (phi u)).trans hd0)
  · rw [iteratedDeriv_one, hderiv1]
    refine supNorm_le_of_forall (fun u => ?_)
    calc |e1 (phi u) * phi1 u| = |e1 (phi u)| * |phi1 u| := abs_mul _ _
      _ ≤ S1 * P1 := mul_le_mul (h1 _) (hP1 u) (abs_nonneg _) hS1
      _ ≤ M := hd1
  · have hiter : iteratedDeriv 2 (fun u => e (phi u))
        = deriv fun u => e1 (phi u) * phi1 u := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv1]
    rw [hiter]
    refine supNorm_le_of_forall (fun u => ?_)
    rw [(hderiv2 u).deriv]
    have hb1 : |e2 (phi u) * phi1 u * phi1 u| ≤ S2 * P1 ^ 2 := by
      rw [abs_mul, abs_mul]
      calc |e2 (phi u)| * |phi1 u| * |phi1 u|
          ≤ S2 * P1 * P1 := by
            refine mul_le_mul (mul_le_mul (h2 _) (hP1 u) (abs_nonneg _) hS2) (hP1 u)
              (abs_nonneg _) (by positivity)
        _ = S2 * P1 ^ 2 := by ring
    have hb2 : |e1 (phi u) * phi2 u| ≤ S1 * G1 := by
      rw [abs_mul]
      exact mul_le_mul (h1 _) (hG1 u) (abs_nonneg _) hS1
    calc |e2 (phi u) * phi1 u * phi1 u + e1 (phi u) * phi2 u|
        ≤ |e2 (phi u) * phi1 u * phi1 u| + |e1 (phi u) * phi2 u| := abs_add_le _ _
      _ ≤ S2 * P1 ^ 2 + S1 * G1 := by linarith
      _ ≤ M := hd2

end GaugeSupDensities
