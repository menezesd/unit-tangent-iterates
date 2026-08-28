import Mathlib
import UnitTangentIterates.SelInvLipschitzPathDist
import UnitTangentIterates.LipschitzShadowing

/-!
# The selected inverse is Lipschitz in the path pseudodistance

`LipschitzShadowing.exists_shadowing_orbit_of_lipschitz` reduces backward
shadowing to two inputs: an `L`-Lipschitz selected inverse, and defects with
`∑ Lⁿeₙ < ∞`.  This file supplies the first one in the metric the paper's
shadowing actually uses.

Two distances are in play on marked curves:

* `dist` — the ambient `C²` sup-distance of `MarkedSpace`;
* `pathDist` — the infimum of costs of normal paths joining the two curves,
  which is the paper's metric (`PathMetric.dist_le_pathDist` records
  `dist ≤ pathDist`).

`SelInvLipUniversal.dist_selInv_le_lipUniversal_pathDist` bounds the *ambient*
distance of the two images by a constant times `pathDist` of the sources.  That
is the wrong shape for iterating: shadowing needs the same quantity on both
sides.  The right shape is

```
  pathDist (𝔅 p) (𝔅 q) ≤ C · pathDist p q,
```

and it follows from the per-path bounds by exactly the passage
`SelInvLipschitzPathDist.le_mul_pathDist_of_costs`, which is generic in the
quantity being bounded.  The per-path bounds are the Jacobi gains
(`MarkedSelInvRegular`), which is where `lem:jacobi` enters.

Main results: `pathDist_selInv_le_mul_pathDist`, `shadowing_of_pathLipschitz`.
-/

noncomputable section

open PathMetric MarkedSpace PathMetric.NormalPath

namespace SelInvPathLipschitz

/-- **The selected inverse is `C`-Lipschitz for the path pseudodistance.**  This
is the shape backward shadowing iterates, and it follows from the per-path
Jacobi bounds by the same infimum passage that
`SelInvLipschitzPathDist.dist_selInv_le_mul_pathDist` uses for the ambient
distance. -/
theorem pathDist_selInv_le_mul_pathDist {p q : Data} {kh C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε > 0, ∃ Γ : NormalPath p q, cost Γ ≤ pathDist p q + ε ∧
      pathDist (SelectedInverseMap.selInv kh p) (SelectedInverseMap.selInv kh q)
        ≤ C * cost Γ) :
    pathDist (SelectedInverseMap.selInv kh p) (SelectedInverseMap.selInv kh q)
      ≤ C * pathDist p q :=
  SelInvLipschitzPathDist.le_mul_pathDist_of_costs hC h

/-- **Backward shadowing from a path-Lipschitz selected inverse.**  Packaging the
two halves: once the selected inverse is `L`-Lipschitz for the metric in which
the space is complete, and the defects satisfy `∑ Lⁿeₙ < ∞`, the terminal
pullbacks converge to an exact orbit.

Stated for an abstract complete metric space so that it can be applied either to
the ambient `C²` metric of `MarkedSpace` or, as the paper does, to the
completion for the path pseudodistance (`lem:complete`). -/
theorem shadowing_of_pathLipschitz {M : Type*} [MetricSpace M] [CompleteSpace M]
    (T B : M → M) {L : ℝ} (hL : 0 < L)
    (hTB : ∀ q, T (B q) = q)
    (hlip : ∀ p q, dist (B p) (B q) ≤ L * dist p q)
    (Q : ℕ → M) (e : ℕ → ℝ)
    (hsum : Summable fun m => L ^ m * e m)
    (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n) :
    ∃ X : ℕ → M, (∀ n, X (n + 1) = T (X n)) ∧
      ∀ n, Filter.Tendsto (fun N => (B^[N]) (Q (n + N))) Filter.atTop (nhds (X n)) :=
  LipschitzShadowing.exists_shadowing_orbit_of_lipschitz T B hL hTB hlip Q e hsum
    hdef

/-- **Exponentially decaying defects are summable against any fixed Lipschitz
constant.**  This is why the Lipschitz hypothesis suffices in place of
non-expansiveness: the paper's defects satisfy `eₙ ≤ C e^{-γn}` with `γ` as large
as one likes (by taking the initial separation large), so `∑ Lⁿeₙ` converges. -/
theorem summable_lipschitz_defects {L C gamma : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    (hgamma : L < Real.exp gamma) {e : ℕ → ℝ} (he0 : ∀ n, 0 ≤ e n)
    (he : ∀ n, e n ≤ C * Real.exp (-gamma * n)) :
    Summable fun n => L ^ n * e n := by
  have hq : |L / Real.exp gamma| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_lt_one (Real.exp_pos gamma)]
    exact hgamma
  have hgeo : Summable fun n : ℕ => C * (L / Real.exp gamma) ^ n :=
    (summable_geometric_of_abs_lt_one hq).mul_left C
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (he0 n)) (fun n => ?_) hgeo
  have hstep : L ^ n * e n ≤ L ^ n * (C * Real.exp (-gamma * n)) :=
    mul_le_mul_of_nonneg_left (he n) (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [div_pow, ← Real.exp_nat_mul]
  have hne : Real.exp ((n : ℝ) * gamma) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  rw [mul_assoc, ← Real.exp_add]
  norm_num

end SelInvPathLipschitz
