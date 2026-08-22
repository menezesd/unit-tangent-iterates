import Mathlib
import UnitTangentIterates.SelInvModulusLinear

/-!
# From a bound on every cost to a bound on the path pseudodistance

`SelInvModulusLinear.dist_selInv_le_lip_cost` bounds the marked distance of the
two marked selected inverses of the ends of a normal path by a constant times
the **cost of that path**.  The path pseudodistance of `PathMetric.lean` is the
infimum of the costs, so a bound valid along a cost-minimizing sequence of paths
passes to the infimum.  This file records that passage.

`le_mul_pathDist_of_costs` is the general statement: a real quantity bounded by
`C` times the cost of paths of cost arbitrarily close to `pathDist p q` is
bounded by `C · pathDist p q`.  `dist_selInv_le_mul_pathDist` is its reading for
the selected inverse: if the `C²` comparison holds with one and the same
constant `C` along such a sequence of paths, then

`dist (selInv κ̂ q) (selInv κ̂ p) ≤ C · pathDist p q` ,

the Lipschitz bound from the path pseudodistance of the fronts to the marked
metric of the rears.  What is *not* proved here is that the geometric
hypotheses of the `C²` comparison hold along a cost-minimizing sequence with a
constant independent of the path; that is the remaining gap between this
statement and non-expansiveness of the selected inverse.

Main results: `le_mul_pathDist_of_costs`, `dist_selInv_le_mul_pathDist`.
-/

noncomputable section

open MarkedSpace PathMetric PathMetric.NormalPath

namespace SelInvLipschitzPathDist

/-- **From costs to the pseudodistance.**  A quantity bounded by `C` times the
cost of normal paths of cost arbitrarily close to the pseudodistance is bounded
by `C` times the pseudodistance. -/
theorem le_mul_pathDist_of_costs {p q : Data} {d C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε > 0, ∃ Γ : NormalPath p q, cost Γ ≤ pathDist p q + ε ∧ d ≤ C * cost Γ) :
    d ≤ C * pathDist p q := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hCpos : 0 < C + 1 := by linarith
  have hεpos : 0 < ε / (C + 1) := by positivity
  obtain ⟨Γ, hcost, hd⟩ := h (ε / (C + 1)) hεpos
  have h1 : C * cost Γ ≤ C * (pathDist p q + ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left hcost hC
  have h2 : C * (ε / (C + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hCpos]
    nlinarith
  nlinarith [hd, h1, h2]

/-- **The Lipschitz bound for the selected inverse, in the path
pseudodistance.**  If the `C²` comparison of the two marked selected inverses
holds with one and the same constant `C` along normal paths of cost arbitrarily
close to `pathDist p q`, then the marked distance of the two selected inverses
is at most `C · pathDist p q`. -/
theorem dist_selInv_le_mul_pathDist {p q : Data} {kh C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε > 0, ∃ Γ : NormalPath p q, cost Γ ≤ pathDist p q + ε ∧
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p) ≤ C * cost Γ) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ C * pathDist p q :=
  le_mul_pathDist_of_costs hC h

end SelInvLipschitzPathDist
