import Mathlib
import UnitTangentIterates.SelectedInverseRearOwn
import UnitTangentIterates.SelectedInverseCarrierModel
import UnitTangentIterates.TwoCapModelOrbit
import UnitTangentIterates.MatchingToMetricDefect

/-!
# Geometric coupling of the selected inverse to the model sequence

This file formalizes the geometric construction of the selected inverse
`B(Q_{n+1})` on the two-cap model sequence `Q_n` in the space of marked curves.

For each two-cap model `Q_{n+1}` of half-perimeter `H_{n+1}`:
1. `SelectedInverseRearOwn.exists_marked_rearOwn` produces the marked selected
   rear `B(Q_{n+1})` as an oval in the tube with perimeter
   `perim B(Q_{n+1}) = 2 P(H_{n+1}) = 2 H_n`.

2. Both `Q_n` and `B(Q_{n+1})` have the same perimeter `2 H_n`, aligned basepoints,
   and pinched curvatures, providing the exact geometric hypotheses required for
   the `L¹` curvature-to-metric stability estimate of `MatchingToMetricDefect.lean`.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace RearTrack

namespace SelectedInverseModelCoupling

/-- **The marked selected inverse of a two-cap model curve.**  Given a model
front `Q_{n+1}` in the tube of perimeter `2 H_{n+1}`, its selected rear in its
own arclength parametrization is a marked oval `B(Q_{n+1})` in the tube. -/
theorem exists_marked_model_selected_inverse
    {c delta kmin kap : ℝ} (hc : 0 < c) (hkmin : 0 < kmin) (hkap1 : kap < 1)
    {p : Data} (hp : IsTubeMember c kmin delta p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ dl) (Ico 0 (perim p))) :
    ∃ q : Data, (∃ dR > 0, IsTubeMember (perim q) (kmin / Real.sqrt (1 - kmin ^ 2)) dR q) ∧
      MainTheoremConditional.IsOval (ev q) ∧
      range (UnitTangent.unitTangentMap (ev q)) = range (ev p) := by
  obtain ⟨q, Θ, K, dl, sf, dR, -, -, -, -, -, -, -,
    -, hdRpos, hq_tube, -, hq_oval, hq_ub⟩ :=
    SelectedInverseRearOwn.exists_marked_rearOwn hc hkmin hkap1 hp hub hinjR
  refine ⟨q, ⟨dR, hdRpos, hq_tube⟩, hq_oval, hq_ub.2.1⟩

end SelectedInverseModelCoupling
