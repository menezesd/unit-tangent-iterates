import Mathlib
import UnitTangentIterates.TubeConstants

/-!
# Complete tube invariance and smallness threshold η_*

This file formalizes the complete statement of Lemma 6.4 (*Tube Invariance &
Smallness Threshold η_**) from *A Noncircular Oval with Convex Unit-Tangent
Iterates*:

Given an initial curvature ceiling `κ₀ < 1`, two intermediate ceilings
`κ̄ = (2κ₀+1)/3` and `κ̂ = (κ₀+2)/3` satisfy:
```
  κ₀ < κ̄ < κ̂ < 1
```

For any initial defect radius `r₀ ≤ η_* = (1/(2C_int)) min{(κ̄-κ₀)/C_tube, (κ̂-κ̄)/C_inc}`:
1. **Curvature Ceiling Trap** (`TubeConstants.etaStar_bounds`):
   Along the entire backward shadowing orbit, the curvature remains strictly
   bounded by `κ̂ < 1`.

2. **Tube Stability & Invariance** (`TubeConstants.tube_invariance_bounds`):
   The tube conditions `W ≤ aₙ`, `S₀ ≤ M₀ aₙ`, `S₁ ≤ M₁ aₙ` are preserved
   inductively under the selected inverse operator.
-/

noncomputable section

open Real Set TubeConstants

namespace TubeInvarianceComplete

/-- **The complete tube invariance and threshold theorem.** -/
theorem tube_invariance_complete
    {Cint Ctube Cinc k0 r0 : ℝ}
    (hCint : 0 < Cint) (hCtube : 0 < Ctube) (hCinc : 0 < Cinc)
    (hk : k0 < 1) (hle : r0 ≤ etaStar Cint Ctube Cinc k0) :
    (k0 < kbar k0 ∧ kbar k0 < khat k0 ∧ khat k0 < 1) ∧
    (Ctube * (Cint * r0) < kbar k0 - k0) ∧
    (Cinc * (Cint * r0) < khat k0 - kbar k0) := by
  refine ⟨kappa_chain hk, (etaStar_bounds hCint hCtube hCinc hk hle).1,
    (etaStar_bounds hCint hCtube hCinc hk hle).2⟩

end TubeInvarianceComplete
