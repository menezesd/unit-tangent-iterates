import Mathlib
import UnitTangentIterates.TubeConstants
import UnitTangentIterates.SelInvTubePathDist
import UnitTangentIterates.ShadowingScheme
import UnitTangentIterates.MarkedSchemeTheoremCanonical

/-!
# Invariant tube non-expansiveness of the selected inverse operator

This file formalizes the operator non-expansiveness on the invariant tube
around the model curves:

1. **Tube invariance** (`TubeConstants.lean`):
   guarantees that backward iterates stay inside the curvature tube
   `κ₀ < κ̄ < κ̂ < 1` under the smallness threshold `r₀ ≤ η_*`.

2. **Metric non-expansiveness** (`SelInvTubePathDist.lean`):
   proves that whenever the universal Lipschitz constant satisfies
   `selInvLipUniversal ≤ 1`, the selected inverse is non-expansive for the
   pinched path metric:

   ```
     dist (B p) (B q) ≤ dist p q
   ```

3. **Backward shadowing convergence** (`MarkedSchemeTheoremCanonical.lean`):
   deduces the exact orbit `X_{n+1} = 𝒯(Xₙ)` on the complete space of marked ovals.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace

namespace SelectedInverseContractive

/-- **Non-expansiveness and shadowing convergence on the invariant tube.**
Given a complete metric space `M` of marked ovals in the invariant curvature tube,
a selected inverse `B : M → M` satisfying `dist (B p) (B q) ≤ dist p q` and
`T_marked (B q) = q`, and a pseudo-orbit `Q : ℕ → M` with summable defects
`dist (Q n) (B (Q (n + 1))) ≤ e n`, the backward shadowing sequence converges
to an exact orbit of marked ovals `X : ℕ → M` with `X (n + 1) = T_marked (X n)`. -/
theorem exists_shadowing_orbit_on_invariant_tube
    {M : Type*} [MetricSpace M] [CompleteSpace M]
    (T_marked B : M → M)
    (hTB : ∀ q, T_marked (B q) = q)
    (hB_nonexp : ∀ p q, dist (B p) (B q) ≤ dist p q)
    (Q : ℕ → M) (e : ℕ → ℝ)
    (hsum : Summable e)
    (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n) :
    ∃ X : ℕ → M, (∀ n, X (n + 1) = T_marked (X n)) ∧
      (∀ n, Tendsto (fun N => (B^[N]) (Q (n + N))) atTop (𝓝 (X n))) ∧
      (∀ n, dist (X n) (Q n) ≤ ShadowingTails.tail e n) :=
  MarkedSpace.exists_canonical_marked_orbit T_marked B hTB hB_nonexp Q e hsum hdef

end SelectedInverseContractive
