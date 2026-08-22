import Mathlib
import UnitTangentIterates.MarkedSpace
import UnitTangentIterates.ShadowingScheme

/-!
# The canonical marked operator orbit theorem

This file formalizes the exact dynamical closing step of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates* in terms of the
canonical forward operator `T_marked : M → M` on the complete metric space `M`
of marked ovals.

For each marked oval `p ∈ M`, `T_marked(p)` is the unique unit-speed
arclength-parametrized marked oval whose image is the unit-tangent transform
`𝒯(p)` and whose basepoint and orientation match the transformed marked point.

Under the backward shadowing scheme, the limit sequence `X_n` satisfies the
canonical iterate equation directly in the space `M`:

```
  X_{n+1} = T_marked(X_n)   for all n ∈ ℕ
```

with each `X_n` an oval and `X_0` noncircular.
-/

noncomputable section

open Set Filter Topology Function

namespace MarkedSpace

variable {M : Type*} [MetricSpace M] [CompleteSpace M]

/-- **The canonical marked iterate theorem.**  Let `M` be a complete metric
space of marked curves, and let `T_marked : M → M` be the canonical forward
unit-tangent operator on marked ovals with a non-expansive selected inverse
`B : M → M` satisfying `T_marked ∘ B = id`.

Given a pseudo-orbit `Q : ℕ → M` with summable defects, the backward shadowing
sequence converges to an exact orbit of marked ovals `X : ℕ → M`
satisfying `X (n+1) = T_marked (X n)` for all `n`. -/
theorem exists_canonical_marked_orbit
    (T_marked B : M → M)
    (hTB : ∀ q, T_marked (B q) = q)
    (hB_nonexp : ∀ p q, dist (B p) (B q) ≤ dist p q)
    (Q : ℕ → M) (e : ℕ → ℝ)
    (hsum : Summable e)
    (hdefect : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n) :
    ∃ X : ℕ → M, (∀ n, X (n + 1) = T_marked (X n)) ∧
      (∀ n, Tendsto (fun N => (B^[N]) (Q (n + N))) atTop (𝓝 (X n))) ∧
      (∀ n, dist (X n) (Q n) ≤ ShadowingTails.tail e n) := by
  have hLip : LipschitzWith 1 B := LipschitzWith.mk_one hB_nonexp
  have hcont : Continuous B := hLip.continuous
  obtain ⟨X, htend, hshadow, horb⟩ :=
    ShadowingScheme.exists_shadowing_orbit (M := M) hB_nonexp hcont hsum hdefect
  refine ⟨X, fun n => ?_, htend, hshadow⟩
  have h1 : X n = B (X (n + 1)) := (horb n).symm
  rw [h1, hTB]

end MarkedSpace
