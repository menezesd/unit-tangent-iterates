import Mathlib
import UnitTangentIterates.UnitTangent
import UnitTangentIterates.GeometricLimit

/-!
# The unit-tangent transform passes to a `C¹` limit

The last identification in the proof of the theorem *Regularizing backward
shadowing* of *A Noncircular Oval with Convex Unit-Tangent Iterates* reads:

> Continuity of `𝒯γ = γ + τ_γ` in `C¹` gives `𝒯X_n = X_{n+1}`.

This file formalizes that step: if the approximating curves converge
pointwise, their velocities converge uniformly, and the transformed curves
converge pointwise, then the limit of the transforms is the transform of the
limit.  In particular an exact relation `𝒯 Z_n = Z_{n+1}` along the
approximating sequence passes to the limit.

Main results:

* `unitTangentMap_eq_of_limit` : `𝒯X = Y` for the limits `X` of the curves and
  `Y` of their transforms;
* `unitTangentMap_limit_exact` : an exact orbit relation passes to the limit.
-/

noncomputable section

open Filter Topology

namespace UnitTangentLimit

variable {Zn Wn : ℕ → ℝ → ℂ} {X Y V : ℝ → ℂ}

/-- **The unit-tangent transform commutes with a `C¹` limit.**  If
`Zₙ' = Wₙ`, `Zₙ → X` pointwise, `Wₙ → V` uniformly and `Zₙ + Wₙ → Y`
pointwise, then `𝒯X = Y`. -/
theorem unitTangentMap_eq_of_limit
    (hderiv : ∀ n u, HasDerivAt (Zn n) (Wn n u) u)
    (hZ : ∀ u, Tendsto (fun n => Zn n u) atTop (𝓝 (X u)))
    (hW : TendstoUniformly Wn V atTop)
    (hY : ∀ u, Tendsto (fun n => Zn n u + Wn n u) atTop (𝓝 (Y u))) :
    UnitTangent.unitTangentMap X = Y := by
  funext u
  have hXderiv : HasDerivAt X (V u) u :=
    GeometricLimit.hasDerivAt_of_uniform_limit hderiv hW hZ u
  have hsum : Tendsto (fun n => Zn n u + Wn n u) atTop (𝓝 (X u + V u)) :=
    (hZ u).add (hW.tendsto_at u)
  have : X u + V u = Y u := tendsto_nhds_unique hsum (hY u)
  rw [UnitTangent.unitTangentMap, hXderiv.deriv]
  exact this

/-- **An exact orbit relation passes to the limit.**  If every approximating
pair satisfies `𝒯 Zₙ = Z'ₙ`, the curves converge pointwise, the velocities
converge uniformly, and the transforms converge pointwise to `Y`, then the
limits satisfy `𝒯X = Y`. -/
theorem unitTangentMap_limit_exact {Zn' : ℕ → ℝ → ℂ}
    (hderiv : ∀ n u, HasDerivAt (Zn n) (Wn n u) u)
    (hexact : ∀ n, UnitTangent.unitTangentMap (Zn n) = Zn' n)
    (hZ : ∀ u, Tendsto (fun n => Zn n u) atTop (𝓝 (X u)))
    (hW : TendstoUniformly Wn V atTop)
    (hY : ∀ u, Tendsto (fun n => Zn' n u) atTop (𝓝 (Y u))) :
    UnitTangent.unitTangentMap X = Y := by
  refine unitTangentMap_eq_of_limit hderiv hZ hW ?_
  intro u
  have hrw : ∀ n, Zn n u + Wn n u = Zn' n u := by
    intro n
    have h := congrFun (hexact n) u
    rw [UnitTangent.unitTangentMap, (hderiv n u).deriv] at h
    exact h
  simpa [hrw] using hY u

end UnitTangentLimit
