import Mathlib
import UnitTangentIterates.HairpinLimit
import UnitTangentIterates.TranslatorRegularity

/-!
# The limit profile of the hairpin iteration

The theorem *Translating hairpin* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* produces the hairpin profile as the pointwise limit of
the monotone iterates `f_{n+1} = 𝒫 f_n`, started at the lower barrier and
trapped under the upper barrier.  `UnitTangentIterates/HairpinIteration.lean` and
`UnitTangentIterates/HairpinLimit.lean` produce the limit and pass to the limit in
the fixed-point equation; `UnitTangentIterates/Hairpin.lean` shows that a profile
squeezed between two positive constants defines a complete embedded strictly
convex hairpin.

This file connects the two: the barriers of the iteration are inherited by the
limit, and — by the bootstrap of `UnitTangentIterates/TranslatorRegularity.lean` —
the limit, being a bounded fixed point, is continuous on `(0, π)`.

Main results:

* `mem_Icc_of_tendsto` : a pointwise limit inherits two-sided bounds;
* `iSup_mem_Icc` : the pointwise supremum of the iterates is trapped between
  the barriers;
* `limit_profile_continuousOn` : the limit profile of the iteration is
  continuous on `(0, π)`.
-/

noncomputable section

open Filter Topology MeasureTheory Set Real

namespace LimitProfile

variable {fseq : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {m M : ℝ}

/-- **Two-sided bounds pass to a pointwise limit.** -/
theorem mem_Icc_of_tendsto {u : ℕ → ℝ} {l : ℝ} (hu : Tendsto u atTop (𝓝 l))
    (hlow : ∀ n, m ≤ u n) (hup : ∀ n, u n ≤ M) : l ∈ Icc m M :=
  ⟨ge_of_tendsto' hu hlow, le_of_tendsto' hu hup⟩

/-- **The barriers of the iteration are inherited by the pointwise limit.**
If every iterate satisfies `m ≤ f_n ≤ M`, then so does the pointwise
supremum. -/
theorem iSup_mem_Icc (hmono : ∀ n θ, fseq n θ ≤ fseq (n + 1) θ)
    (hlow : ∀ n θ, m ≤ fseq n θ) (hup : ∀ n θ, fseq n θ ≤ M) (θ : ℝ) :
    (⨆ n, fseq n θ) ∈ Icc m M :=
  mem_Icc_of_tendsto
    (HairpinLimit.tendsto_iterates (M := fun _ => M) hmono (fun n θ => hup n θ) θ)
    (fun n => hlow n θ) (fun n => hup n θ)

/-- **The limit profile is a continuous profile.**  If the iterates satisfy
`1 < m ≤ f_n ≤ M`, if `F` is their pointwise limit, if `F` is interval
integrable, and if `F` is a fixed point of the translator operator with shift
function `U` on `(0, π)`, then `F` is continuous on `(0, π)` — which is the
hypothesis under which `UnitTangentIterates/Hairpin.lean` shows that the profile
equations define a complete embedded strictly convex hairpin. -/
theorem limit_profile_continuousOn (hm : 1 < m)
    (hlow : ∀ n θ, m ≤ fseq n θ) (hup : ∀ n θ, fseq n θ ≤ M)
    (hpt : ∀ θ, Tendsto (fun n => fseq n θ) atTop (𝓝 (F θ)))
    (hint : ∀ a b : ℝ, IntervalIntegrable F volume a b)
    {U : ℝ → ℝ} (hlt : ∀ θ ∈ Ioo 0 π, θ < U θ)
    (hU : ∀ θ ∈ Ioo 0 π, (∫ t in θ..U θ, F t) = Real.sin θ)
    (hfix : ∀ θ ∈ Ioo 0 π, F θ = Real.sin θ * (Real.cos (U θ - θ) / Real.sin (U θ - θ))) :
    ContinuousOn F (Ioo 0 π) := by
  have hbounds : ∀ θ, F θ ∈ Icc m M := fun θ =>
    mem_Icc_of_tendsto (hpt θ) (fun n => hlow n θ) (fun n => hup n θ)
  exact TranslatorRegularity.fixedPoint_continuousOn hint hm
    (fun t => (hbounds t).1) (fun t => (hbounds t).2) hlt hU hfix

end LimitProfile
