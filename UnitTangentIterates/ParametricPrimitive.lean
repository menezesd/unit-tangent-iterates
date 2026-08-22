import Mathlib
import UnitTangentIterates.JointC1

/-!
# The primitive of a `C¹` family is a `C¹` family

The change of variable between the front and the rear arclength of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates* is the primitive

`A(t, s) = ∫₀ˢ cos δ(t, u) du`

of a family that depends on the time `t` of a path of fronts.  All the
regularity of that change of variable — and, through its inverse, of the family
of rear tracks read in their own arclength — comes from the following two
facts, proved here for a general family `g`:

* `hasDerivAt_primitive_param` — the primitive may be differentiated in the
  parameter under the integral sign, `∂_t ∫₀ˢ g(t,u) du = ∫₀ˢ ∂_t g(t,u) du`
  (the local domination being automatic, by continuity of `∂_t g` on a compact
  box);
* `contDiff_one_primitive` — consequently, if `g` and `∂_t g` are jointly
  continuous, the primitive is jointly `C¹`, its two partial derivatives being
  `∫₀ˢ ∂_t g(t,u) du` and `g(t,s)`.
-/

noncomputable section

open Function Set MeasureTheory intervalIntegral

namespace ParametricPrimitive

variable {g gt : ℝ → ℝ → ℝ}

/-- Each slice of a jointly continuous family is continuous. -/
theorem continuous_slice (hg : Continuous (uncurry g)) (t : ℝ) : Continuous (g t) :=
  hg.comp (continuous_const.prodMk continuous_id)

/-- **Differentiation under the integral sign for the primitive of a family.**
If `g` is jointly continuous, has a partial derivative `∂_t g = gt` in the
parameter everywhere, and `gt` is jointly continuous, then the primitive
`t ↦ ∫₀ˢ g(t,u) du` is differentiable with derivative `∫₀ˢ gt(t,u) du`. -/
theorem hasDerivAt_primitive_param (hg : Continuous (uncurry g))
    (hgd : ∀ t u, HasDerivAt (fun r => g r u) (gt t u) t)
    (hgtc : Continuous (uncurry gt)) (t s : ℝ) :
    HasDerivAt (fun r => ∫ u in (0:ℝ)..s, g r u) (∫ u in (0:ℝ)..s, gt t u) t := by
  -- a bound for `gt` on a compact box around the interval of integration
  have hK : IsCompact ((Icc (t - 1) (t + 1)) ×ˢ (uIcc (0:ℝ) s)) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hgtc.continuousOn
  have hball : Icc (t - 1) (t + 1) ∈ nhds t :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ x in nhds t,
      AEStronglyMeasurable (g x) (volume.restrict (uIoc (0:ℝ) s)) :=
    Filter.Eventually.of_forall fun x => (continuous_slice hg x).aestronglyMeasurable
  have hint : IntervalIntegrable (g t) volume 0 s :=
    (continuous_slice hg t).intervalIntegrable _ _
  have hmeas' : AEStronglyMeasurable (gt t) (volume.restrict (uIoc (0:ℝ) s)) :=
    (continuous_slice hgtc t).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ uIoc (0:ℝ) s →
      ∀ x ∈ Icc (t - 1) (t + 1), ‖gt x u‖ ≤ M := by
    refine Filter.Eventually.of_forall fun u hu x hx => ?_
    exact hM (x, u) ⟨hx, Set.uIoc_subset_uIcc hu⟩
  have hboundint : IntervalIntegrable (fun _ : ℝ => M) volume 0 s :=
    _root_.intervalIntegrable_const
  have hderiv : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ uIoc (0:ℝ) s →
      ∀ x ∈ Icc (t - 1) (t + 1), HasDerivAt (fun x' => g x' u) (gt x u) x :=
    Filter.Eventually.of_forall fun u _ x _ => hgd x u
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => M)
    hball hmeas hint hmeas' hbound hboundint hderiv).2

/-- **The primitive of a `C¹` family is a `C¹` family.**  If `g` and its
parameter derivative `gt` are jointly continuous, then
`A(t,s) = ∫₀ˢ g(t,u) du` is jointly `C¹`. -/
theorem contDiff_one_primitive (hg : Continuous (uncurry g))
    (hgd : ∀ t u, HasDerivAt (fun r => g r u) (gt t u) t)
    (hgtc : Continuous (uncurry gt)) :
    ContDiff ℝ 1 (uncurry fun t s => ∫ u in (0:ℝ)..s, g t u) := by
  refine JointC1.contDiff_one_of_continuous_partials
    (f1 := fun t s => ∫ u in (0:ℝ)..s, gt t u) (f2 := g)
    (fun t s => hasDerivAt_primitive_param hg hgd hgtc t s)
    (fun t s => ((continuous_slice hg t).integral_hasStrictDerivAt 0 s).hasDerivAt) ?_ hg
  exact continuous_parametric_primitive_of_continuous (f := gt) (a₀ := 0) hgtc

/-- The space derivative of the primitive is the integrand. -/
theorem hasDerivAt_primitive_space (hg : Continuous (uncurry g)) (t s : ℝ) :
    HasDerivAt (fun y => ∫ u in (0:ℝ)..y, g t u) (g t s) s :=
  ((continuous_slice hg t).integral_hasStrictDerivAt 0 s).hasDerivAt

end ParametricPrimitive
