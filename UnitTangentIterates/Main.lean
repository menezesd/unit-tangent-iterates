module

public import UnitTangentIterates.Defs
public import UnitTangentIterates.Circle
public import UnitTangentIterates.Resolvent
public import UnitTangentIterates.Steering
public import UnitTangentIterates.RearFront
public import UnitTangentIterates.Translator
public import UnitTangentIterates.HairpinCurve
public import UnitTangentIterates.Periodization
public import UnitTangentIterates.PeriodizationEstimates
public import UnitTangentIterates.PeriodizationIntegral
public import UnitTangentIterates.FrontError
public import UnitTangentIterates.CurveFromCurvature
public import UnitTangentIterates.ClosedPairs
public import UnitTangentIterates.PeriodizedPairs
public import UnitTangentIterates.PerimeterAsymptotics
public import UnitTangentIterates.ResolventBounds
public import UnitTangentIterates.PeriodRecursion
public import UnitTangentIterates.Noncircular
public import UnitTangentIterates.FrontMatching
public import UnitTangentIterates.Width
public import UnitTangentIterates.WidthBound
public import UnitTangentIterates.CurvatureBound
public import UnitTangentIterates.RearMatching
public import UnitTangentIterates.Matching
public import UnitTangentIterates.Interpolation
public import UnitTangentIterates.PeriodSequence
public import UnitTangentIterates.ModelDefects
public import UnitTangentIterates.Reduction
public import UnitTangentIterates.Reparam
public import UnitTangentIterates.Embedded
public import UnitTangentIterates.SelectedRear
public import UnitTangentIterates.WeightedSteering
public import UnitTangentIterates.ParamSteering
public import UnitTangentIterates.Jacobi
public import UnitTangentIterates.WeightedResolvent
public import UnitTangentIterates.JacobiEstimates
public import UnitTangentIterates.Pulse
public import UnitTangentIterates.Shadowing
public import UnitTangentIterates.Assembly

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# A noncircular oval with convex unit-tangent iterates — main theorem

**Theorem 1.1.** There is a noncircular oval `Γ₀` such that `𝒯ⁿ Γ₀` is an oval for every
`n ≥ 0`.

Here `𝒯 γ = γ + γ'/|γ'|` is the unit-tangent transform (`Ovals.unitTangentTransform`),
an oval is a smooth regular simple closed curve of positive curvature (`Ovals.IsOval`), and
`Ovals.IsCircle γ` says that the image of `γ` lies on a circle.  For comparison,
`Ovals.isOval_iterate_circ` shows that circles have this property.
-/

@[expose] public section

namespace Ovals

/-- **Theorem 1.1 (main theorem).**  There is a noncircular oval all of whose unit-tangent
iterates are ovals.  It follows from the thin orbit of `exists_ovalOrbit_bounded_width`
(the closed models of Section 7 shadowed by Theorem 6.4, `backward_shadowing`) by
`Ovals.main_of_orbit`: a circle cannot stay thin, because the iterates of a circle of radius `r`
are circles of radius `√(r² + n)`. -/
theorem exists_noncircular_oval_iterates_ovals :
    ∃ Γ : ℝ → ℂ, IsOval Γ ∧ ¬ IsCircle Γ ∧ ∀ n : ℕ, IsOval (unitTangentTransform^[n] Γ) := by
  obtain ⟨X, p, ψ, W, h, hW⟩ := exists_ovalOrbit_bounded_width
  exact main_of_orbit h hW

end Ovals

end
