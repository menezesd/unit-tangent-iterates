import UnitTangentIterates.CircleRangeSimplePeriod

/-!
# Projecting a simple arclength circle parametrization to geometric circularity

The paper-facing conclusion records circularity as a property of the image
together with its actual perimeter.  Equality of the image with a metric
sphere alone does not identify that perimeter, since an arbitrary displayed
period may be a multiple of the simple period.  For the retained oval
parametrization, positivity of the displayed period and injectivity on its
half-open period interval make it the simple period; the local circle-period
rigidity theorem then identifies it with the circumference.
-/

noncomputable section

open Function Set

namespace CircleRangePerimeterProjection

/-- A positive-period, simple arclength oval whose image is a circle is a
circle *of that displayed perimeter* in the sense used by the closing
argument. -/
theorem isCircleOfPerimeter_of_circleRange
    {gamma : ℝ → ℂ} {L : ℝ}
    (hL : 0 < L) (hperiod : Periodic gamma L)
    (hinj : InjOn gamma (Ico 0 L))
    (hoval : MainTheoremConditional.IsOval gamma)
    {center : ℂ} {radius : ℝ} (hradius : 0 < radius)
    (hrange : range gamma = Metric.sphere center radius) :
    ClosingArgument.IsCircleOfPerimeter (range gamma) L := by
  refine ⟨center, radius, hradius, ?_, hrange⟩
  exact CircleRangeSimplePeriod.period_eq_two_pi_mul_radius_of_circleRange
    hL hperiod hinj hoval hradius hrange

/-- Consequently, same-perimeter noncircularity excludes every circle image;
this is the genuine geometric projection used by the final theorem. -/
theorem not_circleRange_of_not_isCircleOfPerimeter
    {gamma : ℝ → ℂ} {L : ℝ}
    (hL : 0 < L) (hperiod : Periodic gamma L)
    (hinj : InjOn gamma (Ico 0 L))
    (hoval : MainTheoremConditional.IsOval gamma)
    (hnoncircle : ¬ ClosingArgument.IsCircleOfPerimeter (range gamma) L) :
    ¬ ∃ center : ℂ, ∃ radius : ℝ, 0 < radius ∧
      range gamma = Metric.sphere center radius := by
  rintro ⟨center, radius, hradius, hrange⟩
  exact hnoncircle (isCircleOfPerimeter_of_circleRange
    hL hperiod hinj hoval hradius hrange)

end CircleRangePerimeterProjection
