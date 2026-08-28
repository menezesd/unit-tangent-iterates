import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSource
import UnitTangentIterates.RearOwnIsFront

/-!
# The intrinsic successor front carried by a rear-family source

One application of the rear-family construction produces a selected rear.  In
its own arclength that rear is canonically another family of fronts.  This file
retains the part of the next analytic source which follows formally from the
current source, without postulating a new `MarkingAwareSource`.
-/

noncomputable section

open Function MarkedSpace PathMetric RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareSuccessorFront

open FiniteSmoothRearFamilyMarkingAwareSource

def front
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ → ℂ :=
  rearOwn A.F A.Theta A.delta A.sf

def angle
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ → ℝ :=
  rearOwnAngle A.Theta A.delta A.sf

def curvature
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ → ℝ :=
  fun t x => Real.tan (A.delta t (A.sf t x))

def period
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ :=
  fun t => rearArclength (A.delta t) (A.P t)

/-- The exact intrinsic front data inherited by the selected rear.  This is the
geometric part of the next `MarkingAwareSource`; it deliberately does not claim the new
steering family, time jets, or Jacobi majorants. -/
structure Core
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : Prop where
  front_frenet : ∀ t x, HasDerivAt (front A t)
    (Complex.exp (Complex.I * (angle A t x : ℂ))) x
  angle_frenet : ∀ t x, HasDerivAt (angle A t) (curvature A t x) x
  period_pos : ∀ t, 0 < period A t
  front_periodic : ∀ t x, front A t (x + period A t) = front A t x
  angle_periodic : ∀ t x,
    angle A t (x + period A t) = angle A t x + 2 * Real.pi
  curvature_nonnegative : ∀ t x, 0 ≤ curvature A t x

/-- Every analytic rear-family source canonically supplies the intrinsic
successor-front core. -/
theorem MarkingAwareSource.successorFrontCore
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : Core A := by
  have hdelta_cont : ∀ t, Continuous (A.delta t) := fun t =>
    A.steering_contDiff.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨hfront, hfront_periodic, hangle_periodic⟩ :=
    RearOwnIsFront.rearOwn_is_front A.kh_nonnegative A.kh_lt_one
      A.front_frenet A.angle_frenet A.steering hdelta_cont
      A.strip_nonnegative A.strip_le A.steering_periodic A.sf_deriv
      A.sf_rightInverse A.front_periodic A.angle_periodic
  exact
    { front_frenet := hfront
      angle_frenet := fun t x =>
        RearOwnIsFront.hasDerivAt_rearOwnAngle A.angle_frenet A.steering
          A.sf_deriv t x
      period_pos := A.rear_period_pos
      front_periodic := hfront_periodic
      angle_periodic := hangle_periodic
      curvature_nonnegative := fun t x =>
        RearOwnIsFront.rearOwn_curvature_nonneg A.kh_lt_one
          A.strip_nonnegative A.strip_le A.kh_nonnegative t x }

end FiniteSmoothRearFamilyMarkingAwareSuccessorFront
