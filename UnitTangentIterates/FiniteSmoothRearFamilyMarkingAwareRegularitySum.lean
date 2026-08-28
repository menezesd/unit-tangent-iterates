import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSmoothSource

/-!
# Sound recursive regularity sidecars

The stopped `B` clock is not globally smooth.  This module keeps the legacy
all-order branch and adds an exact branch carrying the finite joint and
spatial witnesses which the next source actually consumes.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareRegularitySum

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  RearOwnHigherRegularity

/-- First-order geometry retained by an already assembled exact source. -/
structure ExactSourceRegularity
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (periodLower kap : ℝ) where
  periodLower_eq : periodLower = P0
  kap_eq : kap = kh
  front_C1 : ContDiff ℝ 1 (uncurry A.F)
  angle_C1 : ContDiff ℝ 1 (uncurry A.Theta)
  steering_C1 : ContDiff ℝ 1 (uncurry A.delta)
  inverse_C1 : ContDiff ℝ 1 (uncurry A.sf)
  period_C1 : ContDiff ℝ 1 A.P
  period_deriv : ∀ t, HasDerivAt A.P (A.P' t) t

def ExactSourceRegularity.ofSource
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ExactSourceRegularity A P0 kh where
  periodLower_eq := rfl
  kap_eq := rfl
  front_C1 := A.front_contDiff
  angle_C1 := A.angle_contDiff
  steering_C1 := A.steering_contDiff
  inverse_C1 := A.sf_contDiff
  period_C1 := A.period_contDiff
  period_deriv := A.period_deriv

/-- Legacy smoothness or exact stopped-clock regularity. -/
inductive SourceRegularity
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (periodLower kap : ℝ) : Type
  | smooth (certificate : FiniteSmoothRearFamilyMarkingAwareSmoothSource.SmoothSource A periodLower kap)
  | exact (certificate : ExactSourceRegularity A periodLower kap)

/-- The stored source steering, normalized to unit spatial period. -/
structure ExactNormalizedSteering
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  (E : ExactSourceRegularity A periodLower kap) where
  delta : ℝ → ℝ → ℝ
  equation : ∀ t sigma, HasDerivAt (delta t)
    (A.P t * (A.K t (A.P t * sigma) - Real.sin (delta t sigma))) sigma
  strip : ∀ t sigma, delta t sigma ∈ Icc (0 : ℝ) (Real.arcsin kap)
  periodic : ∀ t, Periodic (delta t) 1
  contDiff : ContDiff ℝ 1 (uncurry delta)

def ExactNormalizedSteering.ofSource
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ExactNormalizedSteering (ExactSourceRegularity.ofSource A) := by
  let delta : ℝ → ℝ → ℝ := fun t sigma ↦ A.delta t (A.P t * sigma)
  refine { delta := delta, equation := ?_, strip := ?_, periodic := ?_, contDiff := ?_ }
  · intro t sigma
    have hs : HasDerivAt (fun z : ℝ ↦ A.P t * z) (A.P t) sigma := by
      simpa using (hasDerivAt_id sigma).const_mul (A.P t)
    convert (A.steering t (A.P t * sigma)).comp sigma hs using 1 <;>
      simp [delta, mul_comm]
  · intro t sigma
    exact ⟨A.strip_nonnegative t (A.P t * sigma), A.strip_le t (A.P t * sigma)⟩
  · intro t sigma
    simpa [delta, mul_add] using A.steering_periodic t (A.P t * sigma)
  · have hmap : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦
        (p.1, A.P p.1 * p.2)) :=
      contDiff_fst.prodMk ((A.period_contDiff.comp contDiff_fst).mul contDiff_snd)
    simpa [delta, uncurry] using A.steering_contDiff.comp hmap

/-- Steering data indexed by the chosen regularity branch. -/
inductive NormalizedSteering
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax} :
    SourceRegularity A periodLower kap → Type
  | smooth (S : FiniteSmoothRearFamilyMarkingAwareSmoothSource.SmoothSource A periodLower kap)
      (data : FiniteSmoothRearFamilyMarkingAwareSmoothSource.NormalizedSteering S) :
      NormalizedSteering (.smooth S)
  | exact (E : ExactSourceRegularity A periodLower kap)
      (data : ExactNormalizedSteering E) :
      NormalizedSteering (.exact E)

namespace NormalizedSteering

def delta {R : SourceRegularity A periodLower kap}
    (D : NormalizedSteering R) : ℝ → ℝ → ℝ := by
  cases D with
  | smooth _ d => exact d.delta
  | exact _ d => exact d.delta

def arclength {R : SourceRegularity A periodLower kap}
    (D : NormalizedSteering R) : ℝ → ℝ → ℝ :=
  fun t s ↦ D.delta t (s / period A t)

theorem exact_contDiff {E : ExactSourceRegularity A periodLower kap}
    (D : NormalizedSteering (.exact E)) : ContDiff ℝ 1 (uncurry D.delta) := by
  cases D with
  | exact _ d => exact d.contDiff

end NormalizedSteering

def nextFront {R : SourceRegularity A periodLower kap}
    (D : NormalizedSteering R) (sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℂ :=
  rearOwn (front A) (angle A) D.arclength sf

def nextAngle {R : SourceRegularity A periodLower kap}
    (D : NormalizedSteering R) (sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  rearOwnAngle (angle A) D.arclength sf

def nextCurvature {R : SourceRegularity A periodLower kap}
    (D : NormalizedSteering R) (sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x ↦ Real.tan (D.arclength t (sf t x))

def nextPeriod {R : SourceRegularity A periodLower kap}
    (D : NormalizedSteering R) : ℝ → ℝ :=
  fun t ↦ rearArclength (D.arclength t) (period A t)

/-- Primitive time, Jacobi, and mixed witnesses of the stored source itself. -/
structure ExactSuccessorRegularity
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : ExactSourceRegularity A periodLower kap}
    (_D : NormalizedSteering (.exact E)) where
  rear_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ rearOwn A.F A.Theta A.delta A.sf r x) (A.Ydot t x) t
  rear_angle_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ rearOwnAngle A.Theta A.delta A.sf r x) (A.alphaT t x) t
  rear_curvature_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ Real.tan (A.delta r (A.sf r x))) (A.kT t x) t
  rear_angle_time_continuous : Continuous (uncurry A.alphaT)
  rear_curvature_time_continuous : Continuous (uncurry A.kT)
  jacobi : ∀ t x, HasDerivAt
    (fun y ↦ frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t y)
    (A.etaF t (A.sf t x) / Real.cos (A.delta t (A.sf t x)) -
      frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t x) x
  gS_deriv : ∀ t x, HasDerivAt
    (fun y ↦ A.etaF t (A.sf t y) / Real.cos (A.delta t (A.sf t y)))
    (A.gS t x) x
  angleTime_spatial : ∀ t x, HasDerivAt (A.alphaT t) (A.kT t x) x
  mixed_derivative : ∀ t x, ∃ Z : ℂ,
    HasDerivAt
      (fun r ↦ Complex.exp
        (Complex.I * (rearOwnAngle A.Theta A.delta A.sf r x : ℂ))) Z t ∧
    HasDerivAt
      (fun y ↦
        (frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t y : ℂ) *
            Complex.exp (Complex.I * (rearOwnAngle A.Theta A.delta A.sf t y : ℂ)) +
        (frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t y : ℂ) *
            (Complex.I * Complex.exp
              (Complex.I * (rearOwnAngle A.Theta A.delta A.sf t y : ℂ)))) Z x

def ExactSuccessorRegularity.ofSource
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ExactSuccessorRegularity
      (NormalizedSteering.exact (ExactSourceRegularity.ofSource A)
        (ExactNormalizedSteering.ofSource A)) where
  rear_time_deriv := A.rear_time_deriv
  rear_angle_time_deriv := A.rear_angle_time_deriv
  rear_curvature_time_deriv := A.rear_curvature_time_deriv
  rear_angle_time_continuous := A.rear_angle_time_continuous
  rear_curvature_time_continuous := A.rear_curvature_time_continuous
  jacobi := A.jacobi
  gS_deriv := A.gS_deriv
  angleTime_spatial := A.rear_angle_time_spatial
  mixed_derivative := A.mixed_derivative

structure ExactSidecars
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) where
  source : ExactSourceRegularity A P0 kh
  steering : ExactNormalizedSteering source
  successor : ExactSuccessorRegularity (.exact source steering)

def ExactSidecars.ofSource
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ExactSidecars A where
  source := ExactSourceRegularity.ofSource A
  steering := ExactNormalizedSteering.ofSource A
  successor := ExactSuccessorRegularity.ofSource A

/-- Legacy all-order successor regularity or the primitive exact C1 branch. -/
inductive SuccessorRegularity
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax} :
    {R : SourceRegularity A periodLower kap} → NormalizedSteering R → Type
  | smooth (S : FiniteSmoothRearFamilyMarkingAwareSmoothSource.SmoothSource A periodLower kap)
      (D : FiniteSmoothRearFamilyMarkingAwareSmoothSource.NormalizedSteering S)
      (certificate : FiniteSmoothRearFamilyMarkingAwareSmoothSource.SuccessorRegularity D) :
      SuccessorRegularity (.smooth S D)
  | exact (E : ExactSourceRegularity A periodLower kap)
      (D : ExactNormalizedSteering E)
      (certificate : ExactSuccessorRegularity (.exact E D)) :
      SuccessorRegularity (.exact E D)

/-- Canonical embedding of every legacy triple. -/
def ofLegacy (S : FiniteSmoothRearFamilyMarkingAwareSmoothSource.SmoothSource A periodLower kap)
    (D : FiniteSmoothRearFamilyMarkingAwareSmoothSource.NormalizedSteering S) (R : FiniteSmoothRearFamilyMarkingAwareSmoothSource.SuccessorRegularity D) :
    Σ source : SourceRegularity A periodLower kap,
      Σ steering : NormalizedSteering source, SuccessorRegularity steering :=
  ⟨.smooth S, .smooth S D, .smooth S D R⟩

end FiniteSmoothRearFamilyMarkingAwareRegularitySum
