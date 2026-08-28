import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink

/-!
# Intrinsic-front functional facts for the direct recost source

The direct successor's intrinsic front is only a rigid, time-dependent
normalized shift of the predecessor's selected rear.  Slice functional
invariance therefore supplies the exact regularity certificate before the
lightweight source interface erases time measurability.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostIntrinsicFunctional

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink
  FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  (W : ChosenPath Gamma A E.Phi a b)
  (S : ExactSelected A (kap := kap))
  (R : PreTransport S)
  (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
  (T : ShiftedTransport R G)
  (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
  (C : Scalar (A := A) (kap := kap) (P0Next := P0Next)
    (khatNext := khatNext) (QmaxNext := QmaxNext))
  (hP0 : 0 < P0Next)
  (hC2 : C2NormalPathData W.Delta)
  (heta : Continuous (uncurry W.Delta.eta))
  (heta1 : Continuous (uncurry hC2.eta1))
  (heta2 : Continuous (uncurry hC2.eta2))
  (B : DirectBounds W S R G T hkap0 hkap1 C hP0
    hC2 heta heta1 heta2)

/-- The normalized phase relating the direct successor's intrinsic front to
the predecessor's selected rear density. -/
def phase (t : ℝ) : ℝ :=
  sigma S G.q t / FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A t

/-- Exact intrinsic-front identity for the direct recost source. -/
theorem intrinsicFront_directSource_eq :
    intrinsicFront
      (directSource W S R G T hkap0 hkap1 C hP0 hC2 heta heta1 heta2 B) =
      fun t u => normalizedRearDensity A t (u + phase S R G t) := by
  funext t u
  have hR : FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A t ≠ 0 :=
    (A.rear_period_pos t).ne'
  simp only [intrinsicFront, directSource, rawSource,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.source,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.etaF,
    TimeDependentSpatialReanchoring.shift,
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period,
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod,
    normalizedRearDensity, phase]
  congr 1
  rw [mul_add]
  congr 1
  symm
  calc
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A t *
          (sigma S G.q t /
            FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A t) =
        FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A t *
          sigma S G.q t *
          (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A t)⁻¹ := by
      rw [div_eq_mul_inv]
      ring
    _ =
        sigma S G.q t *
          (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A t *
            (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A t)⁻¹) := by
      ring
    _ = sigma S G.q t := by rw [mul_inv_cancel₀ hR, mul_one]

/-- The theorem-produced intrinsic functional certificate for every direct
recost successor. -/
def intrinsicFrontFunctionalFacts :
    IntrinsicFrontFunctionalFacts
      (directSource W S R G T hkap0 hkap1 C hP0
        hC2 heta heta1 heta2 B) := by
  let F :=
    FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.normalizedRearFunctionalIntegrable
      (E := E)
  let H := functionalIntegrable_shift F (phase S R G)
    (FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.normalizedRearDensity_periodic
      (A := A))
  refine ⟨?_⟩
  rw [intrinsicFront_directSource_eq W S R G T hkap0 hkap1 C hP0
    hC2 heta heta1 heta2 B]
  exact H

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostIntrinsicFunctional
