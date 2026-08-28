import UnitTangentIterates.ConfiguredGaugeFirstBaseHarnack
import UnitTangentIterates.ConstructedConfiguredInductiveTubeBudget

/-!
# Exact scalar boundary for configured front Harnack data

The physical selected-rear theorem supplies strictness for the rear endpoint,
not for the configured front which initializes each triangular row.  The
precise remaining analytic datum is therefore the scalar Harnack inequality
for the configured front curvature.  This module turns that inequality into
the full geometric certificate and transports it through the gauge-first
phase/rigid presentation.
-/

noncomputable section

open Function MarkedSpace PathMetric

namespace ConfiguredModelFrontHarnackAdapter

open ConfiguredGaugeFirstPhysicalSequence CurvatureInterpolation
  VariableMarkedTube

/-- Exact analytic property still required of the constructed periodized
fronts.  Unlike `LimitStrictnessDataH`, this contains no curve, marking, tube,
or transport callback. -/
def FrontHarnack (D : ConstructedConfiguredSequenceWeighted.Data) : Prop :=
  ∀ (n : ℕ) (a b : ℝ), a ≤ b →
    Real.exp (a - b) *
        (D.kappas n a / Real.sqrt (1 + D.kappas n a ^ 2)) ≤
      D.kappas n b / Real.sqrt (1 + D.kappas n b ^ 2)

/-- Natural construction-facing refinement: the already retained actual
half-ceilings together with the one missing scalar Harnack estimate.  An
upstream periodization proof can return this record without changing `Data`
or the existing public constructor. -/
structure DataWithActualHalfHarnack where
  actual : ConstructedConfiguredSequenceWeighted.DataWithActualHalf
  frontHarnack : FrontHarnack actual.data

/-- The scalar property is invariant under discarding a finite prefix. -/
theorem FrontHarnack.shift
    {D : ConstructedConfiguredSequenceWeighted.Data} (H : FrontHarnack D)
    (N : ℕ) : FrontHarnack
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N) := by
  intro n a b hab
  simpa [ConstructedConfiguredInductiveTubeBudget.WeightedData.shift] using
    H (N + n) a b hab

/-- The scalar configured-front inequality gives integrated strictness on the
canonical marked model front. -/
def modelStrictness
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data}
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (H : FrontHarnack D) (n : ℕ) :
    UnconditionalAssembly.LimitStrictnessDataH (Q n) where
  theta := CurvatureInterpolation.tangentAngle
    (D.kappas n) D.model.thetaBase
  k := D.kappas n
  curve_deriv := by
    intro s
    rw [(hQ n).2]
    exact TwoCapPairsAssembly.front_hasDerivAt
      (D.model.curvature_continuous n) s
  angle_deriv := fun s =>
    CurvatureInterpolation.hasDerivAt_tangentAngle
      (D.model.curvature_continuous n) s
  curvature_periodic := by
    rw [(hQ n).1]
    exact (D.model.curvature_periodic n).nat_mul 2
  curvature_nonnegative := fun s => (D.model_curvature_pos n s).le
  curvature_harnack := H n
  curvature_nonzero := ⟨0, (D.model_curvature_pos n 0).ne'⟩

/-- Fully geometric aligned-base Harnack certificates constructed from the
single scalar front-curvature property. -/
def baseHarnack
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (hdlt : 0 < dlt) (H : FrontHarnack D) :
    ∀ n, ArclengthHarnackCertificate (alignedQ S hQ n) :=
  ConfiguredGaugeFirstBaseHarnack.baseHarnack S hQ hdlt
    (modelStrictness hQ H)

end ConfiguredModelFrontHarnackAdapter
