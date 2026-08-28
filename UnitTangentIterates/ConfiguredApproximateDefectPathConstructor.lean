import UnitTangentIterates.ConfiguredApproximateDefectPath
import UnitTangentIterates.TwoCapPairsAssembly

/-! # Constructor for configured approximate defect residuals

The configured weighted sequence already fixes the model curvature constants,
while the model-orbit constructor supplies the marked front and its perimeter.
This module removes those bookkeeping facts from the genuine defect-path
boundary.  What remains is endpoint curvature smoothness, identification of
the selected rear endpoint, and uniform quantitative domination.
-/

noncomputable section

open Function MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredApproximateDefectPathConstructor

open ModelOrbitDefect CurvatureInterpolation InterpolationEstimate
  InterpolationPathDist InterpolationVariableSpeedConstants
  InterpolationControlledJunctionFinal
  ProfiledInterpolationBoundsConstructor
  PathMetric.WeightedMarkedDefectThreshold

/-- The genuinely analytic residual after the configured model orbit has been
constructed.  The front endpoint is absent: it follows from the marked model
orbit's perimeter and arclength evaluation. -/
structure Residual
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (B : Data → Data) (Q : ℕ → Data)
    (P0 P1 G1 Cg defectScale : ℝ) : Prop where
  rear_endpoint : ∀ n (Phi : ℝ → ℝ → ℝ),
    (∀ u, Phi 0 u = 2 * D.Hs n * u) →
    (∀ u t, HasDerivAt (fun r ↦ Phi r u)
      (InterpolationGauge.gaugeField
        (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
        (D.model.configs n).kH D.model.thetaBase (D.Hs n) t (Phi t u)) t) →
    ∀ u, (B (Q (n + 1))).1 u =
      interpCurve (D.model.configs n).kH D.model.thetaBase (D.Hs n) (Phi 1 u)
  P0_pos : 0 < P0
  P0_le : ∀ n, P0 ≤ interpolationP0 D.kstar D.kd (D.Hs n)
    (curvDist
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      (D.model.configs n).kH (D.Hs n))
  P1_dom : ∀ n, costFac D.kstar (D.Hs n)
    (curvDist
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      (D.model.configs n).kH (D.Hs n)) ≤ P1
  G1_dom : ∀ n, interpolationG1 D.kstar D.kd (D.Hs n)
    (curvDist
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      (D.model.configs n).kH (D.Hs n)) ≤ G1
  Cg_dom : ∀ n, interpolationCgFinal D.kstar D.kd (D.Hs n)
    (curvDist
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      (D.model.configs n).kH (D.Hs n)) ≤ Cg
  cost_dom : ∀ n,
    interpPathCost D.kstar D.kd
      (CurvatureStabilityL1.l1Modulus (2 * D.kd)
        (curvDist
          (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
          (D.model.configs n).kH (D.Hs n)) (D.Hs n))
      (D.Hs n)
      (curvDist
        (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
        (D.model.configs n).kH (D.Hs n)) ≤
    canonicalMarkedDefect D.matchCoefficient defectScale D.kstar D.kd
      D.beta D.Hs n

/-- The standard model-orbit output discharges both the redundant configured
constant equalities and the front half of the interpolation endpoint clause. -/
def Residual.toConfiguredResidual
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {B : Data → Data} {Q : ℕ → Data}
    {P0 P1 G1 Cg defectScale : ℝ}
    (R : Residual D B Q P0 P1 G1 Cg defectScale)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n)) :
    ConfiguredApproximateDefectPath.Residual
      D B Q P0 P1 G1 Cg defectScale where
  model_kstar := D.model_kstar
  model_kd := D.model_kd
  KP_C2 := D.model_KP_C2
  kH_C2 := D.model_kH_C2
  endpoints := by
    intro n Phi hPhi0 hPhid
    constructor
    · intro u
      have hHne : 2 * D.Hs n ≠ 0 := by
        exact mul_ne_zero (by norm_num) (D.model.separation_pos n).ne'
      calc
        (Q n).1 u = ev (Q n) (2 * D.Hs n * u) := by
          simp [ev, (hQ n).1, hHne]
        _ = TwoCapPairsAssembly.front (D.kappas n) D.model.thetaBase
              (D.Hs n) (2 * D.Hs n * u) := by rw [(hQ n).2]
        _ = interpCurve
              (modelCurvature (D.model.configs n).yu
                (D.model.configs n).yu' (D.Hs n))
              D.model.thetaBase (D.Hs n) (2 * D.Hs n * u) := by
                rw [D.model.curvature_eq n]
                rfl
    · exact R.rear_endpoint n Phi hPhi0 hPhid
  P0_pos := R.P0_pos
  P0_le := R.P0_le
  P1_dom := R.P1_dom
  G1_dom := R.G1_dom
  Cg_dom := R.Cg_dom
  cost_dom := R.cost_dom

/-- Family-form defect path using only the reduced analytic residual. -/
theorem hdefect
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {B : Data → Data} {Q : ℕ → Data}
    {P0 P1 G1 Cg defectScale : ℝ}
    (R : Residual D B Q P0 P1 G1 Cg defectScale)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n)) :
    ∀ n : ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
        cost Lambda ≤ canonicalMarkedDefect D.matchCoefficient defectScale
          D.kstar D.kd D.beta D.Hs n + eta ∧
        NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
          P0 P1 D.kstar G1 Cg Lambda :=
  ConfiguredApproximateDefectPath.hdefect D (R.toConfiguredResidual hQ)

end ConfiguredApproximateDefectPathConstructor
