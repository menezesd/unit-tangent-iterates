import Mathlib
import UnitTangentIterates.InterpolationControlledJunctionFinal
import UnitTangentIterates.InterpolationFrenetProfiled
import UnitTangentIterates.GaugeNormalRateFundamental

/-! # Assembly of the profiled interpolation gauge-normal-rate result -/

noncomputable section

open Function MarkedSpace PathMetric

namespace InterpolationGaugeNormalRateAssembly

open CurvatureInterpolation PathMetric.NormalPath
  InterpolationPathDist InterpolationFrame InterpolationNormal
  InterpolationVariableSpeedConstants InterpolationControlledJunctionFinal


/-- Convert the strengthened result of `GaugeNormalRateFundamental` into the
exact single-path package consumed by the public interpolation junction
constructor. -/
theorem hpath_of_gaugeNormalRate_result
    {p q : Data} {k0 k1 : ℝ → ℝ} {theta0 L kstar kd dsup eps : ℝ}
    {Phi : ℝ → ℝ → ℝ} {Gamma : NormalPath p q}
    (hT : Gamma.T = 1)
    (hX : ∀ t u, Gamma.X t u =
      interpCurve (kappaInterp k0 k1 (PathMetricCircle.B t)) theta0 L
        (Phi (PathMetricCircle.B t) u))
    (heta : Gamma.eta = pathEta k0 k1 theta0 L Phi)
    (hp : ∀ u, p.1 u = interpCurve k0 theta0 L (2 * L * u))
    (hq : ∀ u, q.1 u = interpCurve k1 theta0 L (Phi 1 u))
    (hPhi0 : ∀ u, Phi 0 u = 2 * L * u)
    (hvar : NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
      (interpolationP0 kstar kd L eps)
      (costFac kstar L eps) kstar
      (interpolationG1 kstar kd L eps)
      (interpolationCgFinal kstar kd L eps) Gamma)
    (hcost : cost Gamma ≤ interpPathCost kstar kd dsup L eps) :
    ∃ Delta : NormalPath p q,
      Delta.X 0 = p.1 ∧ Delta.X Delta.T = q.1 ∧
      Delta.eta = pathEta k0 k1 theta0 L Phi ∧
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        (interpolationP0 kstar kd L eps)
        (costFac kstar L eps) kstar
        (interpolationG1 kstar kd L eps)
        (interpolationCgFinal kstar kd L eps) Delta ∧
      cost Delta ≤ interpPathCost kstar kd dsup L eps := by
  refine ⟨Gamma, ?_, ?_, heta, hvar, hcost⟩
  · funext u
    rw [hX 0 u, PathMetricCircle.B_zero, hPhi0, hp]
    simp
  · funext u
    rw [hT, hX 1 u, PathMetricCircle.B_one, hq]
    simp

/-- Final public assembly: the profiled gauge-normal-rate path, its spatial C2
normal-rate certificate, its endpoints, explicit constants and interpolation
cost are returned as one controlled junction. -/
theorem exists_interpolationControlledJunctionOutput_of_gaugeNormalRate
    {p q : Data} {k0 k1 : ℝ → ℝ} {theta0 L kstar kd dsup eps : ℝ}
    {Phi : ℝ → ℝ → ℝ} {Gamma : NormalPath p q}
    (C : PathEtaSpatialC2Certificate k0 k1 theta0 L Phi)
    (hT : Gamma.T = 1)
    (hX : ∀ t u, Gamma.X t u =
      interpCurve (kappaInterp k0 k1 (PathMetricCircle.B t)) theta0 L
        (Phi (PathMetricCircle.B t) u))
    (heta : Gamma.eta = pathEta k0 k1 theta0 L Phi)
    (hp : ∀ u, p.1 u = interpCurve k0 theta0 L (2 * L * u))
    (hq : ∀ u, q.1 u = interpCurve k1 theta0 L (Phi 1 u))
    (hPhi0 : ∀ u, Phi 0 u = 2 * L * u)
    (hvar : NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
      (interpolationP0 kstar kd L eps)
      (costFac kstar L eps) kstar
      (interpolationG1 kstar kd L eps)
      (interpolationCgFinal kstar kd L eps) Gamma)
    (hcost : cost Gamma ≤ interpPathCost kstar kd dsup L eps) :
    ∃ I : InterpolationControlledJunctionOutput p q
        (interpolationP0 kstar kd L eps)
        (costFac kstar L eps) kstar
        (interpolationG1 kstar kd L eps)
        (interpolationCgFinal kstar kd L eps)
        (interpPathCost kstar kd dsup L eps),
      I.path.eta = pathEta k0 k1 theta0 L Phi := by
  apply exists_interpolationControlledJunctionOutput C
  exact hpath_of_gaugeNormalRate_result hT hX heta hp hq hPhi0 hvar hcost

/-- Convert the strengthened non-fundamental gauge output directly to the
public interpolation controlled junction. -/
theorem exists_interpolationControlledJunctionOutput_of_nonfundamental
    {p q : Data} {k0 k1 : ℝ → ℝ} {theta0 L kstar kd dsup eps : ℝ}
    {Phi : ℝ → ℝ → ℝ} {Gamma : NormalPath p q}
    (C : PathEtaSpatialC2Certificate k0 k1 theta0 L Phi)
    (hT : Gamma.T = 1)
    (hX : ∀ t u, Gamma.X t u =
      interpCurve (kappaInterp k0 k1 (PathMetricCircle.B t)) theta0 L
        (Phi (PathMetricCircle.B t) u))
    (heta : ∀ t u, Gamma.eta t u =
      pathEta k0 k1 theta0 L Phi t u)
    (hp : ∀ u, p.1 u = interpCurve k0 theta0 L (2 * L * u))
    (hq : ∀ u, q.1 u = interpCurve k1 theta0 L (Phi 1 u))
    (hPhi0 : ∀ u, Phi 0 u = 2 * L * u)
    (hvar : NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
      (interpolationP0 kstar kd L eps) (costFac kstar L eps) kstar
      (interpolationG1 kstar kd L eps)
      (interpolationCgFinal kstar kd L eps) Gamma)
    (hcost : cost Gamma ≤ interpPathCost kstar kd dsup L eps) :
    ∃ I : InterpolationControlledJunctionOutput p q
        (interpolationP0 kstar kd L eps) (costFac kstar L eps) kstar
        (interpolationG1 kstar kd L eps)
        (interpolationCgFinal kstar kd L eps)
        (interpPathCost kstar kd dsup L eps),
      I.path.eta = pathEta k0 k1 theta0 L Phi := by
  have heta' : Gamma.eta = pathEta k0 k1 theta0 L Phi :=
    funext fun t => funext fun u => heta t u
  exact exists_interpolationControlledJunctionOutput_of_gaugeNormalRate C hT hX
    heta' hp hq hPhi0 hvar hcost

end InterpolationGaugeNormalRateAssembly
