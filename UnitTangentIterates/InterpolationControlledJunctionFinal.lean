import Mathlib
import UnitTangentIterates.InterpolationVariableSpeedConstants
import UnitTangentIterates.FlowDerivativeTimeChange
import UnitTangentIterates.InterpolationFrenetEvolution
import UnitTangentIterates.InterpolationGaugeNormalRateOutput

/-! # Final controlled-junction output of curvature interpolation -/

noncomputable section

open Function MarkedSpace PathMetric

namespace InterpolationControlledJunctionFinal

open InterpolationPathDist InterpolationFrame InterpolationNormal PathMetric.NormalPath
  InterpolationVariableSpeedConstants

/-- Explicit second-flow ceiling used by the interpolation controlled
junction. -/
def interpolationG1 (kstar kd L eps : ℝ) : ℝ :=
  rate2Bound kstar kd L eps * (2 * L) ^ 2 *
    Real.exp (2 * rate1Bound kstar L eps)

/-- Public final adapter.  The hypothesis `hpath` is exactly the strengthened
conclusion of the interpolation specialization of
`GaugeNormalRateFundamental`; all constants in the resulting controlled stage
are fixed here, and its spatial C2 data is attached through the exported normal
rate identity rather than through equality with another constructed path. -/
theorem exists_interpolationControlledJunctionOutput
    {p q : Data} {k0 k1 : ℝ → ℝ} {theta0 L kstar kd dsup eps : ℝ}
    {Phi : ℝ → ℝ → ℝ}
    (C : PathEtaSpatialC2Certificate k0 k1 theta0 L Phi)
    (hpath : ∃ Gamma : NormalPath p q,
      Gamma.X 0 = p.1 ∧ Gamma.X Gamma.T = q.1 ∧
      Gamma.eta = pathEta k0 k1 theta0 L Phi ∧
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        (interpolationP0 kstar kd L eps)
        (costFac kstar L eps) kstar
        (interpolationG1 kstar kd L eps)
        (interpolationCgFinal kstar kd L eps) Gamma ∧
      cost Gamma ≤ interpPathCost kstar kd dsup L eps) :
    ∃ I : InterpolationControlledJunctionOutput p q
        (interpolationP0 kstar kd L eps)
        (costFac kstar L eps) kstar
        (interpolationG1 kstar kd L eps)
        (interpolationCgFinal kstar kd L eps)
        (interpPathCost kstar kd dsup L eps),
      I.path.eta = pathEta k0 k1 theta0 L Phi := by
  exact InterpolationGaugeNormalRateOutput.exists_output_of_gaugeNormalRate C hpath

/-- Projection of the public output to the generic gauge-controlled stage
interface used by recursive controlled junctions. -/
theorem exists_gaugeControlledJunctionOutput
    {p q : Data} {k0 k1 : ℝ → ℝ} {theta0 L kstar kd dsup eps : ℝ}
    {Phi : ℝ → ℝ → ℝ}
    (C : PathEtaSpatialC2Certificate k0 k1 theta0 L Phi)
    (hpath : ∃ Gamma : NormalPath p q,
      Gamma.X 0 = p.1 ∧ Gamma.X Gamma.T = q.1 ∧
      Gamma.eta = pathEta k0 k1 theta0 L Phi ∧
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        (interpolationP0 kstar kd L eps)
        (costFac kstar L eps) kstar
        (interpolationG1 kstar kd L eps)
        (interpolationCgFinal kstar kd L eps) Gamma ∧
      cost Gamma ≤ interpPathCost kstar kd dsup L eps) :
    ∃ G : GaugeControlledJunctionOutput p q
        (interpolationP0 kstar kd L eps)
        (costFac kstar L eps) kstar
        (interpolationG1 kstar kd L eps)
        (interpolationCgFinal kstar kd L eps)
        (interpPathCost kstar kd dsup L eps),
      G.path.eta = pathEta k0 k1 theta0 L Phi := by
  obtain ⟨I, heta⟩ := exists_interpolationControlledJunctionOutput C hpath
  exact ⟨I.toGaugeShape, heta⟩

end InterpolationControlledJunctionFinal
