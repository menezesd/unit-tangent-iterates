import Mathlib
import UnitTangentIterates.InterpolationControlledJunctionOutput
import UnitTangentIterates.InterpolationPathEtaC2Adapter
import UnitTangentIterates.GaugeNormalRateFundamental

/-! # Attaching interpolation C2 data to a gauge normal-rate path -/

noncomputable section

open Function MarkedSpace PathMetric

namespace InterpolationGaugeNormalRateOutput

open PathMetric.NormalPath

/-- The path returned by the gauge normal-rate construction can receive the
interpolation spatial-C2 certificate directly through its exported normal-rate
identity.  No equality with the path returned by another constructor is
needed. -/
def ofGaugeNormalRatePath
    {p q : Data} {Gamma : NormalPath p q}
    {k0 k1 : ℝ → ℝ} {theta0 L : ℝ} {Phi : ℝ → ℝ → ℝ}
    {P0 P1 khat G1 Cg E : ℝ}
    (C : InterpolationPathDist.PathEtaSpatialC2Certificate
      k0 k1 theta0 L Phi)
    (heta : Gamma.eta =
      InterpolationPathDist.pathEta k0 k1 theta0 L Phi)
    (hstart : Gamma.X 0 = p.1)
    (hfinish : Gamma.X Gamma.T = q.1)
    (hvar : NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
      P0 P1 khat G1 Cg Gamma)
    (hcost : cost Gamma ≤ E) :
    InterpolationControlledJunctionOutput p q P0 P1 khat G1 Cg E :=
  InterpolationControlledJunctionOutput.ofVariableSpeed
    (C.toC2NormalPathData heta) hstart hfinish hvar hcost

/-- Existential form matching the conclusion of
`GaugeNormalRateFundamental`: once that construction exports its curve,
normal-rate, and variable-speed identities, the controlled interpolation
output is immediate. -/
theorem exists_output_of_gaugeNormalRate
    {p q : Data} {k0 k1 : ℝ → ℝ} {theta0 L : ℝ}
    {Phi : ℝ → ℝ → ℝ} {P0 P1 khat G1 Cg E : ℝ}
    (C : InterpolationPathDist.PathEtaSpatialC2Certificate
      k0 k1 theta0 L Phi)
    (hpath : ∃ Gamma : NormalPath p q,
      Gamma.X 0 = p.1 ∧ Gamma.X Gamma.T = q.1 ∧
      Gamma.eta = InterpolationPathDist.pathEta k0 k1 theta0 L Phi ∧
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg Gamma ∧
      cost Gamma ≤ E) :
    ∃ I : InterpolationControlledJunctionOutput p q P0 P1 khat G1 Cg E,
      I.path.eta = InterpolationPathDist.pathEta k0 k1 theta0 L Phi := by
  obtain ⟨Gamma, hstart, hfinish, heta, hvar, hcost⟩ := hpath
  let I := ofGaugeNormalRatePath C heta hstart hfinish hvar hcost
  refine ⟨I, ?_⟩
  exact heta

end InterpolationGaugeNormalRateOutput
