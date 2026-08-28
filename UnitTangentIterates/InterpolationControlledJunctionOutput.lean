import Mathlib
import UnitTangentIterates.InterpolationPathEtaSmoothChain
import UnitTangentIterates.GaugeControlledJunctionOutput
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed

/-! # Interpolation half of a controlled junction -/

noncomputable section

open Set Function MarkedSpace

namespace PathMetric

open NormalPath

/-- Downstream output of the smooth curvature-interpolation constructor.  The
constant-speed geometry is retained, while the variable-speed form used by
the common controlled-junction metric is derived with `G1 = Cg = 0`. -/
structure InterpolationControlledJunctionOutput
    (p q : Data) (P0 P1 khat G1 Cg E : ℝ) where
  path : NormalPath p q
  c2 : C2NormalPathData path
  start : path.X 0 = p.1
  finish : path.X path.T = q.1
  variableSpeed :
    NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath P0 P1 khat G1 Cg path
  cost_le : cost path ≤ E

/-- Package an interpolation path.  The variable-speed field is canonical and
does not need to be reproved by the interpolation constructor. -/
def InterpolationControlledJunctionOutput.ofVariableSpeed
    {p q : Data} {Gamma : NormalPath p q} {P0 P1 khat G1 Cg E : ℝ}
    (hC2 : C2NormalPathData Gamma)
    (hstart : Gamma.X 0 = p.1) (hfinish : Gamma.X Gamma.T = q.1)
    (hvar : NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
      P0 P1 khat G1 Cg Gamma)
    (hcost : cost Gamma ≤ E) :
    InterpolationControlledJunctionOutput p q P0 P1 khat G1 Cg E where
  path := Gamma
  c2 := hC2
  start := hstart
  finish := hfinish
  variableSpeed := hvar
  cost_le := hcost

/-- Optional specialization for a genuinely constant-speed interpolation
path.  The normal-gauge interpolation does not use this constructor in
general. -/
def InterpolationControlledJunctionOutput.ofConstantSpeed
    {p q : Data} {Gamma : NormalPath p q} {P0 P1 khat E : ℝ}
    (hC2 : C2NormalPathData Gamma)
    (hstart : Gamma.X 0 = p.1) (hfinish : Gamma.X Gamma.T = q.1)
    (hconst : NormalPathC2Increment.IsConstantSpeedNormalPath P0 P1 khat Gamma)
    (hcost : cost Gamma ≤ E) :
    InterpolationControlledJunctionOutput p q P0 P1 khat 0 0 E :=
  .ofVariableSpeed hC2 hstart hfinish
    (NormalPathC2IncrementVariableSpeed.isVariableSpeedNormalPath_of_constantSpeed
      Gamma hconst) hcost

/-- Forget only the stronger constant-speed information and expose exactly
the same path interface as a gauge-controlled stage. -/
def InterpolationControlledJunctionOutput.toGaugeShape
    {p q : Data} {P0 P1 khat G1 Cg E : ℝ}
    (I : InterpolationControlledJunctionOutput p q P0 P1 khat G1 Cg E) :
    GaugeControlledJunctionOutput p q P0 P1 khat G1 Cg E where
  path := I.path
  c2 := I.c2
  start := I.start
  finish := I.finish
  variableSpeed := I.variableSpeed
  cost_le := I.cost_le

/-- A gauge endpoint change of marking, stated in the concrete fieldwise form
normally exported by the endpoint construction, produces the generic
`ReparamJunctionCertificate` consumed by both interpolation and gauge stages. -/
def reparamJunctionCertificate_of_gaugeEndpoint
    {p q p' q' : Data} {Gamma : NormalPath p q}
    (phi phi1 phi2 : ℝ → ℝ) (m M N : ℝ)
    (hm : 0 < m)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hphi1c : Continuous phi1) (hphi2c : Continuous phi2)
    (hlow : ∀ u, m ≤ phi1 u) (hupper : ∀ u, |phi1 u| ≤ M)
    (hsecond : ∀ u, |phi2 u| ≤ N)
    (hzero : phi 0 = 0) (hone : phi 1 = 1)
    (hadd : ∀ u, phi (u + 1) = phi u + 1)
    (hphi1per : Periodic phi1 1) (hphi2per : Periodic phi2 1)
    (hstart : ∀ u, Gamma.X 0 (phi u) = p'.1 u)
    (hfinish : ∀ u, Gamma.X Gamma.T (phi u) = q'.1 u) :
    ReparamJunctionCertificate (p' := p') (q' := q') Gamma where
  phi := phi
  phi1 := phi1
  phi2 := phi2
  m := m
  M := M
  N := N
  m_pos := hm
  phi_deriv := hphi
  phi1_deriv := hphi1
  phi1_cont := hphi1c
  phi2_cont := hphi2c
  jacobian_lower := hlow
  jacobian_upper := hupper
  second_upper := hsecond
  phi_zero := hzero
  phi_one := hone
  phi_add_one := hadd
  phi1_periodic := hphi1per
  phi2_periodic := hphi2per
  start := hstart
  finish := hfinish

/-- Apply a gauge endpoint marking certificate to an interpolation output,
yielding the exact controlled stage used by recursive assembly. -/
theorem InterpolationControlledJunctionOutput.exists_controlledStage
    {p q p' q' : Data} {P0 P1 khat G1 Cg E : ℝ}
    (I : InterpolationControlledJunctionOutput p q P0 P1 khat G1 Cg E)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') I.path)
    (C : ReparamC2Certificate I.path I.c2 J) :
    ∃ Gamma' : NormalPath p' q',
      Nonempty (C2NormalPathData Gamma') ∧
      Gamma'.X 0 = p'.1 ∧ Gamma'.X Gamma'.T = q'.1 ∧
      cost Gamma' ≤ reparamCostConst J.m J.M J.N * E :=
  I.toGaugeShape.exists_controlledStage J C

end PathMetric
