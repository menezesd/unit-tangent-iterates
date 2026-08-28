import UnitTangentIterates.PhysicalArclengthSeparatedTransition
import UnitTangentIterates.ControlledJunctionPathFunctionalBounds

/-!
# Pre-erasure physical gauge-stage certificate

This package retains the component-separated long-gauge estimates, their
integrated physical normalization, and the terminal fixed-reparametrization
transition.  It is the boundary to store in a dependent chosen stage before
forgetting the path to the aggregate rich-family API.
-/

noncomputable section

open Set MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace EnrichedPhysicalGaugeStage

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  PhysicalArclengthJacobiTransition
  PhysicalArclengthSeparatedTransition

structure Output
    (front raw anchored : ℝ → ℝ → ℝ)
    (PF PR a mA MA NA CW C0 C10 C11 C20 C21 C22 K0 K1 K2 : ℝ) : Prop where
  flowed : GaugeNormalPathSeparated.FlowedBounds front raw
    CW C0 C10 C11 C20 C21 C22
  integrated : PhysicalArclengthSeparatedTransition.IntegratedBounds front raw
    CW C0 C10 C11 C20 C21 C22
  rawPhysical : PhysicalArclengthJacobiTransition.RawBounds
    PF PR front raw a K0 K1 K2
  transition : AnchoredJacobiStableTransition.Transition
    (PhysicalArclengthJacobiTransition.components PF front)
    (PhysicalArclengthJacobiTransition.components PR anchored)
    (a * (1 / mA)) MA NA K0 K1 K2

def Output.of_fixedReparam
    {front raw anchored : ℝ → ℝ → ℝ}
    {PF PR a mA MA NA CW C0 C10 C11 C20 C21 C22 K0 K1 K2 : ℝ}
    (hfront : FunctionalIntegrable front)
    (hraw : FunctionalIntegrable raw)
    (F : GaugeNormalPathSeparated.FlowedBounds front raw
      CW C0 C10 C11 C20 C21 C22)
    (D : PhysicalArclengthSeparatedTransition.Domination
      PF PR a CW C0 C10 C11 C20 C21 C22 K0 K1 K2)
    (hPR1 : 1 ≤ PR) (hMA : 0 ≤ MA) (hNA : 0 ≤ NA)
    (J : FixedReparamBounds raw anchored mA MA NA)
    (hmA : 0 < mA) :
    Output front raw anchored PF PR a mA MA NA
      CW C0 C10 C11 C20 C21 C22 K0 K1 K2 := by
  let I := PhysicalArclengthSeparatedTransition.IntegratedBounds.of_flowed
    hfront hraw F
  let R := I.toPhysical D
  exact
    { flowed := F
      integrated := I
      rawPhysical := R
      transition :=
        PhysicalArclengthJacobiTransition.transition_of_raw_and_fixedReparam
          hPR1 hmA hMA hNA R J }

/-- Specialization to the actual fixed endpoint diffeomorphism stored in a
controlled junction. -/
def Output.of_junction
    {pf qf pr qr pr' qr' : Data}
    {front : ℝ → ℝ → ℝ}
    (rawPath : NormalPath pr qr) (rawC2 : C2NormalPathData rawPath)
    (J : ReparamJunctionCertificate (p' := pr') (q' := qr') rawPath)
    {PF PR a CW C0 C10 C11 C20 C21 C22 K0 K1 K2 : ℝ}
    (hfront : FunctionalIntegrable front)
    (hraw : FunctionalIntegrable rawPath.eta)
    (hfinal : FunctionalIntegrable (reparamAtJunction rawPath rawC2 J).eta)
    (F : GaugeNormalPathSeparated.FlowedBounds front rawPath.eta
      CW C0 C10 C11 C20 C21 C22)
    (D : PhysicalArclengthSeparatedTransition.Domination
      PF PR a CW C0 C10 C11 C20 C21 C22 K0 K1 K2)
    (hPR1 : 1 ≤ PR) :
    Output front rawPath.eta (reparamAtJunction rawPath rawC2 J).eta
      PF PR a J.m J.M J.N CW C0 C10 C11 C20 C21 C22 K0 K1 K2 := by
  have hM : 0 ≤ J.M := (abs_nonneg (J.phi1 0)).trans (J.jacobian_upper 0)
  have hN : 0 ≤ J.N := (abs_nonneg (J.phi2 0)).trans (J.second_upper 0)
  apply Output.of_fixedReparam hfront hraw F D hPR1 hM hN
    (reparamAtJunction_bounds rawPath rawC2 J hraw hfinal) J.m_pos

end EnrichedPhysicalGaugeStage
