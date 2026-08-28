import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierScalar
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledPreCarrier

/-!
# Configured multiplier-aware recost pre-carrier

This module removes the scalar-density callback from the recosted pre-carrier.
The only quantitative input retained here is the canonical recost cost estimate;
the final closing output supplies the truthful multiplier and mass budget.
-/

open scoped Topology

namespace ConfiguredRecursiveEdgeRecostMultiplierPreCarrier

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
open ConfiguredRecursiveEdgeRecostMultiplierClosing
open FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
open FiniteSmoothRearFamilyMarkingAwareAppliedSource
open FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
open FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
open FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
open FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
open FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
open FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource

noncomputable def input
    {P0u khatu Qmaxu : ℕ → ℝ} {j : ℕ}
    {S : Stage P0u (fun _ => sourceKh) khatu Qmaxu j}
    {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
    {P0Next khatNext eps : ℝ}
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J}
    (Rclose : RecostClosingOutput J O)
    (r : ℕ)
    (selected : ExactSelected S.source)
    (pre : PreTransport selected)
    (gauge : RearOwnFrameGaugeFlowReanchoring.Gauge (xi pre))
    (shifted : ShiftedTransport pre gauge)
    (scalar : @Scalar S.start S.rear S.Gamma
      (P0u j) sourceKh (khatu j) (Qmaxu j)
      sourceKh P0Next khatNext
        (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap Rclose.data r)
      S.source)
    (P0_pos : 0 < P0Next)
    (jets :
      FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
        C.geometric.output.chosen eps)
    (eps_le_quarter : eps ≤ 1 / 4)
    (heta : Continuous (Function.uncurry C.geometric.output.chosen.Delta.eta))
    (heta1 : Continuous (Function.uncurry C.geometric.output.chosen.c2.eta1))
    (heta2 : Continuous (Function.uncurry C.geometric.output.chosen.c2.eta2))
    (bounds : DirectBounds C.geometric.output.chosen selected pre gauge shifted
      sourceKh_nonnegative sourceKh_lt_one scalar P0_pos
      C.geometric.output.chosen.c2 heta heta1 heta2)
    (rawSlice : AnalyticSuccessorSliceFacts
      (rawSource C.geometric.output.chosen selected pre gauge shifted
        sourceKh_nonnegative sourceKh_lt_one scalar P0_pos))
    (hcost :
      (carrier C.geometric.output.chosen C.geometric.output.chosen.c2
        heta heta1 heta2).cost ≤
        4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 *
        (2 * ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostPeriodScale
          Rclose.data r *
          ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect Rclose.data (r + 1))) :
    ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
      P0Next sourceKh khatNext
        (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap Rclose.data r) := by
  exact
    { selected := selected
      pre := pre
      gauge := gauge
      shifted := shifted
      kh_nonnegative := sourceKh_nonnegative
      kh_lt_one := sourceKh_lt_one
      scalar := scalar
      P0_pos := P0_pos
      eps := eps
      jets := jets
      eps_le_quarter := eps_le_quarter
      bounds := bounds
      recostScalar :=
        ConfiguredRecursiveEdgeRecostMultiplierScalar.recostScalar
          Rclose r C.geometric.output.chosen C.geometric.output.chosen.c2
          heta heta1 heta2 hcost
      rawSlice := rawSlice }

/-- Erase only the multiplier-density layer.  The resulting source is used to
reuse the existing normalized-component history proof; it is not identified
with the scaled source, whose `m` and `Dd` fields are different. -/
noncomputable def unscaled
    {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
    {S : Stage P0u khu khatu Qmaxu j}
    {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
    {P0Next khNext khatNext QmaxNext : ℝ}
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
      P0Next khNext khatNext QmaxNext) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Input C
      P0Next khNext khatNext QmaxNext :=
  { selected := I.selected
    pre := I.pre
    gauge := I.gauge
    shifted := I.shifted
    kh_nonnegative := I.kh_nonnegative
    kh_lt_one := I.kh_lt_one
    scalar := I.scalar
    P0_pos := I.P0_pos
    eps := I.eps
    jets := I.jets
    eps_le_quarter := I.eps_le_quarter
    bounds := I.bounds
    rawSlice := I.rawSlice }

theorem source_phi1_eq_unscaled
    {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
    {S : Stage P0u khu khatu Qmaxu j}
    {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
    {P0Next khNext khatNext QmaxNext : ℝ}
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
      P0Next khNext khatNext QmaxNext) :
    I.source.phi1 = (unscaled I).source.phi1 := by
  rw [I.source_phi1_eq, (unscaled I).source_phi1_eq]

theorem source_period_eq_unscaled
    {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
    {S : Stage P0u khu khatu Qmaxu j}
    {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
    {P0Next khNext khatNext QmaxNext : ℝ}
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
      P0Next khNext khatNext QmaxNext) :
    I.source.P = (unscaled I).source.P := by
  rw [I.source_period_eq, (unscaled I).source_period_eq]

/-- Scaling the density envelope does not change the selected rear marking.
This is the compatibility needed to reuse phase normalization proved for the
unscaled direct recost successor. -/
@[simp] theorem source_selectedRearData_eq_unscaled
    {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
    {S : Stage P0u khu khatu Qmaxu j}
    {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
    {P0Next khNext khatNext QmaxNext : ℝ}
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
      P0Next khNext khatNext QmaxNext) (t : ℝ) :
    I.source.selectedRearData t = (unscaled I).source.selectedRearData t := rfl

/-- The multiplier envelope also leaves the normalized terminal unit-tangent
datum unchanged. -/
@[simp] theorem source_unitTangentData_eq_unscaled
    {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
    {S : Stage P0u khu khatu Qmaxu j}
    {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
    {P0Next khNext khatNext QmaxNext : ℝ}
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
      P0Next khNext khatNext QmaxNext) :
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
        I.source =
      FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
        (unscaled I).source := rfl

end ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
