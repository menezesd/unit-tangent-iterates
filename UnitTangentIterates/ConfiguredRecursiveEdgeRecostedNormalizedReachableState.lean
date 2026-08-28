import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedPreCarrier
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedReachableFacts
import UnitTangentIterates.ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
import UnitTangentIterates.ConfiguredRecursiveEdgeNonaffineAncestryExtension
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostIntrinsicFunctional

/-!
# Normalized state carried by the reachable direct-recost recursion

This is the dependent state between two diagonal layers.  The raw chosen
path supplies the displayed metric edge, while the canonical recost carries
the next exact source.  The normalized nonaffine ancestry is extended before
the resulting split history is installed in a carrier row.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace ConfiguredRecursiveEdgeRecostedNormalizedReachableState

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeNonaffineAncestryExtension
  ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
  ConfiguredRecursiveEdgeNonaffineChosenMajorSplitHistory
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedReachableFacts
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison
  FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSource
  ControlledJunctionPathFunctionalBounds

variable {MA NA Etotal Dtarget : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
    RJ Etotal Dtarget}

variable {P0u khatu Qmaxu : ℕ → ℝ} {r depth : ℕ}
  {S : Stage P0u
    (fun _ => ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    khatu Qmaxu r}
  {P1 edgeDefect : ℝ}

/-- The exact source and normalized-history certificate retained at one
reachable node. -/
structure State (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
    RJ Etotal Dtarget) (S : Stage P0u
      (fun _ => ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      khatu Qmaxu r) (P1 : ℝ) (depth : ℕ) (edgeDefect : ℝ) where
  sourceFacts : SourceFacts O S.source P1 depth
  intrinsic : IntrinsicFrontFunctionalFacts S.source
  periodFloor : ∀ t, 1 ≤ rearPeriod S.source t
  ancestry : ConcreteAncestry (O := O) S.Gamma depth edgeDefect
  terminalJ_eq : ancestry.terminalJ = S.source.phi1
  terminalP_eq : ancestry.terminalP = S.source.P

namespace State

private theorem configuredSourceKh_pos :
    0 < ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
  rw [ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq]
  norm_num

theorem epsPrev_lt_one (H : State O S P1 depth edgeDefect)
    (hE : Etotal ≤ 1 / 8) : H.sourceFacts.eps < 1 := by
  have hmajor : O.major depth ≤ ∑' i, O.major i :=
    O.major_summable'.le_tsum depth (fun i _ => O.major_nonnegative' i)
  have h := H.sourceFacts.eps_le_major.trans
    (hmajor.trans O.major_tsum_le')
  linarith

theorem epsPrev_le_quarter (H : State O S P1 depth edgeDefect)
    (hE : Etotal ≤ 1 / 8) : H.sourceFacts.eps ≤ 1 / 4 := by
  have hmajor : O.major depth ≤ ∑' i, O.major i :=
    O.major_summable'.le_tsum depth (fun i _ => O.major_nonnegative' i)
  have h := H.sourceFacts.eps_le_major.trans
    (hmajor.trans O.major_tsum_le')
  linarith

variable {p0 khat0 qmax0 : ℝ}
  {C : Core S}
  {I : Input C p0
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0}

/-- Component function obtained by installing the new recosted target after
the established ancestry. -/
def nextV (H : State O S P1 depth edgeDefect)
    (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0) :=
  extendV H.ancestry.ancestry
    (markedPhysicalComponents I.source.phi1 I.source.P C.path.eta)

/-- The exact normalized nonaffine link from the current source to the direct
recost source.  All source/target comparison data are theorem-produced. -/
def link (H : State O S P1 depth edgeDefect)
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ O.major (depth + 1)) :
    NonaffineChosenLink O (H.nextV I) depth where
  p := S.start
  q := S.rear
  a := S.displayed
  b := C.geometric.output.jets.rear
  Gamma := S.Gamma
  P0 := P0u r
  khat := khatu r
  Qmax := Qmaxu r
  source := S.source
  applied := S.applied
  chosen := C.geometric.output.chosen
  sourceSlice := H.sourceFacts.slice
  P0Next := p0
  khatNext := khat0
  QmaxNext := qmax0
  targetPath := C.path
  target := I.source
  targetSlice := I.slice
  target_eta_eq := I.path_eta
  target_period_eq := I.source_period_eq
  target_phi1_eq := I.source_phi1_eq
  epsPrev := H.sourceFacts.eps
  epsCur := I.eps
  sourceJets := H.sourceFacts.jets
  chosenJets := I.jets
  epsPrev_le := H.sourceFacts.eps_le_major
  epsCur_le := hcur
  source_eq := by
    rw [nextV, extendV_of_le H.ancestry.ancestry _ (le_refl depth)]
    rw [H.ancestry.terminal_eq, H.terminalJ_eq, H.terminalP_eq]
  target_eq := by
    exact extendV_succ H.ancestry.ancestry _
  rawTransition := by
    have hsource := markedPhysicalComponents_nonnegative_of_sourceJets
      H.sourceFacts.jets (H.epsPrev_le_quarter hE)
    simpa [FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2] using
      (recostRawTransition C.geometric.output.chosen I.source
        configuredSourceKh_pos
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
        H.sourceFacts.nonaffine H.sourceFacts.functional H.intrinsic.functional
        H.sourceFacts.jets (H.epsPrev_lt_one hE)
        I.jets (lt_of_le_of_lt I.eps_le_quarter (by norm_num))
        H.periodFloor I.path_eta I.source_period_eq I.source_phi1_eq hsource)

/-- Extend the concrete ancestry onto the canonical recost path. -/
def nextAncestry (H : State O S P1 depth edgeDefect)
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ O.major (depth + 1)) :
    ConcreteAncestry (O := O) C.path (depth + 1) edgeDefect :=
  H.ancestry.snoc I.source.phi1 I.source.P
    (markedPhysicalComponents_nonnegative_of_sourceJets
      I.sourceJets I.eps_le_quarter)
    (H.link C I hE hcur)

/-- The ancestry index is insensitive to a path whose density is equal.  This
is the precise bridge from the recost carrier back to the raw chosen path
consumed by the metric split history. -/
def castEta
    {p q p' q' : Data} {Gamma : NormalPath p q} {Gamma' : NormalPath p' q'}
    {depth : ℕ} {edgeDefect : ℝ}
    (H : ConcreteAncestry (O := O) Gamma depth edgeDefect)
    (heta : Gamma'.eta = Gamma.eta) :
    ConcreteAncestry (O := O) Gamma' depth edgeDefect where
  ancestry :=
    { V := H.ancestry.V
      baseJ := H.ancestry.baseJ
      baseP := H.ancestry.baseP
      baseEta := H.ancestry.baseEta
      base_eq := H.ancestry.base_eq
      d_nonnegative := H.ancestry.d_nonnegative
      components_nonnegative := H.ancestry.components_nonnegative
      initial_le := H.ancestry.initial_le
      links := H.ancestry.links }
  terminalJ := H.terminalJ
  terminalP := H.terminalP
  terminal_eq := by simpa [heta] using H.terminal_eq

/-- Raw-path form of the newly extended ancestry. -/
def nextRawAncestry (H : State O S P1 depth edgeDefect)
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ O.major (depth + 1)) :
    ConcreteAncestry (O := O) C.geometric.output.chosen.Delta
      (depth + 1) edgeDefect :=
  castEta (H.nextAncestry C I hE hcur) I.path_eta.symm

@[simp] theorem nextRawAncestry_terminalJ
    (H : State O S P1 depth edgeDefect)
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ O.major (depth + 1)) :
    (H.nextRawAncestry C I hE hcur).terminalJ =
      C.geometric.output.chosen.phi1 := by
  rw [nextRawAncestry, castEta, nextAncestry]
  exact I.source_phi1_eq

@[simp] theorem nextRawAncestry_terminalP
    (H : State O S P1 depth edgeDefect)
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ O.major (depth + 1)) :
    (H.nextRawAncestry C I hE hcur).terminalP = rearPeriod S.source := by
  rw [nextRawAncestry, castEta, nextAncestry]
  exact I.source_period_eq

/-- The four terminal regularity facts required by the scaled-history
endpoint are automatic for an exact chosen path. -/
structure ChosenTerminalIntegrability (C : Core S) : Prop where
  hPW : IntervalIntegrable
    (fun t => rearPeriod S.source t *
      ∫ u in (0 : ℝ)..1, |C.geometric.output.chosen.Delta.eta t u|) volume 0 1
  hS1P : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 1
      (C.geometric.output.chosen.Delta.eta t)) / rearPeriod S.source t)
      volume 0 1
  hS2P : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 2
      (C.geometric.output.chosen.Delta.eta t)) / rearPeriod S.source t ^ 2)
      volume 0 1

def chosenTerminalIntegrability (C : Core S) :
    ChosenTerminalIntegrability C := by
  let F :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource
      C.geometric.output.chosen
  have hR : Continuous (rearPeriod S.source) :=
    Differentiable.continuous fun t =>
      (S.applied.frame.period_deriv t).differentiableAt
  have hRinv : Continuous (fun t => (rearPeriod S.source t)⁻¹) :=
    hR.inv₀ fun t => (S.source.rear_period_pos t).ne'
  have hR2inv : Continuous (fun t => (rearPeriod S.source t ^ 2)⁻¹) :=
    (hR.pow 2).inv₀ fun t => (sq_pos_of_pos (S.source.rear_period_pos t)).ne'
  exact
    { hPW := by
        simpa [mul_comm] using F.w.mul_continuousOn hR.continuousOn
      hS1P := by
        simpa [div_eq_mul_inv] using F.s1.mul_continuousOn hRinv.continuousOn
      hS2P := by
        simpa [div_eq_mul_inv] using F.s2.mul_continuousOn hR2inv.continuousOn }

/-- Complete the raw chosen row after extending the normalized ancestry.  The
remaining arguments are only the scalar period cap facts used by the
configured diagonal. -/
def completion (H : State O S P1 depth edgeDefect)
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ O.major (depth + 1))
    (L : ℝ) (hL : 1 ≤ L) (hL2 : 2 ≤ L ^ 2)
    (hPL : ∀ t ∈ Icc (0 : ℝ) 1, rearPeriod S.source t ≤ L) :
    Completion C I Etotal
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2
      (L ^ 2 * (2 * edgeDefect)) := by
  let W := C.geometric.output.chosen
  let Araw := H.nextRawAncestry C I hE hcur
  let F :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource
      W
  let T := chosenTerminalIntegrability C
  let R :=
    FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.normalizedRearFunctionalIntegrable
      (E := S.applied)
  have hRc : Continuous (rearPeriod S.source) :=
    Differentiable.continuous fun t =>
      (S.applied.frame.period_deriv t).differentiableAt
  have hrearW : IntervalIntegrable
      (fun t => rearPeriod S.source t *
        ∫ u in (0 : ℝ)..1,
          |FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity
            S.source t u|) volume 0 1 := by
    simpa [mul_comm] using R.w.mul_continuousOn hRc.continuousOn
  have hjac : IntervalIntegrable
      (fun t => ∫ u in (0 : ℝ)..1,
        W.phi1 t u * |W.Delta.eta t u|) volume 0 1 :=
    chosen_jacobianPhysicalW_integrable W H.sourceFacts.nonaffine hrearW
  have heta : ∀ t, Continuous (W.Delta.eta t) := fun t =>
    C.eta_continuous.comp (continuous_const.prodMk continuous_id)
  let split := Araw.toScaledSplitHistoryOfChosen W
    (H.nextRawAncestry_terminalJ C I hE hcur)
    (H.nextRawAncestry_terminalP C I hE hcur)
    I.jets (I.eps_le_quarter.trans (by norm_num)) hE L hL hL2
    (fun t _ => H.periodFloor t) hPL F heta hjac T.hPW T.hS1P T.hS2P
  exact
    { V := fun j => scaleAll (L ^ 2) (Araw.ancestry.V j)
      major := O.major
      depth := depth + 1
      splitHistory := by
        rw [GeometricInput.rawPath, C.geometric.output.stage_eq]
        exact split }

/-- Exact intrinsic-front certificate for the new direct source. -/
def nextIntrinsic (C : Core S)
    (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0) :
    IntrinsicFrontFunctionalFacts I.source := by
  simpa [Input.source] using
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostIntrinsicFunctional.intrinsicFrontFunctionalFacts
      C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
      I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
      C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
      C.eta2_continuous I.bounds)

end State

end ConfiguredRecursiveEdgeRecostedNormalizedReachableState
