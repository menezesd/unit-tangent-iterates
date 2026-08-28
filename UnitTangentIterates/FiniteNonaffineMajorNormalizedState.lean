import UnitTangentIterates.FiniteNonaffineMajorHistory
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedPreCarrier
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostIntrinsicFunctional
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPreCarrier

/-! # Reachable normalized state over an explicit history major -/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace FiniteNonaffineMajorNormalizedState

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
  FiniteHistoryMajorBudget
  FiniteNonaffineMajorHistory
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison
  FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSource
  ControlledJunctionPathFunctionalBounds

variable {Etotal : ℝ} (B : MajorBudget Etotal)

/-- Current source facts charged to an explicit major slot. -/
structure SourceFacts
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (P1 : ℝ) (j : ℕ) where
  slice :
    FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessorSliceFacts A
  periodUpper_le : slice.periodUpper ≤ P1
  functional : FunctionalIntegrable Gamma.eta
  eps : ℝ
  jets : SourceNormalizedJetBounds A eps
  eps_le_major : eps ≤ B.major j

namespace SourceFacts

def nonaffine
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax P1 : ℝ}
    {j : ℕ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (F : SourceFacts B A P1 j) :
    FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.Nonaffine.Facts
      A P1 F.slice.markingLower F.slice.markingUpper :=
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.Nonaffine.Facts.ofAnalytic
    F.slice F.periodUpper_le

/-- The direct recost input supplies all qualitative successor facts; only
the new period ceiling and its explicit major comparison remain scalar. -/
def ofInput
    {P0u khu khatu Qmaxu : ℕ → ℝ} {r : ℕ}
    {S : Stage P0u khu khatu Qmaxu r}
    {C : Core S} {p0 kh0 khat0 qmax0 P1 : ℝ}
    (I : Input C p0 kh0 khat0 qmax0) (j : ℕ)
    (hP1 : I.slice.periodUpper ≤ P1)
    (heps : I.eps ≤ B.major (j + 1)) :
    SourceFacts B I.source P1 (j + 1) where
  slice := I.slice
  periodUpper_le := hP1
  functional := by
    have F :=
      FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource
        C.geometric.output.chosen
    simpa [I.path_eta] using F
  eps := I.eps
  jets := I.sourceJets
  eps_le_major := heps

end SourceFacts

variable {P0u khatu Qmaxu : ℕ → ℝ} {r depth : ℕ}
  {S : Stage P0u (fun _ =>
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh) khatu Qmaxu r}
  {P1 edgeDefect : ℝ}

/-- Normalized source and forward ancestry over the same explicit budget. -/
structure State where
  sourceFacts : SourceFacts B S.source P1 depth
  intrinsic :
    FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink.IntrinsicFrontFunctionalFacts
      S.source
  periodFloor : ∀ t, 1 ≤ rearPeriod S.source t
  ancestry : FiniteNonaffineMajorHistory.ConcreteAncestry
    B S.Gamma depth edgeDefect
  terminalJ_eq : ancestry.terminalJ = S.source.phi1
  terminalP_eq : ancestry.terminalP = S.source.P

namespace State

private theorem configuredSourceKh_pos :
    0 < ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
  rw [ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq]
  norm_num

theorem epsPrev_lt_one (H : State B (S := S) (P1 := P1)
    (depth := depth) (edgeDefect := edgeDefect))
    (hE : Etotal ≤ 1 / 8) : H.sourceFacts.eps < 1 := by
  have hmajor : B.major depth ≤ ∑' i, B.major i :=
    B.summable.le_tsum depth (fun i _ => B.nonnegative i)
  have h := H.sourceFacts.eps_le_major.trans (hmajor.trans B.tsum_le)
  linarith

theorem epsPrev_le_quarter (H : State B (S := S) (P1 := P1)
    (depth := depth) (edgeDefect := edgeDefect))
    (hE : Etotal ≤ 1 / 8) : H.sourceFacts.eps ≤ 1 / 4 := by
  have hmajor : B.major depth ≤ ∑' i, B.major i :=
    B.summable.le_tsum depth (fun i _ => B.nonnegative i)
  have h := H.sourceFacts.eps_le_major.trans (hmajor.trans B.tsum_le)
  linarith

variable {p0 khat0 qmax0 : ℝ} {C : Core S}
  {I : Input C p0 ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
    khat0 qmax0}

def nextV (H : State B (S := S) (P1 := P1)
    (depth := depth) (edgeDefect := edgeDefect)) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0) :=
  H.ancestry.ancestry.extendV B
    (markedPhysicalComponents I.source.phi1 I.source.P C.path.eta)

/-- Callback-free normalized transition from the current source to the
canonical direct-recost target, charged to the next explicit slot. -/
def link (H : State B (S := S) (P1 := P1)
    (depth := depth) (edgeDefect := edgeDefect))
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ B.major (depth + 1)) :
    FiniteNonaffineMajorHistory.ChosenLink B (H.nextV B I) depth where
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
    rw [nextV, FiniteNonaffineMajorHistory.Ancestry.extendV_of_le B
      H.ancestry.ancestry _ (le_refl depth)]
    rw [H.ancestry.terminal_eq, H.terminalJ_eq, H.terminalP_eq]
  target_eq :=
    FiniteNonaffineMajorHistory.Ancestry.extendV_succ B H.ancestry.ancestry _
  rawTransition := by
    have hsource := markedPhysicalComponents_nonnegative_of_sourceJets
      H.sourceFacts.jets (H.epsPrev_le_quarter B hE)
    simpa [FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2] using
      (recostRawTransition C.geometric.output.chosen I.source
        configuredSourceKh_pos
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
        H.sourceFacts.nonaffine H.sourceFacts.functional H.intrinsic.functional
        H.sourceFacts.jets (H.epsPrev_lt_one B hE)
        I.jets (lt_of_le_of_lt I.eps_le_quarter
          (show (1 / 4 : ℝ) < 1 by norm_num))
        H.periodFloor I.path_eta I.source_period_eq I.source_phi1_eq hsource)

/-- Sound forward extension; no output shift or link reversal occurs. -/
def nextAncestry (H : State B (S := S) (P1 := P1)
    (depth := depth) (edgeDefect := edgeDefect))
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ B.major (depth + 1)) :
    FiniteNonaffineMajorHistory.ConcreteAncestry B C.path
      (depth + 1) edgeDefect :=
  FiniteNonaffineMajorHistory.ConcreteAncestry.snoc B H.ancestry
    I.source.phi1 I.source.P
    (markedPhysicalComponents_nonnegative_of_sourceJets
      I.sourceJets I.eps_le_quarter)
    (H.link B C I hE hcur)

/-- Transport only the terminal path density; no source or scalar record is
cast. -/
def castEta
    {p q p' q' : Data} {Gamma : NormalPath p q} {Gamma' : NormalPath p' q'}
    {depth : ℕ} {edgeDefect : ℝ}
    (H : FiniteNonaffineMajorHistory.ConcreteAncestry
      B Gamma depth edgeDefect)
    (heta : Gamma'.eta = Gamma.eta) :
    FiniteNonaffineMajorHistory.ConcreteAncestry
      B Gamma' depth edgeDefect where
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

def nextRawAncestry (H : State B (S := S) (P1 := P1)
    (depth := depth) (edgeDefect := edgeDefect))
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ B.major (depth + 1)) :
    FiniteNonaffineMajorHistory.ConcreteAncestry B
      C.geometric.output.chosen.Delta (depth + 1) edgeDefect :=
  castEta B (H.nextAncestry B C I hE hcur) I.path_eta.symm

@[simp] theorem nextRawAncestry_terminalJ
    (H : State B (S := S) (P1 := P1)
      (depth := depth) (edgeDefect := edgeDefect))
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ B.major (depth + 1)) :
    (H.nextRawAncestry B C I hE hcur).terminalJ =
      C.geometric.output.chosen.phi1 := by
  rw [nextRawAncestry, castEta, nextAncestry]
  exact I.source_phi1_eq

@[simp] theorem nextRawAncestry_terminalP
    (H : State B (S := S) (P1 := P1)
      (depth := depth) (edgeDefect := edgeDefect))
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ B.major (depth + 1)) :
    (H.nextRawAncestry B C I hE hcur).terminalP = rearPeriod S.source := by
  rw [nextRawAncestry, castEta, nextAncestry]
  exact I.source_period_eq

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

/-- Complete the raw chosen row using the fixed explicit history budget. -/
def completion (H : State B (S := S) (P1 := P1)
    (depth := depth) (edgeDefect := edgeDefect))
    (C : Core S) (I : Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ B.major (depth + 1))
    (L : ℝ) (hL : 1 ≤ L) (hL2 : 2 ≤ L ^ 2)
    (hPL : ∀ t ∈ Icc (0 : ℝ) 1, rearPeriod S.source t ≤ L) :
    Completion C I Etotal
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2
      (L ^ 2 * (2 * edgeDefect)) := by
  let W := C.geometric.output.chosen
  let Araw := H.nextRawAncestry B C I hE hcur
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
  let split :=
    FiniteNonaffineMajorHistory.ConcreteAncestry.toScaledSplitHistoryOfChosen
      B W Araw (H.nextRawAncestry_terminalJ B C I hE hcur)
      (H.nextRawAncestry_terminalP B C I hE hcur)
      I.jets (I.eps_le_quarter.trans (by norm_num)) hE L hL hL2
      (fun t _ => H.periodFloor t) hPL F heta hjac T.hPW T.hS1P T.hS2P
  exact
    { V := fun j => scaleAll (L ^ 2) (Araw.ancestry.V j)
      major := B.major
      depth := depth + 1
      splitHistory := by
        rw [FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.GeometricInput.rawPath,
          C.geometric.output.stage_eq]
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

/-- Multiplier scaling changes only mass envelopes, so the intrinsic-front
certificate transports from the erased direct source. -/
def scaledNextIntrinsic
    (C : Core S)
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0) :
    IntrinsicFrontFunctionalFacts I.source := by
  let F := nextIntrinsic C (unscaled I)
  refine ⟨?_⟩
  simpa [ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.source,
    Input.source, unscaled,
    FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink.intrinsicFront,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource.scaledDirectSource,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSource,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource] using
      F.functional

/-- Complete a multiplier input through its canonical unscaled analytic
carrier while retaining the explicit history budget. -/
def scaledCompletion (H : State B (S := S) (P1 := P1)
    (depth := depth) (edgeDefect := edgeDefect))
    (C : Core S)
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8) (hcur : I.eps ≤ B.major (depth + 1))
    (L : ℝ) (hL : 1 ≤ L) (hL2 : 2 ≤ L ^ 2)
    (hPL : ∀ t ∈ Icc (0 : ℝ) 1, rearPeriod S.source t ≤ L) :
    Completion C (unscaled I) Etotal
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2
      (L ^ 2 * (2 * edgeDefect)) :=
  H.completion B C (unscaled I) hE hcur L hL hL2 hPL

end State

end FiniteNonaffineMajorNormalizedState
