import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedPreCarrier
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSourceStopping

/-! # Multiplier-aware direct recost pre-carrier

This is the truthful recursive-source interface.  Its density is the
composition coefficient times the canonical recost density, so the following
presented application can satisfy both derivative inequalities.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedScaledPreCarrier

open ConfiguredRecursiveEdgeRecostedPreCarrier
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

variable {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
  {S : Stage P0u khu khatu Qmaxu j}
  {p0 kh0 khat0 qmax0 : ℝ}

/-- Exact data determining the multiplier-aware source, before recursive
regularity sidecars are attached. -/
structure Input (C : Core S) (P0Next khNext khatNext QmaxNext : ℝ) where
  selected : ExactSelected S.source (kap := khNext)
  pre : PreTransport selected
  gauge : RearOwnFrameGaugeFlowReanchoring.Gauge (xi pre)
  shifted : ShiftedTransport pre gauge
  kh_nonnegative : 0 ≤ khNext
  kh_lt_one : khNext < 1
  scalar : Scalar (A := S.source) (kap := khNext)
    (P0Next := P0Next) (khatNext := khatNext) (QmaxNext := QmaxNext)
  P0_pos : 0 < P0Next
  eps : ℝ
  jets : FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
    C.geometric.output.chosen eps
  eps_le_quarter : eps ≤ 1 / 4
  bounds : DirectBounds C.geometric.output.chosen selected pre gauge shifted
    kh_nonnegative kh_lt_one scalar P0_pos C.geometric.output.chosen.c2
    C.eta_continuous C.eta1_continuous C.eta2_continuous
  recostScalar : RecostScalar C.geometric.output.chosen
    (kap := khNext) (QmaxNext := QmaxNext) C.geometric.output.chosen.c2
    C.eta_continuous C.eta1_continuous C.eta2_continuous
  rawSlice : AnalyticSuccessorSliceFacts
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
      C.geometric.output.chosen selected pre gauge shifted kh_nonnegative
      kh_lt_one scalar P0_pos)

namespace Input

def source {C : Core S} (I : Input C p0 kh0 khat0 qmax0) :
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      C.path p0 kh0 khat0 qmax0 :=
  scaledDirectSource C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
    I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
    C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
    C.eta2_continuous I.bounds I.recostScalar

/-- Multiplier scaling rebuilds, rather than assumes, the source-indexed
spatial frame bounds for the enlarged density. -/
def spatial {C : Core S} (I : Input C p0 kh0 khat0 qmax0) :
    SpatialFrameRegularity C.path I.source.Ydot I.source.Theta
      I.source.delta I.source.sf I.source.P I.source.m kh0 qmax0 := by
  simpa [source] using
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource.scaledDirectSource_spatial
        C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
        I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
        C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
        C.eta2_continuous I.bounds I.recostScalar)

/-- Slice facts are insensitive to the multiplier envelope: the carrier,
marking, period, and spatial frame are unchanged. -/
def slice {C : Core S} (I : Input C p0 kh0 khat0 qmax0) :
    AnalyticSuccessorSliceFacts I.source := by
  let U := FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
    C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
      I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos
  let D := I.source
  let F := I.rawSlice
  refine
    { periodUpper := F.periodUpper
      periodLower_pos := F.periodLower_pos
      period_lower := by simpa [D, U, source, scaledDirectSource] using F.period_lower
      period_upper := by simpa [D, U, source, scaledDirectSource] using F.period_upper
      etaFs := F.etaFs
      etaF_deriv := by simpa [D, U, source, scaledDirectSource] using F.etaF_deriv
      etaFs_continuous := F.etaFs_continuous
      etaF_periodic := by simpa [D, U, source, scaledDirectSource] using F.etaF_periodic
      rearNormal_c2 := by simpa [D, U, source, scaledDirectSource] using F.rearNormal_c2
      normal_stopped := ?_
      markingLower := F.markingLower
      markingUpper := F.markingUpper
      marking_increment := by
        simpa [D, U, source, scaledDirectSource] using F.marking_increment
      markingLower_pos := F.markingLower_pos
      marking_lower := by
        simpa [D, U, source, scaledDirectSource, Core.path, carrier,
          CanonicalNormalPathRecost.recost] using F.marking_lower
      markingUpper_nonnegative := F.markingUpper_nonnegative
      marking_upper := by
        simpa [D, U, source, scaledDirectSource, Core.path, carrier,
          CanonicalNormalPathRecost.recost] using F.marking_upper
      marked_bdd0 := ?_
      marked_bdd1 := ?_ }
  · intro t ht
    have ht' : t ∉ Ioo (0 : ℝ) C.geometric.output.chosen.Delta.T := by
      simpa [Core.path, carrier, CanonicalNormalPathRecost.recost] using ht
    simpa [D, U, source, scaledDirectSource] using F.normal_stopped t ht'
  · intro t
    simpa [D, source, scaledDirectSource, Core.path, carrier,
      CanonicalNormalPathRecost.recost] using F.marked_bdd0 t
  · intro t
    simpa [D, source, scaledDirectSource, Core.path, carrier,
      CanonicalNormalPathRecost.recost] using F.marked_bdd1 t

@[simp] theorem path_eta {C : Core S} (I : Input C p0 kh0 khat0 qmax0) :
    C.path.eta = C.geometric.output.chosen.Delta.eta :=
  ConfiguredRecursiveEdgeRecostedPreCarrier.Input.path_eta
    { selected := I.selected, pre := I.pre, gauge := I.gauge, shifted := I.shifted
      kh_nonnegative := I.kh_nonnegative, kh_lt_one := I.kh_lt_one
      scalar := I.scalar, P0_pos := I.P0_pos, eps := I.eps, jets := I.jets
      eps_le_quarter := I.eps_le_quarter, bounds := I.bounds
      rawSlice := I.rawSlice }

@[simp] theorem source_period_eq {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0) : I.source.P = rearPeriod S.source := rfl

@[simp] theorem source_phi1_eq {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0) :
    I.source.phi1 = C.geometric.output.chosen.phi1 := rfl

/-- Fresh Taylor-free selection bounds are reconstructed from the scaled
source's retained slice floor and its automatic stopping theorem. -/
theorem exists_selectionBounds {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0) :
    Nonempty
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds.SelectionBounds
        I.source) := by
  exact
    FiniteSmoothRearFamilyMarkingAwareExactSourceStopping.exists_selectionBounds
      I.source I.spatial I.slice.normal_stopped
      I.P0_pos I.slice.period_lower

/-- Complete source-indexed regularity and selection sidecars for a scaled
input, with no external recursive hypothesis. -/
noncomputable def recursiveSidecars {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0) : RecursiveExactSidecars I.source :=
  RecursiveExactSidecars.ofSource I.source
    (Classical.choice (exists_selectionBounds I))

def sourceJets {C : Core S} (I : Input C p0 kh0 khat0 qmax0) :
    FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.SourceNormalizedJetBounds
      I.source I.eps where
  eps_nonnegative := I.jets.eps_nonnegative
  dphi := by
    intro t ht u
    rw [I.source_phi1_eq, I.source_period_eq]
    exact I.jets.dpsi t ht u

theorem mass_nonnegative {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0) :
    0 ≤ ∫ t in (0 : ℝ)..C.path.T, I.source.m t :=
  intervalIntegral.integral_nonneg C.path.T_pos.le
    (fun t _ ↦ I.source.density_nonnegative t)

theorem mass_le_one {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0) :
    (∫ t in (0 : ℝ)..C.path.T, I.source.m t) ≤ 1 := by
  change (∫ t in (0 : ℝ)..C.geometric.output.chosen.Delta.T,
    I.recostScalar.coeff * density (kap := kh0)
      C.geometric.output.chosen C.geometric.output.chosen.c2
      C.eta_continuous C.eta1_continuous C.eta2_continuous t) ≤ 1
  exact I.recostScalar.scaled_mass_le_one

/-- The first presented-application inequality follows from the actual scaled
source mass and the coefficient reserve. -/
theorem composition_d1 {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0)
    (hperiod : rearPeriod I.source 0 ≤ qmax0) (t : ℝ) :
    2 * (C.path.m t / Real.sqrt (1 - kh0 ^ 2)) *
        GaugeFlowDerivCost.costP1 (rearPeriod I.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kh0)
          (∫ s in (0 : ℝ)..C.path.T, I.source.m s) ≤ I.source.m t := by
  let rho := C.path.m t / Real.sqrt (1 - kh0 ^ 2)
  let M := ∫ s in (0 : ℝ)..C.path.T, I.source.m s
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    exact div_nonneg (C.path.m_nonneg t) (Real.sqrt_nonneg _)
  have hp := GaugeFlowDerivCost.costP1_le
    (I.source.rear_period_pos 0).le hperiod
    (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
      I.kh_nonnegative I.kh_lt_one) I.mass_nonnegative I.mass_le_one
  have hc : 2 * GaugeFlowDerivCost.costP1 (rearPeriod I.source 0)
      (GaugeMarkedDataOfRearFamily.rearKappa1 kh0) M ≤ I.recostScalar.coeff :=
    (mul_le_mul_of_nonneg_left hp (by norm_num)).trans I.recostScalar.coeff_first
  have hm : I.source.m t = I.recostScalar.coeff * rho := rfl
  calc
    2 * rho * GaugeFlowDerivCost.costP1 (rearPeriod I.source 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 kh0) M =
        rho * (2 * GaugeFlowDerivCost.costP1 (rearPeriod I.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kh0) M) := by ring
    _ ≤ rho * I.recostScalar.coeff := mul_le_mul_of_nonneg_left hc hrho
    _ = I.source.m t := by rw [hm]; ring

/-- The enlarged direct-recost coefficient gives the second application
inequality without comparing raw and recost densities. -/
theorem composition_d2 {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0)
    (hperiod : rearPeriod I.source 0 ≤ qmax0) (t : ℝ) :
    (I.source.Dd t + 2 * (C.path.m t / Real.sqrt (1 - kh0 ^ 2))) *
        GaugeFlowDerivCost.costP1 (rearPeriod I.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kh0)
          (∫ s in (0 : ℝ)..C.path.T, I.source.m s) ^ 2 +
      2 * (C.path.m t / Real.sqrt (1 - kh0 ^ 2)) *
        GaugeFlowDerivCost.costG1 (rearPeriod I.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kh0)
          (GaugeMarkedDataOfRearFamily.rearKappa2 kh0)
          (∫ s in (0 : ℝ)..C.path.T, I.source.m s) ≤ I.source.m t := by
  let rho := C.path.m t / Real.sqrt (1 - kh0 ^ 2)
  let M := ∫ s in (0 : ℝ)..C.path.T, I.source.m s
  let d := FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst
    (kh := khu j) (kap := kh0)
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    exact div_nonneg (C.path.m_nonneg t) (Real.sqrt_nonneg _)
  have hd : 0 ≤ d := by
    apply RearJacobiSourceCost.jacobiSourceConst_nonneg
    exact one_div_pos.mpr (by
      dsimp [FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.derivativeConst,
        FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
      positivity)
  have hp := GaugeFlowDerivCost.costP1_le
    (I.source.rear_period_pos 0).le hperiod
    (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
      I.kh_nonnegative I.kh_lt_one) I.mass_nonnegative I.mass_le_one
  have hg := GaugeFlowDerivCost.costG1_le
    (I.source.rear_period_pos 0).le hperiod
    (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
      I.kh_nonnegative I.kh_lt_one)
    (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
      I.kh_nonnegative I.kh_lt_one) I.mass_nonnegative I.mass_le_one
  have hp0 : 0 ≤ GaugeFlowDerivCost.costP1 (rearPeriod I.source 0)
      (GaugeMarkedDataOfRearFamily.rearKappa1 kh0) M :=
    (GaugeFlowDerivCost.costP1_pos (I.source.rear_period_pos 0)).le
  have hpQ0 : 0 ≤ GaugeFlowDerivCost.costP1 qmax0
      (GaugeMarkedDataOfRearFamily.rearKappa1 kh0) 1 := hp0.trans hp
  have hpsq := (sq_le_sq₀ hp0 hpQ0).2 hp
  have hinner :
      (2 * d + 2) * GaugeFlowDerivCost.costP1 (rearPeriod I.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kh0) M ^ 2 +
        2 * GaugeFlowDerivCost.costG1 (rearPeriod I.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kh0)
          (GaugeMarkedDataOfRearFamily.rearKappa2 kh0) M ≤ I.recostScalar.coeff := by
    apply (add_le_add
      (mul_le_mul_of_nonneg_left hpsq (by positivity : 0 ≤ 2 * d + 2))
      (mul_le_mul_of_nonneg_left hg (by norm_num))).trans
    exact I.recostScalar.coeff_second
  have hDd : I.source.Dd t = (2 * d) * rho := rfl
  have hm : I.source.m t = I.recostScalar.coeff * rho := rfl
  rw [hDd]
  change ((2 * d) * rho + 2 * rho) *
      GaugeFlowDerivCost.costP1 (rearPeriod I.source 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 kh0) M ^ 2 +
    2 * rho * GaugeFlowDerivCost.costG1 (rearPeriod I.source 0)
      (GaugeMarkedDataOfRearFamily.rearKappa1 kh0)
      (GaugeMarkedDataOfRearFamily.rearKappa2 kh0) M ≤ _
  calc
    ((2 * d) * rho + 2 * rho) * GaugeFlowDerivCost.costP1
          (rearPeriod I.source 0) (GaugeMarkedDataOfRearFamily.rearKappa1 kh0) M ^ 2 +
        2 * rho * GaugeFlowDerivCost.costG1 (rearPeriod I.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kh0)
          (GaugeMarkedDataOfRearFamily.rearKappa2 kh0) M =
      rho * ((2 * d + 2) * GaugeFlowDerivCost.costP1
          (rearPeriod I.source 0) (GaugeMarkedDataOfRearFamily.rearKappa1 kh0) M ^ 2 +
        2 * GaugeFlowDerivCost.costG1 (rearPeriod I.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kh0)
          (GaugeMarkedDataOfRearFamily.rearKappa2 kh0) M) := by ring
    _ ≤ rho * I.recostScalar.coeff := mul_le_mul_of_nonneg_left hinner hrho
    _ = I.source.m t := by rw [hm]; ring

/-- The remaining recursive certificates are source-tied and can be assembled
after the scaled source is known. -/
structure RecursiveFacts {C : Core S} (I : Input C p0 kh0 khat0 qmax0) where
  sidecars : RecursiveExactSidecars I.source
  spatial : SpatialFrameRegularity C.path I.source.Ydot I.source.Theta
    I.source.delta I.source.sf I.source.P I.source.m kh0 qmax0
  terminalCurvature_nonnegative : ∀ s, 0 ≤ I.source.K C.path.T s
  terminalRange : Set.range (I.source.F C.path.T) =
    Set.range C.geometric.output.jets.rear.1

/-- Only terminal curvature and endpoint range remain geometric inputs; the
scaled spatial and selection sidecars are intrinsic to `I`. -/
def RecursiveFacts.ofTerminal {C : Core S}
    (I : Input C p0 kh0 khat0 qmax0)
    (terminalCurvature_nonnegative : ∀ s, 0 ≤ I.source.K C.path.T s)
    (terminalRange : Set.range (I.source.F C.path.T) =
      Set.range C.geometric.output.jets.rear.1) : RecursiveFacts I where
  sidecars := I.recursiveSidecars
  spatial := I.spatial
  terminalCurvature_nonnegative := terminalCurvature_nonnegative
  terminalRange := terminalRange

def recursive {C : Core S} (I : Input C p0 kh0 khat0 qmax0)
    (H : RecursiveFacts I) :
    RecursiveAnalyticSuccessor C.path S.source p0 kh0 khat0 qmax0 :=
  RecursiveAnalyticSuccessor.ofExact I.source I.slice H.sidecars H.spatial
    H.terminalCurvature_nonnegative H.terminalRange

end Input

end ConfiguredRecursiveEdgeRecostedScaledPreCarrier
