import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal

/-!
# Analytic readiness for one reachable intrinsic multiplier layer

The expensive exact-selected and gauge constructions are retained once as an
unscaled pre-carrier input.  The configured multiplier source is then built
by the existing scalar constructor from the canonical recost cost bound.
This is the minimal source-side certificate needed to assemble the public
rowwise `InputData`; no arbitrary global column is introduced.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

abbrev targetIndex (n k : ℕ) : ℕ :=
  diagonal R n (k + 1)

/-- Index in the already-shifted closing data corresponding to
`targetIndex`. -/
abbrev localIndex (n k : ℕ) : ℕ := n + k + 1

/-- The closing data are the global configured data with `totalShift`
rows discarded.  The successor source floor therefore agrees at the local
and global diagonal indices. -/
@[simp] theorem edgeSourceP0_data_local
    (q : ℕ) :
    ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 R.data q =
      ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
        (globalData (J := J)) (R.totalShift + q) := by
  simp [ConfiguredRecursiveEdgeSourceP0.edgeSourceP0,
    RecostClosingOutput.data,
    ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
    ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
    ConfiguredRecursiveSourceP0.sourceP0_shift, Nat.add_assoc]

/-- The same local/global identification for the configured speed cap. -/
@[simp] theorem edgeSpeedCap_data_local
    (q : ℕ) :
    ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap R.data q =
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
        (globalData (J := J)) (R.totalShift + q) := by
  rfl

/-- Multiplier scaling does not change the configured analytic curvature
ceiling. -/
@[simp] theorem analyticKhat_data_local :
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat R.data =
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
        (globalData (J := J)) := by
  rfl

/-- The exact cost statement consumed by the multiplier-density constructor.
It is separated as a named predicate so readiness does not repeat the full
selected/gauge input record. -/
def MultiplierCostBound
    {P0u khu khatu Qmaxu : ℕ → ℝ} {j q : ℕ}
    {S : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.Stage
      P0u khu khatu Qmaxu j}
    (C : Core S) : Prop :=
  (carrier C.geometric.output.chosen C.geometric.output.chosen.c2
      C.eta_continuous C.eta1_continuous C.eta2_continuous).cost ≤
    4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 *
      (2 * recostPeriodScale R.data q *
        ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect R.data (q + 1))

/-- Raw/source provenance and the already-configured displayed metric bound.
The source input is the theorem-produced unscaled direct-recost source; it is
not identified with the multiplier source. -/
structure RawReadiness {k : ℕ} {S : ℕ → Node}
    (L : Layer R k S) where
  pre : ∀ n, Core (S n).stage
  raw : ∀ n, ConfiguredRecursiveEdgeRecostedPreCarrier.Input (pre (n + 1))
    (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 R.data (localIndex n k))
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
    (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat R.data)
    (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap R.data (localIndex n k))
  recostCost_le : ∀ n,
    MultiplierCostBound R (q := localIndex n k) (pre (n + 1))
  rawMetric : ∀ n, RawMetricGeometry.Bounded (pre n).geometric
  edgeBudget_le_error : ∀ n,
    (rawMetric n).edgeBudget ≤ R.error n k
  nextDisplayed : ℕ → Data

namespace RawReadiness

/-- Install the multiplier density on the retained exact direct-recost
source.  Every qualitative field is reused from `raw`; only `m` and `Dd` are
changed by the existing configured constructor. -/
noncomputable def scaled
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : RawReadiness R L) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input (H.pre (n + 1))
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 R.data (localIndex n k))
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat R.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap R.data (localIndex n k)) :=
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.input R
    (localIndex n k)
    (H.raw n).selected (H.raw n).pre (H.raw n).gauge (H.raw n).shifted
    (H.raw n).scalar (H.raw n).P0_pos (H.raw n).jets
    (H.raw n).eps_le_quarter
    (H.pre (n + 1)).eta_continuous
    (H.pre (n + 1)).eta1_continuous
    (H.pre (n + 1)).eta2_continuous
    (H.raw n).bounds (H.raw n).rawSlice (H.recostCost_le n)

/-- The same multiplier source, typed at the public global diagonal.  All
later readiness fields use this single casted object, so its dependent source
projection is never compared to the local object by an additional rewrite. -/
noncomputable def globalScaled
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : RawReadiness R L) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input (H.pre (n + 1))
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (globalData (J := J))
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.diagonal
          R n (k + 1)))
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
        (globalData (J := J)))
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (globalData (J := J))
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.diagonal
          R n (k + 1))) := by
  have hp0 :
      ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 R.data (localIndex n k) =
        ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (globalData (J := J))
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.diagonal
            R n (k + 1)) := by
    rw [edgeSourceP0_data_local]
    congr 1
    simp [localIndex,
      ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.diagonal,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hqmax :
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap R.data (localIndex n k) =
        ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (globalData (J := J))
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.diagonal
            R n (k + 1)) := by
    rw [edgeSpeedCap_data_local]
    congr 1
    simp [localIndex,
      ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.diagonal,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have I := H.scaled R n
  rw [hp0, analyticKhat_data_local, hqmax] at I
  exact I

/-- The predecessor selected rear used as the canonical terminal reference.
This is retained by multiplier scaling and therefore requires no new choice. -/
noncomputable def terminalFrontReference
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : RawReadiness R L) (n : ℕ) : Data :=
  (S (n + 1)).stage.source.selectedRearData
    (H.pre (n + 1)).geometric.output.chosen.Delta.T

/-- The canonical gauge phase relating the multiplier source terminal datum
to `terminalFrontReference`. -/
noncomputable def terminalFrontPhase
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : RawReadiness R L) (n : ℕ) : ℝ :=
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
      (H.globalScaled R n).selected (H.globalScaled R n).gauge.q
      (H.pre (n + 1)).geometric.output.chosen.Delta.T /
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
      (S (n + 1)).stage.source
      (H.pre (n + 1)).geometric.output.chosen.Delta.T

/-- Phase normalization supplies the terminal equality for the actual
multiplier source. -/
theorem terminalFront_eq_phase
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : RawReadiness R L) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
        (H.globalScaled R n).source =
      MarkedShift.shiftData (H.terminalFrontPhase R n)
        (H.terminalFrontReference R n) := by
  simpa only [terminalFrontPhase, terminalFrontReference] using
    source_unitTangentData_eq_shift_selectedRearData (H.globalScaled R n)

end RawReadiness

/-- The remaining quantitative and terminal-reference facts, now stated on
the actual multiplier source. -/
structure Readiness {k : ℕ} {S : ℕ → Node}
    (L : Layer R k S) extends RawReadiness R L where
  eps_le : ∀ n, (toRawReadiness.globalScaled R n).eps ≤
    ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
      (n + 1 + k)).major (k + 1)
  periodUpper_le : ∀ n,
    (toRawReadiness.globalScaled R n).slice.periodUpper ≤
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (globalData (J := J))
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.diagonal
          R n (k + 1))
  periodUpper_le_P1 : ∀ n,
    (toRawReadiness.globalScaled R n).slice.periodUpper ≤
      rowP1 R (n + (k + 1))

namespace Readiness

/-- Callback-free assembly of the exact input consumed by the intrinsic
reachable successor. -/
noncomputable def inputData
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : Readiness R L) : InputData R L where
  pre := H.pre
  analytic := H.toRawReadiness.globalScaled R
  eps_le := H.eps_le
  periodUpper_le := H.periodUpper_le
  periodUpper_le_P1 := H.periodUpper_le_P1
  rawMetric := H.rawMetric
  edgeBudget_le_error := H.edgeBudget_le_error
  nextDisplayed := H.nextDisplayed
  terminalFrontReference := H.toRawReadiness.terminalFrontReference R
  terminalFrontPhase := H.toRawReadiness.terminalFrontPhase R
  terminalFront_eq_phase n := by
    exact RawReadiness.terminalFront_eq_phase R H.toRawReadiness n

theorem exists_inputData
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (H : Readiness R L) : Nonempty (InputData R L) :=
  ⟨H.inputData R⟩

end Readiness

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness
