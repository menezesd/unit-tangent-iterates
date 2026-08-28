import UnitTangentIterates.ConfiguredRecursiveEdgeActualPhysicalHistory
import UnitTangentIterates.ConfiguredRecursiveEdgeActualPhysicalSplitHistory
import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnScalarClosing
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSourceRecostTransport

/-!
# Configured recosted analytic carrier

This is the paper-faithful boundary between a selected raw gauge path and the
recursive analytic source.  The raw path is retained for the physical
comparison, while the next source is required to live on its canonical
functional recost.  Thus the arbitrary majorant stored by `applyLong` is not
silently propagated through the recursion.

The internal recost allowance is deliberately separate from the legacy
composition error.  Displayed convergence is still charged to
`directDiagonal`.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedAnalyticCarrier

open ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

/-! ## The truthful internal scalar allowance -/

/-- Canonical recost length available at the edge indexed by `q`.  The
physical defect is evaluated at the outgoing diagonal `q + 1`. -/
def recostAllowance
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) (q : ℕ) : ℝ :=
  4 * configuredTarget E C0 C1 C2 * edgePhysicalDefect D (q + 1)

theorem recostAllowance_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) (q : ℕ) :
    0 ≤ recostAllowance D E C0 C1 C2 q := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) (configuredTarget_nonnegative E C0 C1 C2))
    (edgePhysicalDefect_nonnegative D (q + 1))

theorem recostAllowance_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) :
    Summable (recostAllowance D E C0 C1 C2) := by
  have hd : Summable (edgePhysicalDefect D) := by
    have H :=
      ConfiguredPolynomialDiagonalStableRowDefectProvider.summable_polynomial_mul_rowDefect
        D (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeffEnvelope D)
    simpa [edgePhysicalDefect,
      ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect,
      mul_assoc] using H
  have hs : Summable (fun q : ℕ ↦ edgePhysicalDefect D (1 + q)) :=
    ShadowingTails.summable_shift hd 1
  have hm := hs.mul_left (4 * configuredTarget E C0 C1 C2)
  simpa [recostAllowance, Nat.add_comm] using hm

/-- Internal mass allowance for a direct source whose density is exactly the
recost density divided by `sqrt (1-sourceKh^2)`.  At the configured
`sourceKh = 5/6`, the inverse-square-root loss is at most two. -/
def recostSourceAllowance
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) (q : ℕ) : ℝ :=
  2 * recostAllowance D E C0 C1 C2 q

theorem recostSourceAllowance_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) (q : ℕ) :
    0 ≤ recostSourceAllowance D E C0 C1 C2 q :=
  mul_nonneg (by norm_num) (recostAllowance_nonnegative D E C0 C1 C2 q)

theorem recostSourceAllowance_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) :
    Summable (recostSourceAllowance D E C0 C1 C2) := by
  simpa [recostSourceAllowance] using
    (recostAllowance_summable D E C0 C1 C2).mul_left 2

theorem div_sqrt_sourceKh_le_two_mul {x : ℝ} (hx : 0 ≤ x) :
    x / Real.sqrt
        (1 - ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) ≤
      2 * x := by
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt
      (1 - ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) := by
    rw [ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq]
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  have hp : 0 < Real.sqrt
      (1 - ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) :=
    Real.sqrt_pos.mpr (by
      nlinarith [ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative,
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one])
  rw [div_le_iff₀ hp]
  nlinarith

theorem scaledCost_le_recostSourceAllowance
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) (q : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (h : x ≤ recostAllowance D E C0 C1 C2 q) :
    x / Real.sqrt
        (1 - ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) ≤
      recostSourceAllowance D E C0 C1 C2 q := by
  exact (div_sqrt_sourceKh_le_two_mul hx).trans
    (mul_le_mul_of_nonneg_left h (by norm_num))

/-- The recost allowance is an internal construction budget.  The public
displayed budget `directDiagonal` is larger because its scale is `4*T+1` and
its conversion factor contains a `c2ConstVar`, which is at least one. -/
theorem recostAllowance_le_directDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E C0 C1 C2 M : ℝ) (q : ℕ) :
    recostAllowance D E C0 C1 C2 q ≤
      directDiagonal D MA NA E C0 C1 C2 M q := by
  have hT : 0 ≤ 4 * configuredTarget E C0 C1 C2 := mul_nonneg (by norm_num)
    (configuredTarget_nonnegative E C0 C1 C2)
  have hA : 1 ≤ edgeConversion D
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
      MA NA q := by
    exact NormalPathC2IncrementVariableSpeed.one_le_c2ConstVar _ _ _ _ _
  have hB : 0 ≤ edgeEndpointConversion D
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh M q :=
    edgeEndpointConversion_nonnegative D
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one q
  have hd : 0 ≤ edgePhysicalDefect D (q + 1) :=
    edgePhysicalDefect_nonnegative D (q + 1)
  have hcoeff : 4 * configuredTarget E C0 C1 C2 ≤
      (4 * configuredTarget E C0 C1 C2 + 1) *
        (edgeConversion D
            (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
            MA NA q +
          edgeEndpointConversion D
            ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh M q) := by
    nlinarith [mul_nonneg hT (sub_nonneg.mpr hA)]
  simpa [recostAllowance, directDiagonal, directConversion, directScale,
      ConfiguredRecursiveEdgeWeightedEffectiveError.weightedSequence,
      edgeCombinedConversion] using
    (mul_le_mul_of_nonneg_right hcoeff hd)

/-- The existing configured closing shift makes every recost allowance less
than the source-construction mass threshold one. -/
theorem recostAllowance_shift_lt_one
    {MA NA E C0 C1 C2 : ℝ}
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {G : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output J E
      (configuredSourceMassTarget E C0 C1 C2)}
    (O : ClosingOutput J G E C0 C1 C2) (q : ℕ) :
    recostAllowance G.data E C0 C1 C2
        (O.preShift + O.large.N + q) < 1 := by
  have H := O.component_small (q + 1)
  have hbudget :
      ReachableVariableSpeedFrontCurvature.sourceCurvatureCostBudget < 1 := by
    norm_num [ReachableVariableSpeedFrontCurvature.sourceCurvatureCostBudget]
  have H' : recostAllowance G.data E C0 C1 C2
      (O.preShift + O.large.N + q) <
        ReachableVariableSpeedFrontCurvature.sourceCurvatureCostBudget := by
    simpa [recostAllowance, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using H
  exact H'.trans hbudget

theorem recostAllowance_shift_le_one
    {MA NA E C0 C1 C2 : ℝ}
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {G : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output J E
      (configuredSourceMassTarget E C0 C1 C2)}
    (O : ClosingOutput J G E C0 C1 C2) (q : ℕ) :
    recostAllowance G.data E C0 C1 C2
        (O.preShift + O.large.N + q) ≤ 1 :=
  (recostAllowance_shift_lt_one O q).le

theorem recostSourceAllowance_shift_lt_one
    {MA NA E C0 C1 C2 : ℝ}
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {G : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output J E
      (configuredSourceMassTarget E C0 C1 C2)}
    (O : ClosingOutput J G E C0 C1 C2) (q : ℕ) :
    recostSourceAllowance G.data E C0 C1 C2
        (O.preShift + O.large.N + q) < 1 := by
  have H := recostAllowance_shift_lt_one O q
  have Hb : recostAllowance G.data E C0 C1 C2
      (O.preShift + O.large.N + q) < 6 / 61 := by
    have H0 := O.component_small (q + 1)
    simpa [recostAllowance,
      ReachableVariableSpeedFrontCurvature.sourceCurvatureCostBudget,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H0
  unfold recostSourceAllowance
  nlinarith

theorem recostSourceAllowance_shift_le_one
    {MA NA E C0 C1 C2 : ℝ}
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {G : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output J E
      (configuredSourceMassTarget E C0 C1 C2)}
    (O : ClosingOutput J G E C0 C1 C2) (q : ℕ) :
    recostSourceAllowance G.data E C0 C1 C2
        (O.preShift + O.large.N + q) ≤ 1 :=
  (recostSourceAllowance_shift_lt_one O q).le

/-! ## A physical-history-backed recosted carrier -/

variable {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
  {S : Stage P0 kh khat Qmax j} (G : GeometricInput S)

/-- Either finite physical-history presentation accepted by the recosted
carrier.  Both produce the same stable-component conclusion. -/
inductive HistoryCertificate
    {p q : Data} (Gamma : NormalPath p q)
    (V : ℕ → AnchoredJacobiStableTransition.Components)
    (major : ℕ → ℝ) (depth : ℕ) (E C0 C1 C2 d : ℝ) : Prop
  | paired
      (history : ConfiguredRecursiveEdgeActualPhysicalHistory.History
        Gamma V major depth E C0 C1 C2 d)
  | split
      (history : ConfiguredRecursiveEdgeActualPhysicalSplitHistory.SplitHistory
        Gamma V major depth E C0 C1 C2 d)

namespace HistoryCertificate

def toStable
    {p q : Data} {Gamma : NormalPath p q}
    {V : ℕ → AnchoredJacobiStableTransition.Components}
    {major : ℕ → ℝ} {depth : ℕ} {E C0 C1 C2 d : ℝ}
    (H : HistoryCertificate Gamma V major depth E C0 C1 C2 d)
    (hT : Gamma.T = 1) (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (uncurry Gamma.eta))
    (heta1 : Continuous (uncurry hC2.eta1))
    (heta2 : Continuous (uncurry hC2.eta2)) :
    FiniteColumnStablePhysicalComponentCompactness.StablePhysicalComponents
      (CanonicalNormalPathRecost.recost Gamma hC2 heta heta1 heta2) 1
      (configuredTarget E C0 C1 C2) d := by
  cases H with
  | paired H => exact H.toStable hT hC2 heta heta1 heta2
  | split H => exact H.toStable hT hC2 heta heta1 heta2

end HistoryCertificate

/-- All data needed to turn the raw selected path into the canonical carrier
and bound its cost by the public physical defect. -/
structure CarrierInput
    (V : ℕ → AnchoredJacobiStableTransition.Components)
    (major : ℕ → ℝ) (depth : ℕ) (E C0 C1 C2 d : ℝ) where
  c2 : C2NormalPathData G.rawPath
  eta_continuous : Continuous (uncurry G.rawPath.eta)
  eta1_continuous : Continuous (uncurry c2.eta1)
  eta2_continuous : Continuous (uncurry c2.eta2)
  time_one : G.rawPath.T = 1
  history : HistoryCertificate G.rawPath V major depth E C0 C1 C2 d

namespace CarrierInput

variable {G} {V : ℕ → AnchoredJacobiStableTransition.Components}
  {major : ℕ → ℝ} {depth : ℕ} {E C0 C1 C2 d : ℝ}

/-- The recursive carrier.  It has the same family, velocity, endpoints, and
normal field as the raw chosen path, but its density is canonical. -/
def path (R : CarrierInput G V major depth E C0 C1 C2 d) :
    NormalPath S.displayed G.output.jets.rear :=
  CanonicalNormalPathRecost.recost G.rawPath R.c2 R.eta_continuous
    R.eta1_continuous R.eta2_continuous

@[simp] theorem path_eta (R : CarrierInput G V major depth E C0 C1 C2 d) :
    R.path.eta = G.rawPath.eta := by
  exact CanonicalNormalPathRecost.recost_eta G.rawPath R.c2
    R.eta_continuous R.eta1_continuous R.eta2_continuous

@[simp] theorem path_X (R : CarrierInput G V major depth E C0 C1 C2 d) :
    R.path.X = G.rawPath.X := rfl

@[simp] theorem path_T (R : CarrierInput G V major depth E C0 C1 C2 d) :
    R.path.T = G.rawPath.T := rfl

/-- Canonical recosting preserves the exact selected rear, hence also its
unmarked curve range. -/
theorem terminal_range
    (R : CarrierInput G V major depth E C0 C1 C2 d) :
    range (R.path.X R.path.T) = range G.output.jets.rear.1 := by
  apply congrArg range
  funext u
  exact R.path.finish u

def stable (R : CarrierInput G V major depth E C0 C1 C2 d) :
    FiniteColumnStablePhysicalComponentCompactness.StablePhysicalComponents R.path 1
      (configuredTarget E C0 C1 C2) d :=
  R.history.toStable R.time_one R.c2 R.eta_continuous
    R.eta1_continuous R.eta2_continuous

theorem cost_le
    (R : CarrierInput G V major depth E C0 C1 C2 d) :
    R.path.cost ≤ 4 * configuredTarget E C0 C1 C2 * d := by
  exact
    FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability.recost_cost_le_four_configuredTarget_mul
      R.c2 R.eta_continuous R.eta1_continuous R.eta2_continuous R.stable

theorem cost_le_recostAllowance
    (R : CarrierInput G V major depth E C0 C1 C2 d)
    (D : ConstructedConfiguredSequenceWeighted.Data) (q : ℕ)
    (hd : d ≤ edgePhysicalDefect D (q + 1)) :
    R.path.cost ≤ recostAllowance D E C0 C1 C2 q := by
  exact R.cost_le.trans (mul_le_mul_of_nonneg_left hd
    (mul_nonneg (by norm_num) (configuredTarget_nonnegative E C0 C1 C2)))

end CarrierInput

/-! ## The recursive analytic boundary -/

/-- An analytic successor whose underlying normal path is the canonical
recost, not `G.rawPath`.  This is the minimal replacement for the legacy
raw-carrier `AnalyticInput`. -/
structure RecostedAnalyticInput
    {V : ℕ → AnchoredJacobiStableTransition.Components}
    {major : ℕ → ℝ} {depth : ℕ} {E C0 C1 C2 d : ℝ}
    (R : CarrierInput G V major depth E C0 C1 C2 d) where
  successor : AnalyticSuccessor R.path S.source
    (P0 (j + 1)) (kh (j + 1)) (khat (j + 1)) (Qmax (j + 1))

namespace RecostedAnalyticInput

variable {G} {V : ℕ → AnchoredJacobiStableTransition.Components}
  {major : ℕ → ℝ} {depth : ℕ} {E C0 C1 C2 d : ℝ}
  {R : CarrierInput G V major depth E C0 C1 C2 d}

/-- The next recursive source is definitionally a source on the canonical
recosted carrier. -/
def nextSource
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RecostedAnalyticInput G R) :
    MarkingAwareSource R.path (P0 (j + 1)) (kh (j + 1))
      (khat (j + 1)) (Qmax (j + 1)) := by
  cases A.successor with
  | legacy smooth steering regularity majorants =>
      exact Classical.choice
        (FiniteSmoothRearFamilyMarkingAwareSmoothSource.exists_markingAwareSuccessorSource_of_majorants
          majorants)
  | exact source slice => exact source

/-- In particular, the successor density dominates the canonical carrier
density (with precisely the unavoidable inverse-cosine factor). -/
theorem recost_density_le_nextSource
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RecostedAnalyticInput G R)
    (t : ℝ) :
    R.path.m t / Real.sqrt (1 - (kh (j + 1)) ^ 2) ≤
      A.nextSource.m t :=
  A.nextSource.density_domination t

end RecostedAnalyticInput

/-! ## Construction from the theorem-produced raw successor -/

/-- The paper-faithful successor input: first use the existing exact analytic
theorem on the chosen raw path, then transport that theorem-produced source
to the canonical recost.  The transport sidecar contains only the two facts
which genuinely depend on the enlarged source density. -/
structure RawSuccessorTransportInput
    {V : ℕ → AnchoredJacobiStableTransition.Components}
    {major : ℕ → ℝ} {depth : ℕ} {E C0 C1 C2 d : ℝ}
    (R : CarrierInput G V major depth E C0 C1 C2 d) where
  raw : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.AnalyticInput G
  transport :
    FiniteSmoothRearFamilyMarkingAwareSourceRecostTransport.TransportInput
      raw.nextSource R.path

namespace RawSuccessorTransportInput

variable {G} {V : ℕ → AnchoredJacobiStableTransition.Components}
  {major : ℕ → ℝ} {depth : ℕ} {E C0 C1 C2 d : ℝ}
  {R : CarrierInput G V major depth E C0 C1 C2 d}

/-- The constructed recursive source on the canonical carrier. -/
def nextSource
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) :
    MarkingAwareSource R.path (P0 (j + 1)) (kh (j + 1))
      (khat (j + 1)) (Qmax (j + 1)) :=
  FiniteSmoothRearFamilyMarkingAwareSourceRecostTransport.transport
    A.raw.nextSource R.c2 R.eta_continuous R.eta1_continuous
      R.eta2_continuous A.transport

/-- The source envelope is exactly the raw successor envelope plus the
canonical carrier density with the unavoidable inverse-cosine loss. -/
theorem nextSource_density
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) (t : ℝ) :
    A.nextSource.m t = A.raw.nextSource.m t +
      R.path.m t / Real.sqrt (1 - (kh (j + 1)) ^ 2) := by
  rfl

theorem recost_density_le_nextSource
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) (t : ℝ) :
    R.path.m t / Real.sqrt (1 - (kh (j + 1)) ^ 2) ≤
      A.nextSource.m t :=
  A.nextSource.density_domination t

/-- Finite analytic slice data retained by the exact raw successor. -/
structure SliceInput
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) where
  rawSlice : AnalyticSuccessorSliceFacts A.raw.nextSource

/-- All exact slice facts transport with the source because canonical
recosting preserves `T` and `eta`, while source transport preserves period,
intrinsic normal velocity, and marking. -/
def slice
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) (F : SliceInput A) :
    AnalyticSuccessorSliceFacts A.nextSource :=
  FiniteSmoothRearFamilyMarkingAwareSourceRecostTransport.transportSlice
    A.raw.nextSource F.rawSlice R.c2 R.eta_continuous R.eta1_continuous
      R.eta2_continuous A.transport

/-- The complete exact analytic successor on the canonical recosted carrier. -/
def exactAnalyticSuccessor
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) (F : SliceInput A) :
    AnalyticSuccessor R.path S.source
      (P0 (j + 1)) (kh (j + 1)) (khat (j + 1)) (Qmax (j + 1)) :=
  AnalyticSuccessor.exact A.nextSource (slice A F)

/-- The recosted analogue of `Successor.mappedColumn` at one row.  Its
analytic carrier runs from the preceding displayed datum to the selected
rear, while its next displayed datum is the canonical presented base.  These
are intentionally not identified: the endpoint cap is the second metric
leg. -/
def mappedStage
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) : Stage P0 kh khat Qmax (j + 1) where
  start := S.displayed
  rear := G.output.jets.rear
  Gamma := R.path
  source := A.nextSource
  applied := Classical.choice
    (FiniteSmoothRearFamilyMarkingAwareAppliedSource.exists_applied A.nextSource)
  displayed := G.base

@[simp] theorem mappedStage_Gamma
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) :
    (mappedStage A).Gamma = R.path := rfl

@[simp] theorem mappedStage_source
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) :
    (mappedStage A).source = A.nextSource := rfl

@[simp] theorem mappedStage_displayed
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) :
    (mappedStage A).displayed = G.base := rfl

/-- Exact unmarked coherence survives the recursive carrier replacement. -/
theorem mappedStage_terminal_range
    (A : ConfiguredRecursiveEdgeRecostedAnalyticCarrier.RawSuccessorTransportInput
      G R) :
    range ((mappedStage A).Gamma.X (mappedStage A).Gamma.T) =
      range G.output.jets.rear.1 := by
  exact R.terminal_range

end RawSuccessorTransportInput

end ConfiguredRecursiveEdgeRecostedAnalyticCarrier
