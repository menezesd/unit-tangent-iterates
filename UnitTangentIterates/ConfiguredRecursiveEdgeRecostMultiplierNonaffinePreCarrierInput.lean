import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNonaffineJetMajor
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedPreCarrier
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
import UnitTangentIterates.ConfiguredRecursiveEdgeDirectRecostBounds
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedDirectInput
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars

/-!
# Nonaffine exact pre-carrier input from retained recursive sidecars

The selection provenance is source-tied: a `SelectionBounds A` belongs to the
current source `A`, independently of how that source was reached.  The chosen
marking jets are obtained from the nonaffine flow equations and are paid for
by the configured gauge major.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierNonaffinePreCarrierInput

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget
  ConfiguredRecursiveEdgeRecostMultiplierNonaffineJetMajor
  ConfiguredRecursiveEdgeRecostedPreCarrier
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds
  FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

variable {MA NA Etotal Dtarget : ℝ}
  {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {P0u khatu Qmaxu : ℕ → ℝ}
  {k q j : ℕ}
  {O : Output J Etotal Dtarget}
  {S : Stage
    P0u
    (fun _ ↦ sourceKh)
    khatu Qmaxu k}

private def rawSlice
    (C : Core S)
    (selected : ExactSelected S.source (kap := sourceKh))
    (pre : PreTransport selected)
    (gauge : RearOwnFrameGaugeFlowReanchoring.Gauge (xi pre))
    (shifted : ShiftedTransport pre gauge)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t) :
    AnalyticSuccessorSliceFacts
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
        C.geometric.output.chosen selected pre gauge shifted
        sourceKh_nonnegative sourceKh_lt_one scalar
        (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)) := by
  let W := C.geometric.output.chosen
  let B :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawBounds
      W selected pre gauge shifted sourceKh_nonnegative sourceKh_lt_one scalar
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)
  let K :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.compatibility
      W selected pre gauge sourceKh_nonnegative sourceKh_lt_one shifted B
  have K' :
      FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.Compatibility W
        (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
          W selected pre gauge shifted sourceKh_nonnegative sourceKh_lt_one scalar
          (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)) := by
    simpa [FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource,
      B] using K
  exact FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.sliceFacts
    W _ K' (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)
    (fun t ↦ by
      rw [K'.period_eq]
      exact
        (ConfiguredRecursiveEdgeRecostedDirectInput.edgeSourceP0_le_one O.data q).trans
          (hfloor t))
    (fun t ↦ by rw [K'.period_eq]; exact scalar.period_le t)

/-- The ReadySource underlying the direct recost, retained before either the
direct-density replacement or the multiplier scaling is applied. -/
private def rawRecursive
    (C : Core S)
    (selected : ExactSelected S.source (kap := sourceKh))
    (pre : PreTransport selected)
    (gauge : RearOwnFrameGaugeFlowReanchoring.Gauge (xi pre))
    (shifted : ShiftedTransport pre gauge)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t) :
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.RecursiveAnalyticSuccessor
        C.geometric.output.chosen.Delta S.source
        (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
        sourceKh (analyticKhat O.data)
        (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q) :=
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.ofReadySource
    C.geometric.output.chosen selected pre gauge sourceKh_nonnegative
    sourceKh_lt_one shifted
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawBounds
      C.geometric.output.chosen selected pre gauge shifted
      sourceKh_nonnegative sourceKh_lt_one scalar
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q))
    (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)
    (rawSlice C selected pre gauge shifted scalar hfloor).period_lower
    (rawSlice C selected pre gauge shifted scalar hfloor).period_upper

/-- An allowance-built direct input together with the terminal facts inherited
from its exact ReadySource.  These facts are retained before multiplier data
is available. -/
structure AllowanceWitness (C : Core S)
    (p0 kh0 khat0 qmax0 eps : ℝ) where
  input : ConfiguredRecursiveEdgeRecostedPreCarrier.Input C
    p0 kh0 khat0 qmax0
  eps_eq : input.eps = eps
  periodUpper_eq : input.slice.periodUpper = qmax0
  terminalCurvature_nonnegative : ∀ s, 0 ≤ input.source.K C.path.T s
  terminalRange : Set.range (input.source.F C.path.T) =
    Set.range C.geometric.output.jets.rear.1

/-- The multiplier-scaled input and its complete recursive package. -/
structure ScaledAllowanceWitness (C : Core S)
    (p0 kh0 khat0 qmax0 eps : ℝ) where
  input : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
    p0 kh0 khat0 qmax0
  eps_eq : input.eps = eps
  periodUpper_eq : input.slice.periodUpper = qmax0
  recursiveFacts :
    ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.RecursiveFacts input

namespace AllowanceWitness

/-- Install genuine multiplier data without changing any of the exact
selection, transport, or raw-source fields. -/
noncomputable def scaledInput
    (X : AllowanceWitness C p0 kh0 khat0 qmax0 eps)
    (K :
      FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource.RecostScalar
        C.geometric.output.chosen
          (kap := kh0) (QmaxNext := qmax0)
          C.geometric.output.chosen.c2 C.eta_continuous
          C.eta1_continuous C.eta2_continuous) :
    ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
      p0 kh0 khat0 qmax0 where
  selected := X.input.selected
  pre := X.input.pre
  gauge := X.input.gauge
  shifted := X.input.shifted
  kh_nonnegative := X.input.kh_nonnegative
  kh_lt_one := X.input.kh_lt_one
  scalar := X.input.scalar
  P0_pos := X.input.P0_pos
  eps := X.input.eps
  jets := X.input.jets
  eps_le_quarter := X.input.eps_le_quarter
  bounds := X.input.bounds
  recostScalar := K
  rawSlice := X.input.rawSlice

/-- Direct recost and multiplier scaling both preserve the terminal front and
curvature fields, so the ReadySource terminal facts complete the scaled
recursive package. -/
noncomputable def recursiveFacts
    (X : AllowanceWitness C p0 kh0 khat0 qmax0 eps)
    (K :
      FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource.RecostScalar
        C.geometric.output.chosen
          (kap := kh0) (QmaxNext := qmax0)
          C.geometric.output.chosen.c2 C.eta_continuous
          C.eta1_continuous C.eta2_continuous) :
    ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.RecursiveFacts
      (X.scaledInput K) :=
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.RecursiveFacts.ofTerminal
    (X.scaledInput K)
    (by
      intro s
      rw [ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.source_K_eq_unscaled]
      simpa [scaledInput,
        ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.unscaled] using
        X.terminalCurvature_nonnegative s)
    (by
      rw [ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.source_F_eq_unscaled]
      simpa [scaledInput,
        ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.unscaled] using
        X.terminalRange)

noncomputable def toScaled
    (X : AllowanceWitness C p0 kh0 khat0 qmax0 eps)
    (K :
      FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource.RecostScalar
        C.geometric.output.chosen
          (kap := kh0) (QmaxNext := qmax0)
          C.geometric.output.chosen.c2 C.eta_continuous
          C.eta1_continuous C.eta2_continuous) :
    ScaledAllowanceWitness C p0 kh0 khat0 qmax0 eps where
  input := X.scaledInput K
  eps_eq := by simpa [scaledInput] using X.eps_eq
  periodUpper_eq := by simpa [scaledInput] using X.periodUpper_eq
  recursiveFacts := X.recursiveFacts K

end AllowanceWitness

/-- Construct the exact recost pre-carrier input from the current source's
retained selection bounds.  All normalized marking estimates are nonaffine;
the error is definitionally the configured major at `j`. -/
def exists_input
    (C : Core S)
    (B : SelectionBounds S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hmass_one : sourceMass S.source ≤ 1)
    (hperiod : rearPeriod S.source 0 ≤ ellCap O.data (j + 1))
    (hmass : sourceMass S.source ≤
      Dtarget * scaledSuccessorPhysicalDefect O.data j)
    (hEtotal : Etotal ≤ 1 / 8) :
    Nonempty (Input C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q)) := by
  let W := C.geometric.output.chosen
  have hPl : ∀ t, ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q ≤
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source t :=
    fun t ↦
      (ConfiguredRecursiveEdgeRecostedDirectInput.edgeSourceP0_le_one O.data q).trans
        (hfloor t)
  obtain ⟨selected⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1.exists_exactSelected
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)
      sourceKh_nonnegative sourceKh_lt_one hPl scalar.period_le
      (fun t s ↦ (le_abs_self _).trans (scalar.curvature_le t s))
      B.normalizedCurvatureTime_le B.periodTime_le
  let pre := FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
    selected sourceKh_nonnegative sourceKh_lt_one
  obtain ⟨gauge⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence.exists_gauge
      selected pre W sourceKh_nonnegative sourceKh_lt_one
  let shifted := FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
    pre gauge sourceKh_nonnegative sourceKh_lt_one
  have hunit : S.Gamma.T = 1 := W.time_eq.symm.trans C.time_one
  let jets := normalizedJetBounds_major O j W hfloor hunit hmass_one hperiod hmass
  have heps : O.major j ≤ 1 / 4 := major_le_quarter O j hEtotal
  exact ⟨{
    selected := selected
    pre := pre
    gauge := gauge
    shifted := shifted
    kh_nonnegative := sourceKh_nonnegative
    kh_lt_one := sourceKh_lt_one
    scalar := scalar
    P0_pos := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q
    eps := O.major j
    jets := jets
    eps_le_quarter := heps
    bounds := by
      simpa only using
        (ConfiguredRecursiveEdgeDirectRecostBounds.directBounds O.data q W
          selected pre gauge shifted scalar C.eta_continuous C.eta1_continuous
          C.eta2_continuous jets heps hfloor C.time_one)
    rawSlice := rawSlice C selected pre gauge shifted scalar hfloor }⟩

/-- The recursive sidecar package projects the only qualitative selection
provenance used by `exists_input`. -/
theorem exists_input_ofSidecars
    (C : Core S)
    (H : RecursiveExactSidecars S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hmass_one : sourceMass S.source ≤ 1)
    (hperiod : rearPeriod S.source 0 ≤ ellCap O.data (j + 1))
    (hmass : sourceMass S.source ≤
      Dtarget * scaledSuccessorPhysicalDefect O.data j)
    (hEtotal : Etotal ≤ 1 / 8) :
    Nonempty (Input C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q)) :=
  exists_input C H.selection scalar hfloor hmass_one hperiod hmass hEtotal

/-- Exact nonaffine pre-carrier input charged directly to the current source
mass.  This is the depth-zero entry point: the physical base source is paid
for by its composition-mass estimate, before any multiplier recost density
has been installed. -/
def exists_input_of_mass_spec
    {eps : ℝ}
    (C : Core S)
    (B : SelectionBounds S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hmass_one : sourceMass S.source ≤ 1)
    (hlinear :
      FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
          S.source 1 J.scalar.Mend * sourceMass S.source ≤ eps)
    (heps_quarter : eps ≤ 1 / 4) :
    ∃ I : Input C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q),
      I.eps = eps ∧
        I.slice.periodUpper =
          ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q := by
  let W := C.geometric.output.chosen
  have hPl : ∀ t, ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q ≤
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source t :=
    fun t ↦
      (ConfiguredRecursiveEdgeRecostedDirectInput.edgeSourceP0_le_one O.data q).trans
        (hfloor t)
  obtain ⟨selected⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1.exists_exactSelected
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)
      sourceKh_nonnegative sourceKh_lt_one hPl scalar.period_le
      (fun t s ↦ (le_abs_self _).trans (scalar.curvature_le t s))
      B.normalizedCurvatureTime_le B.periodTime_le
  let pre := FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
    selected sourceKh_nonnegative sourceKh_lt_one
  obtain ⟨gauge⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence.exists_gauge
      selected pre W sourceKh_nonnegative sourceKh_lt_one
  let shifted := FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
    pre gauge sourceKh_nonnegative sourceKh_lt_one
  have hunit : S.Gamma.T = 1 := W.time_eq.symm.trans C.time_one
  let jets :=
    FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.normalizedJetBounds_mono
      (FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.normalizedJetBounds_linear_one
        W hfloor hunit (hmass_one.trans J.one_le_Mend)) hlinear
  refine ⟨{
    selected := selected
    pre := pre
    gauge := gauge
    shifted := shifted
    kh_nonnegative := sourceKh_nonnegative
    kh_lt_one := sourceKh_lt_one
    scalar := scalar
    P0_pos := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q
    eps := eps
    jets := jets
    eps_le_quarter := heps_quarter
    bounds := by
      simpa only using
        (ConfiguredRecursiveEdgeDirectRecostBounds.directBounds O.data q W
          selected pre gauge shifted scalar C.eta_continuous C.eta1_continuous
          C.eta2_continuous jets heps_quarter hfloor C.time_one)
    rawSlice := rawSlice C selected pre gauge shifted scalar hfloor }, ⟨rfl, rfl⟩⟩

def exists_input_of_mass
    {eps : ℝ}
    (C : Core S)
    (B : SelectionBounds S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hmass_one : sourceMass S.source ≤ 1)
    (hlinear :
      FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
          S.source 1 J.scalar.Mend * sourceMass S.source ≤ eps)
    (heps_quarter : eps ≤ 1 / 4) :
    Nonempty (Input C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q)) :=
  (exists_input_of_mass_spec C B scalar hfloor hmass_one hlinear
    heps_quarter).nonempty

/-- The mass-charged depth-zero input together with the terminal facts of its
exact ReadySource.  This is the base-row analogue of
`exists_input_of_allowance_recursive_spec`; it records the facts before any
multiplier density is installed. -/
def exists_input_of_mass_recursive_spec
    {eps : ℝ}
    (C : Core S)
    (B : SelectionBounds S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hmass_one : sourceMass S.source ≤ 1)
    (hlinear :
      FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
          S.source 1 J.scalar.Mend * sourceMass S.source ≤ eps)
    (heps_quarter : eps ≤ 1 / 4) :
    Nonempty (AllowanceWitness C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q) eps) := by
  obtain ⟨I, hI, hperiod⟩ :=
    exists_input_of_mass_spec C B scalar hfloor hmass_one hlinear heps_quarter
  let R := rawRecursive C I.selected I.pre I.gauge I.shifted I.scalar hfloor
  refine ⟨{
    input := I
    eps_eq := hI
    periodUpper_eq := hperiod
    terminalCurvature_nonnegative := ?_
    terminalRange := ?_ }⟩
  · intro s
    change 0 ≤
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
        C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
        sourceKh_nonnegative sourceKh_lt_one I.scalar I.P0_pos).K
          C.geometric.output.chosen.Delta.T s
    exact R.terminalCurvature_nonnegative s
  · change Set.range
      ((FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
        C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
        sourceKh_nonnegative sourceKh_lt_one I.scalar I.P0_pos).F
          C.geometric.output.chosen.Delta.T) =
        Set.range C.geometric.output.jets.rear.1
    exact R.terminalRange

/-- Truthful multiplier-source constructor charged to an explicit finite
history epsilon.  Unlike `exists_input`, this theorem does not identify the
multiplier source mass with the legacy scaled-successor defect and does not
charge its jets to `O.major j`. -/
def exists_input_of_allowance_recursive_spec
    {E0 C0 C1 C2 eps : ℝ}
    (C : Core S)
    (B : SelectionBounds S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hperiod : rearPeriod S.source 0 ≤ ellCap O.data (q + 1))
    (hmass : sourceMass S.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q)
    (hallow_one :
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q ≤ 1)
    (hrecost_le_eps :
      recostJetMajor O.data J.scalar.Mend E0 C0 C1 C2 q ≤ eps)
    (heps_quarter : eps ≤ 1 / 4) :
    Nonempty (AllowanceWitness C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q) eps) := by
  let W := C.geometric.output.chosen
  have hPl : ∀ t, ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q ≤
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source t :=
    fun t ↦
      (ConfiguredRecursiveEdgeRecostedDirectInput.edgeSourceP0_le_one O.data q).trans
        (hfloor t)
  obtain ⟨selected⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1.exists_exactSelected
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)
      sourceKh_nonnegative sourceKh_lt_one hPl scalar.period_le
      (fun t s ↦ (le_abs_self _).trans (scalar.curvature_le t s))
      B.normalizedCurvatureTime_le B.periodTime_le
  let pre := FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
    selected sourceKh_nonnegative sourceKh_lt_one
  obtain ⟨gauge⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence.exists_gauge
      selected pre W sourceKh_nonnegative sourceKh_lt_one
  let shifted := FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
    pre gauge sourceKh_nonnegative sourceKh_lt_one
  have hunit : S.Gamma.T = 1 := W.time_eq.symm.trans C.time_one
  have hmass_one : sourceMass S.source ≤ 1 := hmass.trans hallow_one
  have hcoeff0 : 0 ≤
      FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
        S.source 1 J.scalar.Mend := by
    unfold FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
      GaugeTerminalNearIdentityJets.jetLinearConst
    apply le_max_of_le_left
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (S.source.rear_period_pos 0).le
          (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
            S.source.kh_nonnegative S.source.kh_lt_one))
        (add_nonneg (Real.exp_pos _).le zero_le_one))
      zero_le_one
  have hlinear :
      FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
          S.source 1 J.scalar.Mend * sourceMass S.source ≤ eps := by
    calc
      _ ≤
          FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
              S.source 1 J.scalar.Mend *
            ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
              O.data E0 C0 C1 C2 q :=
        mul_le_mul_of_nonneg_left hmass hcoeff0
      _ ≤ recostJetMajor O.data J.scalar.Mend E0 C0 C1 C2 q :=
        floorJetLinearConst_mul_allowance_le O.data J.scalar.Mend
          E0 C0 C1 C2 q S.source hperiod
      _ ≤ eps := hrecost_le_eps
  let jets :=
    FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.normalizedJetBounds_mono
      (FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.normalizedJetBounds_linear_one
        W hfloor hunit (hmass_one.trans J.one_le_Mend)) hlinear
  let I : Input C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q) :=
    { selected := selected
      pre := pre
      gauge := gauge
      shifted := shifted
      kh_nonnegative := sourceKh_nonnegative
      kh_lt_one := sourceKh_lt_one
      scalar := scalar
      P0_pos := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q
      eps := eps
      jets := jets
      eps_le_quarter := heps_quarter
      bounds := by
        simpa only using
          (ConfiguredRecursiveEdgeDirectRecostBounds.directBounds O.data q W
            selected pre gauge shifted scalar C.eta_continuous C.eta1_continuous
            C.eta2_continuous jets heps_quarter hfloor C.time_one)
      rawSlice := rawSlice C selected pre gauge shifted scalar hfloor }
  let R := rawRecursive C selected pre gauge shifted scalar hfloor
  have hterminalCurvature_nonnegative :
      ∀ s, 0 ≤ I.source.K C.path.T s := by
    intro s
    change 0 ≤
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
        W selected pre gauge shifted sourceKh_nonnegative sourceKh_lt_one
        scalar (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)).K
          W.Delta.T s
    exact R.terminalCurvature_nonnegative s
  have hterminalRange :
      Set.range (I.source.F C.path.T) =
        Set.range C.geometric.output.jets.rear.1 := by
    change Set.range
        ((FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
          W selected pre gauge shifted sourceKh_nonnegative sourceKh_lt_one
          scalar (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos O.data q)).F
            W.Delta.T) =
      Set.range C.geometric.output.jets.rear.1
    exact R.terminalRange
  exact ⟨{
    input := I
    eps_eq := rfl
    periodUpper_eq := rfl
    terminalCurvature_nonnegative := hterminalCurvature_nonnegative
    terminalRange := hterminalRange }⟩

/-- Compatibility projection retaining the original allowance API. -/
def exists_input_of_allowance_spec
    {E0 C0 C1 C2 eps : ℝ}
    (C : Core S)
    (B : SelectionBounds S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hperiod : rearPeriod S.source 0 ≤ ellCap O.data (q + 1))
    (hmass : sourceMass S.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q)
    (hallow_one :
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q ≤ 1)
    (hrecost_le_eps :
      recostJetMajor O.data J.scalar.Mend E0 C0 C1 C2 q ≤ eps)
    (heps_quarter : eps ≤ 1 / 4) :
    ∃ I : Input C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q), I.eps = eps := by
  obtain ⟨X⟩ := exists_input_of_allowance_recursive_spec C B scalar hfloor
    hperiod hmass hallow_one hrecost_le_eps heps_quarter
  exact ⟨X.input, X.eps_eq⟩

/-- Once the independently justified multiplier scalar is supplied, the same
allowance construction returns the scaled input together with all recursive
facts.  No multiplier existence is inferred from the source allowance. -/
def exists_scaled_input_of_allowance_spec
    {E0 C0 C1 C2 eps : ℝ}
    (C : Core S)
    (B : SelectionBounds S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (recostScalar :
      FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource.RecostScalar
        C.geometric.output.chosen
          (kap := sourceKh)
          (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q)
          C.geometric.output.chosen.c2 C.eta_continuous
          C.eta1_continuous C.eta2_continuous)
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hperiod : rearPeriod S.source 0 ≤ ellCap O.data (q + 1))
    (hmass : sourceMass S.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q)
    (hallow_one :
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q ≤ 1)
    (hrecost_le_eps :
      recostJetMajor O.data J.scalar.Mend E0 C0 C1 C2 q ≤ eps)
    (heps_quarter : eps ≤ 1 / 4) :
    Nonempty (ScaledAllowanceWitness C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q) eps) := by
  obtain ⟨X⟩ := exists_input_of_allowance_recursive_spec C B scalar hfloor
    hperiod hmass hallow_one hrecost_le_eps heps_quarter
  exact ⟨X.toScaled recostScalar⟩

def exists_input_of_allowance
    {E0 C0 C1 C2 eps : ℝ}
    (C : Core S)
    (B : SelectionBounds S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hperiod : rearPeriod S.source 0 ≤ ellCap O.data (q + 1))
    (hmass : sourceMass S.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q)
    (hallow_one :
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q ≤ 1)
    (hrecost_le_eps :
      recostJetMajor O.data J.scalar.Mend E0 C0 C1 C2 q ≤ eps)
    (heps_quarter : eps ≤ 1 / 4) :
    Nonempty (Input C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q)) :=
  (exists_input_of_allowance_spec C B scalar hfloor hperiod hmass hallow_one
    hrecost_le_eps heps_quarter).nonempty

/-- Sidecar specialization of `exists_input_of_allowance`; no new recursive
selection callback is introduced. -/
theorem exists_input_ofSidecars_allowance
    {E0 C0 C1 C2 eps : ℝ}
    (C : Core S)
    (H : RecursiveExactSidecars S.source)
    (scalar : Scalar (A := S.source) (kap := sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      (khatNext := analyticKhat O.data)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q))
    (hfloor : ∀ t, 1 ≤ rearPeriod S.source t)
    (hperiod : rearPeriod S.source 0 ≤ ellCap O.data (q + 1))
    (hmass : sourceMass S.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q)
    (hallow_one :
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        O.data E0 C0 C1 C2 q ≤ 1)
    (hrecost_le_eps :
      recostJetMajor O.data J.scalar.Mend E0 C0 C1 C2 q ≤ eps)
    (heps_quarter : eps ≤ 1 / 4) :
    Nonempty (Input C
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 O.data q)
      sourceKh (analyticKhat O.data)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap O.data q)) :=
  exists_input_of_allowance C H.selection scalar hfloor hperiod hmass
    hallow_one hrecost_le_eps heps_quarter

end ConfiguredRecursiveEdgeRecostMultiplierNonaffinePreCarrierInput
