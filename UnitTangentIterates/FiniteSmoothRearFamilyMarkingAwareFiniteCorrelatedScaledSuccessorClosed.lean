import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedScaledSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenCanonicalEndpointCap

/-!
# Closed geometric sidecars for composition-scaled finite successors

The phase equalities in this file are retained from the same explicit
selected/pretransport/gauge witness which constructs the scaled source.  This
avoids comparing two unrelated classical choices of analytic successor.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization
  FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

private theorem range_shiftData_closed (p : Data) (b : ℝ) :
    range (MarkedShift.shiftData b p).1 = range p.1 := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u + b, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u - b, by simp [MarkedShift.shiftData, MarkedShift.shiftMap]⟩

/-- The affinely marked selected rear at terminal time is exactly the
ordinary terminal datum retained by a presented row. -/
theorem PresentedRow.selectedRearData_terminal_eq_base
    {a b : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (R : PresentedRow A) : A.selectedRearData Gamma.T = R.base := by
  have hperiod : rearPeriod A Gamma.T = perim R.base :=
    R.terminalInput.rearPeriod_terminal
  have hper_ne : perim R.base ≠ 0 := by
    rw [← hperiod]
    exact (A.rear_period_pos Gamma.T).ne'
  have hcurve : ∀ u, (A.selectedRearData Gamma.T).1 u = R.base.1 u := by
    intro u
    rw [MarkingAwareSource.selectedRearData_curve,
      MarkingAwareSource.selectedRearCurve]
    rw [← R.terminalInput.terminal_carrier (rearPeriod A Gamma.T * u)]
    rw [hperiod]
    field_simp
  have hcurveFun : (⇑(A.selectedRearData Gamma.T).1) = R.base.1 := funext hcurve
  have hvel : ∀ u, (A.selectedRearData Gamma.T).2.1 u = R.base.2.1 u := by
    intro u
    have H := A.selectedRearData_curve_deriv Gamma.T u
    rw [hcurveFun] at H
    exact H.unique (R.terminalInput.zero_floor_tube.hasDerivAt_curve u)
  have hvelFun : (⇑(A.selectedRearData Gamma.T).2.1) = R.base.2.1 := funext hvel
  have hacc : ∀ u, (A.selectedRearData Gamma.T).2.2 u = R.base.2.2 u := by
    intro u
    have H := A.selectedRearData_velocity_deriv Gamma.T u
    rw [hvelFun] at H
    exact H.unique (R.terminalInput.zero_floor_tube.hasDerivAt_vel u)
  apply Prod.ext
  · exact BoundedContinuousFunction.ext hcurve
  · apply Prod.ext
    · exact BoundedContinuousFunction.ext hvel
    · exact BoundedContinuousFunction.ext hacc

/-- A positive ordinary tube for the canonical terminal-front datum makes the
normalized front injective on one marked period. -/
theorem normalizedFront_injective_of_unitTangentData_tube
    {a b p : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax c kmin dlt : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (heq : FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData A = p)
    (hp : IsTubeMember c kmin dlt p) (hdlt : 0 < dlt) :
    InjOn
      (FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.normalizedFront A)
      (Ico 0 1) := by
  intro x hx y hy hxy
  have hcurve : p.1 x = p.1 y := by
    rw [← heq]
    simpa only [FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData_curve]
      using hxy
  have hxcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
  have hchord := hp.chord x hxcc y hycc
  rw [hcurve, sub_self, norm_zero] at hchord
  have hcyc0 : cyc x y = 0 := by
    have hcyc := cyc_nonneg hxcc hycc
    nlinarith
  exact cyc_eq_zero_iff hx hy hcyc0.le

/-- A scaled successor together with its two exact spatial phase links. -/
structure PhaseScaledSuccessorBundle
    {p q a b rear : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b) where
  scaled : ScaledSuccessorBundle W (periodLower := periodLower) (kap := kap)
    (khatNext := khatNext) (QmaxNext := QmaxNext)
  initialPhase : ℝ
  initial_eq : scaled.source.selectedRearData 0 =
    MarkedShift.shiftData initialPhase rear
  terminalPhase : ℝ
  terminal_eq :
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      scaled.source = MarkedShift.shiftData terminalPhase
        (A.selectedRearData W.Delta.T)

/-- Explicit phase-retaining composition-scaled construction. -/
theorem ChosenPath.exists_phaseScaledSuccessorBundle
    {p q a b rear frontData : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower periodUpper kap khatNext QmaxNext Md MP : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (hperiodLower : 0 < periodLower)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ t, periodLower ≤ period A t)
    (hPu : ∀ t, period A t ≤ periodUpper)
    (hKnTbd : ∀ t u,
      |RearOwnHigherRegularity.partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
          (curvature A) (period A)) t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t| ≤ MP)
    (C : FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.Scalar
      (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext) W)
    {cF kF dF cR kR dR : ℝ}
    (K : PhysicalRearLimitKinematics kap rear frontData)
    (hcF : 0 < cF) (hfront : IsTubeMember cF kF dF frontData)
    (hcR : 0 < cR) (hrear : IsTubeMember cR kR dR rear)
    (frontPhase : ℝ)
    (hF : front A 0 = ev (MarkedShift.shiftData frontPhase frontData))
    (hP : period A 0 = perim frontData) :
    Nonempty {X : PhaseScaledSuccessorBundle W (rear := rear)
      (periodLower := periodLower) (kap := kap)
      (khatNext := khatNext) (QmaxNext := QmaxNext) //
      X.scaled.slice.periodUpper ≤ periodUpper} := by
  obtain ⟨S⟩ := exists_exactSelected (A := A)
    hperiodLower hkap0 hkap1 hPl hPu
    (fun t s ↦ (le_abs_self (curvature A t s)).trans
      (C.toScalar.curvature_le t s)) hKnTbd hPtbd
  let R : PreTransport S :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
      S hkap0 hkap1
  obtain ⟨G⟩ := exists_gauge S R W hkap0 hkap1
  let T : ShiftedTransport R G :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
      R G hkap0 hkap1
  let Bnd := scaledBounds W S R G T hkap0 hkap1 C hperiodLower
  let A' := source W S R G hkap0 hkap1 T Bnd
  let Compat := compatibility W S R G hkap0 hkap1 T Bnd
  have hPl' : ∀ t, periodLower ≤ A'.P t := by
    intro t
    rw [Compat.period_eq]
    simpa [rearPeriod] using hPl t
  have hPu' : ∀ t, A'.P t ≤ periodUpper := by
    intro t
    rw [Compat.period_eq]
    simpa [rearPeriod] using hPu t
  let Y :=
    FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor.ofScaledReadySource
      W S R G hkap0 hkap1 T C hperiodLower hPl hPu
  let X : ScaledSuccessorBundle W (periodLower := periodLower) (kap := kap)
      (khatNext := khatNext) (QmaxNext := QmaxNext) :=
    { source := A'
      coeff := C.coeff
      density_eq := rfl
      analytic := Y
      analytic_source_eq := rfl
      compatibility := Compat
      slice :=
        FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.sliceFacts
          W A' Compat hperiodLower hPl' hPu' }
  let initialPhase := physicalRearPhase K frontPhase
  have hA'F : A'.F 0 = ev (MarkedShift.shiftData frontPhase frontData) :=
    (readySource_front_zero W S R G hkap0 hkap1 T Bnd).trans hF
  have hA'P : A'.P 0 = perim frontData := by
    change period A 0 = perim frontData
    exact hP
  have hinitial := selectedRearData_zero_eq_shift_physicalRear A' K hcF hfront
    hcR hrear frontPhase hA'F hA'P
  let terminalPhase :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
      S G.q W.Delta.T / period A W.Delta.T
  have hterminal := readySource_unitTangentData_eq_shift_selectedRearData
    W S R G hkap0 hkap1 T Bnd
  let Z : PhaseScaledSuccessorBundle W (rear := rear)
      (periodLower := periodLower) (kap := kap)
      (khatNext := khatNext) (QmaxNext := QmaxNext) :=
    { scaled := X
      initialPhase := initialPhase
      initial_eq := by simpa [X, A', initialPhase] using hinitial
      terminalPhase := terminalPhase
      terminal_eq := by
        simpa [X, A', terminalPhase] using hterminal }
  exact ⟨⟨Z, by rfl⟩⟩

/-- Cross-row physical phase data needed to normalize the source below row
`n+1` against row `n`'s canonical terminal rear. -/
structure ScaledSuccessorPhaseData
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) where
  frontPhase : ℕ → ℝ
  front_zero : ∀ n, front (S.source (n + 1)) 0 =
    ev (MarkedShift.shiftData (frontPhase n) (H.row n).terminalInput.frontData)
  period_zero : ∀ n, period (S.source (n + 1)) 0 =
    perim (H.row n).terminalInput.frontData

/-- The phase-retaining scaled bundles chosen uniformly over a finite
correlated column. -/
structure PhaseScaledSuccessorBundles
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (B : RowBounds H) where
  bundle : ∀ n, PhaseScaledSuccessorBundle
    (H.row (n + 1)).output.chosen (rear := (H.row n).base)
    (periodLower := P0 n) (kap := kh n)
    (khatNext := khat n) (QmaxNext := Qmax n)
  periodUpper_le : ∀ n, (bundle n).scaled.slice.periodUpper ≤ P1 n

def PhaseScaledSuccessorBundles.toScaled
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : PhaseScaledSuccessorBundles H B) :
    ScaledSuccessorBundles H B where
  bundle n := (X.bundle n).scaled
  periodUpper_le n := X.periodUpper_le n

noncomputable def ScaledSuccessorScalarData.phaseBundles
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (D : ScaledSuccessorScalarData H)
    (P : ScaledSuccessorPhaseData H) : PhaseScaledSuccessorBundles H B where
  bundle := fun n ↦
    (Classical.choice (ChosenPath.exists_phaseScaledSuccessorBundle
      (H.row (n + 1)).output.chosen
      (D.periodLower_pos n) (D.kh_nonnegative n) (D.kh_lt_one n)
      (D.periodLower_le n) (D.periodUpper_le n)
      (D.normalizedCurvatureTime_le n) (D.periodTime_le n) (D.scalar n)
      (H.row n).output.frontKinematics
      (H.row n).cFront_pos (H.row n).front_tube
      (H.row n).terminalInput.physical.cq_pos
      (H.row n).terminalInput.zero_floor_tube
      (P.frontPhase n) (P.front_zero n) (P.period_zero n))).1
  periodUpper_le := fun n ↦
    (Classical.choice (ChosenPath.exists_phaseScaledSuccessorBundle
      (H.row (n + 1)).output.chosen
      (D.periodLower_pos n) (D.kh_nonnegative n) (D.kh_lt_one n)
      (D.periodLower_le n) (D.periodUpper_le n)
      (D.normalizedCurvatureTime_le n) (D.periodTime_le n) (D.scalar n)
      (H.row n).output.frontKinematics
      (H.row n).cFront_pos (H.row n).front_tube
      (H.row n).terminalInput.physical.cq_pos
      (H.row n).terminalInput.zero_floor_tube
      (P.frontPhase n) (P.front_zero n) (P.period_zero n))).2

/-- The two Ready sidecars are consequences of the retained phases and row
tubes; no additional oracle is required. -/
noncomputable def PhaseScaledSuccessorBundles.readySidecars
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : PhaseScaledSuccessorBundles H B)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1) :
    ScaledSuccessorReadySidecars X.toScaled where
  front_injective n := by
    let Z := X.bundle n
    let R := H.row (n + 1)
    have hterminal :
        FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
          Z.scaled.source = MarkedShift.shiftData Z.terminalPhase R.base := by
      rw [Z.terminal_eq]
      congr 1
      rw [R.output.chosen.time_eq]
      exact
        FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn.PresentedRow.selectedRearData_terminal_eq_base R
    simpa [PhaseScaledSuccessorBundles.toScaled,
      ScaledSuccessorBundles.nextColumn] using
      (normalizedFront_injective_of_unitTangentData_tube Z.scaled.source
        hterminal
        (MarkedShift.isTubeMember_shiftData R.terminalInput.zero_floor_tube
          Z.terminalPhase)
        R.terminalInput.dlt_pos)
  initial_range_current n := by
    let Z := X.bundle n
    let R := H.row n
    let T := R.canonicalTarget (hkh0 n) (hkh1 n)
    have hbase := T.endpoint_range_eq_target
    have hbase_eq : R.base = MarkedShift.shiftData T.phase
        (SelectedInverseMap.selInv (kh n) R.terminalInput.frontData) := T.base_eq
    rw [← hbase_eq] at hbase
    change range (⇑(Z.scaled.source.selectedRearData 0).1) =
      range (⇑R.output.jets.rear.1)
    rw [Z.initial_eq, range_shiftData_closed]
    exact hbase.symm

/-- The exact coefficient-weighted mass condition needed to place the scaled
successor in a prescribed configured defect envelope. -/
structure ScaledSuccessorMassDomination
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt target : ℝ}
    {defect : ℕ → ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : PhaseScaledSuccessorBundles H B) : Prop where
  weighted_cost_le : ∀ n,
    (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) *
        (H.row (n + 1)).output.chosen.Delta.cost ≤ target * defect n

/-- Noncircular recost inputs for the fixed target.  The `recost_cost_le`
field is the exact interface supplied by stable physical components after the
canonical path has been recosted.  The last field records the scalar
comparison between the row defect used by that estimate and the configured
composition defect. -/
structure RecostedScaledSuccessorMassData
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt stableTarget : ℝ}
    {rawDefect defect : ℕ → ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : PhaseScaledSuccessorBundles H B) where
  coeffBound : ℕ → ℝ
  stableTarget_nonnegative : 0 ≤ stableTarget
  rawDefect_nonnegative : ∀ n, 0 ≤ rawDefect n
  coeffBound_nonnegative : ∀ n, 0 ≤ coeffBound n
  scaledCoeff_nonnegative : ∀ n, 0 ≤
    (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2)
  scaledCoeff_le : ∀ n,
    (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) ≤
      2 * coeffBound n
  recost_cost_le : ∀ n,
    (H.row (n + 1)).output.chosen.Delta.cost ≤
      4 * stableTarget * rawDefect n
  coeff_rawDefect_le : ∀ n, coeffBound n * rawDefect n ≤ defect n

theorem RecostedScaledSuccessorMassData.toMassDomination
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt stableTarget : ℝ}
    {rawDefect defect : ℕ → ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} {X : PhaseScaledSuccessorBundles H B}
    (M : RecostedScaledSuccessorMassData
      (stableTarget := stableTarget) (rawDefect := rawDefect)
      (defect := defect) X) :
    ScaledSuccessorMassDomination (target := 8 * stableTarget)
      (defect := defect) X := by
  constructor
  intro n
  have hcost := mul_le_mul_of_nonneg_left
    (M.recost_cost_le n) (M.scaledCoeff_nonnegative n)
  have hraw0 : 0 ≤ 4 * stableTarget * rawDefect n :=
    mul_nonneg (mul_nonneg (by norm_num) M.stableTarget_nonnegative)
      (M.rawDefect_nonnegative n)
  have hcoeff := mul_le_mul_of_nonneg_right (M.scaledCoeff_le n) hraw0
  calc
    (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) *
        (H.row (n + 1)).output.chosen.Delta.cost ≤
      (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) *
        (4 * stableTarget * rawDefect n) := hcost
    _ ≤ (2 * M.coeffBound n) * (4 * stableTarget * rawDefect n) := hcoeff
    _ = (8 * stableTarget) * (M.coeffBound n * rawDefect n) := by ring
    _ ≤ (8 * stableTarget) * defect n :=
      mul_le_mul_of_nonneg_left (M.coeff_rawDefect_le n)
        (mul_nonneg (by norm_num) M.stableTarget_nonnegative)

/-- One closed scaled successor step: next column, iterative Ready package,
and the exact configured source-mass invariant. -/
structure ClosedScaledSuccessorStep
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt target : ℝ}
    {defect : ℕ → ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (B : RowBounds H) where
  phaseBundles : PhaseScaledSuccessorBundles H B
  nextReady : ReadyColumn phaseBundles.toScaled.nextColumn
  sourceMass : SourceMassInvariant phaseBundles.toScaled.nextColumn target defect

noncomputable def PhaseScaledSuccessorBundles.closedStep
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt target : ℝ}
    {defect : ℕ → ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : PhaseScaledSuccessorBundles H B)
    (hkh0 : ∀ n, 0 ≤ kh n) (hkh1 : ∀ n, kh n < 1)
    (M : ScaledSuccessorMassDomination (target := target) (defect := defect) X) :
    ClosedScaledSuccessorStep (target := target) (defect := defect) H B where
  phaseBundles := X
  nextReady := X.toScaled.nextReadyColumn (X.readySidecars hkh0 hkh1)
  sourceMass := by
    constructor
    intro n
    calc
      FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
          (X.toScaled.nextColumn.source n) =
          (X.bundle n).scaled.coeff / Real.sqrt (1 - (kh n) ^ 2) *
            (H.row (n + 1)).output.chosen.Delta.cost := by
        simpa [PhaseScaledSuccessorBundles.toScaled,
          ScaledSuccessorBundles.nextColumn] using
          (X.bundle n).scaled.sourceMass_eq
      _ ≤ target * defect n := M.weighted_cost_le n

end FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
