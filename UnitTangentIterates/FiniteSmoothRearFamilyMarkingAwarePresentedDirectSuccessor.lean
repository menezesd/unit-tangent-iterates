import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareDirectSuccessor

/-!
# Direct successors with an independently presented terminal

The legacy direct-row interface fixes the terminal marked datum to the
normalized terminal stored by the old rich stage.  A genuinely selected rear
may instead be a different presentation (in particular, the selected inverse
of that carrier).  This parallel interface retains that datum explicitly and
installs it as the terminal base of the newly selected rich stage.

No equality with the legacy terminal is asserted.  The selected output still
has the correct inverse-pullback orientation: its range edge is the old source
endpoint, while its chosen rear is the new predecessor.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor

open AnchoredJacobiStableTransition
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  NormalPathC2IncrementVariableSpeed
  PhysicalArclengthJacobiTransition
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- One selected row whose physical terminal presentation is independent of
the terminal stored by the input column. -/
structure PresentedRowSelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  presented : Data
  applied : Applied
    (S.column.step.richStage (n + 1)).stage.increment (S.source n)
  terminalInput : PresentedTerminalInputCore
    (p := S.column.step.next n) (base := presented)
    (bound := e n (k + 1)) applied
  output : PresentedOutputCore applied terminalInput
  front_range : range (ev terminalInput.frontData) =
    range (S.column.step.next (n + 1)).1
  P1_le : GaugeFlowDerivCost.costP1
      (rearPeriod (S.source n) 0) (khat n)
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ P1 n
  G1_le : GaugeFlowDerivCost.costG1
      (rearPeriod (S.source n) 0) (khat n) (rearKappa2 (kh n))
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ G1 n
  Cg_le : (khat n) * GaugeFlowDerivCost.costG1
        (rearPeriod (S.source n) 0) (khat n) (rearKappa2 (kh n))
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) +
      rearKappa2 (kh n) * GaugeFlowDerivCost.costP1
        (rearPeriod (S.source n) 0) (khat n)
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) ^ 2 ≤ Cg n
  terminal_perim_ge_one : 1 ≤ perim presented
  period_ge_one : 1 ≤ period n (k + 1)
  components_nonnegative :
    (components (period n (k + 1)) output.chosen.Delta.eta).Nonnegative
  components_bound : ComponentBound
    (components (period n (k + 1)) output.chosen.Delta.eta)
    (diagonal (n + (k + 1)))
  transition : Transition
    (components (period (n + 1) k)
      (S.column.step.richStage (n + 1)).stage.increment.eta)
    (components (period n (k + 1)) output.chosen.Delta.eta)
    (a n k) (MA n k) (NA n k) K0 K1 K2

/-- The independently presented terminal has a canonical finite Harnack
certificate, directly from the tube and strictness retained by its exact
`TerminalInput`. -/
def PresentedRowSelection.presentedHarnack
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    VariableMarkedTube.ArclengthHarnackCertificate R.presented where
  q := R.presented
  c := R.terminalInput.physical.cq
  dlt := R.terminalInput.physical.dlt
  c_pos := R.terminalInput.physical.cq_pos
  dlt_pos := R.terminalInput.dlt_pos
  tube := R.terminalInput.zero_floor_tube
  same_range := rfl
  strictness := R.terminalInput.strict

/-- Non-erasing near-identity jets on the exact marking selected by a
presented row.  This is the minimal sidecar missing from `ChosenTerminal.Output`:
the scalar tail bounds a number, but the output record itself does not retain
the two inequalities connecting that number to its actual marking. -/
structure PresentedNearIdentitySelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 eps : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) : Prop where
  eps_nonnegative : 0 ≤ eps
  dpsi : ∀ u, |R.output.marking.dpsi u - 1| ≤ eps
  ddpsi : ∀ u, |R.output.ddpsi u| ≤ eps

/-- Minimal theorem-facing input.  The terminal presentation and its
`TerminalInput` may depend on the actual intrinsic long application. -/
structure PresentedRowConstruction
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  presented : ∀ E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n), Data
  terminalInput : ∀ E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n),
    PresentedTerminalInputCore (p := S.column.step.next n) (base := presented E)
      (bound := e n (k + 1)) E
  front_range : ∀ E, range (ev (terminalInput E).frontData) =
    range (S.column.step.next (n + 1)).1
  P1_le : GaugeFlowDerivCost.costP1
      (rearPeriod (S.source n) 0) (khat n)
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ P1 n
  G1_le : GaugeFlowDerivCost.costG1
      (rearPeriod (S.source n) 0) (khat n) (rearKappa2 (kh n))
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ G1 n
  Cg_le : (khat n) * GaugeFlowDerivCost.costG1
        (rearPeriod (S.source n) 0) (khat n) (rearKappa2 (kh n))
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) +
      rearKappa2 (kh n) * GaugeFlowDerivCost.costP1
        (rearPeriod (S.source n) 0) (khat n)
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) ^ 2 ≤ Cg n
  terminal_perim_ge_one : ∀ E, 1 ≤ perim (presented E)
  period_ge_one : 1 ≤ period n (k + 1)
  components_nonnegative : ∀ E
    (O : PresentedOutputCore E (terminalInput E)),
    (components (period n (k + 1)) O.chosen.Delta.eta).Nonnegative
  components_bound : ∀ E
      (O : PresentedOutputCore E (terminalInput E)),
    ComponentBound (components (period n (k + 1)) O.chosen.Delta.eta)
      (diagonal (n + (k + 1)))
  transition : ∀ E (O : PresentedOutputCore E (terminalInput E)),
    Transition
      (components (period (n + 1) k)
        (S.column.step.richStage (n + 1)).stage.increment.eta)
      (components (period n (k + 1)) O.chosen.Delta.eta)
      (a n k) (MA n k) (NA n k) K0 K1 K2

theorem PresentedRowConstruction.exists_selection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : PresentedRowConstruction (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    Nonempty (PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) := by
  obtain ⟨E⟩ := exists_applied (S.source n)
  let B := R.terminalInput E
  obtain ⟨O⟩ := exists_presentedOutputCore E B
  exact ⟨{
    presented := R.presented E
    applied := E
    terminalInput := B
    output := O
    front_range := R.front_range E
    P1_le := R.P1_le
    G1_le := R.G1_le
    Cg_le := R.Cg_le
    terminal_perim_ge_one := R.terminal_perim_ge_one E
    period_ge_one := R.period_ge_one
    components_nonnegative := R.components_nonnegative E O
    components_bound := R.components_bound E O
    transition := R.transition E O }⟩

noncomputable def PresentedRowConstruction.selection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : PresentedRowConstruction (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S :=
  Classical.choice R.exists_selection

/-- All rows selected at one recursive depth, together with exact analytic
successors on their actual chosen predecessor paths. -/
structure PresentedRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  row : ∀ n, PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
    (K0 := K0) (K1 := K1) (K2 := K2) S
  analytic : ∀ n, AnalyticSuccessor
    (row (n + 1)).output.chosen.Delta (S.source (n + 1))
    (P0 n) (kh n) (khat n) (Qmax n)

/-- A correlated successor whose physical front is the terminal presentation
installed in its own new column, rather than the legacy terminal of the input
column. -/
structure PresentedSuccessor
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  column : CertifiedColumn Q S.column.step.next e (k + 1)
    P0 P1 khat G1 Cg C c dlt period diagonal
      (GaugeFamily period K0 K1 K2)
  transition : TransitionCertificate S.column column a MA NA K0 K1 K2
  analytic : ∀ n, AnalyticSuccessor
    (column.step.richStage (n + 1)).stage.increment (S.source (n + 1))
    (P0 n) (kh n) (khat n) (Qmax n)
  frontData : ∀ n, Data
  front_range : ∀ n, range (ev (frontData n)) =
    range (S.column.step.next (n + 1)).1
  frontKinematics : ∀ n, PhysicalRearLimitKinematics (kh n)
    (column.step.richStage n).terminalBase (frontData n)
  rearStrict : ∀ n, UnconditionalAssembly.LimitStrictnessDataH
    (column.step.richStage n).terminalBase
  rearHarnack : ∀ n, VariableMarkedTube.ArclengthHarnackCertificate
    (column.step.richStage n).terminalBase
  physicalFront : ∀ n, FiniteSmoothRearFamilyPhysicalFront.Certificate (kh n)
    (column.step.richStage n).terminalBase (frontData n)

/-- The correlated column reached by a presented successor. -/
def PresentedSuccessor.mappedColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (X : PresentedSuccessor (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    CorrelatedColumn Q S.column.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2 := by
  refine { column := X.column, source := fun n => ?_ }
  cases X.analytic n with
  | legacy S D R M =>
      exact Classical.choice (exists_markingAwareSuccessorSource_of_majorants M)
  | exact source slice => exact source

def PresentedSuccessor.physicalKinematics
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (X : PresentedSuccessor (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) (n : ℕ) :
    PhysicalRearLimitKinematics (kh n)
      (X.column.step.richStage n).terminalBase
      (X.frontData n) :=
  X.frontKinematics n

theorem PresentedSuccessor.range_physicalFront
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (X : PresentedSuccessor (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) (n : ℕ) :
    range (ev (X.frontData n)) =
      range (ev (X.physicalFront n).physicalFront) :=
  (X.physicalFront n).range_eq

/-- Assemble the ordinary correlated successor while retaining the independent
terminal presentation in every new rich stage. -/
def successorOfPresentedRows
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (W : ∀ n, PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (analytic : ∀ n, AnalyticSuccessor
      (W (n + 1)).output.chosen.Delta (S.source (n + 1))
      (P0 n) (kh n) (khat n) (Qmax n)) :
    PresentedSuccessor (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S := by
  let next : ℕ → Data := fun n => (W n).output.jets.rear
  let step : ColumnStep Q S.column.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt :=
    { next := next
      richStage := fun n => by
        let O := (W n).output
        have hgeom := IsVariableSpeedNormalPath.mono O.chosen.Delta
          (by simpa only [O.stage_eq] using O.stage.increment_geometry)
          ((rearKappa1_nonneg (S.source n).kh_nonnegative
            (S.source n).kh_lt_one).trans (S.source n).rearKappa1_le)
          (W n).P1_le (W n).G1_le (W n).Cg_le
        exact
          { stage :=
              { increment := O.chosen.Delta
                increment_geometry := hgeom
                increment_cost := by
                  simpa [O.stage_eq] using O.stage.increment_cost
                rear_curve_deriv := O.stage.rear_curve_deriv
                rear_vel_deriv := O.stage.rear_vel_deriv
                rear_periodic := O.stage.rear_periodic
                rear_curvature_nonnegative := O.stage.rear_curvature_nonnegative
                range_edge := O.stage.range_edge
                rear_harnack := O.stage.rear_harnack }
            terminalBase := (W n).presented
            lambda := (W n).terminalInput.lambda
            Lambda := (W n).terminalInput.Lambda
            marking :=
              { lambda_pos := (W n).terminalInput.lambda_pos
                marking := O.marking
                ddpsi := O.ddpsi
                psi_deriv := O.psi_deriv
                dpsi_deriv := O.dpsi_deriv
                ddpsi_cont := O.ddpsi_cont
                psi_zero := O.psi_zero } } }
  let T : CertifiedColumn Q S.column.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal
        (GaugeFamily period K0 K1 K2) :=
    { step := step
      period_ge_one := fun n => (W n).period_ge_one
      components_nonnegative := fun n => by
        simpa [step] using (W n).components_nonnegative
      components_bound := fun n => by
        simpa [step] using (W n).components_bound
      gauge := fun n => GaugeCertificate.base
        { terminalBase := (W n).presented
          terminalBase_eq := rfl
          terminalPhysical := (W n).terminalInput.physical } }
  exact
    { column := T
      transition :=
        { transition := fun n => by
            simpa [T, step] using (W n).transition }
      analytic := fun n => by simpa [T, step] using analytic n
      frontData := fun n => (W n).terminalInput.frontData
      front_range := fun n => (W n).front_range
      frontKinematics := fun n => (W n).output.frontKinematics
      rearStrict := fun n => (W n).terminalInput.strict
      rearHarnack := fun n => (W n).presentedHarnack
      physicalFront := fun n => (W n).output.physicalFront }

def PresentedRowFamily.successor
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (F : PresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    PresentedSuccessor (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S :=
  successorOfPresentedRows S F.row F.analytic

/-- All-depth provider restricted to reachable correlated columns. -/
structure PresentedRowProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  rows : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2),
    PresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S

structure PresentedProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  successor : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2),
    PresentedSuccessor (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S

/-- Invariant-indexed presented recursion retaining the exact finite source
slice at every reachable successor. -/
structure PresentedSlicedProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  successor : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2), SlicedCorrelatedColumn S →
    PresentedSuccessor (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S
  mappedSlice : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S) n,
    AnalyticSuccessorSliceFacts (((successor S H).mappedColumn).source n)
  mappedPeriodUpper_le : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S) n,
    (mappedSlice S H n).periodUpper ≤ P1 n

/-- A sliced presented provider retaining the actual near-identity jets of
every selected output.  Its numerical budget is indexed by row and recursive
depth; a successor chosen from depth `k` consumes budget `jetError n (k+1)`. -/
structure PresentedNearIdentitySlicedProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (jetError : ℕ → ℕ → ℝ) where
  rows : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S),
    PresentedRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S
  nearIdentity : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S) n,
    PresentedNearIdentitySelection (eps := jetError n (k + 1))
      ((rows S H).row n)
  mappedSlice : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S) n,
    AnalyticSuccessorSliceFacts ((((rows S H).successor).mappedColumn).source n)
  mappedPeriodUpper_le : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S) n,
    (mappedSlice S H n).periodUpper ≤ P1 n

def PresentedNearIdentitySlicedProvider.slicedProvider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {jetError : ℕ → ℕ → ℝ}
    (G : PresentedNearIdentitySlicedProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2 jetError) :
    PresentedSlicedProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2 where
  successor S H := (G.rows S H).successor
  mappedSlice := G.mappedSlice
  mappedPeriodUpper_le := G.mappedPeriodUpper_le

def PresentedSlicedProvider.mapped
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : PresentedSlicedProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S) :
    SlicedCorrelatedColumn ((G.successor S H).mappedColumn) where
  slice := G.mappedSlice S H
  periodUpper_le := G.mappedPeriodUpper_le S H

/-- One reachable presented recursive state. -/
structure PresentedSlicedState
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (K0 K1 K2 : ℝ) where
  current : ℕ → Data
  depth : ℕ
  column : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  sliced : SlicedCorrelatedColumn column

def PresentedSlicedState.next
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : PresentedSlicedProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (X : PresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax K0 K1 K2) :
    PresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax K0 K1 K2 where
  current := X.column.column.step.next
  depth := X.depth + 1
  column := (G.successor X.column X.sliced).mappedColumn
  sliced := G.mapped X.column X.sliced

def PresentedSlicedProvider.trajectory
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : PresentedSlicedProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (base : PresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (depth : ℕ) :
    PresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2 :=
  (PresentedSlicedState.next G)^[depth] base

def PresentedRowProvider.provider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : PresentedRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) :
    PresentedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax
      a MA NA K0 K1 K2 where
  successor S := (G.rows S).successor

end FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
