import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminalCap
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenMajorants

/-!
# Direct sound marking-aware successor columns

This is the non-erasing boundary between one rowwise long gauge construction
and the correlated recursive column.  Every field below refers to the same
chosen terminal output; in particular the next endpoint, physical front,
component transition, source majorants, and endpoint cap cannot be selected
independently.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareDirectSuccessor

open AnchoredJacobiStableTransition
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  GaugeMarkedDataOfRearFamily
  NormalPathC2IncrementVariableSpeed
  PhysicalArclengthJacobiTransition
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- One exact selected row of the next column.  The only analytic proof field
not produced by the chosen terminal itself is `majorants`; its marking and
density subfields are constructed by `majorantsOfChosenPath`. -/
structure RowSelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  applied : Applied
    (S.column.step.richStage (n + 1)).stage.increment (S.source n)
  terminalInput : TerminalInput
    (p := S.column.step.next n)
    (base := (S.column.step.richStage (n + 1)).terminalBase)
    (bound := e n (k + 1)) applied
  output : Output applied terminalInput
  khat_nonnegative : 0 ≤ khat n
  P1_le : GaugeFlowDerivCost.costP1
      (rearPeriod (S.source n) 0) (khat n)
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ P1 n
  G1_le : GaugeFlowDerivCost.costG1
      (rearPeriod (S.source n) 0) (khat n)
      (rearKappa2 (kh n))
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ G1 n
  Cg_le : (khat n) * GaugeFlowDerivCost.costG1
        (rearPeriod (S.source n) 0) (khat n)
        (rearKappa2 (kh n))
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) +
      rearKappa2 (kh n) * GaugeFlowDerivCost.costP1
        (rearPeriod (S.source n) 0) (khat n)
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) ^ 2 ≤ Cg n
  /-- Lower physical scale needed to normalize the retained terminal flow
  jets.  The abstract column period and the terminal physical perimeter are
  stored independently, so this fact cannot be recovered from
  `period_ge_one`. -/
  terminal_perim_ge_one :
    1 ≤ perim (S.column.step.richStage (n + 1)).terminalBase
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

/-- Minimal concrete data for one row selected from an actual marking-aware
source.  The applied long path and terminal output are retained rather than
reconstructed.  The remaining proof fields are exactly the row ceilings and
component/transition facts not implied by that output. -/
structure ChosenRow
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  applied : Applied
    (S.column.step.richStage (n + 1)).stage.increment (S.source n)
  terminalInput : TerminalInput
    (p := S.column.step.next n)
    (base := (S.column.step.richStage (n + 1)).terminalBase)
    (bound := e n (k + 1)) applied
  output : Output applied terminalInput
  P1_le : GaugeFlowDerivCost.costP1
      (rearPeriod (S.source n) 0) (khat n)
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ P1 n
  G1_le : GaugeFlowDerivCost.costG1
      (rearPeriod (S.source n) 0) (khat n)
      (rearKappa2 (kh n))
      (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
        (S.source n).m t) ≤ G1 n
  Cg_le : (khat n) * GaugeFlowDerivCost.costG1
        (rearPeriod (S.source n) 0) (khat n)
        (rearKappa2 (kh n))
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) +
      rearKappa2 (kh n) * GaugeFlowDerivCost.costP1
        (rearPeriod (S.source n) 0) (khat n)
        (∫ t in (0 : ℝ)..(S.column.step.richStage (n + 1)).stage.increment.T,
          (S.source n).m t) ^ 2 ≤ Cg n
  terminal_perim_ge_one :
    1 ≤ perim (S.column.step.richStage (n + 1)).terminalBase
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

/-- Convert one actual chosen terminal row to the exact row interface consumed
by `successorOfRows`.  Nonnegativity of `khat` is automatic from the source's
retained rear-curvature bound. -/
def ChosenRow.toRowSelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : ChosenRow (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    RowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  applied := R.applied
  terminalInput := R.terminalInput
  output := R.output
  khat_nonnegative :=
    (rearKappa1_nonneg (S.source n).kh_nonnegative
      (S.source n).kh_lt_one).trans (S.source n).rearKappa1_le
  P1_le := R.P1_le
  G1_le := R.G1_le
  Cg_le := R.Cg_le
  terminal_perim_ge_one := R.terminal_perim_ge_one
  period_ge_one := R.period_ge_one
  components_nonnegative := R.components_nonnegative
  components_bound := R.components_bound
  transition := R.transition

/-- Minimal provider input from which the existing long theorem constructs
the `Applied` witness and the chosen-terminal theorem constructs its `Output`.
Only `TerminalInput` geometry and output-dependent component/transition facts
remain external. -/
structure RowConstruction
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  terminalInput : ∀ E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n),
    TerminalInput
      (p := S.column.step.next n)
      (base := (S.column.step.richStage (n + 1)).terminalBase)
      (bound := e n (k + 1)) E
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
  terminal_perim_ge_one :
    1 ≤ perim (S.column.step.richStage (n + 1)).terminalBase
  period_ge_one : 1 ≤ period n (k + 1)
  components_nonnegative : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n))
      (O : Output E (terminalInput E)),
    (components (period n (k + 1)) O.chosen.Delta.eta).Nonnegative
  components_bound : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n))
      (O : Output E (terminalInput E)),
    ComponentBound (components (period n (k + 1)) O.chosen.Delta.eta)
      (diagonal (n + (k + 1)))
  transition : ∀
      (E : Applied
        (S.column.step.richStage (n + 1)).stage.increment (S.source n))
      (O : Output E (terminalInput E)),
    Transition
      (components (period (n + 1) k)
        (S.column.step.richStage (n + 1)).stage.increment.eta)
      (components (period n (k + 1)) O.chosen.Delta.eta)
      (a n k) (MA n k) (NA n k) K0 K1 K2

/-- Apply the long theorem and chosen-terminal theorem, then retain their
actual witnesses as one concrete chosen row. -/
theorem RowConstruction.exists_chosenRow
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : RowConstruction (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    Nonempty (ChosenRow (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) := by
  obtain ⟨E⟩ := exists_applied (S.source n)
  let B := R.terminalInput E
  obtain ⟨O⟩ := FiniteSmoothRearFamilyMarkingAwareChosenTerminal.exists_output E B
  exact ⟨{
    applied := E
    terminalInput := B
    output := O
    P1_le := R.P1_le
    G1_le := R.G1_le
    Cg_le := R.Cg_le
    terminal_perim_ge_one := R.terminal_perim_ge_one
    period_ge_one := R.period_ge_one
    components_nonnegative := R.components_nonnegative E O
    components_bound := R.components_bound E O
    transition := R.transition E O
  }⟩

noncomputable def RowConstruction.chosenRow
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : RowConstruction (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    ChosenRow (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S :=
  Classical.choice R.exists_chosenRow

/-- All-row construction inputs for one depth.  The finite-source majorants
refer to the actual terminal output selected above. -/
structure RowConstructionFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  construction : ∀ n, RowConstruction (n := n) (a := a) (MA := MA)
    (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) S
  analytic : ∀ n, AnalyticSuccessor
    ((construction (n + 1)).chosenRow.output.chosen.Delta)
    (S.source (n + 1)) (P0 n) (kh n) (khat n) (Qmax n)

/-- All actual chosen rows and analytic successor data for one input column.
This is the complete fixed-depth package required by `successorOfRows`. -/
structure ChosenRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  row : ∀ n, ChosenRow (n := n) (a := a) (MA := MA) (NA := NA)
    (K0 := K0) (K1 := K1) (K2 := K2) S
  analytic : ∀ n, AnalyticSuccessor
    (row (n + 1)).output.chosen.Delta
    (S.source (n + 1)) (P0 n) (kh n) (khat n) (Qmax n)

def RowConstructionFamily.chosenFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (F : RowConstructionFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    ChosenRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  row n := (F.construction n).chosenRow
  analytic := F.analytic

/-- Assemble the deterministic selected successor column from exact row
selections. -/
def successorOfRows
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (W : ∀ n : ℕ, RowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (analytic : ∀ n, AnalyticSuccessor
      (W (n + 1)).output.chosen.Delta
      (S.source (n + 1)) (P0 n) (kh n) (khat n) (Qmax n)) :
    Successor S a MA NA := by
  let next : ℕ → Data := fun n ↦ (W n).output.jets.rear
  let step : ColumnStep Q S.column.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt :=
    { next := next
      richStage := fun n ↦ by
        let O := (W n).output
        have hgeom := IsVariableSpeedNormalPath.mono O.chosen.Delta
          (by simpa only [O.stage_eq] using O.stage.increment_geometry)
          (W n).khat_nonnegative
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
            terminalBase := (S.column.step.richStage (n + 1)).terminalBase
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
      period_ge_one := fun n ↦ (W n).period_ge_one
      components_nonnegative := fun n ↦ by
        simpa [step] using (W n).components_nonnegative
      components_bound := fun n ↦ by
        simpa [step] using (W n).components_bound
      gauge := fun n ↦ GaugeCertificate.base
        { terminalBase := (S.column.step.richStage (n + 1)).terminalBase
          terminalBase_eq := rfl
          terminalPhysical := (W n).terminalInput.physical } }
  exact
    { column := T
      transition :=
        { transition := fun n ↦ by
            simpa [T, step] using (W n).transition }
      analytic := fun n ↦ by
        simpa [T, step] using analytic n
      physicalFront := fun n ↦ (W n).output.physicalFront
      physicalFront_eq := fun n ↦ (W n).output.physicalFront_eq }

/-- Backwards-compatible entry point for legacy all-order row data. -/
def successorOfRowsLegacy
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (W : ∀ n : ℕ, RowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (smooth : ∀ n, SmoothSource (S.source (n + 1)) (P0 n) (kh n))
    (steering : ∀ n, NormalizedSteering (smooth n))
    (regularity : ∀ n, SuccessorRegularity (steering n))
    (majorants : ∀ n, MarkingAwareFiniteSourceMajorants
      (W (n + 1)).output.chosen.Delta (regularity n) (khat n) (Qmax n)) :
    Successor S a MA NA :=
  successorOfRows S W (fun n ↦
    AnalyticSuccessor.ofLegacy (smooth n) (steering n) (regularity n)
      (majorants n))

/-- Assemble the successor represented by a complete fixed-depth chosen-row
family. -/
def ChosenRowFamily.successor
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (F : ChosenRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    Successor S a MA NA := by
  apply successorOfRows S (fun n ↦ (F.row n).toRowSelection)
  intro n
  simpa using F.analytic n

/-- All-depth chosen-row production.  This is the minimal concrete provider
interface: for each already selected correlated column it supplies the
all-row family above, and nothing for unrelated terminal choices. -/
structure ChosenRowProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  rows : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2),
    ChosenRowFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S

/-- Forget only the concrete row witnesses, yielding the abstract recursive
provider used downstream. -/
def ChosenRowProvider.provider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : ChosenRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) :
    Provider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 where
  successor S := (G.rows S).successor

/-- All-depth provider stated without preselecting any `Applied` or terminal
`Output`; those witnesses are constructed pointwise from `RowConstruction`. -/
structure RowConstructionProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  families : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2),
    RowConstructionFamily (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S

def RowConstructionProvider.chosenProvider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : RowConstructionProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) :
    ChosenRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2 where
  rows S := (G.families S).chosenFamily

/-- One concrete row for the n-aligned source invariant.  The applied source
belongs to stage `n`; its selected terminal presentation is the terminal base
retained by stage `n + 1`. -/
structure ChosenRow0
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  applied : Applied (S.column.step.richStage n).stage.increment (S.source n)
  terminalInput : TerminalInput (p := S.column.step.next n)
    (base := (S.column.step.richStage (n + 1)).terminalBase)
    (bound := e n (k + 1)) applied
  output : Output applied terminalInput
  P1_le : GaugeFlowDerivCost.costP1 (rearPeriod (S.source n) 0) (khat n)
      (∫ t in (0 : ℝ)..(S.column.step.richStage n).stage.increment.T,
        (S.source n).m t) ≤ P1 n
  G1_le : GaugeFlowDerivCost.costG1 (rearPeriod (S.source n) 0) (khat n)
      (rearKappa2 (kh n))
      (∫ t in (0 : ℝ)..(S.column.step.richStage n).stage.increment.T,
        (S.source n).m t) ≤ G1 n
  Cg_le : (khat n) * GaugeFlowDerivCost.costG1
        (rearPeriod (S.source n) 0) (khat n) (rearKappa2 (kh n))
        (∫ t in (0 : ℝ)..(S.column.step.richStage n).stage.increment.T,
          (S.source n).m t) +
      rearKappa2 (kh n) * GaugeFlowDerivCost.costP1
        (rearPeriod (S.source n) 0) (khat n)
        (∫ t in (0 : ℝ)..(S.column.step.richStage n).stage.increment.T,
          (S.source n).m t) ^ 2 ≤ Cg n
  terminal_perim_ge_one :
    1 ≤ perim (S.column.step.richStage (n + 1)).terminalBase
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

/-- The theorem-producing row input for an n-aligned source. -/
structure RowConstruction0
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  terminalInput : ∀ E : Applied
      (S.column.step.richStage n).stage.increment (S.source n),
    TerminalInput (p := S.column.step.next n)
      (base := (S.column.step.richStage (n + 1)).terminalBase)
      (bound := e n (k + 1)) E
  P1_le : GaugeFlowDerivCost.costP1 (rearPeriod (S.source n) 0) (khat n)
      (∫ t in (0 : ℝ)..(S.column.step.richStage n).stage.increment.T,
        (S.source n).m t) ≤ P1 n
  G1_le : GaugeFlowDerivCost.costG1 (rearPeriod (S.source n) 0) (khat n)
      (rearKappa2 (kh n))
      (∫ t in (0 : ℝ)..(S.column.step.richStage n).stage.increment.T,
        (S.source n).m t) ≤ G1 n
  Cg_le : (khat n) * GaugeFlowDerivCost.costG1
        (rearPeriod (S.source n) 0) (khat n) (rearKappa2 (kh n))
        (∫ t in (0 : ℝ)..(S.column.step.richStage n).stage.increment.T,
          (S.source n).m t) +
      rearKappa2 (kh n) * GaugeFlowDerivCost.costP1
        (rearPeriod (S.source n) 0) (khat n)
        (∫ t in (0 : ℝ)..(S.column.step.richStage n).stage.increment.T,
          (S.source n).m t) ^ 2 ≤ Cg n
  terminal_perim_ge_one :
    1 ≤ perim (S.column.step.richStage (n + 1)).terminalBase
  period_ge_one : 1 ≤ period n (k + 1)
  components_nonnegative : ∀
      (E : Applied (S.column.step.richStage n).stage.increment (S.source n))
      (O : Output E (terminalInput E)),
    (components (period n (k + 1)) O.chosen.Delta.eta).Nonnegative
  components_bound : ∀
      (E : Applied (S.column.step.richStage n).stage.increment (S.source n))
      (O : Output E (terminalInput E)),
    ComponentBound (components (period n (k + 1)) O.chosen.Delta.eta)
      (diagonal (n + (k + 1)))
  transition : ∀
      (E : Applied (S.column.step.richStage n).stage.increment (S.source n))
      (O : Output E (terminalInput E)),
    Transition
      (components (period (n + 1) k)
        (S.column.step.richStage (n + 1)).stage.increment.eta)
      (components (period n (k + 1)) O.chosen.Delta.eta)
      (a n k) (MA n k) (NA n k) K0 K1 K2

theorem RowConstruction0.exists_chosenRow
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : RowConstruction0 (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    Nonempty (ChosenRow0 (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) := by
  obtain ⟨E⟩ := exists_applied (S.source n)
  let B := R.terminalInput E
  obtain ⟨O⟩ := exists_output E B
  exact ⟨{
    applied := E
    terminalInput := B
    output := O
    P1_le := R.P1_le
    G1_le := R.G1_le
    Cg_le := R.Cg_le
    terminal_perim_ge_one := R.terminal_perim_ge_one
    period_ge_one := R.period_ge_one
    components_nonnegative := R.components_nonnegative E O
    components_bound := R.components_bound E O
    transition := R.transition E O }⟩

noncomputable def RowConstruction0.chosenRow
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : RowConstruction0 (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    ChosenRow0 (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S :=
  Classical.choice R.exists_chosenRow

structure RowConstructionFamily0
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  construction : ∀ n, RowConstruction0 (n := n) (a := a) (MA := MA)
    (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) S
  analytic : ∀ n, AnalyticSuccessor
    (construction n).chosenRow.output.chosen.Delta (S.source n)
    (P0 n) (kh n) (khat n) (Qmax n)

structure ChosenRowFamily0
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  row : ∀ n, ChosenRow0 (n := n) (a := a) (MA := MA) (NA := NA)
    (K0 := K0) (K1 := K1) (K2 := K2) S
  analytic : ∀ n, AnalyticSuccessor (row n).output.chosen.Delta (S.source n)
    (P0 n) (kh n) (khat n) (Qmax n)

noncomputable def RowConstructionFamily0.chosenFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (F : RowConstructionFamily0 (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S) :
    ChosenRowFamily0 (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S where
  row n := (F.construction n).chosenRow
  analytic := F.analytic

end FiniteSmoothRearFamilyMarkingAwareDirectSuccessor
