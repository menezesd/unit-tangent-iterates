import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
import UnitTangentIterates.ConfiguredEnrichedQuantitativePhysicalProducer

/-!
# Physical core of the marking-aware correlated recursion

This is the sound sibling of the legacy affine correlated core.  Selected
columns retain nonaffine marking-aware sources, while the recursive physical
edge is recovered from the explicit ordinary front and its proved equality to
the preceding retained terminal base.
-/

noncomputable section

open Filter MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePhysicalCore

open EnrichedPhysicalChosenRichFamily
  ConfiguredEnrichedQuantitativePhysicalProducer
  FiniteSmoothRearFamilyEnrichedMapProvider
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  RichFamilyPhysicalMarkingIntegration
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- The actual selected marking-aware recursion. -/
structure ConstructionCore
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  defect : RowDefectProvider e
  base : CorrelatedColumn Q Q e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  provider : Provider Q e P0 P1 khat G1 Cg C c dlt period diagonal
    kh Qmax a MA NA K0 K1 K2

/-- Dependent sequence of the actually selected marking-aware columns. -/
def ConstructionCore.stageColumns
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) :
    ∀ k, (current : ℕ → Data) ×
      CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
        period diagonal kh Qmax K0 K1 K2
  | 0 => ⟨Q, F.base⟩
  | k + 1 =>
      let S := F.stageColumns k
      ⟨S.2.column.step.next, mappedColumn F.provider S.2⟩

def ConstructionCore.columns
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) (k : ℕ) : ℕ → Data :=
  (F.stageColumns k).1

def ConstructionCore.chosenColumn
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) (k : ℕ) :=
  (F.stageColumns k).2

@[simp] theorem ConstructionCore.columns_zero
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) : F.columns 0 = Q := rfl

@[simp] theorem ConstructionCore.columns_succ
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) (k : ℕ) :
    F.columns (k + 1) = (F.chosenColumn k).column.step.next := rfl

/-- Ordinary retained terminal bases. -/
def ConstructionCore.retainedRows
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) (n k : ℕ) : Data :=
  match k with
  | 0 => Q n
  | j + 1 => ((F.chosenColumn j).column.step.richStage n).terminalBase

/-- Quantitative marking cap on one selected column. -/
structure ColumnCap
    {current : ℕ → Data} {k : ℕ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (endpointConversion diagonal' : ℕ → ℝ) : Prop where
  endpoint_dist : ∀ n,
    dist (S.column.step.next n) (S.column.step.richStage n).terminalBase ≤
      endpointConversion n * diagonal' (n + k)
  terminal_curvature : ∀ n u, 0 ≤
    orientedNumerator (S.column.step.richStage n).terminalBase u

/-- Caps only for columns actually selected by the marking-aware recursion. -/
structure CapFamily
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (endpointConversion diagonal' : ℕ → ℝ) : Prop where
  base : ColumnCap F.base endpointConversion diagonal'
  successor : ∀ k,
    ColumnCap (mappedColumn F.provider (F.chosenColumn k))
      endpointConversion diagonal'

def CapFamily.columnCap
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {endpointConversion diagonal' : ℕ → ℝ}
    (R : CapFamily F endpointConversion diagonal') :
    ∀ k, ColumnCap (F.chosenColumn k) endpointConversion diagonal'
  | 0 => R.base
  | k + 1 => R.successor k

/-- Exact retained-row finite kinematics.  The successor edge uses the
explicit physical front and `physicalFront_eq`, never the marked endpoint. -/
def ConstructionCore.finitePhysical
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    {kh0 : ℝ} (hkh : ∀ n, kh n = kh0)
    (hbase : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase (Q (n + 1)))) :
    FinitePullbackPhysicalRearKinematics kh0 F.retainedRows := by
  refine ⟨?_⟩
  intro n k
  cases k with
  | zero => exact hbase n
  | succ k =>
      let X := F.provider.successor (F.chosenColumn k)
      have H := X.physicalKinematics n
      change Nonempty (PhysicalRearLimitKinematics kh0
        (X.column.step.richStage n).terminalBase
        ((F.chosenColumn k).column.step.richStage (n + 1)).terminalBase)
      exact ⟨by simpa only [hkh n] using H⟩

theorem CapFamily.endpointTendsto
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {endpointConversion diagonal' : ℕ → ℝ}
    (R : CapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') (n : ℕ) :
    Tendsto (fun k ↦ dist (F.retainedRows n k) (F.columns k n))
      atTop (nhds 0) := by
  let upper : ℕ → ℝ := fun k ↦ match k with
    | 0 => 0
    | j + 1 => endpointConversion n * diagonal' (n + j)
  have hshift : Tendsto (fun k ↦ upper (k + 1)) atTop (nhds 0) := by
    simpa [upper] using
      ConfiguredEnrichedQuantitativePhysicalProducer.shifted_diagonal_tendsto_zero
        hsum (endpointConversion n) n
  have hupper : Tendsto upper atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).mp hshift
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ by
    cases k with
    | zero => simp [ConstructionCore.retainedRows, upper]
    | succ k =>
        rw [dist_comm]
        simpa [ConstructionCore.retainedRows, ConstructionCore.columns_succ,
          upper] using (R.columnCap k).endpoint_dist n) hupper

/-- Complete source-free physical input consumed by the direct capstone. -/
structure PhysicalProducer
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (kh0 cb db : ℝ) : Type where
  physicalBounds : PhysicalRowBounds F.retainedRows
    (fun n k ↦ F.columns k n) cb db
  finite : FinitePullbackPhysicalRearKinematics kh0 F.retainedRows
  endpointTendsto : ∀ n, Tendsto
    (fun k ↦ dist (F.retainedRows n k) (F.columns k n)) atTop (nhds 0)

def CapFamily.toPhysicalProducer
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {endpointConversion diagonal' : ℕ → ℝ}
    (R : CapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') {kh0 cb db : ℝ}
    (bounds : PhysicalRowBounds F.retainedRows
      (fun n k ↦ F.columns k n) cb db)
    (hkh : ∀ n, kh n = kh0)
    (hbase : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase (Q (n + 1)))) :
    PhysicalProducer F kh0 cb db :=
  ⟨bounds, F.finitePhysical hkh hbase, R.endpointTendsto hsum⟩

end FiniteSmoothRearFamilyMarkingAwarePhysicalCore
