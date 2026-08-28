import UnitTangentIterates.FiniteSmoothRearFamilyCorrelatedRecursion
import UnitTangentIterates.ConfiguredEnrichedQuantitativePhysicalProducer

/-!
# Physical core of the source-preserving correlated recursion

The legacy provider core quantifies over arbitrary erased columns.  A
source-preserving rear-family recursion cannot honestly inhabit that type:
its next analytic source exists only for the column it actually selected.
This sibling core carries precisely those selected correlated columns.  It
retains enough information to construct finite physical kinematics and the
vanishing terminal-marking defect without any universal provider callback.
-/

noncomputable section

open Filter MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyCorrelatedPhysicalCore

open EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyAnalyticSource
  FiniteSmoothRearFamilyCorrelatedRecursion
  FiniteSmoothRearFamilyEnrichedMapProvider
  ConfiguredEnrichedQuantitativePhysicalProducer
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
  {kh Qmax Mtotal : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- The selected source-preserving recursion.  `base` and `provider.row` are
the only row-construction inputs; no map on unrelated columns is requested. -/
structure ConstructionCore
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (kh Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  defect : RowDefectProvider e
  base : CorrelatedColumn Q Q e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  provider : FiniteSmoothRearFamilyCorrelatedRecursion.Provider
    Q e P0 P1 khat G1 Cg C c dlt period diagonal
    kh Qmax Mtotal a MA NA K0 K1 K2

/-- The dependent sequence of correlated columns actually selected. -/
def ConstructionCore.stageColumns
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2) :
    ∀ k, (current : ℕ → Data) ×
      CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
        period diagonal kh Qmax K0 K1 K2
  | 0 => ⟨Q, F.base⟩
  | k + 1 =>
      let S := F.stageColumns k
      ⟨S.2.column.step.next, mappedColumn F.provider S.2⟩

def ConstructionCore.columns
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2) (k : ℕ) : ℕ → Data :=
  (F.stageColumns k).1

def ConstructionCore.chosenColumn
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2) (k : ℕ) :=
  (F.stageColumns k).2

theorem ConstructionCore.columns_zero
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2) : F.columns 0 = Q := rfl

theorem ConstructionCore.columns_succ
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2) (k : ℕ) :
    F.columns (k + 1) = (F.chosenColumn k).column.step.next := rfl

/-- Canonical physical representatives retained at every actual depth. -/
def ConstructionCore.retainedRows
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2) (n k : ℕ) : Data :=
  match k with
  | 0 => Q n
  | j + 1 => ((F.chosenColumn j).column.step.richStage n).terminalBase

/-- Quantitative terminal cap on one already selected correlated column.
The model-to-column shadow estimate belongs to the independent direct path
scheme and is not needed to construct the retained physical representatives. -/
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

/-- The two physical-terminal facts needed from one selected row image. -/
structure RowTerminalCap
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt}
    (W : RowImage period diagonal kh Qmax Mtotal a MA NA K0 K1 K2 S n)
    (endpointCoeff defect : ℝ) : Prop where
  endpoint_dist : dist W.rear W.output.terminalBase ≤ endpointCoeff * defect
  terminal_curvature : ∀ u, 0 ≤ orientedNumerator W.output.terminalBase u

/-- Caps are required only for the base column and the successors actually
selected from it. -/
structure CapFamily
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    (endpointConversion diagonal' : ℕ → ℝ) : Prop where
  base : ColumnCap F.base endpointConversion diagonal'
  successor : ∀ k n, RowTerminalCap
    (F.provider.row (F.chosenColumn k) n)
    (endpointConversion n) (diagonal' (n + (k + 1)))

/-- The cap on every actual selected column, obtained without extending the
correlated provider to arbitrary erased inputs. -/
def CapFamily.columnCap
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2}
    {endpointConversion diagonal' : ℕ → ℝ}
    (R : CapFamily F endpointConversion diagonal') :
    ∀ k, ColumnCap (F.chosenColumn k) endpointConversion diagonal'
  | 0 => R.base
  | k + 1 => by
      refine ⟨?_, ?_⟩
      · intro n
        change dist (F.provider.row (F.chosenColumn k) n).rear
          (F.provider.row (F.chosenColumn k) n).output.terminalBase ≤ _
        simpa [Nat.add_assoc] using (R.successor k n).endpoint_dist
      · intro n u
        change 0 ≤ orientedNumerator
          (F.provider.row (F.chosenColumn k) n).output.terminalBase u
        exact (R.successor k n).terminal_curvature u

/-- The exact finite physical pullback edges of the correlated recursion. -/
def ConstructionCore.finitePhysical
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    {kh0 : ℝ} (hkh : ∀ n, kh n = kh0)
    (hbase : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase (Q (n + 1)))) :
    FinitePullbackPhysicalRearKinematics kh0 F.retainedRows := by
  refine ⟨?_⟩
  intro n k
  cases k with
  | zero => exact hbase n
  | succ k =>
      let W := F.provider.row (F.chosenColumn k) n
      have H := W.physicalKinematics
      change Nonempty (PhysicalRearLimitKinematics kh0
        W.output.terminalBase
        ((F.chosenColumn k).column.step.richStage (n + 1)).terminalBase)
      exact ⟨by simpa only [hkh n] using H⟩

/-- The cap family gives the vanishing marking defect between retained
physical representatives and selected marked columns. -/
theorem CapFamily.endpointTendsto
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2}
    {endpointConversion diagonal' : ℕ → ℝ}
    (R : CapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') (n : ℕ) :
    Tendsto (fun k ↦ dist (F.retainedRows n k) (F.columns k n))
      atTop (nhds 0) := by
  let upper : ℕ → ℝ := fun k ↦ match k with
    | 0 => 0
    | j + 1 => endpointConversion n * diagonal' (n + j)
  have hshift : Tendsto (fun k ↦ upper (k + 1)) atTop (nhds 0) := by
    simpa [upper] using shifted_diagonal_tendsto_zero hsum
      (endpointConversion n) n
  have hupper : Tendsto upper atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).mp hshift
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ by
    cases k with
    | zero =>
        change dist (Q n) (Q n) ≤ 0
        simp
    | succ k =>
      rw [dist_comm]
      simpa [ConstructionCore.retainedRows, ConstructionCore.columns_succ,
          upper] using (R.columnCap k).endpoint_dist n) hupper

/-- Aggregate produced from a correlated provider and its cap family.  The
row-bound component is kept explicit because it belongs to the independent
configured scalar/tube construction, not to the analytic source producer. -/
structure PhysicalProducer
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    (kh0 cb db : ℝ) : Type where
  physicalBounds : RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
    F.retainedRows (fun n k ↦ F.columns k n) cb db
  finite : FinitePullbackPhysicalRearKinematics kh0 F.retainedRows
  endpointTendsto : ∀ n, Tendsto
    (fun k ↦ dist (F.retainedRows n k) (F.columns k n)) atTop (nhds 0)

/-- One-call physical aggregate from the actual correlated recursion. -/
def CapFamily.toPhysicalProducer
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2}
    {endpointConversion diagonal' : ℕ → ℝ}
    (R : CapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') {kh0 cb db : ℝ}
    (bounds : RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
      F.retainedRows (fun n k ↦ F.columns k n) cb db)
    (hkh : ∀ n, kh n = kh0)
    (hbase : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase (Q (n + 1)))) :
    PhysicalProducer F kh0 cb db :=
  ⟨bounds, F.finitePhysical hkh hbase, R.endpointTendsto hsum⟩

end FiniteSmoothRearFamilyCorrelatedPhysicalCore
