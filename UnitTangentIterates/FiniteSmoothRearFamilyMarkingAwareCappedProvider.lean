import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePhysicalCore

/-!
# Capped marking-aware successor provider

The terminal estimate is part of the same successor choice as its column,
transition, physical front, and next source.  Consequently no independent
all-depth cap family remains in the final analytic package.
-/

noncomputable section

open Filter MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareCappedProvider

open FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  RichFamilyPhysicalMarkingIntegration
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- A concrete successor provider together with the quantitative terminal cap
on every successor it selects. -/
structure CappedProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (endpointConversion diagonal' : ℕ → ℝ) where
  provider : Provider Q e P0 P1 khat G1 Cg C c dlt period diagonal
    kh Qmax a MA NA K0 K1 K2
  successorCap : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2),
    ColumnCap (mappedColumn provider S) endpointConversion diagonal'

/-- Invariant-indexed capped production.  Unlike `CappedProvider`, this asks
for a successor only at a column already carrying the preserved slice facts. -/
structure SlicedCappedProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (endpointConversion diagonal' : ℕ → ℝ) where
  provider : SlicedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
    kh Qmax a MA NA K0 K1 K2
  successorCap : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S),
    ColumnCap ((provider.successor S H).mappedColumn)
      endpointConversion diagonal'

/-- Reachable recursion whose state includes the nonaffine slice invariant. -/
structure SlicedConstructionCore
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  defect : RowDefectProvider e
  base : CorrelatedColumn Q Q e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  baseSlice : SlicedCorrelatedColumn base
  provider : SlicedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
    kh Qmax a MA NA K0 K1 K2

/-- The dependent state at one sliced recursive depth. -/
def SlicedConstructionCore.Stage
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (_F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (k : ℕ) :=
  Σ current : ℕ → Data, Σ S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2, SlicedCorrelatedColumn S

/-- Iterate only inside the invariant-carrying state space. -/
def SlicedConstructionCore.stage
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) :
    ∀ k, F.Stage k
  | 0 => ⟨Q, F.base, F.baseSlice⟩
  | k + 1 => by
      let Z := F.stage k
      let X := F.provider.successor Z.2.1 Z.2.2
      exact ⟨Z.2.1.column.step.next, X.mappedColumn,
        F.provider.mapped Z.2.1 Z.2.2⟩

def SlicedConstructionCore.chosenColumn
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (k : ℕ) :=
  (F.stage k).2.1

def SlicedConstructionCore.columns
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (k : ℕ) : ℕ → Data :=
  (F.stage k).1

@[simp] theorem SlicedConstructionCore.columns_zero
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) : F.columns 0 = Q := rfl

@[simp] theorem SlicedConstructionCore.columns_succ
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (k : ℕ) :
    F.columns (k + 1) = (F.chosenColumn k).column.step.next := rfl

def SlicedConstructionCore.retainedRows
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) : Data :=
  match k with
  | 0 => Q n
  | j + 1 => ((F.chosenColumn j).column.step.richStage n).terminalBase

def SlicedConstructionCore.chosenSlice
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (k : ℕ) :
    SlicedCorrelatedColumn (F.chosenColumn k) :=
  (F.stage k).2.2

/-- Caps for exactly the reachable sliced columns. -/
structure SlicedCapFamily
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (endpointConversion diagonal' : ℕ → ℝ) : Prop where
  base : ColumnCap F.base endpointConversion diagonal'
  successor : ∀ k,
    ColumnCap ((F.provider.successor (F.chosenColumn k) (F.chosenSlice k)).mappedColumn)
      endpointConversion diagonal'

/-- Retrieve the cap of the actual reachable column at a fixed depth. -/
def SlicedCapFamily.columnCap
    {F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    (R : SlicedCapFamily F endpointConversion diagonal') : ∀ k,
    ColumnCap (F.chosenColumn k) endpointConversion diagonal'
  | 0 => R.base
  | k + 1 => R.successor k

/-- Exact finite physical edges of the reachable sliced recursion. -/
def SlicedConstructionCore.finitePhysical
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    {kh0 : ℝ} (hkh : ∀ n, kh n = kh0)
    (hbase : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase (Q (n + 1)))) :
    FinitePullbackPhysicalRearKinematics kh0 F.retainedRows := by
  refine ⟨?_⟩
  intro n k
  cases k with
  | zero => exact hbase n
  | succ k =>
      let X := F.provider.successor (F.chosenColumn k) (F.chosenSlice k)
      have H := X.physicalKinematics n
      change Nonempty (PhysicalRearLimitKinematics kh0
        (X.column.step.richStage n).terminalBase
        ((F.chosenColumn k).column.step.richStage (n + 1)).terminalBase)
      exact ⟨by simpa only [hkh n] using H⟩

theorem SlicedCapFamily.endpointTendsto
    {F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {endpointConversion diagonal' : ℕ → ℝ}
    (R : SlicedCapFamily F endpointConversion diagonal')
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
    | zero => simp [SlicedConstructionCore.retainedRows, upper]
    | succ k =>
        rw [dist_comm]
        simpa [SlicedConstructionCore.retainedRows,
          SlicedConstructionCore.columns_succ, upper] using
          (R.columnCap k).endpoint_dist n) hupper

/-- Source-free physical data for the reachable sliced capstone. -/
structure SlicedPhysicalProducer
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (kh0 cb db : ℝ) : Type where
  physicalBounds : PhysicalRowBounds F.retainedRows
    (fun n k ↦ F.columns k n) cb db
  finite : FinitePullbackPhysicalRearKinematics kh0 F.retainedRows
  endpointTendsto : ∀ n, Tendsto
    (fun k ↦ dist (F.retainedRows n k) (F.columns k n)) atTop (nhds 0)

def SlicedCapFamily.toPhysicalProducer
    {F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2}
    {endpointConversion diagonal' : ℕ → ℝ}
    (R : SlicedCapFamily F endpointConversion diagonal')
    (hsum : Summable diagonal') {kh0 cb db : ℝ}
    (bounds : PhysicalRowBounds F.retainedRows
      (fun n k ↦ F.columns k n) cb db)
    (hkh : ∀ n, kh n = kh0)
    (hbase : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase (Q (n + 1)))) :
    SlicedPhysicalProducer F kh0 cb db :=
  ⟨bounds, F.finitePhysical hkh hbase, R.endpointTendsto hsum⟩

/-- Assemble the reachable sliced recursion and all of its caps. -/
def SlicedCappedProvider.capFamily
    (G : SlicedCappedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 endpointConversion diagonal')
    (defect : RowDefectProvider e)
    (base : CorrelatedColumn Q Q e 0 P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (baseSlice : SlicedCorrelatedColumn base)
    (baseCap : ColumnCap base endpointConversion diagonal') :
    SlicedCapFamily
      (SlicedConstructionCore.mk defect base baseSlice G.provider)
      endpointConversion diagonal' where
  base := baseCap
  successor k := G.successorCap _ _

/-- Common endpoint coefficient for the distinct configured base and
successor estimates. -/
def mergedConversion (baseConversion successorConversion : ℕ → ℝ) :
    ℕ → ℝ :=
  fun n ↦ max (baseConversion n) (successorConversion n)

/-- Project the complete cap family for the actual selected recursion. -/
def CappedProvider.capFamily
    (G : CappedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 endpointConversion diagonal')
    (defect : RowDefectProvider e)
    (base : CorrelatedColumn Q Q e 0 P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (baseCap : ColumnCap base endpointConversion diagonal') :
    CapFamily
      ({ defect := defect, base := base, provider := G.provider } :
        ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
          kh Qmax a MA NA K0 K1 K2)
      endpointConversion diagonal' := by
  let F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 :=
    { defect := defect, base := base, provider := G.provider }
  change CapFamily F endpointConversion diagonal'
  refine { base := baseCap, successor := ?_ }
  intro k
  exact G.successorCap (F.chosenColumn k)

/-- Merge an automatic configured base cap with the caps retained by the
successor provider. -/
def CappedProvider.capFamilyOfSeparate
    {baseConversion successorConversion diagonal' : ℕ → ℝ}
    (G : CappedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 successorConversion diagonal')
    (defect : RowDefectProvider e)
    (base : CorrelatedColumn Q Q e 0 P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (baseCap : ColumnCap base baseConversion diagonal')
    (hdiag : ∀ j, 0 ≤ diagonal' j) :
    CapFamily
      ({ defect := defect, base := base, provider := G.provider } :
        ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
          kh Qmax a MA NA K0 K1 K2)
      (mergedConversion baseConversion successorConversion) diagonal' := by
  let F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 :=
    { defect := defect, base := base, provider := G.provider }
  change CapFamily F (mergedConversion baseConversion successorConversion)
    diagonal'
  refine { base := ?_, successor := ?_ }
  · refine ⟨?_, baseCap.terminal_curvature⟩
    intro n
    exact (baseCap.endpoint_dist n).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hdiag (n + 0)))
  · intro k
    let S := F.chosenColumn k
    let R := G.successorCap S
    refine ⟨?_, R.terminal_curvature⟩
    intro n
    exact (R.endpoint_dist n).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hdiag (n + (k + 1))))

/-- Merge distinct configured base and successor coefficients along the
reachable sliced recursion. -/
def SlicedCappedProvider.capFamilyOfSeparate
    {baseConversion successorConversion diagonal' : ℕ → ℝ}
    (G : SlicedCappedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 successorConversion diagonal')
    (defect : RowDefectProvider e)
    (base : CorrelatedColumn Q Q e 0 P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (baseSlice : SlicedCorrelatedColumn base)
    (baseCap : ColumnCap base baseConversion diagonal')
    (hdiag : ∀ j, 0 ≤ diagonal' j) :
    SlicedCapFamily
      (SlicedConstructionCore.mk defect base baseSlice G.provider)
      (mergedConversion baseConversion successorConversion) diagonal' where
  base := ⟨fun n ↦ (baseCap.endpoint_dist n).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (hdiag (n + 0))),
    baseCap.terminal_curvature⟩
  successor k := by
    let F := SlicedConstructionCore.mk defect base baseSlice G.provider
    let R := G.successorCap (F.chosenColumn k) (F.chosenSlice k)
    refine ⟨?_, R.terminal_curvature⟩
    intro n
    exact (R.endpoint_dist n).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hdiag (n + (k + 1))))

/-- The same geometric cap, stated for an n-aligned correlated column. -/
structure ColumnCap0
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ} {current : ℕ → Data} {k : ℕ}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (endpointConversion diagonal' : ℕ → ℝ) : Prop where
  endpoint_dist : ∀ n, dist (S.column.step.next n)
    (S.column.step.richStage n).terminalBase ≤
      endpointConversion n * diagonal' (n + k)
  terminal_curvature : ∀ n u, 0 ≤
    ConfiguredEnrichedQuantitativePhysicalProducer.orientedNumerator
      (S.column.step.richStage n).terminalBase u

/-- Terminal caps for the invariant-indexed n-aligned recursion.  This stays
parallel to `SlicedCappedProvider`; no total coercion of columns is used. -/
structure SlicedCappedProvider0
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (endpointConversion diagonal' : ℕ → ℝ) where
  provider : SlicedProvider0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
    kh Qmax a MA NA K0 K1 K2
  successorCap : ∀ {current k}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : SlicedCorrelatedColumn0 S),
    ColumnCap0 ((provider.successor S H).mappedColumn)
      endpointConversion diagonal'

/-- N-aligned sliced construction core. -/
structure SlicedConstructionCore0
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  defect : RowDefectProvider e
  base : CorrelatedColumn0 Q Q e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  baseSlice : SlicedCorrelatedColumn0 base
  provider : SlicedProvider0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
    kh Qmax a MA NA K0 K1 K2

/-- N-aligned sliced core together with the caps used at each reachable
successor. -/
structure SlicedCappedConstructionCore0
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (endpointConversion diagonal' : ℕ → ℝ) where
  defect : RowDefectProvider e
  base : CorrelatedColumn0 Q Q e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  baseSlice : SlicedCorrelatedColumn0 base
  capped : SlicedCappedProvider0 Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2 endpointConversion diagonal'

def SlicedCappedConstructionCore0.core
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {endpointConversion diagonal' : ℕ → ℝ}
    (X : SlicedCappedConstructionCore0 Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2
      endpointConversion diagonal') :
    SlicedConstructionCore0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 where
  defect := X.defect
  base := X.base
  baseSlice := X.baseSlice
  provider := X.capped.provider

end FiniteSmoothRearFamilyMarkingAwareCappedProvider
