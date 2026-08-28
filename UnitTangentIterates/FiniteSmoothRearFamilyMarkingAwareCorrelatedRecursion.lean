import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRegularitySum
import UnitTangentIterates.FiniteSmoothRearFamilyPhysicalFront
import UnitTangentIterates.FiniteSmoothRearFamilyEnrichedMapProvider

/-!
# Sound source-preserving rear-family recursion

This is the marking-aware replacement for the legacy affine correlated
provider.  The ordinary physical front is retained explicitly and is not
identified with its marked representative.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion

open EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  FiniteSmoothRearFamilyMarkingAwareRegularitySum
  FiniteSmoothRearFamilyPhysicalFront
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- A selected column with the actual nonaffine analytic source belonging to
each next-row increment. -/
structure CorrelatedColumn
    (Q current : ℕ → Data) (e : ℕ → ℕ → ℝ) (k : ℕ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (kh Qmax : ℕ → ℝ) (K0 K1 K2 : ℝ) where
  column : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
    period diagonal (GaugeFamily period K0 K1 K2)
  source : ∀ n, MarkingAwareSource
    (column.step.richStage (n + 1)).stage.increment
    (P0 n) (kh n) (khat n) (Qmax n)

/-- The source-tied slice regularity consumed by separated nonaffine density
transport.  It is retained explicitly in the exact branch because these facts
are not fields of the lighter `MarkingAwareSource` API. -/
structure AnalyticSuccessorSliceFacts
    {a b : Data} {Delta : NormalPath a b}
    {periodLower kap khatNext QmaxNext : ℝ}
    (source : MarkingAwareSource Delta periodLower kap khatNext QmaxNext) where
  periodUpper : ℝ
  periodLower_pos : 0 < periodLower
  period_lower : ∀ t, periodLower ≤ source.P t
  period_upper : ∀ t, source.P t ≤ periodUpper
  etaFs : ℝ → ℝ → ℝ
  etaF_deriv : ∀ t s, HasDerivAt (source.etaF t) (etaFs t s) s
  etaFs_continuous : ∀ t, Continuous (etaFs t)
  etaF_periodic : ∀ t, Function.Periodic (source.etaF t) (source.P t)
  rearNormal_c2 : ∀ t, ContDiff ℝ (2 : ℕ)
    (RearFamilyFrame.frameNormal source.Ydot
      (RearOwnArclength.rearOwnAngle source.Theta source.delta source.sf) t)
  normal_stopped : ∀ t ∉ Set.Ioo (0 : ℝ) Delta.T,
    RearFamilyFrame.frameNormal source.Ydot
      (RearOwnArclength.rearOwnAngle source.Theta source.delta source.sf) t = fun _ ↦ 0
  markingLower : ℝ
  markingUpper : ℝ
  marking_increment : ∀ t,
    source.phi t 1 - source.phi t 0 = source.P t
  markingLower_pos : 0 < markingLower
  marking_lower : ∀ t ∈ Set.Ioo (0 : ℝ) Delta.T, ∀ u,
    markingLower ≤ source.phi1 t u
  markingUpper_nonnegative : 0 ≤ markingUpper
  marking_upper : ∀ t ∈ Set.Ioo (0 : ℝ) Delta.T, ∀ u,
    source.phi1 t u ≤ markingUpper
  marked_bdd0 : ∀ t, BddAbove (Set.range fun u ↦ |Delta.eta t u|)
  marked_bdd1 : ∀ t, BddAbove
    (Set.range fun u ↦ |iteratedDeriv 1 (Delta.eta t) u|)

/-- A correlated column together with the finite slice information needed by
the nonaffine separated estimates.  The comparison with the configured
`P1` is stored here rather than weakening the source-tied analytic package. -/
structure SlicedCorrelatedColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  slice : ∀ n, AnalyticSuccessorSliceFacts (S.source n)
  periodUpper_le : ∀ n, (slice n).periodUpper ≤ P1 n

/-- The n-aligned variant of `CorrelatedColumn`.  Here the analytic source at
row `n` belongs to the stage at that same index.  This is intentionally a
parallel invariant: there is no sound total coercion to `CorrelatedColumn`,
whose source is attached to stage `n + 1`. -/
structure CorrelatedColumn0
    (Q current : ℕ → Data) (e : ℕ → ℕ → ℝ) (k : ℕ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (kh Qmax : ℕ → ℝ) (K0 K1 K2 : ℝ) where
  column : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
    period diagonal (GaugeFamily period K0 K1 K2)
  source : ∀ n, MarkingAwareSource
    (column.step.richStage n).stage.increment
    (P0 n) (kh n) (khat n) (Qmax n)

/-- Finite slice information for an n-aligned correlated column. -/
structure SlicedCorrelatedColumn0
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) where
  slice : ∀ n, AnalyticSuccessorSliceFacts (S.source n)
  periodUpper_le : ∀ n, (slice n).periodUpper ≤ P1 n

/-- Analytic production for one recursive row.  The legacy branch derives the
next source from all-order regularity and majorants.  The exact branch retains
the already assembled stopped-clock source and its finite regularity sidecars. -/
inductive AnalyticSuccessor
    {p q a b : Data} {Gamma : NormalPath p q} (Delta : NormalPath a b)
    {P0a kha khata Qmaxa : ℝ}
    (A : MarkingAwareSource Gamma P0a kha khata Qmaxa)
    (periodLower kap khatNext QmaxNext : ℝ) : Type
  | legacy
      (S : SmoothSource A periodLower kap)
      (D : FiniteSmoothRearFamilyMarkingAwareSmoothSource.NormalizedSteering S)
      (R : FiniteSmoothRearFamilyMarkingAwareSmoothSource.SuccessorRegularity D)
      (majorants : MarkingAwareFiniteSourceMajorants Delta R khatNext QmaxNext)
  | exact
      (source : MarkingAwareSource Delta periodLower kap khatNext QmaxNext)
      (slice : AnalyticSuccessorSliceFacts source)

namespace AnalyticSuccessor

/-- Compatibility constructor for the former smooth/steering/regularity/
majorants tuple. -/
def ofLegacy
    (S : SmoothSource A periodLower kap)
    (D : FiniteSmoothRearFamilyMarkingAwareSmoothSource.NormalizedSteering S)
    (R : FiniteSmoothRearFamilyMarkingAwareSmoothSource.SuccessorRegularity D)
    (M : MarkingAwareFiniteSourceMajorants Delta R khatNext QmaxNext) :
    AnalyticSuccessor Delta A periodLower kap khatNext QmaxNext :=
  .legacy S D R M

/-- Exact stopped-clock constructor.  No smooth bootstrap is invoked: the
primitive C1 successor certificate and its assembled source are retained. -/
def ofExact
    (source : MarkingAwareSource Delta periodLower kap khatNext QmaxNext)
    (slice : AnalyticSuccessorSliceFacts source) :
    AnalyticSuccessor Delta A periodLower kap khatNext QmaxNext :=
  .exact source slice

end AnalyticSuccessor

/-- All correlated data for one selected successor column.  In particular,
`majorants` contains no arbitrary Jacobi functions: the finite source theorem
constructs them.  `physicalFront` separates the marked front from its ordinary
physical representative. -/
structure Successor
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (a MA NA : ℕ → ℕ → ℝ) where
  column : CertifiedColumn Q S.column.step.next e (k + 1)
    P0 P1 khat G1 Cg C c dlt period diagonal
      (GaugeFamily period K0 K1 K2)
  transition : TransitionCertificate S.column column a MA NA K0 K1 K2
  analytic : ∀ n, AnalyticSuccessor
    (column.step.richStage (n + 1)).stage.increment (S.source (n + 1))
    (P0 n) (kh n) (khat n) (Qmax n)
  physicalFront : ∀ n, Certificate (kh n)
    (column.step.richStage n).terminalBase (S.column.step.next (n + 1))
  physicalFront_eq : ∀ n, (physicalFront n).physicalFront =
    (S.column.step.richStage (n + 1)).terminalBase

/-- The provider chooses only the correlated geometric successor.  Analytic
successor sources are subsequently constructed by
`exists_markingAwareSuccessorSource_of_majorants`. -/
structure Provider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (kh Qmax : ℕ → ℝ) (a MA NA : ℕ → ℕ → ℝ)
    (K0 K1 K2 : ℝ) where
  successor : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2),
    Successor S a MA NA

/-- Build the correlated column belonging to one already selected successor. -/
def Successor.mappedColumn
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {a MA NA : ℕ → ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    {current : ℕ → Data} {k : ℕ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (X : Successor S a MA NA) :
    CorrelatedColumn Q S.column.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2 := by
  refine
    { column := X.column
      source := fun n => ?_ }
  cases X.analytic n with
  | legacy S D R M =>
      exact Classical.choice (exists_markingAwareSuccessorSource_of_majorants M)
  | exact source slice => exact source

/-- Build the successor correlated column.  The `source` field is not selected
independently: it is the source assembled from the analytic data of the same
successor. -/
def mappedColumn
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {a MA NA : ℕ → ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    (G : Provider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    {current : ℕ → Data} {k : ℕ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) :
    CorrelatedColumn Q S.column.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2 :=
  (G.successor S).mappedColumn

/-- A recursive provider that retains the finite slice sidecar of every source
it selects.  This is genuinely stronger than `Provider`: the legacy analytic
branch does not itself contain enough information to synthesize these facts. -/
structure SlicedProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  successor : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2), SlicedCorrelatedColumn S →
    Successor S a MA NA
  mappedSlice : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S) n,
    AnalyticSuccessorSliceFacts (((successor S H).mappedColumn).source n)
  mappedPeriodUpper_le : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S) n,
    (mappedSlice S H n).periodUpper ≤ P1 n

/-- One recursion step in the enriched column category. -/
def SlicedProvider.mapped
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : SlicedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (H : SlicedCorrelatedColumn S) :
    SlicedCorrelatedColumn ((G.successor S H).mappedColumn) where
  slice := G.mappedSlice S H
  periodUpper_le := G.mappedPeriodUpper_le S H

/-- The physical edge retained by a selected successor, stated against the
ordinary representative rather than its nonaffine marking. -/
def Successor.physicalKinematics
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {a MA NA : ℕ → ℕ → ℝ} (X : Successor S a MA NA) (n : ℕ) :
    PhysicalRearLimitKinematics (kh n)
      (X.column.step.richStage n).terminalBase
      (S.column.step.richStage (n + 1)).terminalBase := by
  rw [← X.physicalFront_eq n]
  exact (X.physicalFront n).kinematics

/-- Marking-independent range alignment for the same selected edge. -/
theorem Successor.range_physicalFront
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {a MA NA : ℕ → ℕ → ℝ} (X : Successor S a MA NA) (n : ℕ) :
    Set.range (ev (S.column.step.next (n + 1))) =
      Set.range (ev (S.column.step.richStage (n + 1)).terminalBase) := by
  rw [← X.physicalFront_eq n]
  exact (X.physicalFront n).range_eq

/-- One selected successor for the n-aligned invariant. -/
structure Successor0
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (a MA NA : ℕ → ℕ → ℝ) where
  column : CertifiedColumn Q S.column.step.next e (k + 1)
    P0 P1 khat G1 Cg C c dlt period diagonal
      (GaugeFamily period K0 K1 K2)
  transition : TransitionCertificate S.column column a MA NA K0 K1 K2
  analytic : ∀ n, AnalyticSuccessor
    (column.step.richStage n).stage.increment (S.source n)
    (P0 n) (kh n) (khat n) (Qmax n)
  physicalFront : ∀ n, Certificate (kh n)
    (column.step.richStage n).terminalBase (S.column.step.next (n + 1))
  physicalFront_eq : ∀ n, (physicalFront n).physicalFront =
    (S.column.step.richStage (n + 1)).terminalBase

/-- Extract the n-aligned correlated column from one selected successor. -/
def Successor0.mappedColumn
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {current : ℕ → Data} {k : ℕ}
    {S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (X : Successor0 S a MA NA) :
    CorrelatedColumn0 Q S.column.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2 where
  column := X.column
  source n := by
    cases h : X.analytic n with
    | legacy S D R M =>
        exact Classical.choice (exists_markingAwareSuccessorSource_of_majorants M)
    | exact source slice => exact source

/-- Total successor production for n-aligned correlated columns. -/
structure Provider0
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  successor : ∀ {current k}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2),
    Successor0 S a MA NA

/-- Invariant-indexed successor production for n-aligned columns. -/
structure SlicedProvider0
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  successor : ∀ {current k}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : SlicedCorrelatedColumn0 S), Successor0 S a MA NA
  mappedSlice : ∀ {current k}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : SlicedCorrelatedColumn0 S) n,
    AnalyticSuccessorSliceFacts (((successor S H).mappedColumn).source n)
  mappedPeriodUpper_le : ∀ {current k}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : SlicedCorrelatedColumn0 S) n,
    (mappedSlice S H n).periodUpper ≤ P1 n

def SlicedProvider0.mapped
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : SlicedProvider0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    {current k}
    (S : CorrelatedColumn0 Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : SlicedCorrelatedColumn0 S) :
    SlicedCorrelatedColumn0 ((G.successor S H).mappedColumn) where
  slice := G.mappedSlice S H
  periodUpper_le := G.mappedPeriodUpper_le S H

/-- A reachable n-aligned recursive state packages its varying presentation
and depth existentially while retaining the slice invariant. -/
structure SlicedState0
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (K0 K1 K2 : ℝ) where
  current : ℕ → Data
  depth : ℕ
  column : CorrelatedColumn0 Q current e depth P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  sliced : SlicedCorrelatedColumn0 column

def SlicedState0.next
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : SlicedProvider0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (X : SlicedState0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax K0 K1 K2) :
    SlicedState0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax K0 K1 K2 where
  current := X.column.column.step.next
  depth := X.depth + 1
  column := (G.successor X.column X.sliced).mappedColumn
  sliced := G.mapped X.column X.sliced

/-- The all-depth reachable n-aligned recursion. -/
def SlicedProvider0.trajectory
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : SlicedProvider0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (base : SlicedState0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax K0 K1 K2) (depth : ℕ) :
    SlicedState0 Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax K0 K1 K2 :=
  (SlicedState0.next G)^[depth] base

end FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
