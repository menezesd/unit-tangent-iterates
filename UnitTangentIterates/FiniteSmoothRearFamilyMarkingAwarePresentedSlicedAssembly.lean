import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
import UnitTangentIterates.TriangularMarkedPathSchemeVariableTerminalDirect
import UnitTangentIterates.PaperMainTheoremDirectProjection

/-!
# Direct sliced assembly for independently presented terminals

The presented successor cannot be coerced to the legacy sliced provider,
whose physical-front equality targets the input column's normalized terminal.
This module instead forms its triangular family directly from reachable
presented successors.  Every finite path, cost cap, and range edge is already
stored by the successor rich stage; only the common tube and limit Harnack
facts remain as closure data.
-/

noncomputable section

open Filter Set Topology MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly

open EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  GaugeRearFamilyVariableTerminal
  NormalPathC2IncrementVariableSpeed
  TriangularMarkedPathSchemeVariableTerminal
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- The invariant-indexed presented construction, with no total slicer for
unreachable columns. -/
structure ConstructionCore
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  current0 : ℕ → Data
  base : CorrelatedColumn Q current0 e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  baseSlice : SlicedCorrelatedColumn base
  base_eq : ∀ n, base.column.step.next n = Q n
  provider : PresentedSlicedProvider Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2

namespace ConstructionCore

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

def initialState
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) :
    PresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax K0 K1 K2 where
  current := F.current0
  depth := 0
  column := F.base
  sliced := F.baseSlice

/-- The actually reachable column at depth `k`. -/
def state
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) : ℕ →
    PresentedSlicedState Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax K0 K1 K2
  | 0 => F.initialState
  | k + 1 => PresentedSlicedState.next F.provider (F.state k)

@[simp] theorem state_zero
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) : F.state 0 = F.initialState := rfl

@[simp] theorem state_succ
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) (k : ℕ) :
    F.state (k + 1) = PresentedSlicedState.next F.provider (F.state k) := rfl

@[simp] theorem state_depth
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) (k : ℕ) : (F.state k).depth = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [state, PresentedSlicedState.next, ih]

/-- The path selected after column depth `k` carries the original depth-`k+1`
row budget. -/
def depthError (e : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ := e n (k + 1)

/-- Row `n`, depth `k` of the presented triangular family. -/
def columns
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) (n k : ℕ) : Data :=
  (F.state k).column.column.step.next n

@[simp] theorem columns_zero
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) (n : ℕ) : F.columns n 0 = Q n := by
  exact F.base_eq n

/-- The rich path joining depths `k` and `k+1` in row `n`. -/
def stage
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) (n k : ℕ) :
    RichStageData (F.columns n k) (F.columns (n + 1) k)
      (F.columns n (k + 1)) (depthError e n k)
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c (C n) dlt := by
  change RichStageData
    ((F.state k).column.column.step.next n)
    ((F.state k).column.column.step.next (n + 1))
    ((F.state (k + 1)).column.column.step.next n) (depthError e n k)
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c (C n) dlt
  rw [F.state_succ k]
  simpa [depthError, F.state_depth k] using
    ((F.provider.successor (F.state k).column
      (F.state k).sliced).column.step.richStage n)

end ConstructionCore

/-- Quantitative and physical closure facts on the actual presented family.
The path-cost caps themselves are already fields of `ConstructionCore.stage`.
-/
structure CapFamily
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) : Type where
  error_nonnegative : ∀ n k, 0 ≤ e n k
  error_summable : ∀ n, Summable (e n)
  tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
    c (C n) 0 dlt (F.columns n k)
  limitHarnack : ∀ n x, Tendsto (F.columns n) atTop (nhds x) →
    VariableMarkedTube.ArclengthHarnackCertificate x

namespace CapFamily

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
  {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
    kh Qmax a MA NA K0 K1 K2}

/-- Assemble the cap family from scalar error/tube bounds, finite Harnack
certificates on the selected rows, and the genuinely uniform Harnack closure
theorem.  Pointwise Harnack alone is intentionally not treated as closed. -/
def ofScalarAndHarnackClosure
    (error_nonnegative : ∀ n k, 0 ≤ e n k)
    (error_summable : ∀ n, Summable (e n))
    (tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (F.columns n k))
    (finiteHarnack : ∀ n k,
      VariableMarkedTube.ArclengthHarnackCertificate (F.columns n k))
    (harnackClosed : ∀ n x, Tendsto (F.columns n) atTop (nhds x) →
      (∀ k, VariableMarkedTube.ArclengthHarnackCertificate (F.columns n k)) →
      VariableMarkedTube.ArclengthHarnackCertificate x) : CapFamily F where
  error_nonnegative := error_nonnegative
  error_summable := error_summable
  tube := tube
  limitHarnack := fun n x hx => harnackClosed n x hx (finiteHarnack n)

def scheme (R : CapFamily F) :
    TriangularMarkedPathSchemeVariableTerminalDirect.Scheme
      Q F.columns (ConstructionCore.depthError e) P0 P1 khat G1 Cg C c dlt where
  base := F.columns_zero
  error_nonnegative := fun n k => R.error_nonnegative n (k + 1)
  error_summable := fun n => by
    simpa [ConstructionCore.depthError, Nat.add_comm] using
      ShadowingTails.summable_shift (R.error_summable n) 1
  tube := R.tube
  stepPath := fun n k => (F.stage n k).stage.increment
  stepGeometry := fun n k => (F.stage n k).stage.increment_geometry
  stepCost := fun n k => (F.stage n k).stage.increment_cost
  finiteEdge := fun n k => (F.stage n k).stage.range_edge
  limitHarnack := R.limitHarnack

/-- Direct rowwise convergence and diagonal range closure for the presented
recursive family. -/
theorem exists_limitOutput (R : CapFamily F) (hc : 0 < c) :
    Nonempty (LimitOutput Q F.columns (ConstructionCore.depthError e)
      P0 P1 khat G1 Cg C c dlt) :=
  TriangularMarkedPathSchemeVariableTerminalDirect.exists_limitOutput R.scheme hc

end CapFamily

/-- The complete paper-facing output attached to one presented sliced core.
This separates the already-proved limit construction from the oriented
representative/width closing step. -/
structure CoherentPackage
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (R : CapFamily F) (direction : ℂ) (modelWidth H : ℝ) where
  limit : LimitOutput Q F.columns (ConstructionCore.depthError e)
    P0 P1 khat G1 Cg C c dlt
  paper : PaperFacingVariableTerminalOutput.Output limit direction modelWidth H

namespace CoherentPackage

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
  {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
    kh Qmax a MA NA K0 K1 K2} {R : CapFamily F}
  {direction : ℂ} {modelWidth H : ℝ}

/-- Build the complete package once oriented representatives and the
configured row-zero closing inequalities have been discharged. -/
theorem exists_of_orientedRepresentatives
    (hc : 0 < c)
    (representatives : ∀ O : LimitOutput Q F.columns
      (ConstructionCore.depthError e) P0 P1 khat G1 Cg C c dlt,
      ∀ n, VariableMarkedTube.OrientedArclengthRepresentative (O.X n))
    (hdirection : ‖direction‖ = 1)
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤ MarkedReparam.totalLength (fun u => (Q 0).2.1 u))
    (hgap : ∀ O : LimitOutput Q F.columns
      (ConstructionCore.depthError e) P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (CoherentPackage F R direction modelWidth H) := by
  obtain ⟨O⟩ := R.exists_limitOutput hc
  exact ⟨{
    limit := O
    paper := PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
      O (representatives O) hdirection hQbounded hQwidth hQlength (hgap O) }⟩

/-- Ordinary-curve paper theorem for the presented sliced recursion. -/
theorem paperMain (P : CoherentPackage F R direction modelWidth H) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  PaperMainTheoremDirectProjection.of_output P.paper

end CoherentPackage

end FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly
