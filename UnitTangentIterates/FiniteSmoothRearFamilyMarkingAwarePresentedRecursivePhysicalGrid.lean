import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalPhysicalAdapter
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
import UnitTangentIterates.MixedFinitePhysicalRearKinematics

/-! # Range-aligned physical grids from presented recursion

The legacy finite-pullback package requires the ordinary physical front to be
literally the marked node in the preceding column.  Presented recursion keeps
these as distinct markings of the same curve.  This module records the sound
range-aligned statement and proves the same strictness/oval closure once tube
membership of the ordinary representatives is available.
-/

noncomputable section

open Function Set Filter Topology MarkedSpace

namespace PathMetric

/-- Physical selected-rear kinematics on every diagonal edge, with an explicit
ordinary front representative whose image is the image of the marked node. -/
structure FinitePullbackPhysicalRearRangeKinematics
    (kh : ℝ) (B Q : ℕ → ℕ → Data) where
  front : ℕ → ℕ → Data
  stage : ∀ n k, Nonempty
    (PhysicalRearLimitKinematics kh (B n (k + 1)) (front (n + 1) k))
  front_range : ∀ n k,
    range (ev (front (n + 1) k)) = range (ev (Q (n + 1) k))

/-- Forget image alignment and retain the mixed ordinary physical grid used by
the existing Harnack closure theorem. -/
def FinitePullbackPhysicalRearRangeKinematics.toMixed
    {kh : ℝ} {B Q : ℕ → ℕ → Data}
    (R : FinitePullbackPhysicalRearRangeKinematics kh B Q) :
    MixedFinitePhysicalRearKinematics kh B R.front where
  stage := R.stage

/-- Range-aligned physical edges give the standard limiting strictness package.
Tube membership is required for the actual ordinary representatives; it is not
inferred from equality of images. -/
def limitStrictnessDataH_of_finitePullbackPhysicalRearRangeKinematics
    {kh cb db cp dp : ℝ} {B Q : ℕ → ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hcp : 0 < cp)
    (hBtube : ∀ n k, IsTubeMember cb 0 db (B n k))
    (R : FinitePullbackPhysicalRearRangeKinematics kh B Q)
    (hFtube : ∀ n k, IsTubeMember cp 0 dp (R.front n k))
    (X : ℕ → Data) (hX : ∀ n, Tendsto (B n) atTop (nhds (X n)))
    (n : ℕ) : UnconditionalAssembly.LimitStrictnessDataH (X n) :=
  limitStrictnessDataH_of_mixedFinitePhysicalRearKinematics
    hkh0 hkh1 hcb hcp hBtube hFtube R.toMixed X hX n

/-- Direct ovality of every simultaneous rear-row limit in the range-aligned
physical grid. -/
theorem isOval_ev_of_finitePullbackPhysicalRearRangeKinematics
    {kh cb db cp dp : ℝ} {B Q : ℕ → ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (hBtube : ∀ n k, IsTubeMember cb 0 db (B n k))
    (R : FinitePullbackPhysicalRearRangeKinematics kh B Q)
    (hFtube : ∀ n k, IsTubeMember cp 0 dp (R.front n k))
    (X : ℕ → Data) (hX : ∀ n, Tendsto (B n) atTop (nhds (X n)))
    (n : ℕ) : MainTheoremConditional.IsOval (ev (X n)) := by
  have hXmem : IsTubeMember cb 0 db (X n) :=
    (isClosed_tube cb 0 db).mem_of_tendsto (hX n)
      (Eventually.of_forall (hBtube n))
  exact UnconditionalAssembly.isOval_ev_of_limitStrictnessDataH hcb hdb hXmem
    (limitStrictnessDataH_of_finitePullbackPhysicalRearRangeKinematics
      hkh0 hkh1 hcb hcp hBtube R hFtube X hX n)

end PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid

open FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedExactAnalyticProvider
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- The row family selected at one reachable recursive depth. -/
noncomputable def rowFamilyAt
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (k : ℕ) :=
  F.provider.rows (F.state k).column (F.state k).invariant

/-- The presented successor selected at one reachable recursive depth. -/
noncomputable def successorAt
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (k : ℕ) :=
  (rowFamilyAt F k).successor

/-- The actual variable-marked node grid retained by the recursive states. -/
def markedGrid
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) : Data :=
  (F.state k).column.column.step.next n

/-- Ordinary rear representatives installed by each presented successor.  The
depth-zero boundary is unused by diagonal edges but is filled from the base. -/
def rearGrid
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n : ℕ) : ℕ → Data
  | 0 => (F.base.column.step.richStage n).terminalBase
  | k + 1 => ((successorAt F k).column.step.richStage n).terminalBase

/-- Every positive-depth rear representative retains its exact strictness. -/
def rearGrid_succ_strict
  (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) :
  UnconditionalAssembly.LimitStrictnessDataH (rearGrid F n (k + 1)) := by
simpa [rearGrid] using (successorAt F k).rearStrict n

/-- Every positive-depth rear representative retains its full Harnack
certificate, including its own ordinary tube. -/
def rearGrid_succ_harnack
  (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) :
  VariableMarkedTube.ArclengthHarnackCertificate (rearGrid F n (k + 1)) := by
simpa [rearGrid] using (successorAt F k).rearHarnack n

/-- Add the configured depth-zero boundary certificate to obtain a Harnack
certificate at every finite rear-grid entry. -/
def rearGrid_harnack
  (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2)
  (hbase : ∀ n,
    VariableMarkedTube.ArclengthHarnackCertificate (rearGrid F n 0)) :
  ∀ n k, VariableMarkedTube.ArclengthHarnackCertificate (rearGrid F n k)
| n, 0 => hbase n
| n, k + 1 => rearGrid_succ_harnack F n k

/-- The ordinary physical front representative retained on edge `(n,k)`. -/
def physicalFrontGrid
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) : ℕ → ℕ → Data
  | 0, _ => Q 0
  | n + 1, k => (successorAt F k).frontData n

/-- The auxiliary representative retained solely for compatibility. -/
def retainedPhysicalFrontGrid
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) : ℕ → ℕ → Data
  | 0, _ => Q 0
  | n + 1, k => ((successorAt F k).physicalFront n).physicalFront

/-- The canonical marked front data retained alongside each physical front. -/
def frontDataGrid
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) : Data :=
  (successorAt F k).frontData n

/-- Canonical front data retrace the preceding marked node as a raw marked
curve. -/
theorem frontDataGrid_range_markedCurve
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) :
    range (ev (frontDataGrid F n k)) =
      range (((markedGrid F (n + 1) k).1 : ℝ → ℂ)) := by
  exact (successorAt F k).front_range n

/-- The ordinary physical representative has the same raw range as the
preceding marked node. -/
theorem physicalFrontGrid_range_markedCurve
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) :
    range (ev (physicalFrontGrid F (n + 1) k)) =
      range (((markedGrid F (n + 1) k).1 : ℝ → ℂ)) := by
  exact (successorAt F k).front_range n

/-- Convert the raw endpoint range into the arclength-evaluated range used by
the physical grid.  The nonzero-perimeter fact is the only marking fact not
retained by the current recursive state interface. -/
theorem physicalFrontGrid_range_markedGrid
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (hperim : ∀ n k, perim (markedGrid F n k) ≠ 0) (n k : ℕ) :
    range (ev (physicalFrontGrid F (n + 1) k)) =
      range (ev (markedGrid F (n + 1) k)) :=
  (physicalFrontGrid_range_markedCurve F n k).trans
    (range_ev_of_perim_ne_zero (hperim (n + 1) k)).symm

/-- The recursive construction supplies every diagonal physical edge, aligned
by image with its preceding variable-marked node. -/
noncomputable def rangeKinematics
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (kap : ℝ) (hkh : ∀ n, kh n = kap)
    (hperim : ∀ n k, perim (markedGrid F n k) ≠ 0) :
    PathMetric.FinitePullbackPhysicalRearRangeKinematics kap
      (rearGrid F) (markedGrid F) where
  front := physicalFrontGrid F
  stage := by
    intro n k
    refine ⟨?_⟩
    have H := (successorAt F k).physicalKinematics n
    cases hkh n
    exact H
  front_range := physicalFrontGrid_range_markedGrid F hperim

end FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
