import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRowBudget
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedOuterTubeStep
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray

/-!
# Coherent phases for a reachable diagonal recursion

This module is independent of the concrete source/row constructor.  A
reachable successor only has to retain its actual initial phase, the equality
to the shifted canonical displayed datum, the raw diagonal range edge, and the
terminal-front reference equality.  The cumulative phase then removes every
cyclic re-marking.

The resulting coherent grid has the same one-step metric bound as the raw
canonical row, its distances from the fixed base are bounded by finite error
prefixes, and its diagonal range edges are exact.  For the configured recost
closing output, the existing row budget converts those two metric bounds into
the common variable-tube certificate.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open scoped BigOperators

namespace CoherentPhaseReachableMetricRange

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeRecostedOuterTubeStep
  FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray
  VariableMarkedTube

/-- The four phase/range facts which a theorem-produced reachable successor
must retain.  `canonical n` is the unshifted displayed endpoint controlled by
the raw metric row; `next n` is the actual arclength-marked recursive datum. -/
structure StepCoherence
    (current next canonical terminalReference : ℕ → Data) where
  initialPhase : ℕ → ℝ
  nextDisplayed_eq_phase : ∀ n,
    next n = MarkedShift.shiftData (initialPhase n) (canonical n)
  rawDiagonalRangeEdge : ∀ n,
    GeometricUnitTangentRangeEdge (current (n + 1)) (canonical n)
  terminalReference_eq : ∀ n, terminalReference n = next (n + 1)

namespace StepCoherence

variable {current next canonical terminalReference : ℕ → Data}

/-- The successor phase which cancels the newly introduced initial phase. -/
def nextPhase (H : StepCoherence current next canonical terminalReference)
    (phase : ℕ → ℝ) (n : ℕ) : ℝ :=
  phase n - H.initialPhase n

def rephasedCurrent
    (H : StepCoherence current next canonical terminalReference)
    (phase : ℕ → ℝ) (n : ℕ) : Data :=
  MarkedShift.shiftData (phase n) (current n)

def rephasedNext
    (H : StepCoherence current next canonical terminalReference)
    (phase : ℕ → ℝ) (n : ℕ) : Data :=
  MarkedShift.shiftData (H.nextPhase phase n) (next n)

/-- After cancellation, the actual successor is the canonical endpoint under
the preceding cumulative phase. -/
theorem rephasedNext_eq_shift_canonical
    (H : StepCoherence current next canonical terminalReference)
    (phase : ℕ → ℝ) (n : ℕ) :
    H.rephasedNext phase n =
      MarkedShift.shiftData (phase n) (canonical n) := by
  unfold rephasedNext nextPhase
  rw [H.nextDisplayed_eq_phase n, MarkedShift.shiftData_add]
  congr 1
  ring

/-- A common cyclic shift preserves the raw endpoint distance. -/
theorem rephasedEdgeDistance
    (H : StepCoherence current next canonical terminalReference)
    (phase : ℕ → ℝ) {error : ℕ → ℝ}
    (hdist : ∀ n, dist (current n) (canonical n) ≤ error n) (n : ℕ) :
    dist (H.rephasedCurrent phase n) (H.rephasedNext phase n) ≤ error n := by
  rw [H.rephasedNext_eq_shift_canonical phase n]
  unfold rephasedCurrent
  rw [dist_shiftData]
  exact hdist n

/-- Independent cyclic shifts do not alter either range in the diagonal
unit-tangent relation. -/
theorem rephasedRangeEdge
    (H : StepCoherence current next canonical terminalReference)
    (phase : ℕ → ℝ) (n : ℕ) :
    GeometricUnitTangentRangeEdge
      (H.rephasedCurrent phase (n + 1)) (H.rephasedNext phase n) := by
  unfold GeometricUnitTangentRangeEdge rephasedCurrent rephasedNext
  rw [H.nextDisplayed_eq_phase n]
  simp only [range_shiftData, range_geometricUnitTangent_shiftData]
  exact H.rawDiagonalRangeEdge n

end StepCoherence

/-- An all-depth reachable recursion.  Unlike an unrestricted provider, this
record asks for successor data only along its actually chosen raw columns. -/
structure System (modelBase : ℕ → Data) (error : ℕ → ℕ → ℝ) where
  raw : ℕ → ℕ → Data
  canonical : ℕ → ℕ → Data
  terminalReference : ℕ → ℕ → Data
  base_eq : ∀ n, raw n 0 = modelBase n
  coherence : ∀ k, StepCoherence (fun n ↦ raw n k)
    (fun n ↦ raw n (k + 1)) (canonical · k) (terminalReference · k)
  rawDistance : ∀ n k, dist (raw n k) (canonical n k) ≤ error n k

namespace System

variable {modelBase : ℕ → Data} {error : ℕ → ℕ → ℝ}

/-- Cumulative phase cancelling every reachable successor re-marking. -/
def coherentPhase (F : System modelBase error) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => coherentPhase F n k - (F.coherence k).initialPhase n

/-- The phase-normalized reachable grid. -/
def P (F : System modelBase error) (n k : ℕ) : Data :=
  MarkedShift.shiftData (F.coherentPhase n k) (F.raw n k)

@[simp] theorem P_zero (F : System modelBase error) (n : ℕ) :
    F.P n 0 = modelBase n := by
  simp [P, coherentPhase, F.base_eq n]

/-- The coherent successor is the canonical endpoint shifted by the preceding
cumulative phase. -/
theorem P_succ_eq_shift_canonical
    (F : System modelBase error) (n k : ℕ) :
    F.P n (k + 1) =
      MarkedShift.shiftData (F.coherentPhase n k) (F.canonical n k) := by
  exact (F.coherence k).rephasedNext_eq_shift_canonical
    (F.coherentPhase · k) n

/-- Exact one-step coherent metric bound. -/
theorem stepDistance (F : System modelBase error) (n k : ℕ) :
    dist (F.P n k) (F.P n (k + 1)) ≤ error n k := by
  exact (F.coherence k).rephasedEdgeDistance
    (F.coherentPhase · k) (fun n ↦ F.rawDistance n k) n

/-- Exact diagonal range transport, with no marked-data equality assertion. -/
theorem rangeEdge (F : System modelBase error) (n k : ℕ) :
    GeometricUnitTangentRangeEdge (F.P (n + 1) k) (F.P n (k + 1)) := by
  exact (F.coherence k).rephasedRangeEdge (F.coherentPhase · k) n

/-- Finite triangle accumulation from the fixed row model. -/
theorem prefixDistance (F : System modelBase error) (n k : ℕ) :
    dist (modelBase n) (F.P n k) ≤
      Finset.sum (Finset.range k) (fun j ↦ error n j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        dist (modelBase n) (F.P n (k + 1)) ≤
            dist (modelBase n) (F.P n k) +
              dist (F.P n k) (F.P n (k + 1)) := dist_triangle _ _ _
        _ ≤ Finset.sum (Finset.range k) (fun j ↦ error n j) + error n k :=
          add_le_add ih (F.stepDistance n k)
        _ = Finset.sum (Finset.range (k + 1)) (fun j ↦ error n j) := by
          rw [Finset.sum_range_succ]

end System

/-! ## Configured common tube -/

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J}

/-- The final configured row budget turns coherent prefix and one-step metric
bounds into the fixed variable tube needed by the next reachable row. -/
theorem System.variableTube_next
    (R : RecostClosingOutput J O)
    (F : System (base R) R.error)
    (B : BudgetType R) (n k : ℕ)
    (hmodel : IsTubeMember
      (2 * R.data.Hs 0) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model) (base R n))
    (hmodel_acc : ∀ u, ‖(base R n).2.2 u‖ ≤
      ConfiguredInductiveTubeBudget.accBound R.data.model n)
    (hcurve : ∀ u, HasDerivAt (⇑(F.P n (k + 1)).1)
      ((F.P n (k + 1)).2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑(F.P n (k + 1)).2.1)
      ((F.P n (k + 1)).2.2 u) u)
    (hperiodic : Function.Periodic (⇑(F.P n (k + 1)).1) 1)
    (hcurvature : ∀ u, 0 ≤ ((starRingEnd ℂ)
      ((F.P n (k + 1)).2.1 u) * (F.P n (k + 1)).2.2 u).im) :
    IsVariableTubeMember
      (R.data.Hs 0) (upper R n) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (F.P n (k + 1)) := by
  apply variableTube_next_of_rowBudget B n hmodel hmodel_acc hcurve hvel
    hperiodic hcurvature (F.prefixDistance n k) (F.stepDistance n k)
  exact error_prefix_add_step_le_radius R n k

end CoherentPhaseReachableMetricRange
