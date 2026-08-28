import UnitTangentIterates.ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedPreCarrier

/-! # Callback-free scalar package for normalized reachable completion -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedCompletionScalars

open ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeSourceP0
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

variable {P0u khu khatu Qmaxu : ℕ → ℝ} {r q : ℕ}
  {S : Stage P0u khu khatu Qmaxu r}
  {C : Core S} {p0 kh0 khat0 qmax0 : ℝ}

/-- The sole scalar fact retained from construction of the exact direct
source.  Every argument subsequently passed to `State.completion` is derived
from this comparison and the exact recost period identity. -/
structure CompletionScalars
    (D : ConstructedConfiguredSequenceWeighted.Data) (q : ℕ)
    (I : Input C p0 kh0 khat0 qmax0) : Prop where
  slicePeriodUpper_le : I.slice.periodUpper ≤ edgeSpeedCap D q

namespace CompletionScalars

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {I : Input C p0 kh0 khat0 qmax0}

def ofSliceUpper
    (hupper : I.slice.periodUpper ≤ edgeSpeedCap D q) :
    CompletionScalars D q I :=
  ⟨hupper⟩

abbrev L (_H : CompletionScalars D q I) : ℝ := edgeSpeedCap D q

theorem one_le (H : CompletionScalars D q I) : 1 ≤ H.L :=
  one_le_edgeSpeedCap D q

theorem two_le_sq (H : CompletionScalars D q I) : 2 ≤ H.L ^ 2 := by
  simpa [L, recostPeriodScale] using two_le_recostPeriodScale D q

/-- Exact target-period transport closes the predecessor rear-period cap.
The interval hypothesis is retained only to match `State.completion`. -/
theorem rearPeriod_le (H : CompletionScalars D q I) :
    ∀ t ∈ Icc (0 : ℝ) 1, rearPeriod S.source t ≤ H.L := by
  intro t _ht
  calc
    rearPeriod S.source t = I.source.P t :=
      (congrFun I.source_period_eq t).symm
    _ ≤ I.slice.periodUpper := I.slice.period_upper t
    _ ≤ edgeSpeedCap D q := H.slicePeriodUpper_le

end CompletionScalars

end ConfiguredRecursiveEdgeRecostedCompletionScalars
