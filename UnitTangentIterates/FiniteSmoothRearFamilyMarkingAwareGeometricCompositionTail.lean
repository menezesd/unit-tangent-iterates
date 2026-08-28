import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

/-!
# Rowwise tail view of a geometric composition column

`MarkingAwareSource` depends on the values of the `P0` and `Qmax` profiles.
Consequently, reindexing a complete column through `N + n` would insert
non-definitional transports into every analytic field.  The sound reusable
interface is instead a rowwise view which keeps the original global source
type and merely selects row `N + n`.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareGeometricCompositionTail

open FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
  {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}

/-- The exact global row selected by local row `n` after a tail shift `N`. -/
def rowIndex (N n : ℕ) : ℕ := N + n

/-- A tail row retains the original dependent source type. -/
def source
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax) (N n : ℕ) :=
  S.source (rowIndex N n)

def initial
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax) (N n : ℕ) : Data :=
  S.initial (rowIndex N n)

def path
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax) (N n : ℕ) :=
  S.path (rowIndex N n)

def slice
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax) (H : GeometricCompositionInvariant S) (N n : ℕ) :=
  H.slice (rowIndex N n)

theorem source_cost_le
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax) (H : GeometricCompositionInvariant S) (N n : ℕ) :
    ∫ t in (0 : ℝ)..(S.path (rowIndex N n)).T,
        (S.source (rowIndex N n)).m t ≤ e (rowIndex N n) (k + 1) :=
  H.source_cost_le (rowIndex N n)

theorem initial_range
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax) (H : GeometricCompositionInvariant S) (N n : ℕ) :
    range (S.initial (rowIndex N n)).1 =
      range (current (rowIndex N n)).1 :=
  H.initialRange (rowIndex N n)

theorem path_end_range
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax) (H : GeometricCompositionInvariant S) (N n : ℕ) :
    range (S.pathEnd (rowIndex N n)).1 =
      range (S.initial (rowIndex N n + 1)).1 :=
  H.pathEndRange (rowIndex N n)

end FiniteSmoothRearFamilyMarkingAwareGeometricCompositionTail
