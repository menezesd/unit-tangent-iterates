import UnitTangentIterates.WeightedRecursiveDefect
import UnitTangentIterates.VariableMarkedTubeGeometry

/-!
# Cap-aware actual pullback stages

The nonaffine terminal correction is an ambient marked-distance step, not a
normal path.  This interface therefore keeps the selected rear between the
actual path and the next displayed datum.  It is the honest input needed by
the direct paper capstone.
-/

noncomputable section

open Filter Topology MarkedSpace PathMetric

namespace WeightedRecursiveDefect

/-- A dependent grid of actual paths followed by nonaffine endpoint caps.
`P` is the displayed grid and `R` is the selected rear reached by the real
normal path.  The diagonal range equation is deliberately stated on `P`.
-/
structure CapAwareActualPullbackStages
    (Q : ℕ → Data) (P R : ℕ → ℕ → Data)
    (pathError capError e : ℕ → ℕ → ℝ) where
  base : ∀ n, P n 0 = Q n
  path : ∀ n k, NormalPath (P n k) (R n k)
  path_dist_le : ∀ n k,
    dist (P n k) (R n k) ≤ pathError n k
  cap_dist_le : ∀ n k,
    dist (R n k) (P n (k + 1)) ≤ capError n k
  combined_le : ∀ n k,
    pathError n k + capError n k ≤ e n k
  range_edge : ∀ n k,
    VariableMarkedTube.GeometricUnitTangentRangeEdge
      (P (n + 1) k) (P n (k + 1))

namespace CapAwareActualPullbackStages

variable {Q : ℕ → Data} {P R : ℕ → ℕ → Data}
  {pathError capError e : ℕ → ℕ → ℝ}

/-- The displayed step is bounded by the sum of the real path budget and the
single ambient endpoint cap. -/
theorem stepDistance
    (S : CapAwareActualPullbackStages Q P R pathError capError e)
    (n k : ℕ) :
    dist (P n k) (P n (k + 1)) ≤ e n k := by
  calc
    dist (P n k) (P n (k + 1)) ≤
        dist (P n k) (R n k) + dist (R n k) (P n (k + 1)) :=
      dist_triangle _ _ _
    _ ≤ pathError n k + capError n k :=
      add_le_add (S.path_dist_le n k) (S.cap_dist_le n k)
    _ ≤ e n k := S.combined_le n k

end CapAwareActualPullbackStages

end WeightedRecursiveDefect
