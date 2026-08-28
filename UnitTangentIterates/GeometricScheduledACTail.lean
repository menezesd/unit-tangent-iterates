import UnitTangentIterates.GeometricCountableNormalTailSchedule
import UnitTangentIterates.RegularizingBackwardShadowingTerminalTails

/-!
# Scheduled absolutely-continuous normal tails

The paper permits countable concatenations which are piecewise smooth in the
path parameter and absolutely continuous at their unique accumulation point.
The repository's `NormalPath` type is deliberately stronger: it asks for a
classical derivative at every real time, including every seam.  This module
therefore records the paper object by its exact constructive data rather than
asserting that the countable gluing is a single `NormalPath`.

The pieces have summable durations, their cost densities tend uniformly to
zero at the accumulation point, all finite concatenations are genuine normal
paths, and their endpoints converge to the declared endpoint.  These are the
quantitative hypotheses used by the absolutely-continuous gluing argument.
-/

noncomputable section

open Filter Topology MarkedTopology
open MarkedSpace PathMetric PathMetric.NormalPath

namespace GeometricScheduledACTail

open GeometricCountableNormalTailSchedule
  RegularizingBackwardShadowingTerminalTails

variable {p : ℕ → MarkedSpace.Data}

/-- Constructive representation of the paper's countably concatenated
piecewise-smooth/absolutely-continuous tail. -/
structure Certificate
    (step : ∀ j, NormalPath (p j) (p (j + 1)))
    (limit : MarkedSpace.Data) (C q : ℝ) where
  slow : SlowPieces step C q
  endpoint_tendsto : Tendsto p atTop (nhds limit)

namespace Certificate

variable {step : ∀ j, NormalPath (p j) (p (j + 1))}
  {limit : MarkedSpace.Data} {C q : ℝ}

/-- The scheduled `j`-th piece. -/
noncomputable def piece (H : Certificate step limit C q) (j : ℕ) :
    NormalPath (p j) (p (j + 1)) :=
  H.slow.scheduled j

@[simp] theorem piece_time (H : Certificate step limit C q) (j : ℕ) :
    (H.piece j).T = q ^ j :=
  H.slow.scheduled_time j

theorem piece_cost_le (H : Certificate step limit C q) (j : ℕ) :
    cost (H.piece j) ≤ 2 * C * (q ^ 2) ^ j :=
  H.slow.scheduled_cost_le j

theorem piece_density_le (H : Certificate step limit C q) (j : ℕ) (t : ℝ) :
    (H.piece j).m t ≤ 3 * C * q ^ j :=
  H.slow.scheduled_density_le j t

/-- The total scheduled time is finite. -/
theorem duration_summable (H : Certificate step limit C q) :
    Summable fun j : ℕ ↦ (H.piece j).T :=
  H.slow.duration_summable

/-- The uniform density majorant vanishes at the unique accumulation point. -/
theorem density_bound_tendsto_zero (H : Certificate step limit C q) :
    Tendsto (fun j : ℕ ↦ 3 * C * q ^ j) atTop (nhds 0) :=
  H.slow.density_bound_tendsto_zero

/-- The scheduled pieces have summable total cost. -/
theorem cost_summable (H : Certificate step limit C q) :
    Summable fun j : ℕ ↦ cost (H.piece j) :=
  H.slow.cost_summable

/-- All finite truncations are genuine normal paths and their terminal
endpoints converge to the declared endpoint. -/
noncomputable def completedTail (H : Certificate step limit C q) :
    CompletedTail H.piece limit
      (ShadowingTails.tail fun j ↦ cost (H.piece j)) :=
  completedTail_of_summable H.piece limit (fun j ↦ cost (H.piece j))
    H.endpoint_tendsto (fun _ ↦ le_rfl)
    (fun j ↦ (H.piece j).cost_nonneg) H.cost_summable

/-- A genuine finite normal path from the `N`-th node to the `N+k`-th node. -/
noncomputable def finitePath (H : Certificate step limit C q) (N k : ℕ) :
    NormalPath (p N) (p (N + k)) :=
  H.completedTail.path N k

theorem finitePath_cost_le (H : Certificate step limit C q) (N k : ℕ) :
    cost (H.finitePath N k) ≤
      ShadowingTails.tail (fun j ↦ cost (H.piece j)) N :=
  H.completedTail.path_cost_le N k

theorem finitePath_endpoint_tendsto (H : Certificate step limit C q) (N : ℕ) :
    Tendsto (fun k ↦ p (N + k)) atTop (nhds limit) :=
  H.completedTail.path_endpoint_tendsto N

/-- The low-order terminal inequality for every finite truncation. -/
theorem terminal_tail_low (H : Certificate step limit C q) (N k : ℕ) :
    S 0 (H.finitePath N k).eta + S 1 (H.finitePath N k).eta ≤
      2 * ShadowingTails.tail (fun j ↦ cost (H.piece j)) N :=
  H.completedTail.terminal_tail_low N k

/-- The second-order terminal inequality for every finite truncation. -/
theorem terminal_tail_two (H : Certificate step limit C q) (N k : ℕ) :
    S 2 (H.finitePath N k).eta ≤
      ShadowingTails.tail (fun j ↦ cost (H.piece j)) N :=
  H.completedTail.terminal_tail_two N k

end Certificate

end GeometricScheduledACTail
