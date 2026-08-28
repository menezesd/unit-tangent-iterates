import UnitTangentIterates.CoherentPhaseReachableMetricRange
import UnitTangentIterates.ShadowingTails

/-! # Metric completion of a coherent phase-normalized grid -/

noncomputable section

open Function Filter Topology MarkedSpace PathMetric

namespace CoherentPhaseReachableMetricRangeCompletion

open CoherentPhaseReachableMetricRange

variable {modelBase : ℕ → Data} {error : ℕ → ℕ → ℝ}

/-- Rowwise completion data for a coherent grid.  Besides marked convergence,
the record retains both the sharp infinite-tail estimate and the original
finite-prefix estimate from the fixed model row. -/
structure GridCompletion (F : System modelBase error) where
  X : ℕ → Data
  row_cauchy : ∀ n, CauchySeq (F.P n)
  row_tendsto : ∀ n, Tendsto (F.P n) atTop (nhds (X n))
  tail_dist : ∀ n k,
    dist (F.P n k) (X n) ≤ ShadowingTails.tail (error n) k
  base_dist : ∀ n,
    dist (modelBase n) (X n) ≤ ShadowingTails.tail (error n) 0
  prefix_dist : ∀ n k,
    dist (modelBase n) (F.P n k) ≤
      Finset.sum (Finset.range k) (fun j ↦ error n j)

/-- Every coherent system with rowwise summable error has a marked row
completion. -/
theorem exists_gridCompletion
    (F : System modelBase error) (hsum : ∀ n, Summable (error n)) :
    Nonempty (GridCompletion F) := by
  have hcauchy : ∀ n, CauchySeq (F.P n) := by
    intro n
    apply cauchySeq_of_summable_dist
    exact Summable.of_nonneg_of_le (fun _ ↦ dist_nonneg)
      (F.stepDistance n) (hsum n)
  have hlimit : ∀ n, ∃ x : Data,
      Tendsto (F.P n) atTop (nhds x) ∧
        ∀ k, dist (F.P n k) x ≤ ShadowingTails.tail (error n) k := by
    intro n
    obtain ⟨x, hx, hdist⟩ :=
      ShadowingTails.exists_limit_of_summable_increments
        (C := (1 : ℝ)) (hsum n) (by
          intro k
          simpa using F.stepDistance n k)
    exact ⟨x, hx, fun k ↦ by simpa using hdist k⟩
  choose X hXtendsto hXdist using hlimit
  refine ⟨⟨X, hcauchy, hXtendsto, hXdist, ?_, F.prefixDistance⟩⟩
  intro n
  rw [← F.P_zero n]
  exact hXdist n 0

/-- A fixed choice of row limits for downstream physical and smooth adapters. -/
noncomputable def completion
    (F : System modelBase error) (hsum : ∀ n, Summable (error n)) :
    GridCompletion F :=
  Classical.choice (exists_gridCompletion F hsum)

namespace GridCompletion

variable {F : System modelBase error}

/-- Any independently constructed row limit agrees with the canonical
completion limit.  This is the equality transport used when a paper capstone
has already named its representative data. -/
theorem limit_eq (C : GridCompletion F) {Y : ℕ → Data}
    (hY : ∀ n, Tendsto (F.P n) atTop (nhds (Y n))) (n : ℕ) :
    C.X n = Y n :=
  tendsto_nhds_unique (C.row_tendsto n) (hY n)

/-- Positive-column convergence used verbatim by the physical rear closure
adapter. -/
theorem row_tail_tendsto (C : GridCompletion F) (n : ℕ) :
    Tendsto (fun k ↦ F.P n (k + 1)) atTop (nhds (C.X n)) :=
  (C.row_tendsto n).comp (tendsto_add_atTop_nat 1)

end GridCompletion

/-! ## Configured recost specialization -/

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {O : GaugeOutput J}

/-- The configured closing output already proves summability of every error
row, so a coherent system has a canonical completion without further input. -/
noncomputable def configuredCompletion
    (R : RecostClosingOutput J O)
    (F : System (base R) R.error) : GridCompletion F :=
  completion F R.error_summable

namespace Configured

variable (R : RecostClosingOutput J O) (F : System (base R) R.error)

/-- Canonical configured limiting marked data. -/
noncomputable def X : ℕ → Data :=
  (configuredCompletion R F).X

theorem row_cauchy (n : ℕ) : CauchySeq (F.P n) :=
  (configuredCompletion R F).row_cauchy n

theorem row_tendsto (n : ℕ) :
    Tendsto (F.P n) atTop (nhds (X R F n)) :=
  (configuredCompletion R F).row_tendsto n

theorem tail_dist (n k : ℕ) :
    dist (F.P n k) (X R F n) ≤ ShadowingTails.tail (R.error n) k :=
  (configuredCompletion R F).tail_dist n k

theorem base_dist (n : ℕ) :
    dist (base R n) (X R F n) ≤ ShadowingTails.tail (R.error n) 0 :=
  (configuredCompletion R F).base_dist n

end Configured

end CoherentPhaseReachableMetricRangeCompletion
