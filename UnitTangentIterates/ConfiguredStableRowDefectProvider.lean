import UnitTangentIterates.ConfiguredRowDefectProvider

/-!
# Paper-stable configured row defects

The invariant-tube proof in the paper propagates the four Jacobi quantities
separately.  Its `W` component is nonexpansive, while the `S_j` components are
reset from `W` after each selected-rear step.  Consequently the defect at row
`n`, depth `k` is bounded by the ordinary shifted defect `d (n + k)`, without
a factor `K ^ k`.

This file packages the corresponding scalar `RowDefectProvider`.  It does not
claim that the current aggregate-cost map-stage API supplies the required
componentwise Jacobi transport certificate.
-/

noncomputable section

open PathMetric

namespace ConfiguredStableRowDefectProvider

open ConfiguredApproximateDefectPathRowwise
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- Paper-faithful diagonal error before the fixed Jacobi conversion constants
are applied: the model defect is shifted, not multiplied at every depth. -/
def error (D : ConstructedConfiguredSequenceWeighted.Data) (n k : ℕ) : ℝ :=
  rowDefect D (n + k)

/-- The stable error is the old weighted error specialized to the
nonexpansive factor `1`. -/
theorem error_eq_weight_one
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    error D = ConfiguredRowDefectProvider.error D 1 := by
  funext n k
  simp [error, ConfiguredRowDefectProvider.error,
    WeightedRecursiveDefect.pullbackError]

/-- The scalar threshold at factor `1` is automatic from the positive model
decay rate and positive separation step. -/
theorem unweighted_threshold
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    (1 : ℝ) * Real.exp
      (-((D.model.beta / 4) * D.deltaStep)) < 1 := by
  rw [one_mul, Real.exp_lt_one_iff]
  exact neg_neg_of_pos (mul_pos
    (div_pos (D.model.configs 0).hbeta0 (by norm_num)) D.deltaStep_pos)

/-- The ordinary shifted configured defects are summable in every triangular
row.  No transport amplification or `K * exp (-beta*delta/4) < 1` premise is
present. -/
def provider (D : ConstructedConfiguredSequenceWeighted.Data) :
    RowDefectProvider (error D) := by
  rw [error_eq_weight_one D]
  exact ConfiguredRowDefectProvider.provider D (K := 1) le_rfl
    (unweighted_threshold D)

/-- Every finite stable row prefix is bounded by its ordinary additive tail. -/
theorem prefix_le_tail
    (D : ConstructedConfiguredSequenceWeighted.Data) (n k : ℕ) :
    (∑ j ∈ Finset.range k, error D n j) ≤
      ShadowingTails.tail (error D n) 0 := by
  simpa [ShadowingTails.tail] using
    ((provider D).summable n |>.sum_le_tsum (Finset.range k)
      (fun j _ => (provider D).nonnegative n j))

end ConfiguredStableRowDefectProvider
