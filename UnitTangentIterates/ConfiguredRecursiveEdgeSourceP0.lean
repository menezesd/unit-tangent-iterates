import UnitTangentIterates.ConfiguredRecursiveSourceP0

/-!
# A successor-edge speed floor for configured recursive sources

The recursive base source at row `n` lives on the retained interpolation
output indexed by `n + 1`.  Its natural period cap is therefore the configured
cap at `n + 1`.  The minimum below preserves the weakening available at the
current base stage while retaining the numerical reserve at the successor
edge.
-/

noncomputable section

namespace ConfiguredRecursiveEdgeSourceP0

open ConfiguredApproximateDefectPathRowwise
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveSourceP0

def edgeSpeedCap
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  speedCap D (n + 1)

def edgeSourceP0
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  min (sourceP0 D n) (sourceP0 D (n + 1))

theorem edgeSpeedCap_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ edgeSpeedCap D n := by
  unfold edgeSpeedCap speedCap
  exact mul_nonneg (by norm_num)
    (add_nonneg zero_le_one (D.model.separation_pos (n + 1)).le)

theorem edgeSourceP0_pos
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 < edgeSourceP0 D n := by
  exact lt_min (sourceP0_pos D n) (sourceP0_pos D (n + 1))

theorem edgeSourceP0_le_current
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    edgeSourceP0 D n ≤ sourceP0 D n :=
  min_le_left _ _

theorem edgeSourceP0_le_next
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    edgeSourceP0 D n ≤ sourceP0 D (n + 1) :=
  min_le_right _ _

theorem edgeSourceP0_le_rowP0
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    edgeSourceP0 D n ≤ rowP0 D n :=
  (edgeSourceP0_le_current D n).trans (sourceP0_le_rowP0 D n)

theorem one_div_next_le_edge
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    1 / sourceP0 D (n + 1) ≤ 1 / edgeSourceP0 D n :=
  one_div_le_one_div_of_le (edgeSourceP0_pos D n)
    (edgeSourceP0_le_next D n)

theorem one_div_sq_next_le_edge
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    1 / sourceP0 D (n + 1) ^ 2 ≤ 1 / edgeSourceP0 D n ^ 2 := by
  apply one_div_le_one_div_of_le (sq_pos_of_pos (edgeSourceP0_pos D n))
  exact pow_le_pow_left₀ (edgeSourceP0_pos D n).le
    (edgeSourceP0_le_next D n) 2

theorem numerical_A
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    2 + 2 * analyticKhat D *
        GaugeRearFamilyFromFront.rearDriftConst (edgeSpeedCap D n) sourceKh ≤
      1 / edgeSourceP0 D n := by
  exact (ConfiguredRecursiveSourceP0.numerical_A D (n + 1)
    (edgeSpeedCap_nonnegative D n) le_rfl).trans (one_div_next_le_edge D n)

theorem numerical_K
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
        (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst
          sourceKh) + 2) +
        analyticKhat D ^ 2 +
        2 * GaugeRearFamilyFromFront.rearDriftConst
          (edgeSpeedCap D n) sourceKh *
          FiniteSmoothRearFamilyMarkingAwareSmoothSource.successorKx sourceKh ≤
      1 / edgeSourceP0 D n ^ 2 + analyticKhat D ^ 2 := by
  apply (ConfiguredRecursiveSourceP0.numerical_K D (n + 1)
    (edgeSpeedCap_nonnegative D n) le_rfl).trans
  simpa [add_comm] using
    (add_le_add_right (one_div_sq_next_le_edge D n) (analyticKhat D ^ 2))

end ConfiguredRecursiveEdgeSourceP0
