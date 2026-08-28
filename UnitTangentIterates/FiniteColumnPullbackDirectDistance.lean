import UnitTangentIterates.FiniteColumnStablePhysicalComponentCompactness
import UnitTangentIterates.FiniteColumnPullbackConfiguredSidecars

/-!
# Direct distance bounds for finite canonical pullback columns

The finite physical path at depth `k` need not end at the canonical datum at
depth `k + 1`.  The stable-component estimate controls the path leg and the
endpoint cap controls the remaining marked-distance leg.  This file
telescopes those genuine consecutive increments directly from depth zero.
No infinite recursive core or global selected-inverse map estimate is used.
-/

noncomputable section

open MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace FiniteColumnPullbackDirectDistance

open FiniteColumnPullbackPaperCapstone
open FiniteColumnStablePhysicalComponentCompactness

/-- The canonical one-step error: stable physical path leg followed by the
endpoint cap to the next canonical pullback. -/
def incrementError (componentConst conversionConst : ℝ)
    (defect cap : ℕ → ℝ) (k : ℕ) : ℝ :=
  conversionConst * ((4 * componentConst) * defect k) + cap k

/-- Pure finite telescoping from the depth-zero identity `grid n 0 = Q n`.
This statement deliberately requires neither nonnegativity nor summability. -/
theorem dist_grid_le_sum_of_step
    {kh : ℝ} {Q : ℕ → Data} {n k : ℕ} {e : ℕ → ℝ}
    (hstep : ∀ j,
      dist (grid kh Q n j) (grid kh Q n (j + 1)) ≤ e j) :
    dist (Q n) (grid kh Q n k) ≤ ∑ j ∈ Finset.range k, e j := by
  have hchain := dist_le_range_sum_dist (grid kh Q n) k
  calc
    dist (Q n) (grid kh Q n k) =
        dist (grid kh Q n 0) (grid kh Q n k) := by simp [grid]
    _ ≤ ∑ j ∈ Finset.range k,
          dist (grid kh Q n j) (grid kh Q n (j + 1)) := hchain
    _ ≤ ∑ j ∈ Finset.range k, e j :=
      Finset.sum_le_sum fun j _ => hstep j

/-- Stable physical components and endpoint caps furnish the canonical
partial-sum distance bound for one finite row. -/
theorem dist_grid_le_incrementError_sum
    {kh : ℝ} {Q : ℕ → Data} {n k : ℕ}
    {g : ℕ → Data}
    {Gamma : ∀ j, NormalPath (grid kh Q n j) (g j)}
    {period P0 P1 khat G1 Cg defect cap : ℕ → ℝ}
    {componentConst conversionConst c dlt : ℝ}
    (hmem : ∀ j, IsTubeMember c 0 dlt (grid kh Q n j))
    (hg : ∀ j u, HasDerivAt (⇑(g j).1) ((g j).2.1 u) u)
    (hgv : ∀ j u, HasDerivAt (⇑(g j).2.1) ((g j).2.2 u) u)
    (hgeom : ∀ j, IsVariableSpeedNormalPath
      (P0 j) (P1 j) (khat j) (G1 j) (Cg j) (Gamma j))
    (Hcomp : ∀ j, StablePhysicalComponents
      (Gamma j) (period j) componentConst (defect j))
    (hcomponent : 0 ≤ componentConst)
    (hconversionConst : 0 ≤ conversionConst)
    (hdefect : ∀ j, 0 ≤ defect j)
    (hconversion : ∀ j,
      c2ConstVar (P0 j) (P1 j) (khat j) (G1 j) (Cg j) ≤ conversionConst)
    (hcap : ∀ j, dist (g j) (grid kh Q n (j + 1)) ≤ cap j) :
    dist (Q n) (grid kh Q n k) ≤
      ∑ j ∈ Finset.range k,
        incrementError componentConst conversionConst defect cap j := by
  apply dist_grid_le_sum_of_step
  intro j
  exact canonical_increment_le
    (hmem j).hasDerivAt_curve (hmem j).hasDerivAt_vel
    (hg j) (hgv j) (hgeom j) (Hcomp j)
    hcomponent (hdefect j) hconversionConst (hconversion j) (hcap j)

theorem incrementError_nonnegative
    {componentConst conversionConst : ℝ} {defect cap : ℕ → ℝ}
    (hcomponent : 0 ≤ componentConst)
    (hconversionConst : 0 ≤ conversionConst)
    (hdefect : ∀ j, 0 ≤ defect j) (hcap : ∀ j, 0 ≤ cap j) :
    ∀ j, 0 ≤ incrementError componentConst conversionConst defect cap j := by
  intro j
  exact add_nonneg
    (mul_nonneg hconversionConst
      (mul_nonneg (mul_nonneg (by norm_num) hcomponent) (hdefect j)))
    (hcap j)

theorem incrementError_summable
    {componentConst conversionConst : ℝ} {defect cap : ℕ → ℝ}
    (hsumDefect : Summable defect) (hsumCap : Summable cap) :
    Summable (incrementError componentConst conversionConst defect cap) := by
  have H :=
    ((hsumDefect.mul_left (4 * componentConst)).mul_left conversionConst).add
      hsumCap
  refine H.congr ?_
  intro j
  dsimp [incrementError]

/-- The weakest uniform-in-depth consequence: summability is used only to
replace the exact finite partial sum by its full tail at zero. -/
theorem dist_grid_le_incrementError_tail
    {kh : ℝ} {Q : ℕ → Data} {n k : ℕ}
    {g : ℕ → Data}
    {Gamma : ∀ j, NormalPath (grid kh Q n j) (g j)}
    {period P0 P1 khat G1 Cg defect cap : ℕ → ℝ}
    {componentConst conversionConst c dlt : ℝ}
    (hmem : ∀ j, IsTubeMember c 0 dlt (grid kh Q n j))
    (hg : ∀ j u, HasDerivAt (⇑(g j).1) ((g j).2.1 u) u)
    (hgv : ∀ j u, HasDerivAt (⇑(g j).2.1) ((g j).2.2 u) u)
    (hgeom : ∀ j, IsVariableSpeedNormalPath
      (P0 j) (P1 j) (khat j) (G1 j) (Cg j) (Gamma j))
    (Hcomp : ∀ j, StablePhysicalComponents
      (Gamma j) (period j) componentConst (defect j))
    (hcomponent : 0 ≤ componentConst)
    (hconversionConst : 0 ≤ conversionConst)
    (hdefect : ∀ j, 0 ≤ defect j)
    (hconversion : ∀ j,
      c2ConstVar (P0 j) (P1 j) (khat j) (G1 j) (Cg j) ≤ conversionConst)
    (hcap : ∀ j, dist (g j) (grid kh Q n (j + 1)) ≤ cap j)
    (hsumDefect : Summable defect) (hsumCap : Summable cap) :
    dist (Q n) (grid kh Q n k) ≤
      ShadowingTails.tail
        (incrementError componentConst conversionConst defect cap) 0 := by
  have hcap0 : ∀ j, 0 ≤ cap j := fun j => dist_nonneg.trans (hcap j)
  have hsum := incrementError_summable
    (componentConst := componentConst)
    (conversionConst := conversionConst) hsumDefect hsumCap
  have hnonneg := incrementError_nonnegative hcomponent hconversionConst
    hdefect hcap0
  refine (dist_grid_le_incrementError_sum hmem hg hgv hgeom Hcomp
    hcomponent hconversionConst hdefect hconversion hcap).trans ?_
  simpa [ShadowingTails.tail] using
    hsum.sum_le_tsum (Finset.range k) (fun j _ => hnonneg j)

end FiniteColumnPullbackDirectDistance
