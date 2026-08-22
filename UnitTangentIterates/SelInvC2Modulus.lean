import Mathlib
import UnitTangentIterates.SelInvRearFamilySupC2

/-!
# The `C²` estimate of the selected inverse is a modulus of continuity

`SelInvRearFamilySupC2.dist_selInv_le_of_rear_family_sup_C2` bounds the marked
distance of the two selected inverses of the ends of a normal path by

`markingC2Bound (2P₁κ̂'c) (flowDefectC1Int ℓ (κ̂'c)) (flowDefectC2Int ℓ (κ̂'c) (γ₂c)) L kb kL
  + c2ConstVar Pv₀ (costP1 ℓ κ̂ M) κ̂ (costG1 ℓ κ̂ κ₂ M) (…) · M` ,

a function of the two costs `c = cost Γ` (the cost of the path of fronts) and
`M = ∫₀^T m` (the cost of the family of rears) alone, all the other arguments
being fixed data of the two ends.

This file names that function, `selInvC2Modulus`, records that it is literally
the right-hand side of the estimate, and shows that it is a *modulus*: it is
continuous and vanishes at `(0,0)`, so the bound tends to zero as the two costs
do.  In particular the selected-inverse map is continuous along families of
paths whose costs shrink to zero.

Main results: `bound_eq_modulus`, `tendsto_selInvC2Modulus_zero`.
-/

noncomputable section

open Filter Topology

namespace SelInvC2Modulus

open MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2Increment NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

/-- **The bound of the `C²` selected-inverse estimate, as a function of the two
costs.**  `c` is the cost of the normal path of fronts and `M` the total cost of
the family of selected rears; all the other arguments are fixed data of the two
ends. -/
def selInvC2Modulus (P1 kh ell L kb kL Pv0 khat kappa2 : ℝ) (c M : ℝ) : ℝ :=
  markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * c)
      (flowDefectC1Int ell (kh / (1 - kh ^ 2) * c))
      (flowDefectC2Int ell (kh / (1 - kh ^ 2) * c) (gaugeGrowth2 kh * c)) L kb kL
    + c2ConstVar Pv0 (costP1 ell khat M) khat (costG1 ell khat kappa2 M)
        (khat * costG1 ell khat kappa2 M + kappa2 * costP1 ell khat M ^ 2) * M

/-- The right-hand side of the `C²` selected-inverse estimate *is* the
modulus. -/
theorem bound_eq_modulus (P1 kh ell L kb kL Pv0 khat kappa2 c M : ℝ) :
    markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * c)
        (flowDefectC1Int ell (kh / (1 - kh ^ 2) * c))
        (flowDefectC2Int ell (kh / (1 - kh ^ 2) * c) (gaugeGrowth2 kh * c)) L kb kL
      + c2ConstVar Pv0 (costP1 ell khat M) khat (costG1 ell khat kappa2 M)
          (khat * costG1 ell khat kappa2 M + kappa2 * costP1 ell khat M ^ 2) * M
    = selInvC2Modulus P1 kh ell L kb kL Pv0 khat kappa2 c M := rfl

/-- The modulus is jointly continuous in the two costs. -/
theorem continuous_selInvC2Modulus (P1 kh ell L kb kL Pv0 khat kappa2 : ℝ) :
    Continuous fun z : ℝ × ℝ =>
      selInvC2Modulus P1 kh ell L kb kL Pv0 khat kappa2 z.1 z.2 := by
  unfold selInvC2Modulus markingC2Bound flowDefectC1Int flowDefectC2Int c2ConstVar
    velConst accConstVar costG1 costP1
  refine Continuous.add (Continuous.max ?_ (Continuous.max ?_ ?_))
    (Continuous.mul (Continuous.max ?_ (Continuous.max ?_ ?_)) continuous_snd) <;> fun_prop

/-- The modulus vanishes when both costs vanish. -/
theorem selInvC2Modulus_zero (P1 kh ell L kb kL Pv0 khat kappa2 : ℝ) :
    selInvC2Modulus P1 kh ell L kb kL Pv0 khat kappa2 0 0 = 0 := by
  unfold selInvC2Modulus markingC2Bound flowDefectC1Int flowDefectC2Int
  norm_num

/-- **The `C²` selected-inverse estimate is a modulus of continuity**: its bound
tends to zero as the cost of the path of fronts and the cost of the family of
selected rears both tend to zero. -/
theorem tendsto_selInvC2Modulus_zero (P1 kh ell L kb kL Pv0 khat kappa2 : ℝ) :
    Tendsto (fun z : ℝ × ℝ =>
        selInvC2Modulus P1 kh ell L kb kL Pv0 khat kappa2 z.1 z.2)
      (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 0) :=
  (continuous_selInvC2Modulus P1 kh ell L kb kL Pv0 khat kappa2).tendsto' _ _
    (selInvC2Modulus_zero P1 kh ell L kb kL Pv0 khat kappa2)

end SelInvC2Modulus
