import Mathlib
import UnitTangentIterates.SelInvPerimBound
import UnitTangentIterates.PinchedCurveSelInv
import UnitTangentIterates.PinchedPathMetricCircle

/-!
# The universal Lipschitz bound is not vacuous

The bounds of `SelInvPerimBound.lean` are checked on the marked circle of radius
`r > 1`, an admissible curve for the pinching `kminP = κ̂ = 1/r`
(`PinchedPathMetricCircle.circle_isPinchedCurve`): the perimeter of its selected
inverse is at most `2πr`, and the Lipschitz estimate with the universal constant
applies to it.

Main results: `circle_perim_selInv_le`,
`circle_dist_selInv_le_pinchedDist_universal`,
`circle_isMarkedSelectedInverse_selInv`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open SelInvTubePathDist SelectedInverseMap SelInvLipUniversal
  GaugeMarkedDataOfRearFamily

variable {r : ℝ}

/-- **The selected inverse of the circle of radius `r > 1` has perimeter at most
`2πr`.** -/
theorem circle_perim_selInv_le (hr : 1 < r) :
    perim (selInv (1 / r) (circleData r)) ≤ 2 * Real.pi * r := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hkmin : (0 : ℝ) < 1 / r := by positivity
  have hp := circleData_mem_tube hr0
  have h := perim_selInv_le_of_isPinchedCurve hkmin (circle_isPinchedCurve hr)
    hp.hasDerivAt_curve
  have hrw : 2 * Real.pi / (1 / r) = 2 * Real.pi * r := by field_simp
  rwa [hrw] at h

/-- **The Lipschitz bound with the universal constant applies to the circle.**
-/
theorem circle_dist_selInv_le_pinchedDist_universal (hr : 1 < r) :
    dist (selInv (1 / r) (circleData r)) (selInv (1 / r) (circleData r))
      ≤ selInvLipUniversal (1 / r) (1 / r) (rearKappa1 (1 / r)) (2 * Real.pi * r)
          (2 * Real.pi * r) * pinchedDist (1 / r) (1 / r) (circleData r) (circleData r) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hkmin : (0 : ℝ) < 1 / r := by positivity
  have hkh1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have hp := circleData_mem_tube hr0
  have h := dist_selInv_le_pinchedDist_universal (kminP := 1 / r) (kh := 1 / r)
    (khat := rearKappa1 (1 / r)) hp.hasDerivAt_curve hp.hasDerivAt_vel
    hp.hasDerivAt_curve hp.hasDerivAt_vel hkh1 hkmin le_rfl
    (rearKappa1_nonneg hkmin.le hkh1) (circle_pinchedSet_nonempty hr)
  have hrw : 2 * Real.pi / (1 / r) = 2 * Real.pi * r := by field_simp
  rwa [hrw] at h

/-- **The marked selected inverse of the circle exists** by admissibility alone.
-/
theorem circle_isMarkedSelectedInverse_selInv (hr : 1 < r) :
    IsMarkedSelectedInverse (1 / r) (circleData r) (selInv (1 / r) (circleData r)) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hkmin : (0 : ℝ) < 1 / r := by positivity
  have hkh1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have hp := circleData_mem_tube hr0
  exact isMarkedSelectedInverse_selInv_of_isPinchedCurve hkmin hkh1
    (circle_isPinchedCurve hr) hp.hasDerivAt_curve hp.hasDerivAt_vel

/-- **The selected inverse of the circle can be iterated.**  For `r > √2` the
two thresholds of `isMarkedSelectedInverse_selInv_selInv` hold, so the marked
selected inverse of the image of the circle exists in its turn. -/
theorem circle_isMarkedSelectedInverse_selInv_selInv (hr : Real.sqrt 2 < r) :
    IsMarkedSelectedInverse (1 / r / Real.sqrt (1 - (1 / r) ^ 2))
      (selInv (1 / r) (circleData r))
      (selInv (1 / r / Real.sqrt (1 - (1 / r) ^ 2)) (selInv (1 / r) (circleData r))) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1s : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hr1 : 1 < r := lt_trans h1s hr
  have hr0 : 0 < r := lt_trans one_pos hr1
  have hrsq : 2 < r ^ 2 := by nlinarith
  have hkmin : (0 : ℝ) < 1 / r := by positivity
  have hkh1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr1
  have hsq : (1 / r : ℝ) ^ 2 = 1 / r ^ 2 := by rw [div_pow, one_pow]
  have hinv : 1 / r ^ 2 < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hy : (1 / 2 : ℝ) < 1 - (1 / r) ^ 2 := by rw [hsq]; linarith
  have hsqrtpos : 0 < Real.sqrt (1 - (1 / r) ^ 2) :=
    Real.sqrt_pos.2 (by linarith)
  have hhalf : (1 / 2 : ℝ) < Real.sqrt (1 - (1 / r) ^ 2) :=
    (Real.lt_sqrt (by norm_num)).2 (by nlinarith)
  have hlt : 1 / r < Real.sqrt (1 - (1 / r) ^ 2) :=
    (Real.lt_sqrt (by positivity)).2 (by rw [hsq]; linarith)
  have hkap1 : 1 / r / Real.sqrt (1 - (1 / r) ^ 2) < 1 := (div_lt_one hsqrtpos).2 hlt
  have hshort : 1 / r / Real.sqrt (1 - (1 / r) ^ 2) * (2 * Real.pi / (1 / r))
      < 4 * Real.pi := by
    have hrw : 2 * Real.pi / (1 / r) = 2 * Real.pi * r := by field_simp
    rw [hrw]
    have hval : 1 / r / Real.sqrt (1 - (1 / r) ^ 2) * (2 * Real.pi * r)
        = 2 * Real.pi / Real.sqrt (1 - (1 / r) ^ 2) := by
      field_simp
    rw [hval, div_lt_iff₀ hsqrtpos]
    nlinarith [Real.pi_pos]
  have hp := circleData_mem_tube hr0
  exact isMarkedSelectedInverse_selInv_selInv hkmin hkh1 (circle_isPinchedCurve hr1)
    hp.hasDerivAt_curve hp.hasDerivAt_vel hkap1 hshort

end PinchedPath
