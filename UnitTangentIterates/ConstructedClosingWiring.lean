import UnitTangentIterates.ConstructedPulseWidth
import UnitTangentIterates.ConstructedWeightedClosingGap
import UnitTangentIterates.ConstructedConfiguredSequenceWeighted
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed

/-!
# Wiring uniform width to the weighted closing gap

The constructed sequence supplies both a uniform transverse width bound
`Cw = 4*Am + 2` (via `ConstructedPulseWidth`) and an explicit weighted
shadow tail majorant (via `ConstructedWeightedClosingGap`).  This file
shows the two thresholds can be met simultaneously by choosing the initial
separation `Hs 0` large, which is exactly the `Hrequired` parameter of
`exists_dataWithActualHalf_above_of_eps`.
-/

noncomputable section

open Real Set Function MeasureTheory intervalIntegral
open ConstructedConfiguredSequenceWeighted
open ConstructedWeightedClosingGap
open UnconditionalAssembly.ApproximatePaperAssemblyResidual

namespace ConstructedClosingWiring

/-- If the model front at `n=0` has width ≤ `Cw` and the weighted tail
is ≤ `R`, then the coarse-gap inequality holds as soon as `Hs 0` is
above `(π*Cw + (2π+1)*Csh*R)/2`. This is the user-visible form of
`ConstructedWeightedClosingGap.gap_of_start_above_coarseTail`. -/
theorem width_tail_imply_gap
    {Cw Csh R H0 : ℝ} {E : ℝ}
    (hCw : 0 ≤ Cw) (hCsh : 0 ≤ Csh) (hE : 0 ≤ E) (hER : E ≤ R)
    (hstart : (Real.pi * Cw + (2 * Real.pi + 1) * (Csh * R)) / 2 < H0) :
    Cw + 2 * (Csh * E) < (2 * H0 - Csh * E) / Real.pi :=
  gap_of_start_above_coarseTail hCw hCsh hE hER hstart

/-- **Combined threshold.**  For a constructed weighted datum `D`,
a width constant `Cw` (e.g. `4*Am+2` from `ConstructedPulseWidth`),
and any `Csh ≥ 0`, the exact `hgap` required by
`ApproximatePaperAssemblySelectedInverse.conclude_of_approx_weighted_markedDefect_selInv`
holds whenever `D.Hs 0` exceeds both the width `Hstar` and the
tail `Htail`.  The datum itself can be made to satisfy this by
choosing `Hrequired` large in `exists_dataWithActualHalf_above_of_eps`. -/
theorem final_gap_of_large_start
    (D : Data)
    {Cw Csh C2 K P0 Pv0 Pv1 khat G1 Cg : ℝ}
    (hC2eq : C2 = NormalPathC2IncrementVariableSpeed.c2ConstVar Pv0 Pv1 khat G1 Cg)
    (hC2 : 0 ≤ C2) (hK : 0 ≤ K) (hP0 : 0 < P0) (hP0le : P0 ≤ D.Hs 0)
    (hthreshold : K * Real.exp (-(D.beta * D.deltaStep)) < 1)
    (hCw : 0 ≤ Cw) (hCsh : 0 ≤ Csh)
    (hwidth : Width.width
        (range (TwoCapPairsAssembly.front (D.kappas 0) 0 (D.Hs 0)))
        (ConstructedPulseWidth.phaseDirection (D.kappas 0) 0 (D.Hs 0)) ≤ Cw)
    (hstart : (Real.pi * Cw + (2 * Real.pi + 1) *
        (Csh * coarseTailMajorant C2 K D.matchCoefficient 1 D.kstar D.kd
          P0 D.beta D.deltaStep)) / 2 < D.Hs 0) :
    Cw + 2 * (Csh * shadowError K Pv0 Pv1 khat G1 Cg D.matchCoefficient 1
        D.kstar D.kd D.beta D.Hs) <
      (2 * D.Hs 0 - Csh * shadowError K Pv0 Pv1 khat G1 Cg D.matchCoefficient 1
        D.kstar D.kd D.beta D.Hs) / Real.pi := by
  -- coarse tail dominates the actual shadow error
  have hE := shadowError_le_coarseTailMajorant (C2 := C2) (Pv0 := Pv0) (Pv1 := Pv1)
      (khat := khat) (G1 := G1) (Cg := Cg)
      (Cm := D.matchCoefficient) (L := 1) (kstar := D.kstar) (kd := D.kd)
      (P0 := P0) (H0 := D.Hs 0) (beta := D.beta) (deltaStep := D.deltaStep)
      hC2eq hC2 hK D.matchCoefficient_nonneg (by norm_num) D.kstar_nonneg D.kd_nonneg hP0
      D.separation_zero_pos.le D.beta_pos D.deltaStep_pos
      (fun n => hP0le.trans (D.separation_lower n))
      D.separation_linear hthreshold
  have hEnn : 0 ≤ shadowError K Pv0 Pv1 khat G1 Cg D.matchCoefficient 1
      D.kstar D.kd D.beta D.Hs := by
    dsimp [shadowError]
    apply ShadowingTails.tail_nonneg
    intro n
    have hc2 : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar Pv0 Pv1 khat G1 Cg := by
      rw [← hC2eq]; exact hC2
    have hd : 0 ≤ PathMetric.WeightedMarkedDefectThreshold.canonicalMarkedDefect
        D.matchCoefficient 1 D.kstar D.kd D.beta D.Hs n := by
      dsimp [PathMetric.WeightedMarkedDefectThreshold.canonicalMarkedDefect]
      exact mul_nonneg
        (mul_nonneg (CurvatureStabilityL1.l1Modulus_nonneg _ _ _) (sq_nonneg (1 : ℝ)))
        (add_nonneg zero_le_one (mul_nonneg D.kstar_nonneg zero_le_one))
    exact mul_nonneg hc2 (mul_nonneg (pow_nonneg hK n) hd)
  -- apply the scalar gap lemma with E := shadowError, R := coarseTailMajorant
  exact gap_of_start_above_coarseTail hCw hCsh hEnn hE hstart

/-- Existence form: for any width threshold `Hwidth` we can choose a combined
threshold that also exceeds the gap threshold `(π*Cw + (2π+1)*Csh*R)/2`. -/
theorem exists_combined_threshold
    {Cw Csh R : ℝ} (hCw : 0 ≤ Cw) (hCsh : 0 ≤ Csh) (hR : 0 ≤ R)
    {Hwidth : ℝ} (hHwidth : 0 < Hwidth) :
    ∃ Hstar_comb : ℝ, 0 < Hstar_comb ∧
      ∀ H0 : ℝ, Hstar_comb ≤ H0 →
        (Real.pi * Cw + (2 * Real.pi + 1) * (Csh * R)) / 2 < H0 := by
  refine ⟨max Hwidth ((Real.pi * Cw + (2 * Real.pi + 1) * (Csh * R)) / 2 + 1),
    lt_of_lt_of_le hHwidth (le_max_left _ _), ?_⟩
  intro H0 hH0
  have hle : (Real.pi * Cw + (2 * Real.pi + 1) * (Csh * R)) / 2 + 1 ≤
      max Hwidth ((Real.pi * Cw + (2 * Real.pi + 1) * (Csh * R)) / 2 + 1) :=
    le_max_right _ _
  linarith

end ConstructedClosingWiring
