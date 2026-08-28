import UnitTangentIterates.ApproximatePaperAssemblyResidual
import UnitTangentIterates.DirectMarkedLimitOrbit

/-!
# Approximate paper assembly for the canonical selected inverse

This removes the auxiliary total forward map from the final interface.  The
physical rear components themselves identify every successor with the
unit-tangent range of its predecessor.
-/

noncomputable section

open Set Function Complex MarkedSpace Metric PathMetric
open PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace UnconditionalAssembly

open PaperFaithfulAssemblyRemainder
open PathMetric.WeightedMarkedDefectThreshold
open PathMetric.WeightedRecursiveDefect

namespace ApproximatePaperAssemblySelectedInverse

/-- Paper-faithful approximate closing with the actual selected inverse.
Compared with `conclude_of_approx_weighted_markedDefect`, the artificial map
`T` and both compatibility assumptions `hTB`, `hTev` are absent. -/
theorem conclude_of_approx_weighted_markedDefect_selInv
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 eps : ℕ → ℝ}
    {Q : ℕ → Data}
    {K P0 P1 kh G1 Cg Cm L kstar kd H0 deltaStep beta c dlt Cw Csh : ℝ}
    {dir : ℂ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (hceiling : model.kstar < 1) (hstrict : ∀ n s, 0 < kappas n s)
    (hK : 1 ≤ K) (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hCm : 0 ≤ Cm) (hL : 0 ≤ L) (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ Hs n)
    (hgrow : ∀ n : ℕ, H0 + n * deltaStep ≤ Hs n)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1)
    (hmap : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 kh G1 Cg Gamma →
      ∀ eta : ℝ, 0 < eta →
        ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
            (SelectedInverseMap.selInv kh q),
          cost Delta ≤ K * cost Gamma + eta ∧
          IsVariableSpeedNormalPath P0 P1 kh G1 Cg Delta)
    (hdefect : ∀ n : ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ Lambda : NormalPath (Q n)
          (SelectedInverseMap.selInv kh (Q (n + 1))),
        cost Lambda ≤
          canonicalMarkedDefect Cm L kstar kd beta Hs n + eta ∧
        IsVariableSpeedNormalPath P0 P1 kh G1 Cg Lambda)
    (hC : 0 ≤ c2ConstVar P0 P1 kh G1 Cg)
    (residual : ClosedTubeInvarianceResidual
      (SelectedInverseMap.selInv kh) Q c dlt)
    (hBcont : Continuous (SelectedInverseMap.selInv kh))
    (physical : PhysicalRearLimitComponentFamily
      (fun n k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k))
    (hc : 0 < c) (hdlt : 0 < dlt)
    (hQfront : ∀ n, ev (Q n) =
      TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n))
    (hQperim : perim (Q 0) = 2 * Hs 0)
    (hCsh : 1 ≤ Csh) (hdir : ‖dir‖ = 1)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh *
        ApproximatePaperAssemblyResidual.shadowError
          K P0 P1 kh G1 Cg Cm L kstar kd beta Hs) <
      (2 * Hs 0 - Csh *
        ApproximatePaperAssemblyResidual.shadowError
          K P0 P1 kh G1 Cg Cm L kstar kd beta Hs) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) =
        range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  let d : ℕ → ℝ := canonicalMarkedDefect Cm L kstar kd beta Hs
  let E : ℝ := ApproximatePaperAssemblyResidual.shadowError
    K P0 P1 kh G1 Cg Cm L kstar kd beta Hs
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hd0 : ∀ n, 0 ≤ d n := by
    intro n
    dsimp [d, canonicalMarkedDefect]
    exact mul_nonneg
      (mul_nonneg (CurvatureStabilityL1.l1Modulus_nonneg _ _ _) (sq_nonneg L))
      (by positivity)
  have hweighted : Summable (weightedDefect K d) := by
    simpa [d] using summable_weighted_canonicalMarkedDefect
      hK0 hbeta hdelta hCm hL hkstar hkd hP0 hPle hgrow hthreshold
  have hrows : ∀ n, Summable (fun k => K ^ k * d (n + k)) := by
    have h := summable_pullbackError_of_summable_weighted hK hd0 hweighted
    intro n
    simpa [pullbackError] using h n
  have hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k) :=
    pullback_mem_closedTube residual
  obtain ⟨X, hXmem, hXlim, hinv, hdist⟩ :=
    PaperFaithfulApproximatePullback.exists_markedLimit_of_approx_variableSpeed_transport
      hK0 hrows hmap (by simpa [d] using hdefect) hC hmem hBcont
  have hEnonneg : 0 ≤ E := by
    dsimp [E, ApproximatePaperAssemblyResidual.shadowError]
    apply ShadowingTails.tail_nonneg
    intro n
    exact mul_nonneg hC (mul_nonneg (pow_nonneg hK0 n) (hd0 n))
  have hdist0 : dist (Q 0) (X 0) ≤ E := by
    simpa [E, ApproximatePaperAssemblyResidual.shadowError, d] using hdist 0
  have hclose : ∀ u, ‖(X 0).1 u - (Q 0).1 u‖ ≤ Csh * E := by
    intro u
    calc
      ‖(X 0).1 u - (Q 0).1 u‖ ≤ dist (X 0) (Q 0) :=
        MarkedSpace.dist_apply_le (X 0) (Q 0) u
      _ = dist (Q 0) (X 0) := dist_comm _ _
      _ ≤ E := hdist0
      _ ≤ Csh * E := by nlinarith
  have hperim : |perim (X 0) - perim (Q 0)| ≤ Csh * E := by
    calc
      |perim (X 0) - perim (Q 0)| ≤ dist (X 0) (Q 0) :=
        MarkedSpace.abs_perim_sub_le_dist _ _
      _ = dist (Q 0) (X 0) := dist_comm _ _
      _ ≤ E := hdist0
      _ ≤ Csh * E := by nlinarith
  have hoval : ∀ n, MainTheoremConditional.IsOval (ev (X n)) := by
    intro n
    have hstrictX := physical.limitStrictness hc hmem X hXlim n
    exact isOval_ev_of_limitStrictnessData hc hdlt (hXmem n) hstrictX
  have horbit : ∀ n, range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n))) := by
    intro n
    let S := Nonempty.some (physical.stage X hXlim n)
    exact S.range_front_eq_unitTangent_rear
  have hshadow : ∃ (Y : ℕ → ℝ → ℂ) (LY : ℝ),
      (∀ n, MainTheoremConditional.IsOval (Y n)) ∧
      (∀ n, range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n))) ∧
      0 < LY ∧ Periodic (Y 0) LY ∧
      Metric.hausdorffDist (range (Y 0))
        (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤
          Csh * E ∧
      2 * Hs 0 - Csh * E ≤ LY :=
    PaperFaithfulAssemblyRemainder.shadowingOrbit_of_markedLimit_direct
      hc residual.model_mem hXmem hQfront horbit hoval hclose hperim hQperim
  let assembly : PaperFaithfulAssemblyRemainder
      kappas Hs theta0 eps Cw Csh dir :=
    { model := model
      shadow_error := E
      shadow_error_nonneg := hEnonneg
      shadow_factor_nonneg := zero_le_one.trans hCsh
      direction_unit := hdir
      model_width := hwidth
      transverse_gap := by simpa [E] using hgap
      shadowing_orbit := hshadow }
  exact PaperFaithfulAssemblyRemainder.conclude assembly

end ApproximatePaperAssemblySelectedInverse

end UnconditionalAssembly
