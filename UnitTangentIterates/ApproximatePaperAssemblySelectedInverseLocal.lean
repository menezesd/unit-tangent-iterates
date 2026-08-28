import UnitTangentIterates.ApproximatePaperAssemblySelectedInverse
import UnitTangentIterates.LocalVariableSpeedApproximatePullback
import UnitTangentIterates.InductiveLocalPullbackTube
import UnitTangentIterates.PhysicalRearLimitHarnackAdapter
import UnitTangentIterates.SelectedInverseFiniteRangeConstructor
import UnitTangentIterates.WeightedDefectUniformCap

/-!
# Selected-inverse paper assembly from local bounded transport

This is the selected-inverse capstone with the global `hmap` premise replaced
by transport local to the invariant closed tube and to paths of cost at most
`Mtotal`.  The strict weighted-stage cap supplies the epsilon room required by
the local approximate iteration.
-/

noncomputable section

open Set Function Complex MarkedSpace Metric PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace ApproximatePaperAssemblySelectedInverseLocal

open PathMetric.WeightedMarkedDefectThreshold
open PathMetric.WeightedRecursiveDefect
open UnconditionalAssembly
open UnconditionalAssembly.PaperFaithfulAssemblyRemainder

theorem conclude_of_local_approx_weighted_markedDefect_selInv
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 eps : ℕ → ℝ}
    {Q : ℕ → Data}
    {K P0 P1 kh G1 Cg Cm L kstar kd H0 deltaStep beta c d0 dlt Mtotal Cw Csh : ℝ}
    {A0 rho : ℕ → ℝ}
    {dir : ℂ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (hK : 1 ≤ K) (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hCm : 0 ≤ Cm) (hL : 0 ≤ L) (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ Hs n)
    (hgrow : ∀ n : ℕ, H0 + n * deltaStep ≤ Hs n)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1)
    (hmap : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 P1 kh G1 Cg Gamma →
      cost Gamma ≤ Mtotal →
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
    (hcap : ∀ n k, K ^ k *
      canonicalMarkedDefect Cm L kstar kd beta Hs (n + k) < Mtotal)
    (htube : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      (SelectedInverseMap.selInv kh) Q (c2ConstVar P0 P1 kh G1 Cg) K
      (canonicalMarkedDefect Cm L kstar kd beta Hs) c d0 dlt A0 rho)
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
  obtain ⟨hfiniteMem, _hincr⟩ :=
    PaperFaithfulLocalApproximatePullback.diagonal_membership_and_increment_of_inductive_budget
      hK hd0 hrows hmap (by simpa [d] using hdefect) hC
        (by simpa [d] using hcap) (by simpa [d] using htube)
  have hmem := hfiniteMem
  obtain ⟨X, hXmem, hXlim, hinv, hdist⟩ :=
    PaperFaithfulLocalApproximatePullback.exists_markedLimit_of_local_transport
      hK hrows hmap (by simpa [d] using hdefect) hC hfiniteMem
        (by simpa [d] using hcap) hBcont
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
      hc (fun n => by simpa [TubePullbackLimit.pullback] using hfiniteMem n 0)
        hXmem hQfront horbit hoval hclose hperim hQperim
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

/-- Local selected-inverse closing without continuity of the selected-inverse
map and without a physical reconstruction package at the limit.  Aligned
finite physical edges supply Harnack strictness of each marked row limit,
while finite curvature/turning data supply the unit-tangent range orbit.
-/
theorem conclude_of_local_approx_weighted_markedDefect_selInv_finite
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 eps : ℕ → ℝ}
    {Q : ℕ → Data}
    {K P0 P1 kh G1 Cg Cm L kstar kd H0 deltaStep beta c d0 dlt Mtotal Cw Csh : ℝ}
    {A0 rho : ℕ → ℝ}
    {dir : ℂ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (hK : 1 ≤ K) (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hCm : 0 ≤ Cm) (hL : 0 ≤ L) (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ Hs n)
    (hgrow : ∀ n : ℕ, H0 + n * deltaStep ≤ Hs n)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1)
    (hmap : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 P1 kstar G1 Cg Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eta : ℝ, 0 < eta →
        ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
            (SelectedInverseMap.selInv kh q),
          cost Delta ≤ K * cost Gamma + eta ∧
          IsVariableSpeedNormalPath P0 P1 kstar G1 Cg Delta)
    (hdefect : ∀ n : ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ Lambda : NormalPath (Q n)
          (SelectedInverseMap.selInv kh (Q (n + 1))),
        cost Lambda ≤
          canonicalMarkedDefect Cm L kstar kd beta Hs n + eta ∧
        IsVariableSpeedNormalPath P0 P1 kstar G1 Cg Lambda)
    (hC : 0 ≤ c2ConstVar P0 P1 kstar G1 Cg)
    (hcap : ∀ n k, K ^ k *
      canonicalMarkedDefect Cm L kstar kd beta Hs (n + k) < Mtotal)
    (htube : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      (SelectedInverseMap.selInv kh) Q (c2ConstVar P0 P1 kstar G1 Cg) K
      (canonicalMarkedDefect Cm L kstar kd beta Hs) c d0 dlt A0 rho)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (finitePhysical : PathMetric.FinitePullbackPhysicalRearKinematics kh
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
          K P0 P1 kstar G1 Cg Cm L kstar kd beta Hs) <
      (2 * Hs 0 - Csh *
        ApproximatePaperAssemblyResidual.shadowError
          K P0 P1 kstar G1 Cg Cm L kstar kd beta Hs) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) =
        range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  let d : ℕ → ℝ := canonicalMarkedDefect Cm L kstar kd beta Hs
  let E : ℝ := ApproximatePaperAssemblyResidual.shadowError
    K P0 P1 kstar G1 Cg Cm L kstar kd beta Hs
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
  obtain ⟨hfiniteMem, _hincr⟩ :=
    PaperFaithfulLocalApproximatePullback.diagonal_membership_and_increment_of_inductive_budget
      hK hd0 hrows hmap (by simpa [d] using hdefect) hC
        (by simpa [d] using hcap) (by simpa [d] using htube)
  have hmem := hfiniteMem
  obtain ⟨X, hXmem, hXlim, hdist⟩ :=
    PaperFaithfulLocalApproximatePullback.exists_markedLimit_of_local_transport_without_map_continuity
      hK hrows hmap (by simpa [d] using hdefect) hC hfiniteMem
        (by simpa [d] using hcap)
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
    exact PathMetric.isOval_ev_of_finitePullbackPhysicalRearKinematics
      hkh0 hkh1 hc hdlt hmem finitePhysical X hXlim n
  have hfiniteRange : ∀ n k,
      range (ev (TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q (n + 1) k)) =
      range (UnitTangent.unitTangentMap (ev (TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n (k + 1)))) := by
    intro n k
    let K := Classical.choice (finitePhysical.stage n k)
    let S := K.toStageComponents hkh0 hkh1 hc (hmem (n + 1) k)
    exact S.range_front_eq_unitTangent_rear
  have horbit : ∀ n, range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n))) :=
    PullbackUnitTangentRangeOrbit.orbitRange_of_finite_pullbackEdges
      hc hmem hXmem hXlim hfiniteRange
  have hshadow : ∃ (Y : ℕ → ℝ → ℂ) (LY : ℝ),
      (∀ n, MainTheoremConditional.IsOval (Y n)) ∧
      (∀ n, range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n))) ∧
      0 < LY ∧ Periodic (Y 0) LY ∧
      Metric.hausdorffDist (range (Y 0))
        (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤
          Csh * E ∧
      2 * Hs 0 - Csh * E ≤ LY :=
    PaperFaithfulAssemblyRemainder.shadowingOrbit_of_markedLimit_direct
      hc (fun n => by simpa [TubePullbackLimit.pullback] using hfiniteMem n 0)
        hXmem hQfront horbit hoval hclose hperim hQperim
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

/-- When local transport is available for every positive cost cap, weighted
summability supplies a suitable cap automatically.  The fixed-cap theorem
above remains the interface for raw-gauge estimates whose constants depend on
`Mtotal`. -/
theorem conclude_of_local_approx_weighted_markedDefect_selInv_existsCap
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 eps : ℕ → ℝ}
    {Q : ℕ → Data}
    {K P0 P1 kh G1 Cg Cm L kstar kd H0 deltaStep beta c d0 dlt Cw Csh : ℝ}
    {A0 rho : ℕ → ℝ}
    {dir : ℂ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (hK : 1 ≤ K) (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hCm : 0 ≤ Cm) (hL : 0 ≤ L) (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ Hs n)
    (hgrow : ∀ n : ℕ, H0 + n * deltaStep ≤ Hs n)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1)
    (hmap : ∀ Mtotal : ℝ, 0 < Mtotal →
      ∀ (p q : Data) (Gamma : NormalPath p q),
        IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
        IsVariableSpeedNormalPath P0 P1 kh G1 Cg Gamma →
        cost Gamma ≤ Mtotal →
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
    (htube : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      (SelectedInverseMap.selInv kh) Q (c2ConstVar P0 P1 kh G1 Cg) K
      (canonicalMarkedDefect Cm L kstar kd beta Hs) c d0 dlt A0 rho)
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
  obtain ⟨Mtotal, hMtotal, hcap⟩ :=
    exists_uniform_weighted_stage_cap hK hd0 hweighted
  exact conclude_of_local_approx_weighted_markedDefect_selInv
    model hK hbeta hdelta hCm hL hkstar hkd hP0 hPle hgrow
      hthreshold (hmap Mtotal hMtotal) hdefect hC
      (by simpa [d] using hcap) htube hBcont physical hc hdlt hQfront hQperim
      hCsh hdir hwidth hgap

end ApproximatePaperAssemblySelectedInverseLocal
