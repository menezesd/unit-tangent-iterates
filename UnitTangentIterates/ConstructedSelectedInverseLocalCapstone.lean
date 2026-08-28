import UnitTangentIterates.ApproximatePaperAssemblySelectedInverseLocal
import UnitTangentIterates.ConfiguredFinitePullbackPhysicalRearKinematics
import UnitTangentIterates.ConfiguredApproximateDefectPath
import UnitTangentIterates.SelectedInverseApproximateMapPath
import UnitTangentIterates.ConstructedConfiguredInductiveTubeBudget
import UnitTangentIterates.ConstructedWeightedClosingGap

/-!
# Constructed selected-inverse local capstone

This module orders the dependent choices in the recursive construction:

1. weighted summability chooses the strict stage cap `Mtotal`;
2. `Mtotal` fixes the uniform selected-rear gauge ceilings;
3. those ceilings fix `c2ConstVar`;
4. a finite prefix is discarded so the automatic tube budget and final width
   gap hold simultaneously;
5. the configured defect and selected-rear map adapters feed the local
   approximate pullback capstone.

No scalar recursive constant or tube parameter is supplied by the caller.
-/

noncomputable section

set_option maxHeartbeats 8000000

open Set Function Complex MarkedSpace PathMetric
open PathMetric.NormalPath PathMetric.WeightedMarkedDefectThreshold
open PathMetric.WeightedRecursiveDefect
open NormalPathC2IncrementVariableSpeed

namespace ConstructedSelectedInverseLocalCapstone

open ConstructedConfiguredInductiveTubeBudget
open ConstructedConfiguredInductiveTubeBudget.WeightedData
open ConstructedWeightedClosingGap

/-- The genuinely external analytic boundary of the constructed local
selected-inverse assembly.  Every field is tied to the same shifted weighted
configured sequence. -/
structure Residual
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (kh Qmax P0 Cw : ℝ) (direction : ℕ → ℂ) : Prop where
  kstar_le_selected : D.kstar ≤ kh
  P0_le_initial : P0 ≤ D.Hs 0
  width_nonneg : 0 ≤ Cw
  direction_unit : ∀ N : ℕ, ‖direction N‖ = 1
  width : ∀ N : ℕ,
    Width.width
      (range (TwoCapPairsAssembly.front ((shift D N).kappas 0)
        (shift D N).model.thetaBase ((shift D N).Hs 0))) (direction N) ≤ Cw
  defect : ∀ (Mtotal : ℝ) (N : ℕ) (Q : ℕ → Data),
    ConfiguredApproximateDefectPath.Residual
      (shift D N) (SelectedInverseMap.selInv kh) Q P0
      (SelectedInverseApproximateMapPath.mapRearP1 kh Qmax
        (shift D N).kstar Mtotal)
      (SelectedInverseApproximateMapPath.mapRearG1 kh Qmax
        (shift D N).kstar Mtotal)
      (SelectedInverseApproximateMapPath.mapRearCg kh Qmax
        (shift D N).kstar Mtotal)
      1
  map : ∀ (Mtotal : ℝ) (N : ℕ) (Q : ℕ → Data),
    SelectedInverseApproximateMapPath.Residual P0 kh (shift D N).kstar Qmax
      Mtotal ((shift D N).Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase (shift D N).model / 2)

/-- The complete local selected-inverse conclusion from one retained weighted
datum and only the residual analytic package above. -/
theorem conclude
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {kh Qmax P0 Cw : ℝ} {direction : ℕ → ℂ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hP0 : 0 < P0)
    (R : Residual D kh Qmax P0 Cw direction)
    (hthreshold : SelectedInverseApproximateMapPath.mapK kh *
      Real.exp (-(D.beta * D.deltaStep)) < 1) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) =
        range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  let K : ℝ := SelectedInverseApproximateMapPath.mapK kh
  have hK : 1 ≤ K := SelectedInverseApproximateMapPath.one_le_mapK hkh0 hkh1
  obtain ⟨Mtotal, hMtotal, hcap⟩ :=
    D.exists_uniformCanonicalMarkedDefect_cap hK (by simpa [K] using hthreshold)
  let P1 : ℝ := SelectedInverseApproximateMapPath.mapRearP1 kh Qmax
    D.kstar Mtotal
  let G1 : ℝ := SelectedInverseApproximateMapPath.mapRearG1 kh Qmax
    D.kstar Mtotal
  let Cg : ℝ := SelectedInverseApproximateMapPath.mapRearCg kh Qmax
    D.kstar Mtotal
  let C2 : ℝ := c2ConstVar P0 P1 D.kstar G1 Cg
  have hC2 : 0 ≤ C2 := c2ConstVar_nonneg _ _ _ _ _
  let Rtail : ℝ := coarseTailMajorant C2 K D.matchCoefficient 1 D.kstar
    D.kd P0 D.beta D.deltaStep
  let Hrequired : ℝ :=
    (Real.pi * Cw + (2 * Real.pi + 1) * Rtail) / 2 + 1
  obtain ⟨N, Q, hrequired, hQ, htube⟩ :=
    exists_shifted_inductiveTubeBudget D Hrequired hkh0 hkh1 hC2
      (zero_le_one.trans hK) (by simpa [K] using hthreshold)
  let D' := shift D N
  let d : ℕ → ℝ := canonicalMarkedDefect D'.matchCoefficient 1 D'.kstar
    D'.kd D'.beta D'.Hs
  have hP0D' : P0 ≤ D'.Hs 0 := by
    exact R.P0_le_initial.trans (D.separation_lower N)
  have hgap : Cw + 2 *
      UnconditionalAssembly.ApproximatePaperAssemblyResidual.shadowError K P0 P1 D'.kstar G1 Cg
        D'.matchCoefficient 1 D'.kstar D'.kd D'.beta D'.Hs <
      (2 * D'.Hs 0 -
        UnconditionalAssembly.ApproximatePaperAssemblyResidual.shadowError K P0 P1 D'.kstar G1 Cg
          D'.matchCoefficient 1 D'.kstar D'.kd D'.beta D'.Hs) / Real.pi := by
    have hs :
        (Real.pi * Cw + (2 * Real.pi + 1) * Rtail) / 2 < D'.Hs 0 := by
      have hreq : Hrequired ≤ D'.Hs 0 := by simpa [D'] using hrequired
      dsimp [Hrequired] at hreq
      linarith
    have hg := D'.final_gap (C2 := C2) (K := K) (P0 := P0) (Cw := Cw)
      (Csh := 1) (Pv0 := P0) (Pv1 := P1) (khat := D'.kstar)
      (G1 := G1) (Cg := Cg) rfl (by simpa [C2]) (zero_le_one.trans hK)
      hP0 hP0D' (by simpa [D', K] using hthreshold) R.width_nonneg
      (by norm_num) (by simpa [Rtail, C2, K, D'] using hs)
    simpa using hg
  have hmap := SelectedInverseApproximateMapPath.hmap_local
    (R.map Mtotal N Q) hkh0 hkh1 D'.kstar_nonneg
  have hdefect := ConfiguredApproximateDefectPath.hdefect
    D' (R.defect Mtotal N Q)
  have hcap' : ∀ n k, K ^ k * d (n + k) < Mtotal := by
    intro n k
    have h := hcap (N + n) k
    simpa [d, D', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hd0 : ∀ n, 0 ≤ d n := by
    intro n
    dsimp [d, canonicalMarkedDefect]
    exact mul_nonneg
      (mul_nonneg
        (CurvatureStabilityL1.l1Modulus_nonneg _ _ _) (sq_nonneg (1 : ℝ)))
      (add_nonneg zero_le_one (mul_nonneg D'.kstar_nonneg zero_le_one))
  have hweighted : Summable (weightedDefect K d) := by
    simpa [d] using D'.summable_weightedCanonicalMarkedDefect
      (zero_le_one.trans hK) (by simpa [D', K] using hthreshold)
  have hrows : ∀ n, Summable (fun k => K ^ k * d (n + k)) := by
    have h := summable_pullbackError_of_summable_weighted hK hd0 hweighted
    intro n
    simpa [pullbackError] using h n
  obtain ⟨hmem, _hincr⟩ :=
    PaperFaithfulLocalApproximatePullback.diagonal_membership_and_increment_of_inductive_budget
      hK hd0 hrows (by simpa [P1, G1, Cg, D'] using hmap)
      (by simpa [P1, G1, Cg, d, D'] using hdefect) hC2
      (by simpa [d] using hcap') (by simpa [C2, K, d, D'] using htube)
  have hchordPos : 0 < ConfiguredInductiveTubeBudget.chordBase D'.model := by
    rw [chordBase_eq_min D'.model (configured_kstar_pos D'.model)]
    exact lt_min D'.separation_zero_pos
      (div_pos Real.pi_pos
        (mul_pos (by norm_num) (configured_kstar_pos D'.model)))
  have hQfront : ∀ n, ev (Q n) =
      TwoCapPairsAssembly.front (D'.kappas n) D'.model.thetaBase (D'.Hs n) :=
    fun n => (hQ n).2
  have hQperim : perim (Q 0) = 2 * D'.Hs 0 := (hQ 0).1
  have hwidth : Width.width
      (range (TwoCapPairsAssembly.front (D'.kappas 0)
        D'.model.thetaBase (D'.Hs 0))) (direction N) ≤ Cw := by
    simpa [D'] using R.width N
  have hfinitePhysical : PathMetric.FinitePullbackPhysicalRearKinematics kh
      (fun n k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k) :=
    ConfiguredFinitePullbackPhysicalRearKinematics.finitePullbackKinematics_of_configuredModel_and_localTransport
      (kh := kh) (Q := Q) (d := d) (K := K) (P0 := P0) (P1 := P1)
      (G1 := G1) (Cg := Cg) (c := D'.Hs 0)
      (dlt := ConfiguredInductiveTubeBudget.chordBase D'.model / 2)
      (Mtotal := Mtotal) D'.model hQ hK D'.separation_zero_pos hkh0 hkh1
      (by simpa [D'] using R.kstar_le_selected)
      (by simpa [P1, G1, Cg, D'] using hmap)
      (by simpa [P1, G1, Cg, d, D'] using hdefect)
      hmem (by simpa [d] using hcap')
  exact ApproximatePaperAssemblySelectedInverseLocal.conclude_of_local_approx_weighted_markedDefect_selInv_finite
      (kappas := D'.kappas) (Hs := D'.Hs)
      (theta0 := fun _ => D'.model.thetaBase) (eps := fun _ => (1 : ℝ))
      (Q := Q) (K := K) (P0 := P0) (P1 := P1) (kh := kh)
      (G1 := G1) (Cg := Cg) (Cm := D'.matchCoefficient) (L := 1)
      (kstar := D'.kstar) (kd := D'.kd) (H0 := D'.Hs 0)
      (deltaStep := D'.deltaStep) (beta := D'.beta) (c := D'.Hs 0)
      (d0 := ConfiguredInductiveTubeBudget.chordBase D'.model)
      (dlt := ConfiguredInductiveTubeBudget.chordBase D'.model / 2)
      (Mtotal := Mtotal) (Cw := Cw) (Csh := 1)
      (A0 := ConfiguredInductiveTubeBudget.accBound D'.model)
      (rho := ConfiguredInductiveTubeBudget.rowRho D'.model C2 K d)
      (dir := direction N)
      D'.model hK D'.beta_pos D'.deltaStep_pos D'.matchCoefficient_nonneg
      (by norm_num) D'.kstar_nonneg D'.kd_nonneg hP0
      (fun n => hP0D'.trans (D'.separation_lower n)) D'.separation_linear
      (by simpa [D', K] using hthreshold)
      (by simpa [P1, G1, Cg, D'] using hmap)
      (by simpa [P1, G1, Cg, D'] using hdefect)
      (by simpa [C2, P1, G1, Cg, D'] using hC2)
      (by simpa [d] using hcap')
      (by simpa [C2, K, d, D'] using htube)
      hkh0 hkh1 hfinitePhysical
      D'.separation_zero_pos (half_pos hchordPos)
      (by simpa using hQfront) hQperim (by norm_num) (R.direction_unit N)
      hwidth (by simpa [K, P1, G1, Cg, D'] using hgap)

/-- Epsilon-level form: the paper's profile constructs the retained weighted
datum.  For every admissible selected-rear parameter, the residual package on
that datum implies the final noncircular unit-tangent orbit. -/
theorem exists_data_conclude_of_eps {eps : ℝ}
    (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ D : ConstructedConfiguredSequenceWeighted.Data,
      ∀ {kh Qmax P0 Cw : ℝ} {direction : ℕ → ℂ},
        0 ≤ kh → kh < 1 → 0 < P0 →
        Residual D kh Qmax P0 Cw direction →
        SelectedInverseApproximateMapPath.mapK kh *
          Real.exp (-(D.beta * D.deltaStep)) < 1 →
        ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
          (∀ n, MainTheoremConditional.IsOval (X n)) ∧
          (∀ n, range (X (n + 1)) =
            range (UnitTangent.unitTangentMap (X n))) ∧
          0 < LX ∧ Periodic (X 0) LX ∧
          ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  obtain ⟨D⟩ := ConstructedConfiguredSequenceWeighted.exists_data_of_eps heps heps10
  exact ⟨D, fun hkh0 hkh1 hP0 R hthreshold =>
    conclude D hkh0 hkh1 hP0 R hthreshold⟩

end ConstructedSelectedInverseLocalCapstone
