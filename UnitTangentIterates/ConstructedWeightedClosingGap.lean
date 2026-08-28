import UnitTangentIterates.ApproximatePaperAssemblyResidual
import UnitTangentIterates.ClosingGapThreshold
import UnitTangentIterates.ConstructedConfiguredSequenceWeighted
import UnitTangentIterates.WidthUniformProduced

/-!
# Synchronizing the constructed weighted tail and the width gap

The path constants are not produced by the epsilon-profile construction, so
they remain parameters.  This file gives an explicit tail majorant and a
starting-separation threshold.  Thus an arbitrary-start configured sequence
can be placed beyond the width threshold and this scalar threshold
simultaneously.
-/

noncomputable section

open Real CurvatureStabilityL1

namespace ConstructedWeightedClosingGap

open PathMetric.WeightedMarkedDefectThreshold
open UnconditionalAssembly.ApproximatePaperAssemblyResidual

/-- A separation-independent upper bound for the zeroth weighted shadowing
tail.  The sharper bound has an additional factor `exp (-beta * Hs 0)`. -/
def coarseTailMajorant
    (C2 K Cm L kstar kd P0 beta deltaStep : ℝ) : ℝ :=
  C2 * (Real.sqrt (4 * kd * Cm) + 4 * Cm / P0) *
      (L ^ 2 * (1 + kstar * L)) /
    (1 - K * Real.exp (-(beta * deltaStep)))

/-- **Explicit weighted-tail estimate.**  The canonical marked defect has no
growing polynomial separation factor.  Its square-root modulus loses half of
the curvature-matching exponent, after which the pullback weights give the
geometric ratio `K * exp (-(beta * deltaStep))`. -/
theorem shadowError_le_exp_geometric
    {C2 K Cm L kstar kd P0 H0 beta deltaStep Pv0 Pv1 khat G1 Cg : ℝ}
    {Hs : ℕ → ℝ}
    (hC2eq : C2 = NormalPathC2IncrementVariableSpeed.c2ConstVar Pv0 Pv1 khat G1 Cg)
    (hC2 : 0 ≤ C2) (hK : 0 ≤ K) (hCm : 0 ≤ Cm) (hL : 0 ≤ L)
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hP0 : 0 < P0)
    (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hPle : ∀ n, P0 ≤ Hs n)
    (hgrow : ∀ n : ℕ, H0 + n * deltaStep ≤ Hs n)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1) :
    shadowError K Pv0 Pv1 khat G1 Cg Cm L kstar kd beta Hs ≤
      C2 * (Real.sqrt (4 * kd * Cm) + 4 * Cm / P0) *
          Real.exp (-(beta * H0)) * (L ^ 2 * (1 + kstar * L)) /
        (1 - K * Real.exp (-(beta * deltaStep))) := by
  let q : ℝ := Real.exp (-(beta * deltaStep))
  let A : ℝ := Real.sqrt (4 * kd * Cm) + 4 * Cm / P0
  let F : ℝ := L ^ 2 * (1 + kstar * L)
  let R : ℝ := K * q
  let d : ℕ → ℝ := canonicalMarkedDefect Cm L kstar kd beta Hs
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hR0 : 0 ≤ R := mul_nonneg hK hq0
  have hR1 : R < 1 := by simpa [R, q] using hthreshold
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg (by positivity) hP0.le)
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hd0 : ∀ n, 0 ≤ d n := by
    intro n
    dsimp [d, canonicalMarkedDefect]
    exact mul_nonneg (mul_nonneg (l1Modulus_nonneg _ _ _) (sq_nonneg L))
      (by positivity)
  have hexp : ∀ n : ℕ, Real.exp (-(beta * Hs (n + 1))) ≤
      Real.exp (-(beta * H0)) * q ^ n := by
    intro n
    have hs : Real.exp (-(beta * Hs (n + 1))) ≤
        Real.exp (-(beta * (H0 + ((n : ℝ) + 1) * deltaStep))) := by
      apply Real.exp_le_exp.mpr
      have h := hgrow (n + 1)
      push_cast at h
      nlinarith
    have heq : Real.exp (-(beta * (H0 + ((n : ℝ) + 1) * deltaStep))) =
        Real.exp (-(beta * H0)) * q ^ (n + 1) := by
      dsimp [q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      congr 1
      ring
    have hq1 : q < 1 := by
      dsimp [q]
      exact Real.exp_lt_one_iff.mpr (by nlinarith)
    have hp : q ^ (n + 1) ≤ q ^ n := by
      rw [pow_succ]
      nlinarith [pow_nonneg hq0 n]
    exact hs.trans (heq.le.trans
      (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le))
  have hdgeo : ∀ n, d n ≤
      A * Real.exp (-(beta * H0)) * F * q ^ n := by
    intro n
    have hmod := ModelOrbitDefectMarked.l1Modulus_le_exp
      (Cm := Cm) (kd := kd) (P0 := P0) (beta := 2 * beta)
      (Pp := Hs n) (H := Hs (n + 1))
      (by positivity) hCm hkd hP0 (hPle n) (le_trans hP0.le (hPle (n + 1)))
    have hmod' : l1Modulus (2 * kd)
        (Cm * Real.exp (-((2 * beta) * Hs (n + 1)))) (Hs n) ≤
        A * Real.exp (-(beta * Hs (n + 1))) := by
      simpa [A] using hmod
    dsimp [d, canonicalMarkedDefect]
    calc
      l1Modulus (2 * kd)
            (Cm * Real.exp (-((2 * beta) * Hs (n + 1)))) (Hs n) * L ^ 2 *
          (1 + kstar * L)
          ≤ (A * Real.exp (-(beta * Hs (n + 1)))) * F := by
            dsimp [F]
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hmod' (by positivity)
      _ ≤ (A * (Real.exp (-(beta * H0)) * q ^ n)) * F := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hexp n) hA0) hF0
      _ = A * Real.exp (-(beta * H0)) * F * q ^ n := by ring
  have hactual : Summable (fun n => C2 * (K ^ n * d n)) := by
    have hs := summable_weighted_canonicalMarkedDefect
      hK hbeta hdelta hCm hL hkstar hkd hP0 hPle hgrow hthreshold
    simpa [d, PathMetric.WeightedRecursiveDefect.weightedDefect] using
      hs.mul_left C2
  have hmajor : Summable (fun n : ℕ =>
      (C2 * (A * Real.exp (-(beta * H0)) * F)) * R ^ n) :=
    (summable_geometric_of_lt_one hR0 hR1).mul_left _
  have hterm : ∀ n, C2 * (K ^ n * d n) ≤
      (C2 * (A * Real.exp (-(beta * H0)) * F)) * R ^ n := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hdgeo n) (pow_nonneg hK n)
    calc
      C2 * (K ^ n * d n) ≤ C2 * (K ^ n *
          (A * Real.exp (-(beta * H0)) * F * q ^ n)) :=
        mul_le_mul_of_nonneg_left h hC2
      _ = (C2 * (A * Real.exp (-(beta * H0)) * F)) * R ^ n := by
        dsimp [R]
        rw [mul_pow]
        ring
  have hsumle := hactual.tsum_le_tsum hterm hmajor
  have hgeom : (∑' n : ℕ,
      (C2 * (A * Real.exp (-(beta * H0)) * F)) * R ^ n) =
      C2 * (A * Real.exp (-(beta * H0)) * F) / (1 - R) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR1]
    rw [div_eq_mul_inv]
  dsimp [shadowError, ShadowingTails.tail]
  simp only [zero_add]
  rw [← hC2eq]
  rw [hgeom] at hsumle
  convert hsumle using 1 <;> simp only [A, F, R, q, d] <;> ring

/-- Removing the exponentially small initial factor gives a threshold that is
independent of the chosen start. -/
theorem shadowError_le_coarseTailMajorant
    {C2 K Cm L kstar kd P0 H0 beta deltaStep Pv0 Pv1 khat G1 Cg : ℝ}
    {Hs : ℕ → ℝ}
    (hC2eq : C2 = NormalPathC2IncrementVariableSpeed.c2ConstVar Pv0 Pv1 khat G1 Cg)
    (hC2 : 0 ≤ C2) (hK : 0 ≤ K) (hCm : 0 ≤ Cm) (hL : 0 ≤ L)
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hP0 : 0 < P0)
    (hH0 : 0 ≤ H0) (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hPle : ∀ n, P0 ≤ Hs n)
    (hgrow : ∀ n : ℕ, H0 + n * deltaStep ≤ Hs n)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1) :
    shadowError K Pv0 Pv1 khat G1 Cg Cm L kstar kd beta Hs ≤
      coarseTailMajorant C2 K Cm L kstar kd P0 beta deltaStep := by
  have hsharp := shadowError_le_exp_geometric hC2eq hC2 hK hCm hL hkstar hkd hP0
    hbeta hdelta hPle hgrow hthreshold
  have hexp : Real.exp (-(beta * H0)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hbeta.le hH0))
  have hden : 0 < 1 - K * Real.exp (-(beta * deltaStep)) := by linarith
  dsimp [coarseTailMajorant]
  refine hsharp.trans ?_
  apply div_le_div_of_nonneg_right _ hden.le
  have hA : 0 ≤ Real.sqrt (4 * kd * Cm) + 4 * Cm / P0 := by
    exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg (by positivity) hP0.le)
  have hF : 0 ≤ L ^ 2 * (1 + kstar * L) := by positivity
  calc
    C2 * (Real.sqrt (4 * kd * Cm) + 4 * Cm / P0) *
          Real.exp (-(beta * H0)) * (L ^ 2 * (1 + kstar * L))
        = (C2 * (Real.sqrt (4 * kd * Cm) + 4 * Cm / P0) *
            (L ^ 2 * (1 + kstar * L))) * Real.exp (-(beta * H0)) := by ring
    _ ≤ (C2 * (Real.sqrt (4 * kd * Cm) + 4 * Cm / P0) *
            (L ^ 2 * (1 + kstar * L))) * 1 := by
      exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (mul_nonneg hC2 hA) hF)
    _ = C2 * (Real.sqrt (4 * kd * Cm) + 4 * Cm / P0) *
          (L ^ 2 * (1 + kstar * L)) := by ring

/-- **Exact final gap from one explicit starting threshold.** -/
theorem gap_of_start_above_coarseTail
    {Cw Csh E R H : ℝ} (hCw : 0 ≤ Cw) (hCsh : 0 ≤ Csh)
    (hE : 0 ≤ E) (hER : E ≤ R)
    (hstart : (Real.pi * Cw + (2 * Real.pi + 1) * (Csh * R)) / 2 < H) :
    Cw + 2 * (Csh * E) < (2 * H - Csh * E) / Real.pi := by
  have hpi := Real.pi_pos
  rw [lt_div_iff₀ hpi]
  have hCE : Csh * E ≤ Csh * R := mul_le_mul_of_nonneg_left hER hCsh
  have hlarge : Real.pi * Cw + (2 * Real.pi + 1) * (Csh * R) < 2 * H := by
    nlinarith [hstart]
  have hleft : (Cw + 2 * (Csh * E)) * Real.pi + Csh * E ≤
      Real.pi * Cw + (2 * Real.pi + 1) * (Csh * R) := by
    nlinarith [hCE, Real.pi_pos]
  nlinarith

/-- Adapter for the retained epsilon-level data.  An arbitrary-start capstone
need only place `D.Hs 0` above the displayed scalar threshold and beyond the
upstream `WidthUniformProduced` threshold; the supplied width bound then
satisfies exactly the `hgap` consumed by the final approximate assembly. -/
theorem ConstructedConfiguredSequenceWeighted.Data.final_gap
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {C2 K P0 Cw Csh Pv0 Pv1 khat G1 Cg : ℝ}
    (hC2eq : C2 = NormalPathC2IncrementVariableSpeed.c2ConstVar Pv0 Pv1 khat G1 Cg)
    (hC2 : 0 ≤ C2) (hK : 0 ≤ K) (hP0 : 0 < P0) (hP0le : P0 ≤ D.Hs 0)
    (hthreshold : K * Real.exp (-(D.beta * D.deltaStep)) < 1)
    (hCw : 0 ≤ Cw) (hCsh : 0 ≤ Csh)
    (hstart : (Real.pi * Cw + (2 * Real.pi + 1) *
        (Csh * coarseTailMajorant C2 K D.matchCoefficient 1 D.kstar D.kd
          P0 D.beta D.deltaStep)) / 2 < D.Hs 0) :
    Cw + 2 * (Csh * shadowError K Pv0 Pv1 khat G1 Cg D.matchCoefficient 1
        D.kstar D.kd D.beta D.Hs) <
      (2 * D.Hs 0 - Csh * shadowError K Pv0 Pv1 khat G1 Cg D.matchCoefficient 1
        D.kstar D.kd D.beta D.Hs) / Real.pi := by
  have hPle : ∀ n, P0 ≤ D.Hs n := fun n => hP0le.trans (D.separation_lower n)
  have hE := shadowError_le_coarseTailMajorant
    (C2 := C2) (Pv0 := Pv0) (Pv1 := Pv1) (khat := khat) (G1 := G1) (Cg := Cg)
    (Cm := D.matchCoefficient) (L := 1) (kstar := D.kstar) (kd := D.kd)
    (P0 := P0) (H0 := D.Hs 0) (beta := D.beta) (deltaStep := D.deltaStep)
    hC2eq hC2 hK
    D.matchCoefficient_nonneg (by norm_num) D.kstar_nonneg D.kd_nonneg hP0
    D.separation_zero_pos.le D.beta_pos D.deltaStep_pos hPle D.separation_linear
    hthreshold
  have hEnn : 0 ≤ shadowError K Pv0 Pv1 khat G1 Cg D.matchCoefficient 1
      D.kstar D.kd D.beta D.Hs := by
    dsimp [shadowError]
    apply ShadowingTails.tail_nonneg
    intro n
    have hc2 : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar Pv0 Pv1 khat G1 Cg := by
      rw [← hC2eq]
      exact hC2
    have hd : 0 ≤ canonicalMarkedDefect D.matchCoefficient 1 D.kstar D.kd
        D.beta D.Hs n := by
      dsimp [canonicalMarkedDefect]
      exact mul_nonneg
        (mul_nonneg (l1Modulus_nonneg _ _ _) (sq_nonneg (1 : ℝ)))
        (by simpa using add_nonneg zero_le_one D.kstar_nonneg)
    exact mul_nonneg hc2 (mul_nonneg (pow_nonneg hK n) hd)
  exact gap_of_start_above_coarseTail hCw hCsh hEnn hE hstart

end ConstructedWeightedClosingGap
