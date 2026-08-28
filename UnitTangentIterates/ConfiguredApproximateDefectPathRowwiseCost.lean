import UnitTangentIterates.ConfiguredApproximateDefectPathRowwise
import UnitTangentIterates.InterpolationPathCostPolynomialScale

noncomputable section

open Real

namespace ConfiguredApproximateDefectPathRowwiseCost

open ConfiguredApproximateDefectPathRowwise InterpolationPathCostPolynomialScale
  InterpolationFrame InterpolationPathDist CurvatureStabilityL1

def modulusConst (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  Real.sqrt (4 * D.kd * edgeCoefficient D) + 4 * edgeCoefficient D / D.Hs 0

def ratioT (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  (Real.sqrt (edgeCoefficient D) * (2 / D.model.beta)) /
    (2 * Real.sqrt D.kd)

def ratioU (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  ratioT D / D.Hs 0

def rateCap (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  6 * D.kstar * ratioT D * modulusConst D

def configuredCostConst (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  let T := ratioT D
  let U := ratioU D
  let A := modulusConst D
  let R := rateCap D
  let E := Real.exp R
  let CE := (3 / 2) * T / (4 * (D.Hs 0) ^ 2)
  let CG1 := U + (3 / 2) * D.kstar * T
  let CG2 := 1 + (D.kd + D.kstar ^ 2) * (3 / 2) * T
  let CR2 := 6 * D.kd * T + 4 * D.kstar * U + 24 * D.kstar ^ 2 * T
  let CF := 2 * E
  let J := 1 / (4 * D.Hs 0)
  aggregationConst CE CG1 CG2 CR2 CF A E (Real.exp (2 * R)) J

theorem ratioT_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ ratioT D := by
  unfold ratioT
  have hb : 0 < D.model.beta := (D.model.configs 0).hbeta0
  positivity

theorem ratioU_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ ratioU D := by
  exact div_nonneg (ratioT_nonneg D) D.separation_zero_pos.le

theorem modulusConst_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ modulusConst D := by
  unfold modulusConst
  exact add_nonneg (Real.sqrt_nonneg _)
    (div_nonneg (mul_nonneg (by norm_num) (edgeCoefficient_nonneg D))
      D.separation_zero_pos.le)

theorem sqrt_edgeEps_le (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    Real.sqrt (edgeEps D n) ≤ Real.sqrt (edgeCoefficient D) *
      Real.exp (-((D.model.beta / 2) * D.Hs n)) := by
  have he := edgeEps_le_exp_at_row D n
  have hCm := edgeCoefficient_nonneg D
  have h1 := Real.sqrt_le_sqrt he
  have hsplit : Real.sqrt (edgeCoefficient D *
      Real.exp (-(D.model.beta * D.Hs n))) =
      Real.sqrt (edgeCoefficient D) *
        Real.exp (-((D.model.beta / 2) * D.Hs n)) := by
    rw [Real.sqrt_mul hCm]
    congr 1
    have hs : (Real.exp (-((D.model.beta / 2) * D.Hs n))) ^ 2 =
        Real.exp (-(D.model.beta * D.Hs n)) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [← hs, Real.sqrt_sq (Real.exp_pos _).le]
  exact h1.trans_eq hsplit

theorem mul_sqrt_edgeEps_le (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    D.Hs n * Real.sqrt (edgeEps D n) ≤
      Real.sqrt (edgeCoefficient D) * (2 / D.model.beta) := by
  have hH := (D.model.separation_pos n).le
  have hs := sqrt_edgeEps_le D n
  have hp := ModelDefectSummable.pow_mul_exp_neg_le
    (gamma := D.model.beta / 2) (x := D.Hs n) (k := 1)
    (by norm_num) (by have := (D.model.configs n).hbeta0; linarith) hH
  have hmul := mul_le_mul_of_nonneg_left hs hH
  calc
    D.Hs n * Real.sqrt (edgeEps D n) ≤
        Real.sqrt (edgeCoefficient D) *
          (D.Hs n * Real.exp (-((D.model.beta / 2) * D.Hs n))) := by
      nlinarith
    _ ≤ Real.sqrt (edgeCoefficient D) * (2 / D.model.beta) := by
      have hp' : D.Hs n * Real.exp (-((D.model.beta / 2) * D.Hs n)) ≤
          2 / D.model.beta := by simpa using hp
      exact mul_le_mul_of_nonneg_left hp' (Real.sqrt_nonneg _)

set_option maxHeartbeats 2000000 in
theorem mul_edgeEps_le_ratioT_mul_dsup
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    D.Hs n * edgeEps D n ≤ ratioT D * rowDsup D n := by
  have hkd : 0 < D.kd := by
    simpa [D.model_kd] using (D.model.configs n).hkd
  have hr : 0 < Real.sqrt D.kd := Real.sqrt_pos.2 hkd
  have he : 0 ≤ edgeEps D n := edgeEps_nonneg D n
  have hs : 0 ≤ Real.sqrt (edgeEps D n) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (edgeEps D n) ^ 2 = edgeEps D n := Real.sq_sqrt he
  have hmod : 2 * Real.sqrt D.kd * Real.sqrt (edgeEps D n) ≤ rowDsup D n := by
    have hleft : Real.sqrt (4 * D.kd * edgeEps D n) ≤ rowDsup D n := by
      unfold rowDsup l1Modulus
      simpa only [show 2 * (2 * D.kd) = 4 * D.kd by ring] using
        (le_max_left (Real.sqrt (4 * D.kd * edgeEps D n))
          (4 * edgeEps D n / D.Hs n))
    have hid : Real.sqrt (4 * D.kd * edgeEps D n) =
        2 * Real.sqrt D.kd * Real.sqrt (edgeEps D n) := by
      rw [show 4 * D.kd * edgeEps D n = (4 * D.kd) * edgeEps D n by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rwa [hid] at hleft
  have hLs := mul_sqrt_edgeEps_le D n
  have hds : 0 ≤ rowDsup D n := l1Modulus_nonneg _ _ _
  have hprod := mul_le_mul hmod hLs
    (mul_nonneg (D.model.separation_pos n).le hs) hds
  unfold ratioT
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt D.kd)).2
  calc
    D.Hs n * edgeEps D n * (2 * Real.sqrt D.kd) =
        (2 * Real.sqrt D.kd * Real.sqrt (edgeEps D n)) *
          (D.Hs n * Real.sqrt (edgeEps D n)) := by
      conv_lhs => rw [← hs2]
      ring
    _ ≤ rowDsup D n * (Real.sqrt (edgeCoefficient D) * (2 / D.model.beta)) := hprod
    _ = Real.sqrt (edgeCoefficient D) * (2 / D.model.beta) * rowDsup D n := by ring

set_option maxHeartbeats 3000000 in
theorem rowDefect_le_configuredCostConst
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rowDefect D n ≤ configuredCostConst D * rowModelDefect D n := by
  let L := D.Hs n
  let eps := edgeEps D n
  let ds := rowDsup D n
  let T := ratioT D
  let U := ratioU D
  let A := modulusConst D
  let R := rateCap D
  let E := Real.exp R
  let CE := (3 / 2) * T / (4 * (D.Hs 0) ^ 2)
  let CG1 := U + (3 / 2) * D.kstar * T
  let CG2 := 1 + (D.kd + D.kstar ^ 2) * (3 / 2) * T
  let CR2 := 6 * D.kd * T + 4 * D.kstar * U + 24 * D.kstar ^ 2 * T
  let CF := 2 * E
  let J := 1 / (4 * D.Hs 0)
  have hL : 0 < L := D.model.separation_pos n
  have hP : D.Hs 0 ≤ L := D.separation_lower n
  have he : 0 ≤ eps := edgeEps_nonneg D n
  have hds : 0 ≤ ds := l1Modulus_nonneg _ _ _
  have hT : 0 ≤ T := by simpa [T] using ratioT_nonneg D
  have hU : 0 ≤ U := by
    dsimp [U, ratioU]
    exact div_nonneg (ratioT_nonneg D) D.separation_zero_pos.le
  have hA : 0 ≤ A := by simpa [A] using modulusConst_nonneg D
  have hLeps : L * eps ≤ T * ds := by
    simpa [L, eps, ds, T] using mul_edgeEps_le_ratioT_mul_dsup D n
  have hepsU : eps ≤ U * ds := by
    dsimp [U, ratioU]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ D.separation_zero_pos).2
    have hPe : D.Hs 0 * eps ≤ L * eps :=
      mul_le_mul_of_nonneg_right hP he
    simpa [mul_comm] using hPe.trans hLeps
  have hdsA : ds ≤ A := by
    have hm := ModelDefectSummable.l1Modulus_le_of_exp
      (M := 2 * D.kd) (eps := eps) (Cm := edgeCoefficient D)
      (P0 := D.Hs 0) (Pp := L) (beta := D.model.beta) (H := L)
      (D.model.configs n).hbeta0.le (mul_nonneg (by norm_num) D.kd_nonneg)
      (edgeCoefficient_nonneg D)
      he (by simpa [eps, L] using edgeEps_le_exp_at_row D n)
      D.separation_zero_pos hP hL.le
    have hexp : Real.exp (-((D.model.beta / 2) * L)) ≤ 1 := by
      apply (Real.exp_le_one_iff).2
      have hb : 0 < D.model.beta := (D.model.configs n).hbeta0
      nlinarith
    have hc :
        Real.sqrt (2 * (2 * D.kd) * edgeCoefficient D) +
            4 * edgeCoefficient D / D.Hs 0 = modulusConst D := by
      unfold modulusConst
      congr 2
      ring_nf
    rw [hc] at hm
    exact hm.trans (by
      simpa using mul_le_mul_of_nonneg_left hexp (modulusConst_nonneg D))
  have hR : rate1Bound D.kstar L eps ≤ R := by
    have hk6 : 0 ≤ 6 * D.kstar := mul_nonneg (by norm_num) D.kstar_nonneg
    have h1 := mul_le_mul_of_nonneg_left hLeps hk6
    have h2 := mul_le_mul_of_nonneg_left hdsA
      (mul_nonneg hk6 hT)
    dsimp [R, rateCap]
    unfold rate1Bound
    nlinarith
  have hG1 : costG1 D.kstar L eps ≤ CG1 * ds := by
    have hk := mul_le_mul_of_nonneg_left hLeps
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) D.kstar_nonneg)
    dsimp [CG1]
    unfold costG1
    nlinarith
  have hG2 : costG2 D.kstar D.kd ds L eps ≤ CG2 * ds := by
    have hk := mul_le_mul_of_nonneg_left hLeps
      (mul_nonneg (add_nonneg D.kd_nonneg (sq_nonneg D.kstar))
        (by norm_num : (0 : ℝ) ≤ 3 / 2))
    dsimp [CG2]
    unfold costG2 costE
    nlinarith
  have hR2 : rate2Bound D.kstar D.kd L eps ≤ CR2 * ds := by
    have hkd' := mul_le_mul_of_nonneg_left hLeps
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) D.kd_nonneg)
    have hk := mul_le_mul_of_nonneg_left hepsU
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) D.kstar_nonneg)
    have hk2 := mul_le_mul_of_nonneg_left hLeps
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (sq_nonneg D.kstar))
    dsimp [CR2]
    unfold rate2Bound
    nlinarith
  have hfac : costFac D.kstar L eps ≤ CF * L := by
    dsimp [CF, E]
    unfold costFac
    calc
      2 * L * Real.exp (rate1Bound D.kstar L eps) ≤
          2 * L * Real.exp R :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hR) (by positivity)
      _ = 2 * Real.exp R * L := by ring
  have hexp : Real.exp (rate1Bound D.kstar L eps) ≤ E := by
    dsimp [E]
    exact Real.exp_le_exp.mpr hR
  have hexp2 : Real.exp (2 * rate1Bound D.kstar L eps) ≤ Real.exp (2 * R) :=
    Real.exp_le_exp.mpr (by linarith)
  let S := polyScale D.kstar ds L
  have hshape : 1 ≤ 1 + D.kstar * (2 * L) := by
    have hkL : 0 ≤ D.kstar * (2 * L) :=
      mul_nonneg D.kstar_nonneg (mul_nonneg (by norm_num) hL.le)
    linarith
  have hdsL2 : ds * L ^ 2 ≤ S / 4 := by
    dsimp [S, polyScale]
    have hb : 0 ≤ ds * (2 * L) ^ 2 := mul_nonneg hds (sq_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hshape hb
    nlinarith
  have hdsL : ds * L ≤ J * S := by
    dsimp [J]
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ (mul_pos (by norm_num) D.separation_zero_pos)).2
    have hcomp : D.Hs 0 * (ds * L) ≤ ds * L ^ 2 := by
      calc
        D.Hs 0 * (ds * L) = (ds * L) * D.Hs 0 := by ring
        _ ≤ (ds * L) * L := mul_le_mul_of_nonneg_left hP (mul_nonneg hds hL.le)
        _ = ds * L ^ 2 := by ring
    nlinarith [hdsL2]
  have hds0 : ds ≤ (1 / (4 * (D.Hs 0) ^ 2)) * S := by
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos D.separation_zero_pos))).2
    have hsquare : (D.Hs 0) ^ 2 ≤ L ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hP)
        (add_nonneg hL.le D.separation_zero_pos.le)]
    have hcomp : ds * (D.Hs 0) ^ 2 ≤ ds * L ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hds
    nlinarith [hdsL2]
  have hcostE : costE L eps ≤ CE * S := by
    dsimp [CE]
    unfold costE
    calc
      (3 / 2) * L * eps ≤ (3 / 2) * T * ds := by nlinarith
      _ ≤ ((3 / 2) * T) * ((1 / (4 * (D.Hs 0) ^ 2)) * S) :=
        mul_le_mul_of_nonneg_left hds0 (by positivity)
      _ = ((3 / 2) * T / (4 * (D.Hs 0) ^ 2)) * S := by ring
  have hCE : 0 ≤ CE := by
    dsimp [CE]
    exact div_nonneg (mul_nonneg (by norm_num) hT) (by positivity)
  have hCG1 : 0 ≤ CG1 := by
    dsimp [CG1]
    exact add_nonneg hU (mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg) hT)
  have hCG2 : 0 ≤ CG2 := by
    dsimp [CG2]
    have hp : 0 ≤ (D.kd + D.kstar ^ 2) * (3 / 2) * T :=
      mul_nonneg
        (mul_nonneg (add_nonneg D.kd_nonneg (sq_nonneg D.kstar))
          (by norm_num : (0 : ℝ) ≤ 3 / 2)) hT
    exact add_nonneg (by norm_num) hp
  have hCR2 : 0 ≤ CR2 := by
    dsimp [CR2]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) D.kd_nonneg) hT)
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) D.kstar_nonneg) hU))
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (sq_nonneg D.kstar)) hT)
  have hCF : 0 ≤ CF := by dsimp [CF, E]; positivity
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) D.separation_zero_pos.le)
  have hagg := interpPathCost_le_polyScale
    D.kstar_nonneg D.kd_nonneg hL.le hds he
    hCE hCG1 hCG2 hCR2 hCF hA (Real.exp_pos _).le (Real.exp_pos _).le
    hJ hcostE hG1 hG2 hR2 hfac hexp hexp2 hdsA hdsL hdsL2
  simpa [rowDefect, rowDsup, rowModelDefect, configuredCostConst,
    L, eps, ds, T, U, A, R, E, CE, CG1, CG2, CR2, CF, J, S] using hagg

theorem configuredCostConst_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ configuredCostConst D := by
  unfold configuredCostConst
  apply aggregationConst_nonneg
  · exact div_nonneg (mul_nonneg (by norm_num) (ratioT_nonneg D)) (by positivity)
  · exact add_nonneg
      (div_nonneg (ratioT_nonneg D) D.separation_zero_pos.le)
      (mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg) (ratioT_nonneg D))
  · exact add_nonneg (by norm_num)
      (mul_nonneg
        (mul_nonneg (add_nonneg D.kd_nonneg (sq_nonneg D.kstar))
          (by norm_num : (0 : ℝ) ≤ 3 / 2))
        (ratioT_nonneg D))
  · exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) D.kd_nonneg) (ratioT_nonneg D))
        (mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg)
          (div_nonneg (ratioT_nonneg D) D.separation_zero_pos.le)))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg D.kstar)) (ratioT_nonneg D))
  · positivity
  · exact modulusConst_nonneg D
  · positivity
  · positivity
  · exact div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) D.separation_zero_pos.le)

/-! Exported uniform bounds used by the concrete row-ceiling envelopes. -/

theorem rowDsup_le_modulusConst
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rowDsup D n ≤ modulusConst D := by
  have hm := ModelDefectSummable.l1Modulus_le_of_exp
    (M := 2 * D.kd) (eps := edgeEps D n) (Cm := edgeCoefficient D)
    (P0 := D.Hs 0) (Pp := D.Hs n) (beta := D.model.beta) (H := D.Hs n)
    (D.model.configs n).hbeta0.le (mul_nonneg (by norm_num) D.kd_nonneg)
    (edgeCoefficient_nonneg D) (edgeEps_nonneg D n)
    (edgeEps_le_exp_at_row D n) D.separation_zero_pos
    (D.separation_lower n) (D.model.separation_pos n).le
  have hexp : Real.exp (-((D.model.beta / 2) * D.Hs n)) ≤ 1 := by
    apply (Real.exp_le_one_iff).2
    exact neg_nonpos.mpr (mul_nonneg
      (div_nonneg (D.model.configs n).hbeta0.le (by norm_num))
      (D.model.separation_pos n).le)
  have hc :
      Real.sqrt (2 * (2 * D.kd) * edgeCoefficient D) +
          4 * edgeCoefficient D / D.Hs 0 = modulusConst D := by
    unfold modulusConst
    congr 2
    ring_nf
  rw [hc] at hm
  exact hm.trans (by
    simpa [rowDsup] using mul_le_mul_of_nonneg_left hexp
      (modulusConst_nonneg D))

theorem rate1Bound_le_rateCap
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rate1Bound D.kstar (D.Hs n) (edgeEps D n) ≤ rateCap D := by
  have hLeps := mul_edgeEps_le_ratioT_mul_dsup D n
  have hdsA := rowDsup_le_modulusConst D n
  have h1 := mul_le_mul_of_nonneg_left hLeps
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) D.kstar_nonneg)
  have h2 := mul_le_mul_of_nonneg_left hdsA
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
      D.kstar_nonneg) (ratioT_nonneg D))
  unfold rate1Bound rateCap
  nlinarith

theorem rowP1_le_linear
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rowP1 D n ≤ (2 * Real.exp (rateCap D)) * D.Hs n := by
  unfold rowP1 costFac
  have h : (2 * D.Hs n) *
      Real.exp (rate1Bound D.kstar (D.Hs n) (edgeEps D n)) ≤
      (2 * D.Hs n) * Real.exp (rateCap D) := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (rate1Bound_le_rateCap D n))
    (mul_nonneg (by norm_num) (D.model.separation_pos n).le)
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

def rate2Cap (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  (6 * D.kd * ratioT D + 4 * D.kstar * ratioU D +
    24 * D.kstar ^ 2 * ratioT D) * modulusConst D

theorem rate2Bound_le_rate2Cap
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rate2Bound D.kstar D.kd (D.Hs n) (edgeEps D n) ≤ rate2Cap D := by
  have hLeps := mul_edgeEps_le_ratioT_mul_dsup D n
  have hPe : D.Hs 0 * edgeEps D n ≤ D.Hs n * edgeEps D n :=
    mul_le_mul_of_nonneg_right (D.separation_lower n) (edgeEps_nonneg D n)
  have heps : edgeEps D n ≤ ratioU D * rowDsup D n := by
    unfold ratioU
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ D.separation_zero_pos).2
    simpa [mul_comm] using hPe.trans hLeps
  have hkd := mul_le_mul_of_nonneg_left hLeps
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) D.kd_nonneg)
  have hk := mul_le_mul_of_nonneg_left heps
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) D.kstar_nonneg)
  have hk2 := mul_le_mul_of_nonneg_left hLeps
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (sq_nonneg D.kstar))
  have hraw : rate2Bound D.kstar D.kd (D.Hs n) (edgeEps D n) ≤
      (6 * D.kd * ratioT D + 4 * D.kstar * ratioU D +
        24 * D.kstar ^ 2 * ratioT D) * rowDsup D n := by
    unfold rate2Bound
    nlinarith
  exact hraw.trans (mul_le_mul_of_nonneg_left (rowDsup_le_modulusConst D n)
    (add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) D.kd_nonneg) (ratioT_nonneg D))
        (mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg) (ratioU_nonneg D)))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg D.kstar))
        (ratioT_nonneg D))))

theorem summable_weighted_rowDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) {K : ℝ}
    (hK : 0 ≤ K)
    (hthreshold : K * Real.exp (-((D.model.beta / 4) * D.deltaStep)) < 1) :
    Summable (PathMetric.WeightedRecursiveDefect.weightedDefect K (rowDefect D)) :=
  summable_weighted_rowDefect_of_modelScale D hK (configuredCostConst_nonneg D)
    (rowDefect_le_configuredCostConst D) hthreshold

end ConfiguredApproximateDefectPathRowwiseCost
