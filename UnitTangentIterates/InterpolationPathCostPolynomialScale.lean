import UnitTangentIterates.InterpolationPathDist

noncomputable section

open Real

namespace InterpolationPathCostPolynomialScale

open InterpolationFrame InterpolationPathDist

def polyScale (kstar dsup L : ℝ) : ℝ :=
  dsup * (2 * L) ^ 2 * (1 + kstar * (2 * L))

def aggregationConst (CE CG1 CG2 CR2 CF A E E2 J : ℝ) : ℝ :=
  CE + CE * E + CG1 * CF * J + CG2 * CF ^ 2 / 4 +
    CG1 * CR2 * A * E2

theorem aggregationConst_nonneg {CE CG1 CG2 CR2 CF A E E2 J : ℝ}
    (hCE : 0 ≤ CE) (hCG1 : 0 ≤ CG1) (hCG2 : 0 ≤ CG2)
    (hCR2 : 0 ≤ CR2) (hCF : 0 ≤ CF) (hA : 0 ≤ A)
    (hE : 0 ≤ E) (hE2 : 0 ≤ E2) (hJ : 0 ≤ J) :
    0 ≤ aggregationConst CE CG1 CG2 CR2 CF A E E2 J := by
  unfold aggregationConst
  positivity

set_option maxHeartbeats 1000000 in
theorem interpPathCost_le_polyScale
    {kstar kd dsup L eps CE CG1 CG2 CR2 CF A E E2 J : ℝ}
    (hk : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 ≤ L)
    (hds : 0 ≤ dsup) (heps : 0 ≤ eps)
    (hCE : 0 ≤ CE) (hCG1 : 0 ≤ CG1) (hCG2 : 0 ≤ CG2)
    (hCR2 : 0 ≤ CR2) (hCF : 0 ≤ CF) (hA : 0 ≤ A)
    (hE : 0 ≤ E) (hE2 : 0 ≤ E2) (hJ : 0 ≤ J)
    (hcostE : costE L eps ≤ CE * polyScale kstar dsup L)
    (hG1 : costG1 kstar L eps ≤ CG1 * dsup)
    (hG2 : costG2 kstar kd dsup L eps ≤ CG2 * dsup)
    (hR2 : rate2Bound kstar kd L eps ≤ CR2 * dsup)
    (hfac : costFac kstar L eps ≤ CF * L)
    (hexp : Real.exp (rate1Bound kstar L eps) ≤ E)
    (hexp2 : Real.exp (2 * rate1Bound kstar L eps) ≤ E2)
    (hdsA : dsup ≤ A)
    (hdsL : dsup * L ≤ J * polyScale kstar dsup L)
    (hdsL2 : dsup * L ^ 2 ≤ polyScale kstar dsup L / 4) :
    interpPathCost kstar kd dsup L eps ≤
      aggregationConst CE CG1 CG2 CR2 CF A E E2 J * polyScale kstar dsup L := by
  let S := polyScale kstar dsup L
  have hS : 0 ≤ S := by
    dsimp [S, polyScale]
    positivity
  have hcfac : 0 ≤ costFac kstar L eps := costFac_nonneg hL
  have hcg1 : 0 ≤ costG1 kstar L eps := costG1_nonneg hk hL heps
  have hcg2 : 0 ≤ costG2 kstar kd dsup L eps :=
    costG2_nonneg hkd hds hL heps
  have hr2 : 0 ≤ rate2Bound kstar kd L eps :=
    rate2Bound_nonneg hk hkd hL heps
  have hW : costTermW kstar L eps ≤ (CE * E) * S := by
    unfold costTermW
    exact (mul_le_mul hexp hcostE (costE_nonneg hL heps) hE).trans_eq
      (by dsimp [S]; ring)
  have hS1 : costTermS1 kstar L eps ≤ (CG1 * CF * J) * S := by
    unfold costTermS1
    calc
      costG1 kstar L eps * costFac kstar L eps ≤
          (CG1 * dsup) * (CF * L) :=
        mul_le_mul hG1 hfac hcfac (mul_nonneg hCG1 hds)
      _ = (CG1 * CF) * (dsup * L) := by ring
      _ ≤ (CG1 * CF) * (J * S) :=
        mul_le_mul_of_nonneg_left hdsL (mul_nonneg hCG1 hCF)
      _ = (CG1 * CF * J) * S := by ring
  have hfacSq : costFac kstar L eps ^ 2 ≤ CF ^ 2 * L ^ 2 := by
    calc
      costFac kstar L eps ^ 2 ≤ (CF * L) ^ 2 :=
        (sq_le_sq₀ hcfac (mul_nonneg hCF hL)).2 hfac
      _ = CF ^ 2 * L ^ 2 := by rw [mul_pow]
  have hS2a : costG2 kstar kd dsup L eps * costFac kstar L eps ^ 2 ≤
      (CG2 * CF ^ 2 / 4) * S := by
    calc
      _ ≤ (CG2 * dsup) * (CF ^ 2 * L ^ 2) :=
        mul_le_mul hG2 hfacSq (sq_nonneg _) (mul_nonneg hCG2 hds)
      _ = (CG2 * CF ^ 2) * (dsup * L ^ 2) := by ring
      _ ≤ (CG2 * CF ^ 2) * (S / 4) :=
        mul_le_mul_of_nonneg_left hdsL2 (mul_nonneg hCG2 (sq_nonneg CF))
      _ = (CG2 * CF ^ 2 / 4) * S := by ring
  have hdsSqL2 : dsup ^ 2 * L ^ 2 ≤ A * (S / 4) := by
    have hsq : dsup ^ 2 ≤ A * dsup := by nlinarith
    calc
      dsup ^ 2 * L ^ 2 ≤ (A * dsup) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg L)
      _ = A * (dsup * L ^ 2) := by ring
      _ ≤ A * (S / 4) := mul_le_mul_of_nonneg_left hdsL2 hA
  have hS2b : costG1 kstar L eps *
      (rate2Bound kstar kd L eps * (2 * L) ^ 2 *
        Real.exp (2 * rate1Bound kstar L eps)) ≤
      (CG1 * CR2 * A * E2) * S := by
    have hprod : costG1 kstar L eps * rate2Bound kstar kd L eps ≤
        (CG1 * dsup) * (CR2 * dsup) :=
      mul_le_mul hG1 hR2 hr2 (mul_nonneg hCG1 hds)
    calc
      _ = (costG1 kstar L eps * rate2Bound kstar kd L eps) *
          ((2 * L) ^ 2 * Real.exp (2 * rate1Bound kstar L eps)) := by ring
      _ ≤ ((CG1 * dsup) * (CR2 * dsup)) *
          ((2 * L) ^ 2 * E2) := by
        exact mul_le_mul hprod
          (mul_le_mul_of_nonneg_left hexp2 (sq_nonneg (2 * L)))
          (by positivity) (by positivity)
      _ = (4 * CG1 * CR2 * E2) * (dsup ^ 2 * L ^ 2) := by ring
      _ ≤ (4 * CG1 * CR2 * E2) * (A * (S / 4)) :=
        mul_le_mul_of_nonneg_left hdsSqL2 (by positivity)
      _ = (CG1 * CR2 * A * E2) * S := by ring
  unfold interpPathCost costTermS2 aggregationConst
  dsimp [S] at hcostE hW hS1 hS2a hS2b ⊢
  linarith

end InterpolationPathCostPolynomialScale
