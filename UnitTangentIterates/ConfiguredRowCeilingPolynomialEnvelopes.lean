import UnitTangentIterates.ConfiguredApproximateDefectPathRowwiseCost
import UnitTangentIterates.ConfiguredRichMapStageProvider
import UnitTangentIterates.ConstructedRowCPolynomialGrowth

/-!
# Concrete polynomial envelopes for the configured row ceilings

The interpolation rates are uniformly bounded after the common pulse is
fixed.  Consequently its speed ceiling grows linearly in the separation and
its first/mixed derivative ceilings grow quadratically.  This file records
those estimates, including the widened ceilings used after a controlled
marking.
-/

noncomputable section

open Real

namespace ConfiguredRowCeilingPolynomialEnvelopes

open ConfiguredApproximateDefectPathRowwise
  ConfiguredApproximateDefectPathRowwiseCost
  ConfiguredRichMapStageProvider
  ConstructedRowCPolynomialGrowth
  InterpolationControlledJunctionFinal
  InterpolationFrame
  InterpolationPathDist
  InterpolationVariableSpeedConstants

def facCoeff (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  2 * Real.exp (rateCap D)

def g1Coeff (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  4 * rate2Cap D * Real.exp (2 * rateCap D)

def rate2LinearCap (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  4 * D.kd + 16 * D.kstar ^ 2 + 8 * D.kstar / (3 * D.Hs 0)

def cgCoeff (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  (4 * D.kstar * g1Coeff D + rate2LinearCap D * facCoeff D ^ 2) +
    (D.kstar * g1Coeff D + D.kd * facCoeff D ^ 2 +
      D.kstar * facCoeff D)

def frameCap (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  1 + 1 / (2 * D.Hs 0) + 2 * D.kstar +
    1 / (2 * D.Hs 0) ^ 2 + D.kstar ^ 2 + 2 * D.kd

def pmin (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  1 / frameCap D

theorem rateCap_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ rateCap D := by
  unfold rateCap
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg) (ratioT_nonneg D))
    (modulusConst_nonneg D)

theorem rate2Cap_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ rate2Cap D := by
  unfold rate2Cap
  exact mul_nonneg
    (add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) D.kd_nonneg) (ratioT_nonneg D))
        (mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg) (ratioU_nonneg D)))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg D.kstar))
        (ratioT_nonneg D)))
    (modulusConst_nonneg D)

theorem facCoeff_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ facCoeff D := by
  unfold facCoeff
  positivity

theorem g1Coeff_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ g1Coeff D := by
  unfold g1Coeff
  exact mul_nonneg
    (mul_nonneg (by norm_num) (rate2Cap_nonneg D)) (Real.exp_pos _).le

theorem rate2LinearCap_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ rate2LinearCap D := by
  unfold rate2LinearCap
  exact add_nonneg
    (add_nonneg (mul_nonneg (by norm_num) D.kd_nonneg)
      (mul_nonneg (by norm_num) (sq_nonneg D.kstar)))
    (div_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg)
      (mul_nonneg (by norm_num) D.separation_zero_pos.le))

theorem cgCoeff_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ cgCoeff D := by
  unfold cgCoeff
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg) (g1Coeff_nonneg D))
      (mul_nonneg (rate2LinearCap_nonneg D) (sq_nonneg _)))
    (add_nonneg
      (add_nonneg (mul_nonneg D.kstar_nonneg (g1Coeff_nonneg D))
        (mul_nonneg D.kd_nonneg (sq_nonneg _)))
      (mul_nonneg D.kstar_nonneg (facCoeff_nonneg D)))

theorem rowP1_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ rowP1 D n := by
  unfold rowP1
  exact costFac_nonneg (D.model.separation_pos n).le

theorem rowG1_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ rowG1 D n := by
  unfold rowG1 interpolationG1
  exact mul_nonneg
    (mul_nonneg
      (rate2Bound_nonneg D.kstar_nonneg D.kd_nonneg
        (D.model.separation_pos n).le (edgeEps_nonneg D n))
      (sq_nonneg _))
    (Real.exp_pos _).le

theorem rowCg_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ rowCg D n := by
  unfold rowCg
  exact interpolationCgFinal_nonneg D.kstar_nonneg D.kd_nonneg
    (D.model.separation_pos n).le (edgeEps_nonneg D n)

theorem rowG1_le_quadratic
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rowG1 D n ≤ g1Coeff D * (1 + D.Hs n) ^ 2 := by
  have hr := rate2Bound_le_rate2Cap D n
  have he : Real.exp (2 * rate1Bound D.kstar (D.Hs n) (edgeEps D n)) ≤
      Real.exp (2 * rateCap D) := by
    apply Real.exp_le_exp.mpr
    nlinarith [rate1Bound_le_rateCap D n]
  have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
  have hz : 0 ≤ 1 + D.Hs n := by linarith
  have hsquare : (D.Hs n) ^ 2 ≤ (1 + D.Hs n) ^ 2 :=
    (sq_le_sq₀ hH hz).2 (by linarith)
  unfold rowG1 interpolationG1 g1Coeff
  calc
    rate2Bound D.kstar D.kd (D.Hs n) (edgeEps D n) * (2 * D.Hs n) ^ 2 *
          Real.exp (2 * rate1Bound D.kstar (D.Hs n) (edgeEps D n))
        ≤ rate2Cap D * (2 * D.Hs n) ^ 2 *
          Real.exp (2 * rate1Bound D.kstar (D.Hs n) (edgeEps D n)) := by
            gcongr
    _ ≤ rate2Cap D * (2 * D.Hs n) ^ 2 * Real.exp (2 * rateCap D) := by
          exact mul_le_mul_of_nonneg_left he
            (mul_nonneg (rate2Cap_nonneg D) (sq_nonneg _))
    _ = (4 * rate2Cap D * Real.exp (2 * rateCap D)) * (D.Hs n) ^ 2 := by ring
    _ ≤ (4 * rate2Cap D * Real.exp (2 * rateCap D)) *
          (1 + D.Hs n) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by
        exact mul_nonneg (mul_nonneg (by norm_num) (rate2Cap_nonneg D))
          (Real.exp_pos _).le)

theorem rate2LinearCoeff_le_cap
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rate2LinearCoeff D.kstar D.kd (D.Hs n) ≤ rate2LinearCap D := by
  have hi : 1 / D.Hs n ≤ 1 / D.Hs 0 :=
    one_div_le_one_div_of_le D.separation_zero_pos (D.separation_lower n)
  have hk8 : 0 ≤ 8 * D.kstar := mul_nonneg (by norm_num) D.kstar_nonneg
  have h := mul_le_mul_of_nonneg_left hi hk8
  unfold rate2LinearCoeff rate2LinearCap
  have hfrac : 8 * D.kstar / (3 * D.Hs n) ≤
      8 * D.kstar / (3 * D.Hs 0) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 3))
  linarith

theorem rowP1_le_envelope
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rowP1 D n ≤ facCoeff D * (1 + D.Hs n) := by
  have h := rowP1_le_linear D n
  have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
  calc
    rowP1 D n ≤ facCoeff D * D.Hs n := by simpa [facCoeff] using h
    _ ≤ facCoeff D * (1 + D.Hs n) :=
      mul_le_mul_of_nonneg_left (by linarith) (facCoeff_nonneg D)

theorem rowCg_le_quadratic
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rowCg D n ≤ cgCoeff D * (1 + D.Hs n) ^ 2 := by
  let z : ℝ := 1 + D.Hs n
  have hz1 : 1 ≤ z := by dsimp [z]; linarith [(D.model.separation_pos n).le]
  have hz0 : 0 ≤ z := zero_le_one.trans hz1
  have hP := rowP1_le_envelope D n
  have hG := rowG1_le_quadratic D n
  have hP0 := rowP1_nonneg D n
  have hG0 := rowG1_nonneg D n
  have hf0 := facCoeff_nonneg D
  have hg0 := g1Coeff_nonneg D
  have hP' : rowP1 D n ≤ facCoeff D * z := by simpa [z] using hP
  have hG' : rowG1 D n ≤ g1Coeff D * z ^ 2 := by simpa [z] using hG
  have hP2 : rowP1 D n ^ 2 ≤ facCoeff D ^ 2 * z ^ 2 := by
    calc
      rowP1 D n ^ 2 ≤ (facCoeff D * z) ^ 2 :=
        (sq_le_sq₀ hP0 (mul_nonneg hf0 hz0)).2 hP'
      _ = facCoeff D ^ 2 * z ^ 2 := by rw [mul_pow]
  have hlc := rate2LinearCoeff_le_cap D n
  have hlc0 := rate2LinearCoeff_nonneg D.kstar_nonneg D.kd_nonneg
    (D.model.separation_pos n)
  have hleft :
      4 * D.kstar * rowG1 D n +
          rate2LinearCoeff D.kstar D.kd (D.Hs n) * rowP1 D n ^ 2 ≤
        (4 * D.kstar * g1Coeff D + rate2LinearCap D * facCoeff D ^ 2) * z ^ 2 := by
    have ha : 4 * D.kstar * rowG1 D n ≤
        4 * D.kstar * (g1Coeff D * z ^ 2) := mul_le_mul_of_nonneg_left hG'
      (mul_nonneg (by norm_num) D.kstar_nonneg)
    have hb : rate2LinearCoeff D.kstar D.kd (D.Hs n) * rowP1 D n ^ 2 ≤
        rate2LinearCap D * (facCoeff D ^ 2 * z ^ 2) :=
      mul_le_mul hlc hP2 (sq_nonneg _) (rate2LinearCap_nonneg D)
    calc
      _ ≤ 4 * D.kstar * (g1Coeff D * z ^ 2) +
          rate2LinearCap D * (facCoeff D ^ 2 * z ^ 2) := add_le_add ha hb
      _ = _ := by ring
  have hlin : rowP1 D n ≤ facCoeff D * z ^ 2 := by
    exact hP'.trans (mul_le_mul_of_nonneg_left
      (show z ≤ z ^ 2 by nlinarith [sq_nonneg (z - 1)]) hf0)
  have hright :
      D.kstar * rowG1 D n + D.kd * rowP1 D n ^ 2 +
          D.kstar * rowP1 D n ≤
        (D.kstar * g1Coeff D + D.kd * facCoeff D ^ 2 +
          D.kstar * facCoeff D) * z ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left hG' D.kstar_nonneg
    have hb := mul_le_mul_of_nonneg_left hP2 D.kd_nonneg
    have hc := mul_le_mul_of_nonneg_left hlin D.kstar_nonneg
    calc
      _ ≤ D.kstar * (g1Coeff D * z ^ 2) +
          D.kd * (facCoeff D ^ 2 * z ^ 2) +
          D.kstar * (facCoeff D * z ^ 2) := add_le_add (add_le_add ha hb) hc
      _ = _ := by ring
  unfold rowCg interpolationCgFinal interpolationCg
  apply max_le
  · exact hleft.trans (by
      unfold cgCoeff
      have hr0 : 0 ≤ D.kstar * g1Coeff D + D.kd * facCoeff D ^ 2 +
          D.kstar * facCoeff D := by
        exact add_nonneg
          (add_nonneg (mul_nonneg D.kstar_nonneg (g1Coeff_nonneg D))
            (mul_nonneg D.kd_nonneg (sq_nonneg _)))
          (mul_nonneg D.kstar_nonneg (facCoeff_nonneg D))
      nlinarith [sq_nonneg z])
  · exact hright.trans (by
      unfold cgCoeff
      have hl0 : 0 ≤ 4 * D.kstar * g1Coeff D +
          rate2LinearCap D * facCoeff D ^ 2 := by
        exact add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg) (g1Coeff_nonneg D))
          (mul_nonneg (rate2LinearCap_nonneg D) (sq_nonneg _))
      nlinarith [sq_nonneg z])

theorem frameCap_pos (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 < frameCap D := by
  unfold frameCap
  have h1 : 0 ≤ 1 / (2 * D.Hs 0) :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num) D.separation_zero_pos.le)
  have h2 : 0 ≤ 1 / (2 * D.Hs 0) ^ 2 :=
    div_nonneg zero_le_one (sq_nonneg _)
  nlinarith [D.kstar_nonneg, D.kd_nonneg, sq_nonneg D.kstar]

theorem pmin_pos (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 < pmin D := one_div_pos.mpr (frameCap_pos D)

theorem rowP0_lower (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    pmin D ≤ rowP0 D n := by
  have hH0 : 0 < 2 * D.Hs 0 := mul_pos (by norm_num) D.separation_zero_pos
  have hHn : 0 < 2 * D.Hs n := mul_pos (by norm_num) (D.model.separation_pos n)
  have hr1 : 0 ≤ rate1Bound D.kstar (D.Hs n) (edgeEps D n) := by
    exact rate1Bound_nonneg D.kstar_nonneg (D.model.separation_pos n).le
      (edgeEps_nonneg D n)
  have he : 1 ≤ Real.exp (rate1Bound D.kstar (D.Hs n) (edgeEps D n)) :=
    (Real.one_le_exp_iff).2 hr1
  have hfac : 2 * D.Hs 0 ≤ costFac D.kstar (D.Hs n) (edgeEps D n) := by
    calc
      2 * D.Hs 0 ≤ 2 * D.Hs n := by nlinarith [D.separation_lower n]
      _ ≤ costFac D.kstar (D.Hs n) (edgeEps D n) := by
        unfold costFac
        nlinarith [mul_le_mul_of_nonneg_left he hHn.le]
  have hfacpos := costFac_pos (kstar := D.kstar) (eps := edgeEps D n)
    (D.model.separation_pos n)
  have hinv : 1 / costFac D.kstar (D.Hs n) (edgeEps D n) ≤
      1 / (2 * D.Hs 0) := one_div_le_one_div_of_le hH0 hfac
  have hsq : (2 * D.Hs 0) ^ 2 ≤
      costFac D.kstar (D.Hs n) (edgeEps D n) ^ 2 :=
    (sq_le_sq₀ hH0.le hfacpos.le).2 hfac
  have hinv2 : 1 / costFac D.kstar (D.Hs n) (edgeEps D n) ^ 2 ≤
      1 / (2 * D.Hs 0) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hH0) hsq
  have hframe : frameD D.kstar D.kd (D.Hs n) (edgeEps D n) ≤ frameCap D := by
    unfold frameD frameCap
    linarith
  unfold pmin rowP0 interpolationP0
  exact one_div_le_one_div_of_le
    (frameD_pos D.kstar_nonneg D.kd_nonneg (D.model.separation_pos n)) hframe

def rowP1Envelope (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (rowP1 D) where
  coeff := facCoeff D
  degree := 1
  coeff_nonneg := facCoeff_nonneg D
  value_nonneg := rowP1_nonneg D
  bound n := by simpa using rowP1_le_envelope D n

def rowKstarEnvelope (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (fun _ ↦ D.kstar) where
  coeff := D.kstar
  degree := 0
  coeff_nonneg := D.kstar_nonneg
  value_nonneg _ := D.kstar_nonneg
  bound n := by simp

def rowG1Envelope (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (rowG1 D) where
  coeff := g1Coeff D
  degree := 2
  coeff_nonneg := g1Coeff_nonneg D
  value_nonneg := rowG1_nonneg D
  bound := rowG1_le_quadratic D

def rowCgEnvelope (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (rowCg D) where
  coeff := cgCoeff D
  degree := 2
  coeff_nonneg := cgCoeff_nonneg D
  value_nonneg := rowCg_nonneg D
  bound := rowCg_le_quadratic D

def wideP1 (D : ConstructedConfiguredSequenceWeighted.Data) (MA : ℝ) : ℕ → ℝ :=
  mapP1 D (rowP1 D) MA

def wideG1 (D : ConstructedConfiguredSequenceWeighted.Data) (MA NA : ℝ) : ℕ → ℝ :=
  mapG1 D (rowP1 D) (rowG1 D) MA NA

def wideCg (D : ConstructedConfiguredSequenceWeighted.Data) (MA NA : ℝ) : ℕ → ℝ :=
  mapCg D (rowP1 D) (rowCg D) MA NA

/-- The mapped curvature-numerator ceiling with an independent path-curvature
ceiling.  The configured `D.kstar` remains the canonical interpolation
ceiling; recursive selected-rear paths may require a larger `khat`. -/
def wideCgWithKhat (D : ConstructedConfiguredSequenceWeighted.Data)
    (khat MA NA : ℝ) : ℕ → ℝ :=
  fun n ↦ max (rowCg D n)
    (rowCg D n * MA ^ 2 + khat * rowP1 D n * NA)

def wideP1Envelope (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA : ℝ} (hMA : 0 ≤ MA) : PolynomialEnvelope D.Hs (wideP1 D MA) where
  coeff := facCoeff D * (1 + MA)
  degree := 1
  coeff_nonneg := mul_nonneg (facCoeff_nonneg D) (by linarith)
  value_nonneg n := by
    unfold wideP1 mapP1
    exact (rowP1_nonneg D n).trans (le_max_left _ _)
  bound n := by
    unfold wideP1 mapP1
    simp only [pow_one]
    have hz0 : 0 ≤ 1 + D.Hs n := by linarith [(D.model.separation_pos n).le]
    apply max_le
    · exact (rowP1_le_envelope D n).trans
        (mul_le_mul_of_nonneg_right
          (by nlinarith [facCoeff_nonneg D]) hz0)
    · have h := mul_le_mul_of_nonneg_right (rowP1_le_envelope D n) hMA
      calc
        rowP1 D n * MA ≤ (facCoeff D * (1 + D.Hs n)) * MA := h
        _ ≤ (facCoeff D * (1 + D.Hs n)) * (1 + MA) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (facCoeff_nonneg D) hz0)
        _ = facCoeff D * (1 + MA) * (1 + D.Hs n) := by ring

def wideG1Envelope (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA : ℝ} (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    PolynomialEnvelope D.Hs (wideG1 D MA NA) where
  coeff := g1Coeff D * (1 + MA ^ 2) + facCoeff D * NA
  degree := 2
  coeff_nonneg := add_nonneg
    (mul_nonneg (g1Coeff_nonneg D) (add_nonneg zero_le_one (sq_nonneg _)))
    (mul_nonneg (facCoeff_nonneg D) hNA)
  value_nonneg n := by
    unfold wideG1 mapG1
    exact (rowG1_nonneg D n).trans (le_max_left _ _)
  bound n := by
    let z : ℝ := 1 + D.Hs n
    have hz1 : 1 ≤ z := by dsimp [z]; linarith [(D.model.separation_pos n).le]
    have hG : rowG1 D n ≤ g1Coeff D * z ^ 2 := by
      simpa [z] using rowG1_le_quadratic D n
    have hP : rowP1 D n ≤ facCoeff D * z := by
      simpa [z] using rowP1_le_envelope D n
    have hP2 : rowP1 D n ≤ facCoeff D * z ^ 2 :=
      hP.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (z - 1)])
        (facCoeff_nonneg D))
    unfold wideG1 mapG1
    apply max_le
    · exact hG.trans (mul_le_mul_of_nonneg_right
        (by nlinarith [g1Coeff_nonneg D, mul_nonneg (facCoeff_nonneg D) hNA])
        (sq_nonneg z))
    · calc
        rowG1 D n * MA ^ 2 + rowP1 D n * NA ≤
            (g1Coeff D * z ^ 2) * MA ^ 2 +
              (facCoeff D * z ^ 2) * NA := by gcongr
        _ = (g1Coeff D * MA ^ 2 + facCoeff D * NA) * z ^ 2 := by ring
        _ ≤ (g1Coeff D * (1 + MA ^ 2) + facCoeff D * NA) * z ^ 2 :=
          mul_le_mul_of_nonneg_right
            (by nlinarith [g1Coeff_nonneg D]) (sq_nonneg z)

def wideCgEnvelope (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA : ℝ} (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    PolynomialEnvelope D.Hs (wideCg D MA NA) where
  coeff := cgCoeff D * (1 + MA ^ 2) + D.kstar * facCoeff D * NA
  degree := 2
  coeff_nonneg := add_nonneg
    (mul_nonneg (cgCoeff_nonneg D) (add_nonneg zero_le_one (sq_nonneg _)))
    (mul_nonneg (mul_nonneg D.kstar_nonneg (facCoeff_nonneg D)) hNA)
  value_nonneg n := by
    unfold wideCg mapCg
    exact (rowCg_nonneg D n).trans (le_max_left _ _)
  bound n := by
    let z : ℝ := 1 + D.Hs n
    have hz1 : 1 ≤ z := by dsimp [z]; linarith [(D.model.separation_pos n).le]
    have hC : rowCg D n ≤ cgCoeff D * z ^ 2 := by
      simpa [z] using rowCg_le_quadratic D n
    have hP : rowP1 D n ≤ facCoeff D * z := by
      simpa [z] using rowP1_le_envelope D n
    have hP2 : rowP1 D n ≤ facCoeff D * z ^ 2 :=
      hP.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (z - 1)])
        (facCoeff_nonneg D))
    unfold wideCg mapCg
    apply max_le
    · nlinarith [mul_nonneg (cgCoeff_nonneg D) (sq_nonneg z),
        mul_nonneg (mul_nonneg D.kstar_nonneg (facCoeff_nonneg D)) hNA]
    · have ha := mul_le_mul_of_nonneg_right hC (sq_nonneg MA)
      have hb0 := mul_le_mul_of_nonneg_left hP2 D.kstar_nonneg
      have hb := mul_le_mul_of_nonneg_right hb0 hNA
      calc
        rowCg D n * MA ^ 2 + D.kstar * rowP1 D n * NA ≤
            (cgCoeff D * z ^ 2) * MA ^ 2 +
              D.kstar * (facCoeff D * z ^ 2) * NA := add_le_add ha hb
        _ = (cgCoeff D * MA ^ 2 + D.kstar * facCoeff D * NA) * z ^ 2 := by ring
        _ ≤ (cgCoeff D * (1 + MA ^ 2) + D.kstar * facCoeff D * NA) * z ^ 2 :=
          mul_le_mul_of_nonneg_right
            (by nlinarith [cgCoeff_nonneg D]) (sq_nonneg z)

def constantKhatEnvelope (D : ConstructedConfiguredSequenceWeighted.Data)
    {khat : ℝ} (hkhat : 0 ≤ khat) :
    PolynomialEnvelope D.Hs (fun _ ↦ khat) where
  coeff := khat
  degree := 0
  coeff_nonneg := hkhat
  value_nonneg _ := hkhat
  bound n := by simp

def wideCgWithKhatEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {khat MA NA : ℝ} (hkhat : 0 ≤ khat)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    PolynomialEnvelope D.Hs (wideCgWithKhat D khat MA NA) where
  coeff := cgCoeff D * (1 + MA ^ 2) + khat * facCoeff D * NA
  degree := 2
  coeff_nonneg := add_nonneg
    (mul_nonneg (cgCoeff_nonneg D) (add_nonneg zero_le_one (sq_nonneg _)))
    (mul_nonneg (mul_nonneg hkhat (facCoeff_nonneg D)) hNA)
  value_nonneg n := by
    unfold wideCgWithKhat
    exact (rowCg_nonneg D n).trans (le_max_left _ _)
  bound n := by
    let z : ℝ := 1 + D.Hs n
    have hz1 : 1 ≤ z := by dsimp [z]; linarith [(D.model.separation_pos n).le]
    have hC : rowCg D n ≤ cgCoeff D * z ^ 2 := by
      simpa [z] using rowCg_le_quadratic D n
    have hP : rowP1 D n ≤ facCoeff D * z := by
      simpa [z] using rowP1_le_envelope D n
    have hP2 : rowP1 D n ≤ facCoeff D * z ^ 2 :=
      hP.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (z - 1)])
        (facCoeff_nonneg D))
    unfold wideCgWithKhat
    apply max_le
    · nlinarith [mul_nonneg (cgCoeff_nonneg D) (sq_nonneg z),
        mul_nonneg (mul_nonneg hkhat (facCoeff_nonneg D)) hNA]
    · have ha := mul_le_mul_of_nonneg_right hC (sq_nonneg MA)
      have hb0 := mul_le_mul_of_nonneg_left hP2 hkhat
      have hb := mul_le_mul_of_nonneg_right hb0 hNA
      calc
        rowCg D n * MA ^ 2 + khat * rowP1 D n * NA ≤
            (cgCoeff D * z ^ 2) * MA ^ 2 +
              khat * (facCoeff D * z ^ 2) * NA := add_le_add ha hb
        _ = (cgCoeff D * MA ^ 2 + khat * facCoeff D * NA) * z ^ 2 := by ring
        _ ≤ (cgCoeff D * (1 + MA ^ 2) + khat * facCoeff D * NA) * z ^ 2 :=
          mul_le_mul_of_nonneg_right
            (by nlinarith [cgCoeff_nonneg D]) (sq_nonneg z)

theorem exists_wide_c2ConstVar_growth_majorant
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA gamma : ℝ} (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (rowP0 D n) (wideP1 D MA n) D.kstar
        (wideG1 D MA NA n) (wideCg D MA NA n) ≤
        C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  exact exists_c2ConstVar_growth_majorant (pmin := pmin D)
    (fun n ↦ (D.model.separation_pos n).le)
    (pmin_pos D) (rowP0_lower D)
    (wideP1Envelope D hMA) (rowKstarEnvelope D)
    (wideG1Envelope D hMA hNA) (wideCgEnvelope D hMA hNA) hgamma

/-- Growth majorant for the recursive path class with an independent
curvature ceiling. -/
theorem exists_wide_c2ConstVar_growth_majorant_withKhat
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {khat MA NA gamma : ℝ} (hkhat : 0 ≤ khat)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (rowP0 D n) (wideP1 D MA n) khat
        (wideG1 D MA NA n) (wideCgWithKhat D khat MA NA n) ≤
        C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  exact exists_c2ConstVar_growth_majorant (pmin := pmin D)
    (fun n ↦ (D.model.separation_pos n).le)
    (pmin_pos D) (rowP0_lower D)
    (wideP1Envelope D hMA) (constantKhatEnvelope D hkhat)
    (wideG1Envelope D hMA hNA)
    (wideCgWithKhatEnvelope D hkhat hMA hNA) hgamma

end ConfiguredRowCeilingPolynomialEnvelopes
