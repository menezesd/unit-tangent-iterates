import Mathlib
import UnitTangentIterates.SelInvPathTubeBaseC2

/-!
# The `C²` selected-inverse estimate is *linear* in the cost

`SelInvPathTubeBaseC2.dist_selInv_le_modulus_of_path_tube_base_C2` bounds the
marked distance of the two marked selected inverses of the ends of a normal path
of fronts by `SelInvFrontCostC2.selInvFrontModulus … (cost Γ)`, and
`SelInvFrontCostC2.tendsto_selInvFrontModulus_zero` shows that this bound is a
*modulus of continuity*: it is continuous in the cost and vanishes with it.

A modulus is weaker than what the shadowing scheme of `TubeInvariance.lean` and
`TubePullbackLimit.lean` consumes, which is a *Lipschitz* bound — a constant `K`
by which the selected inverse multiplies the size of a perturbation.  This file
upgrades the modulus to that shape on the range of costs the estimate is stated
for: for `0 ≤ c ≤ 1`,

`selInvFrontModulus P₁ κ̂ ℓ L k_b k_L v₀ κ̄ d c ≤ selInvFrontLip P₁ κ̂ ℓ L k_b k_L v₀ κ̄ d · c` ,

with the constant `selInvFrontLip` explicit and independent of `c`.  Each of the
three defects of the marking is linear in the cost up to an exponential factor
frozen at `c = 1` — `e^{x} − e^{−x} ≤ x(e^{x} + 1)` for the velocity defect and
the monotonicity of the exponential for the other two — the bound
`markingC2Bound` is monotone in the three defects, and the second summand is the
product of a constant which is monotone in the total cost of the family of rears
with that cost, itself proportional to the cost of the path.

The main results are `selInvFrontModulus_le_lip`, the linear bound for the
modulus, and `dist_selInv_le_lip_cost`, the resulting statement that along a
normal path of cost at most one the two marked selected inverses are at marked
distance at most `selInvFrontLip … · cost Γ`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace SelInvModulusLinear

open MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2Increment NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost
  SelInvFrontCostC2 GaugeMarkedDataOfRearFamily RearCostDensity
  RearJacobiSourceCost SelInvPathGaugeC2 SelInvPathRegularityC2 SelInvPathPerimC2
  SelInvPathCurvatureC2 RearTrack

/-! ### Elementary bounds -/

/-- `e^x − e^{−x} ≤ x(e^x + 1)`: the two halves are `e^x − 1 ≤ x e^x` and
`1 − e^{−x} ≤ x`. -/
theorem exp_sub_exp_neg_le (x : ℝ) :
    Real.exp x - Real.exp (-x) ≤ x * (Real.exp x + 1) := by
  have hlow : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x); linarith
  have hprod : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hmul : (1 - x) * Real.exp x ≤ 1 := by
    calc (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_right hlow hpos.le
      _ = 1 := hprod
  nlinarith [hlow, hmul]

/-- The exponential factor of the position defect is nonnegative. -/
theorem kappa1_nonneg {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ kh / (1 - kh ^ 2) := by
  have h : 0 < 1 - kh ^ 2 := by nlinarith
  positivity

theorem gaugeGrowth2_nonneg {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ gaugeGrowth2 kh := by
  have h : 0 < 1 - kh ^ 2 := by nlinarith
  unfold gaugeGrowth2
  positivity

/-! ### Monotonicity of the constants -/

theorem costP1_nonneg {ell khat M : ℝ} (hell : 0 ≤ ell) : 0 ≤ costP1 ell khat M := by
  unfold costP1; positivity

theorem costP1_mono {ell khat M M' : ℝ} (hell : 0 ≤ ell) (hkhat : 0 ≤ khat)
    (h : M ≤ M') : costP1 ell khat M ≤ costP1 ell khat M' := by
  unfold costP1
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hkhat)) hell

theorem costG1_mono {ell khat kappa2 M M' : ℝ} (hell : 0 ≤ ell) (hkhat : 0 ≤ khat)
    (hk2 : 0 ≤ kappa2) (hM : 0 ≤ M) (h : M ≤ M') :
    costG1 ell khat kappa2 M ≤ costG1 ell khat kappa2 M' := by
  have h1 : costP1 ell khat M ≤ costP1 ell khat M' := costP1_mono hell hkhat h
  have h0 : 0 ≤ costP1 ell khat M := costP1_nonneg hell
  have hsq : costP1 ell khat M ^ 2 ≤ costP1 ell khat M' ^ 2 := by nlinarith
  have hlin : kappa2 * M ≤ kappa2 * M' := mul_le_mul_of_nonneg_left h hk2
  unfold costG1
  exact mul_le_mul hsq hlin (by positivity) (by positivity)

/-- `c2ConstVar` is monotone in the size `P₁` of the velocity, in the bound `G₁`
for the first derivative of the marking and in the bound `Cg` for its second
derivative. -/
theorem c2ConstVar_mono {P0 P1 P1' khat G1 G1' Cg Cg' : ℝ} (hP0 : 0 ≤ P0)
    (hkhat : 0 ≤ khat) (hP1 : 0 ≤ P1) (h1 : P1 ≤ P1') (hG : G1 ≤ G1') (hC : Cg ≤ Cg') :
    c2ConstVar P0 P1 khat G1 Cg ≤ c2ConstVar P0 P1' khat G1' Cg' := by
  have hinv : (0 : ℝ) ≤ 1 / P0 := by positivity
  have hinv2 : (0 : ℝ) ≤ 1 / P0 ^ 2 := by positivity
  have hsq : P1 ^ 2 ≤ P1' ^ 2 := by nlinarith
  have hvel : velConst P0 P1 khat ≤ velConst P0 P1' khat := by
    unfold velConst; nlinarith
  have hacc : accConstVar P0 P1 khat G1 Cg ≤ accConstVar P0 P1' khat G1' Cg' := by
    unfold accConstVar
    have h2 : P1 ^ 2 * (1 / P0 ^ 2 + khat ^ 2) ≤ P1' ^ 2 * (1 / P0 ^ 2 + khat ^ 2) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    have h3 : 2 * khat ^ 2 * P1 ^ 2 ≤ 2 * khat ^ 2 * P1' ^ 2 := by nlinarith
    have h4 : (G1 + P1 ^ 2 * khat) * (1 / P0) ≤ (G1' + P1' ^ 2 * khat) * (1 / P0) := by
      have : G1 + P1 ^ 2 * khat ≤ G1' + P1' ^ 2 * khat := by nlinarith
      exact mul_le_mul_of_nonneg_right this hinv
    linarith
  unfold c2ConstVar
  exact max_le_max le_rfl (max_le_max hvel hacc)

/-! ### The linear constant -/

/-- The linear coefficient of the position defect of the marking. -/
def defC0 (P1 kh : ℝ) : ℝ := 2 * P1 * (kh / (1 - kh ^ 2))

/-- The linear coefficient of the velocity defect of the marking, the
exponential factor frozen at cost one. -/
def defC1 (kh ell : ℝ) : ℝ :=
  ell * (kh / (1 - kh ^ 2)) * (Real.exp (kh / (1 - kh ^ 2)) + 1)

/-- The linear coefficient of the acceleration defect of the marking, the
exponential factor frozen at cost one. -/
def defC2 (kh ell : ℝ) : ℝ :=
  ell ^ 2 * Real.exp (2 * (kh / (1 - kh ^ 2))) * gaugeGrowth2 kh

/-- The total cost of the family of selected rears, per unit cost of the path of
fronts. -/
def rearLin (kh ell khat dd : ℝ) : ℝ := rearCostConst kh khat (rearKappa2 kh) ell dd

/-- The constant of the marking defect, per unit cost. -/
def markLin (P1 kh ell L kb kL : ℝ) : ℝ :=
  markingC2Bound (defC0 P1 kh) (defC1 kh ell) (defC2 kh ell) L kb kL

/-- The constant of the `C²` increment along the comparison path, frozen at the
largest total cost the estimate is stated for. -/
def c2Lin (kh ell Pv0 khat dd : ℝ) : ℝ :=
  c2ConstVar Pv0 (costP1 ell khat (rearLin kh ell khat dd)) khat
    (costG1 ell khat (rearKappa2 kh) (rearLin kh ell khat dd))
    (khat * costG1 ell khat (rearKappa2 kh) (rearLin kh ell khat dd)
      + rearKappa2 kh * costP1 ell khat (rearLin kh ell khat dd) ^ 2)

/-- **The Lipschitz constant of the `C²` selected-inverse estimate** on the
range `0 ≤ cost ≤ 1`. -/
def selInvFrontLip (P1 kh ell L kb kL Pv0 khat dd : ℝ) : ℝ :=
  markLin P1 kh ell L kb kL + c2Lin kh ell Pv0 khat dd * rearLin kh ell khat dd

theorem defC0_nonneg {P1 kh : ℝ} (hP1 : 0 ≤ P1) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ defC0 P1 kh :=
  mul_nonneg (by linarith) (kappa1_nonneg hkh0 hkh1)

theorem defC1_nonneg {kh ell : ℝ} (hell : 0 ≤ ell) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ defC1 kh ell := by
  have h := kappa1_nonneg hkh0 hkh1
  unfold defC1
  have : (0 : ℝ) ≤ Real.exp (kh / (1 - kh ^ 2)) + 1 := by positivity
  exact mul_nonneg (mul_nonneg hell h) this

theorem defC2_nonneg {kh ell : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ defC2 kh ell := by
  have h := gaugeGrowth2_nonneg hkh0 hkh1
  unfold defC2
  positivity

theorem rearLin_nonneg {kh ell khat dd : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ rearLin kh ell khat dd :=
  le_trans zero_le_one (rearCostConst_ge_one hkh0 hkh1)

/-! ### The three defects are linear in the cost -/

theorem defect0_eq {P1 kh c : ℝ} :
    2 * P1 * (kh / (1 - kh ^ 2)) * c = defC0 P1 kh * c := rfl

theorem defect1_nonneg {ell kh c : ℝ} (hell : 0 ≤ ell) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hc0 : 0 ≤ c) : 0 ≤ flowDefectC1Int ell (kh / (1 - kh ^ 2) * c) := by
  have hx : 0 ≤ kh / (1 - kh ^ 2) * c := mul_nonneg (kappa1_nonneg hkh0 hkh1) hc0
  unfold flowDefectC1Int
  have : Real.exp (-(kh / (1 - kh ^ 2) * c)) ≤ Real.exp (kh / (1 - kh ^ 2) * c) :=
    Real.exp_le_exp.2 (by linarith)
  exact mul_nonneg hell (by linarith)

theorem defect1_le {ell kh c : ℝ} (hell : 0 ≤ ell) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    flowDefectC1Int ell (kh / (1 - kh ^ 2) * c) ≤ defC1 kh ell * c := by
  set k := kh / (1 - kh ^ 2) with hk
  have hk0 : 0 ≤ k := kappa1_nonneg hkh0 hkh1
  have hx : 0 ≤ k * c := mul_nonneg hk0 hc0
  have hstep := exp_sub_exp_neg_le (k * c)
  have hexp : Real.exp (k * c) ≤ Real.exp k :=
    Real.exp_le_exp.2 (by nlinarith)
  have hmain : Real.exp (k * c) - Real.exp (-(k * c)) ≤ k * (Real.exp k + 1) * c := by
    have h1 : k * c * (Real.exp (k * c) + 1) ≤ k * c * (Real.exp k + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hx
    calc Real.exp (k * c) - Real.exp (-(k * c)) ≤ k * c * (Real.exp (k * c) + 1) := hstep
      _ ≤ k * c * (Real.exp k + 1) := h1
      _ = k * (Real.exp k + 1) * c := by ring
  unfold flowDefectC1Int defC1
  calc ell * (Real.exp (k * c) - Real.exp (-(k * c)))
      ≤ ell * (k * (Real.exp k + 1) * c) := mul_le_mul_of_nonneg_left hmain hell
    _ = ell * k * (Real.exp k + 1) * c := by ring

theorem defect2_le {ell kh c : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    flowDefectC2Int ell (kh / (1 - kh ^ 2) * c) (gaugeGrowth2 kh * c) ≤ defC2 kh ell * c := by
  set k := kh / (1 - kh ^ 2) with hk
  have hk0 : 0 ≤ k := kappa1_nonneg hkh0 hkh1
  have hg0 : 0 ≤ gaugeGrowth2 kh := gaugeGrowth2_nonneg hkh0 hkh1
  have hexp : Real.exp (2 * (k * c)) ≤ Real.exp (2 * k) :=
    Real.exp_le_exp.2 (by nlinarith)
  unfold flowDefectC2Int defC2
  have hnn : (0 : ℝ) ≤ ell ^ 2 * (gaugeGrowth2 kh * c) := by positivity
  calc ell ^ 2 * Real.exp (2 * (k * c)) * (gaugeGrowth2 kh * c)
      = ell ^ 2 * (gaugeGrowth2 kh * c) * Real.exp (2 * (k * c)) := by ring
    _ ≤ ell ^ 2 * (gaugeGrowth2 kh * c) * Real.exp (2 * k) :=
        mul_le_mul_of_nonneg_left hexp hnn
    _ = ell ^ 2 * Real.exp (2 * k) * gaugeGrowth2 kh * c := by ring

/-! ### The linear bound for the modulus -/

/-- **The `C²` selected-inverse estimate is linear in the cost.**  On the range
`0 ≤ c ≤ 1` the modulus `selInvFrontModulus` is bounded by the explicit constant
`selInvFrontLip` times the cost. -/
theorem selInvFrontModulus_le_lip {P1 kh ell L kb kL Pv0 khat dd c : ℝ}
    (hP1 : 0 ≤ P1) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hell : 0 ≤ ell) (hL : 0 ≤ L)
    (hkb : 0 ≤ kb) (hkL : 0 ≤ kL) (hPv0 : 0 ≤ Pv0) (hkhat : 0 ≤ khat)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    selInvFrontModulus P1 kh ell L kb kL Pv0 khat dd c
      ≤ selInvFrontLip P1 kh ell L kb kL Pv0 khat dd * c := by
  have hC0 : 0 ≤ defC0 P1 kh := defC0_nonneg hP1 hkh0 hkh1
  have hC1 : 0 ≤ defC1 kh ell := defC1_nonneg hell hkh0 hkh1
  have hC2 : 0 ≤ defC2 kh ell := defC2_nonneg (ell := ell) hkh0 hkh1
  have hR0 : 0 ≤ rearLin kh ell khat dd := rearLin_nonneg (ell := ell) (khat := khat)
    (dd := dd) hkh0 hkh1
  have hk2 : 0 ≤ rearKappa2 kh := gaugeGrowth2_nonneg hkh0 hkh1
  ------------------------------------------------------------------
  -- the marking defect
  ------------------------------------------------------------------
  have hmark : markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * c)
        (flowDefectC1Int ell (kh / (1 - kh ^ 2) * c))
        (flowDefectC2Int ell (kh / (1 - kh ^ 2) * c) (gaugeGrowth2 kh * c)) L kb kL
      ≤ markLin P1 kh ell L kb kL * c := by
    have hstep := markingC2Bound_mono (e0 := 2 * P1 * (kh / (1 - kh ^ 2)) * c)
      (e1 := flowDefectC1Int ell (kh / (1 - kh ^ 2) * c))
      (e2 := flowDefectC2Int ell (kh / (1 - kh ^ 2) * c) (gaugeGrowth2 kh * c))
      (e0' := defC0 P1 kh * c) (e1' := defC1 kh ell * c) (e2' := defC2 kh ell * c)
      hL hkb hkL (defect1_nonneg hell hkh0 hkh1 hc0) (le_of_eq defect0_eq)
      (defect1_le hell hkh0 hkh1 hc0 hc1) (defect2_le hkh0 hkh1 hc0 hc1)
    refine le_trans hstep ?_
    unfold markingC2Bound markLin
    unfold markingC2Bound
    refine max_le ?_ (max_le ?_ ?_)
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hc0
    · calc defC1 kh ell * c + L * kb * (defC0 P1 kh * c)
          = (defC1 kh ell + L * kb * defC0 P1 kh) * c := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (le_trans (le_max_left _ _) (le_max_right _ _)) hc0
    · have hquad : defC2 kh ell * c
          + kb * (defC1 kh ell * c) * (2 * L + defC1 kh ell * c)
          + L ^ 2 * (kL + kb ^ 2) * (defC0 P1 kh * c)
          ≤ (defC2 kh ell + kb * defC1 kh ell * (2 * L + defC1 kh ell)
              + L ^ 2 * (kL + kb ^ 2) * defC0 P1 kh) * c := by
        nlinarith [mul_nonneg (mul_nonneg hkb hC1) (mul_nonneg hC1 hc0),
          mul_nonneg hkb hC1, sub_nonneg.2 hc1]
      exact le_trans hquad (mul_le_mul_of_nonneg_right
        (le_trans (le_max_right _ _) (le_max_right _ _)) hc0)
  ------------------------------------------------------------------
  -- the increment along the comparison path
  ------------------------------------------------------------------
  set R := rearLin kh ell khat dd with hRdef
  have hM0 : 0 ≤ R * c := mul_nonneg hR0 hc0
  have hMle : R * c ≤ R := by nlinarith
  have hP1le : costP1 ell khat (R * c) ≤ costP1 ell khat R := costP1_mono hell hkhat hMle
  have hG1le : costG1 ell khat (rearKappa2 kh) (R * c)
      ≤ costG1 ell khat (rearKappa2 kh) R := costG1_mono hell hkhat hk2 hM0 hMle
  have hP1nn : 0 ≤ costP1 ell khat (R * c) := costP1_nonneg hell
  have hCgle : khat * costG1 ell khat (rearKappa2 kh) (R * c)
        + rearKappa2 kh * costP1 ell khat (R * c) ^ 2
      ≤ khat * costG1 ell khat (rearKappa2 kh) R
        + rearKappa2 kh * costP1 ell khat R ^ 2 := by
    have h1 : khat * costG1 ell khat (rearKappa2 kh) (R * c)
        ≤ khat * costG1 ell khat (rearKappa2 kh) R := mul_le_mul_of_nonneg_left hG1le hkhat
    have hsq : costP1 ell khat (R * c) ^ 2 ≤ costP1 ell khat R ^ 2 :=
      pow_le_pow_left₀ hP1nn hP1le 2
    have h2 : rearKappa2 kh * costP1 ell khat (R * c) ^ 2
        ≤ rearKappa2 kh * costP1 ell khat R ^ 2 := mul_le_mul_of_nonneg_left hsq hk2
    linarith
  have hconst : c2ConstVar Pv0 (costP1 ell khat (R * c)) khat
        (costG1 ell khat (rearKappa2 kh) (R * c))
        (khat * costG1 ell khat (rearKappa2 kh) (R * c)
          + rearKappa2 kh * costP1 ell khat (R * c) ^ 2)
      ≤ c2Lin kh ell Pv0 khat dd :=
    c2ConstVar_mono hPv0 hkhat hP1nn hP1le hG1le hCgle
  have hsecond : c2ConstVar Pv0 (costP1 ell khat (R * c)) khat
        (costG1 ell khat (rearKappa2 kh) (R * c))
        (khat * costG1 ell khat (rearKappa2 kh) (R * c)
          + rearKappa2 kh * costP1 ell khat (R * c) ^ 2) * (R * c)
      ≤ c2Lin kh ell Pv0 khat dd * R * c := by
    have := mul_le_mul_of_nonneg_right hconst hM0
    calc _ ≤ c2Lin kh ell Pv0 khat dd * (R * c) := this
      _ = c2Lin kh ell Pv0 khat dd * R * c := by ring
  ------------------------------------------------------------------
  -- the sum
  ------------------------------------------------------------------
  unfold selInvFrontModulus SelInvC2Modulus.selInvC2Modulus selInvFrontLip
  rw [add_mul]
  have hRrw : RearCostDensity.rearCostConst kh khat (rearKappa2 kh) ell dd = R := rfl
  rw [hRrw]
  exact add_le_add hmark hsecond

/-- The Lipschitz constant is nonnegative. -/
theorem selInvFrontLip_nonneg {P1 kh ell L kb kL Pv0 khat dd : ℝ}
    (hP1 : 0 ≤ P1) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ selInvFrontLip P1 kh ell L kb kL Pv0 khat dd := by
  have h1 : 0 ≤ markLin P1 kh ell L kb kL :=
    markingC2Bound_nonneg (defC0_nonneg hP1 hkh0 hkh1)
  have h2 : 0 ≤ c2Lin kh ell Pv0 khat dd := c2ConstVar_nonneg _ _ _ _ _
  have h3 : 0 ≤ rearLin kh ell khat dd := rearLin_nonneg (ell := ell) hkh0 hkh1
  have : 0 ≤ c2Lin kh ell Pv0 khat dd * rearLin kh ell khat dd := mul_nonneg h2 h3
  unfold selInvFrontLip
  linarith

/-! ### The path estimate in Lipschitz form -/

/-- **The `C²` comparison of the two marked selected inverses, in Lipschitz
form.**  The hypotheses are those of
`SelInvPathTubeBaseC2.dist_selInv_le_modulus_of_path_tube_base_C2`, together with
the requirement that the cost of the path be at most one; the conclusion is the
same bound with the modulus replaced by the explicit constant
`selInvFrontLip` times the cost.  So along paths of cost at most one the
selected inverse multiplies the size of the perturbation by at most a fixed
factor, which is the shape the shadowing scheme of `TubeInvariance.lean` and
`TubePullbackLimit.lean` consumes. -/
theorem dist_selInv_le_lip_cost {p q : Data} (Γ : NormalPath p q) {kh kminP : ℝ}
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hkh1 : kh < 1)
    (hXC6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X))
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hkminP : 0 < kminP)
    (hKnmin : ∀ t σ, kminP ≤ pathKn Γ.X (pathPerim Γ.X) t σ)
    (hKnk : ∀ t σ, pathKn Γ.X (pathPerim Γ.X) t σ ≤ kh)
    (hshort : ∀ t, kh * pathPerim Γ.X t < 4 * Real.pi)
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane)
    (hmark : ∀ t, Γ.eta t 0 = 0)
    (hcost : cost Γ ≤ 1) :
    ∃ P0 P1 : ℝ, 0 < P0 ∧ (∀ t, P0 ≤ pathPerim Γ.X t) ∧
      (∀ t, pathPerim Γ.X t ≤ P1) ∧
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t)
        ((pathPerim Γ.X) t * (pathKn Γ.X (pathPerim Γ.X) t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / (pathPerim Γ.X) t)) ∧
      ∀ (khat : ℝ),
        rearKappa1 kh ≤ khat →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (RearTrack.rearArclength (δ 0) ((pathPerim Γ.X) 0))
            (jacobiSourceConst kh P0) * cost Γ ≤ 1 →
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
        ≤ selInvFrontLip P1 kh (perim (SelectedInverseMap.selInv kh p))
            (perim (SelectedInverseMap.selInv kh q)) (kh / Real.sqrt (1 - kh ^ 2))
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)
            (pathPv0 kh P0 khat (P1 * (kh / (1 - kh ^ 2)))) khat
            (jacobiSourceConst kh P0) * cost Γ := by
  have hkh0 : 0 ≤ kh := le_trans hkminP.le (le_trans (hKnmin 0 0) (hKnk 0 0))
  obtain ⟨P0, P1, hP0, hP0le, hP1le, dn, δ, hdnper, hstrip, hsol, hδ, hbound⟩ :=
    SelInvPathTubeBaseC2.dist_selInv_le_modulus_of_path_tube_base_C2 Γ hpd hpd2 hqd hqd2
      hkh1 hXC6 hconst hXper hnu hkminP hKnmin hKnk hshort hslit hmark
  refine ⟨P0, P1, hP0, hP0le, hP1le, dn, δ, hdnper, hstrip, hsol, hδ, ?_⟩
  intro khat hkhat hsmall
  have hP1nn : 0 ≤ P1 := le_trans hP0.le (le_trans (hP0le 0) (hP1le 0))
  have hkap1 : 0 ≤ rearKappa1 kh := by
    unfold rearKappa1
    exact kappa1_nonneg hkh0 hkh1
  have hkhat0 : 0 ≤ khat := le_trans hkap1 hkhat
  have hrr : 0 ≤ P1 * (kh / (1 - kh ^ 2)) :=
    mul_nonneg hP1nn (kappa1_nonneg hkh0 hkh1)
  have hPv0 : 0 ≤ pathPv0 kh P0 khat (P1 * (kh / (1 - kh ^ 2))) :=
    (pathPv0_pos hP0 hkh0 hkhat0 hrr).le
  have hellnn : 0 ≤ perim (SelectedInverseMap.selInv kh p) := norm_nonneg _
  have hLnn : 0 ≤ perim (SelectedInverseMap.selInv kh q) := norm_nonneg _
  have hkbnn : 0 ≤ kh / Real.sqrt (1 - kh ^ 2) := by positivity
  have hkLnn : 0 ≤ 2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3 := by positivity
  exact le_trans (hbound khat hkhat hsmall)
    (selInvFrontModulus_le_lip hP1nn hkh0 hkh1 hellnn hLnn hkbnn hkLnn hPv0 hkhat0
      Γ.cost_nonneg hcost)

end SelInvModulusLinear
