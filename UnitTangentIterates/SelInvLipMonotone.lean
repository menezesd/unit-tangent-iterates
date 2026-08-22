import Mathlib
import UnitTangentIterates.PinchedPathGlobal

/-!
# Monotonicity of the universal Lipschitz constant, and a uniform bound

`PinchedPathGlobal.dist_selInv_le_pinchedDist_uniformLip` asks for a bound `L`,
valid over all admissible curves, for the universal constant
`selInvLipUniversal κ̂ … ℓ L` of the `C²` estimate, whose two arguments are the
perimeters of the two images.  This file reduces that hypothesis to a bound on
those perimeters alone.

Each ingredient of the constant — the flow constants `costP1`, `costG1`, the
total rear cost `rearCostConst`, the marking defects `defC1`, `defC2`, the
marking bound `markingC2Bound` and the `C²` increment constant `c2ConstVar` —
is monotone in the length parameters, so `selInvFrontLip`, and with it
`selInvLipUniversal`, is monotone in the two perimeters
(`selInvLipUniversal_mono`).  Consequently a single bound `E` for the perimeter
of the selected inverse of an admissible curve turns the global estimate into

`dist (selInv κ̂ q) (selInv κ̂ p) ≤ selInvLipUniversal … E E · pinchedDist … p q`

(`dist_selInv_le_pinchedDist_of_perim_le`).

Main results: `selInvFrontLip_mono`, `selInvLipUniversal_mono`,
`dist_selInv_le_pinchedDist_of_perim_le`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open RearOwnHigherRegularity SelInvTubePathDist RearJacobiSourceCost
  SelInvLipUniversal GaugeMarkedDataOfRearFamily SelInvModulusLinear
  GaugeFlowDerivCost RearCostDensity MarkingDeviationC2
  NormalPathC2IncrementVariableSpeed RearOwnTangentialCostC2

variable {kminP kh khat : ℝ} {p q : Data}

/-! ### The flow constants -/

theorem costP1_mono_pair {ell ell' kappa M M' : ℝ} (hell : 0 ≤ ell) (hkappa : 0 ≤ kappa)
    (hM : M ≤ M') (hle : ell ≤ ell') : costP1 ell kappa M ≤ costP1 ell' kappa M' := by
  have hexp : Real.exp (kappa * M) ≤ Real.exp (kappa * M') :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hM hkappa)
  exact mul_le_mul hle hexp (Real.exp_pos _).le (le_trans hell hle)

theorem costP1_nonneg' {ell kappa M : ℝ} (hell : 0 ≤ ell) : 0 ≤ costP1 ell kappa M :=
  mul_nonneg hell (Real.exp_pos _).le

theorem costG1_mono_pair {ell ell' kappa kappa2 M M' : ℝ} (hell : 0 ≤ ell)
    (hkappa : 0 ≤ kappa) (hkappa2 : 0 ≤ kappa2) (hM0 : 0 ≤ M) (hM : M ≤ M')
    (hle : ell ≤ ell') : costG1 ell kappa kappa2 M ≤ costG1 ell' kappa kappa2 M' := by
  have hP : costP1 ell kappa M ≤ costP1 ell' kappa M' := costP1_mono_pair hell hkappa hM hle
  have hP0 : 0 ≤ costP1 ell kappa M := costP1_nonneg' hell
  have hsq : costP1 ell kappa M ^ 2 ≤ costP1 ell' kappa M' ^ 2 := by nlinarith
  have hMM : kappa2 * M ≤ kappa2 * M' := mul_le_mul_of_nonneg_left hM hkappa2
  exact mul_le_mul hsq hMM (mul_nonneg hkappa2 hM0) (by positivity)

theorem costG1_nonneg' {ell kappa kappa2 M : ℝ} (hkappa2 : 0 ≤ kappa2) (hM : 0 ≤ M) :
    0 ≤ costG1 ell kappa kappa2 M :=
  mul_nonneg (sq_nonneg _) (mul_nonneg hkappa2 hM)

/-! ### The total cost of the family of rears -/

theorem rearCostConst_mono {kh khat kappa2 ell ell' dd : ℝ} (hell : 0 ≤ ell)
    (hkhat : 0 ≤ khat) (hkappa2 : 0 ≤ kappa2) (hdd : 0 ≤ dd) (hkh1 : kh < 1)
    (hkh0 : 0 ≤ kh) (hle : ell ≤ ell') :
    rearCostConst kh khat kappa2 ell dd ≤ rearCostConst kh khat kappa2 ell' dd := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hinv : 0 ≤ 1 / Real.sqrt (1 - kh ^ 2) := by positivity
  have hP : costP1 ell khat 1 ≤ costP1 ell' khat 1 :=
    costP1_mono_pair hell hkhat le_rfl hle
  have hP0 : 0 ≤ costP1 ell khat 1 := costP1_nonneg' hell
  have hG : costG1 ell khat kappa2 1 ≤ costG1 ell' khat kappa2 1 :=
    costG1_mono_pair hell hkhat hkappa2 zero_le_one le_rfl hle
  have hsq2 : costP1 ell khat 1 ^ 2 ≤ costP1 ell' khat 1 ^ 2 := by nlinarith
  unfold rearCostConst
  refine max_le_max le_rfl (max_le_max ?_ ?_)
  · have : 2 * costP1 ell khat 1 ≤ 2 * costP1 ell' khat 1 := by linarith
    exact mul_le_mul_of_nonneg_right this hinv
  · have h1 : (dd + 2 * (1 / Real.sqrt (1 - kh ^ 2))) * costP1 ell khat 1 ^ 2
        ≤ (dd + 2 * (1 / Real.sqrt (1 - kh ^ 2))) * costP1 ell' khat 1 ^ 2 :=
      mul_le_mul_of_nonneg_left hsq2 (by linarith)
    have h2 : 2 * costG1 ell khat kappa2 1 * (1 / Real.sqrt (1 - kh ^ 2))
        ≤ 2 * costG1 ell' khat kappa2 1 * (1 / Real.sqrt (1 - kh ^ 2)) := by
      have : 2 * costG1 ell khat kappa2 1 ≤ 2 * costG1 ell' khat kappa2 1 := by linarith
      exact mul_le_mul_of_nonneg_right this hinv
    linarith

theorem rearLin_mono {kh ell ell' khat dd : ℝ} (hell : 0 ≤ ell) (hkhat : 0 ≤ khat)
    (hdd : 0 ≤ dd) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hle : ell ≤ ell') :
    rearLin kh ell khat dd ≤ rearLin kh ell' khat dd :=
  rearCostConst_mono hell hkhat (rearKappa2_nonneg hkh0 hkh1) hdd hkh1 hkh0 hle

/-! ### The marking constant -/

theorem defC1_mono {kh ell ell' : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hle : ell ≤ ell') :
    defC1 kh ell ≤ defC1 kh ell' := by
  have hk : 0 ≤ kh / (1 - kh ^ 2) := kappa1_nonneg hkh0 hkh1
  have hpos : (0 : ℝ) ≤ Real.exp (kh / (1 - kh ^ 2)) + 1 := by positivity
  unfold defC1
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hk) hpos

theorem defC2_mono {kh ell ell' : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hell : 0 ≤ ell)
    (hle : ell ≤ ell') : defC2 kh ell ≤ defC2 kh ell' := by
  have hg : 0 ≤ gaugeGrowth2 kh := RearOwnTangentialCostC2.gaugeGrowth2_nonneg hkh0 hkh1
  have hsq : ell ^ 2 ≤ ell' ^ 2 := by nlinarith
  unfold defC2
  have hexp : (0 : ℝ) ≤ Real.exp (2 * (kh / (1 - kh ^ 2))) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hexp) hg

/-- The marking bound is monotone in the length of the curve. -/
theorem markingC2Bound_mono_length {e0 e1 e2 L L' kb kL : ℝ} (he0 : 0 ≤ e0) (he1 : 0 ≤ e1)
    (hkb : 0 ≤ kb) (hkL : 0 ≤ kL) (hL : 0 ≤ L) (hle : L ≤ L') :
    markingC2Bound e0 e1 e2 L kb kL ≤ markingC2Bound e0 e1 e2 L' kb kL := by
  unfold markingC2Bound
  refine max_le_max le_rfl (max_le_max ?_ ?_)
  · have : L * kb * e0 ≤ L' * kb * e0 := by
      have h1 : L * kb ≤ L' * kb := mul_le_mul_of_nonneg_right hle hkb
      exact mul_le_mul_of_nonneg_right h1 he0
    linarith
  · have h1 : kb * e1 * (2 * L + e1) ≤ kb * e1 * (2 * L' + e1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hkb he1)
    have h2 : L ^ 2 * (kL + kb ^ 2) * e0 ≤ L' ^ 2 * (kL + kb ^ 2) * e0 := by
      have hsq : L ^ 2 ≤ L' ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right hsq (by positivity : (0:ℝ) ≤ kL + kb ^ 2)
      exact mul_le_mul_of_nonneg_right this he0
    linarith

theorem markLin_mono {P1 kh ell ell' L L' kb kL : ℝ} (hP1 : 0 ≤ P1) (hkh0 : 0 ≤ kh)
    (hkh1 : kh < 1) (hkb : 0 ≤ kb) (hkL : 0 ≤ kL) (hell : 0 ≤ ell) (hL : 0 ≤ L)
    (hlee : ell ≤ ell') (hleL : L ≤ L') :
    markLin P1 kh ell L kb kL ≤ markLin P1 kh ell' L' kb kL := by
  have he0 : 0 ≤ defC0 P1 kh := defC0_nonneg hP1 hkh0 hkh1
  have he1 : 0 ≤ defC1 kh ell := defC1_nonneg hell hkh0 hkh1
  have hell' : 0 ≤ ell' := le_trans hell hlee
  have he1' : 0 ≤ defC1 kh ell' := defC1_nonneg hell' hkh0 hkh1
  have hstep1 : markingC2Bound (defC0 P1 kh) (defC1 kh ell) (defC2 kh ell) L kb kL
      ≤ markingC2Bound (defC0 P1 kh) (defC1 kh ell') (defC2 kh ell') L kb kL :=
    markingC2Bound_mono hL hkb hkL he1 le_rfl (defC1_mono hkh0 hkh1 hlee)
      (defC2_mono hkh0 hkh1 hell hlee)
  have hstep2 : markingC2Bound (defC0 P1 kh) (defC1 kh ell') (defC2 kh ell') L kb kL
      ≤ markingC2Bound (defC0 P1 kh) (defC1 kh ell') (defC2 kh ell') L' kb kL :=
    markingC2Bound_mono_length he0 he1' hkb hkL hL hleL
  exact le_trans hstep1 hstep2

/-! ### The `C²` increment constant -/

theorem c2Lin_mono {kh ell ell' Pv0 khat dd : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPv0 : 0 ≤ Pv0) (hkhat : 0 ≤ khat) (hdd : 0 ≤ dd) (hell : 0 ≤ ell)
    (hle : ell ≤ ell') : c2Lin kh ell Pv0 khat dd ≤ c2Lin kh ell' Pv0 khat dd := by
  have hk2 : 0 ≤ rearKappa2 kh := rearKappa2_nonneg hkh0 hkh1
  have hR : rearLin kh ell khat dd ≤ rearLin kh ell' khat dd :=
    rearLin_mono hell hkhat hdd hkh0 hkh1 hle
  have hR0 : 0 ≤ rearLin kh ell khat dd :=
    le_trans zero_le_one (rearCostConst_ge_one hkh0 hkh1)
  have hP : costP1 ell khat (rearLin kh ell khat dd)
      ≤ costP1 ell' khat (rearLin kh ell' khat dd) :=
    costP1_mono_pair hell hkhat hR hle
  have hP0 : 0 ≤ costP1 ell khat (rearLin kh ell khat dd) := costP1_nonneg' hell
  have hG : costG1 ell khat (rearKappa2 kh) (rearLin kh ell khat dd)
      ≤ costG1 ell' khat (rearKappa2 kh) (rearLin kh ell' khat dd) :=
    costG1_mono_pair hell hkhat hk2 hR0 hR hle
  have hG0 : 0 ≤ costG1 ell khat (rearKappa2 kh) (rearLin kh ell khat dd) :=
    costG1_nonneg' hk2 hR0
  have hCg : khat * costG1 ell khat (rearKappa2 kh) (rearLin kh ell khat dd)
        + rearKappa2 kh * costP1 ell khat (rearLin kh ell khat dd) ^ 2
      ≤ khat * costG1 ell' khat (rearKappa2 kh) (rearLin kh ell' khat dd)
        + rearKappa2 kh * costP1 ell' khat (rearLin kh ell' khat dd) ^ 2 := by
    have h1 : khat * costG1 ell khat (rearKappa2 kh) (rearLin kh ell khat dd)
        ≤ khat * costG1 ell' khat (rearKappa2 kh) (rearLin kh ell' khat dd) :=
      mul_le_mul_of_nonneg_left hG hkhat
    have hsq : costP1 ell khat (rearLin kh ell khat dd) ^ 2
        ≤ costP1 ell' khat (rearLin kh ell' khat dd) ^ 2 := by nlinarith
    have h2 : rearKappa2 kh * costP1 ell khat (rearLin kh ell khat dd) ^ 2
        ≤ rearKappa2 kh * costP1 ell' khat (rearLin kh ell' khat dd) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hk2
    linarith
  exact c2ConstVar_mono hPv0 hkhat hP0 hP hG hCg

/-! ### Monotonicity of the Lipschitz constant -/

/-- **The Lipschitz constant of the `C²` estimate is monotone in the two
perimeters.** -/
theorem selInvFrontLip_mono {P1 kh ell ell' L L' kb kL Pv0 khat dd : ℝ} (hP1 : 0 ≤ P1)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hkb : 0 ≤ kb) (hkL : 0 ≤ kL) (hPv0 : 0 ≤ Pv0)
    (hkhat : 0 ≤ khat) (hdd : 0 ≤ dd) (hell : 0 ≤ ell) (hL : 0 ≤ L)
    (hlee : ell ≤ ell') (hleL : L ≤ L') :
    selInvFrontLip P1 kh ell L kb kL Pv0 khat dd
      ≤ selInvFrontLip P1 kh ell' L' kb kL Pv0 khat dd := by
  have hmark : markLin P1 kh ell L kb kL ≤ markLin P1 kh ell' L' kb kL :=
    markLin_mono hP1 hkh0 hkh1 hkb hkL hell hL hlee hleL
  have hc2 : c2Lin kh ell Pv0 khat dd ≤ c2Lin kh ell' Pv0 khat dd :=
    c2Lin_mono hkh0 hkh1 hPv0 hkhat hdd hell hlee
  have hc20 : 0 ≤ c2Lin kh ell Pv0 khat dd := c2ConstVar_nonneg _ _ _ _ _
  have hR : rearLin kh ell khat dd ≤ rearLin kh ell' khat dd :=
    rearLin_mono hell hkhat hdd hkh0 hkh1 hlee
  have hR0 : 0 ≤ rearLin kh ell khat dd :=
    le_trans zero_le_one (rearCostConst_ge_one hkh0 hkh1)
  unfold selInvFrontLip
  exact add_le_add hmark (mul_le_mul hc2 hR hR0 (le_trans hc20 hc2))

/-- **The universal Lipschitz constant is monotone in the two perimeters.** -/
theorem selInvLipUniversal_mono {ell ell' L L' : ℝ} (hkminP : 0 < kminP) (hkh0 : 0 < kh)
    (hkh1 : kh < 1) (hkhat : 0 ≤ khat) (hell : 0 ≤ ell) (hL : 0 ≤ L)
    (hlee : ell ≤ ell') (hleL : L ≤ L') :
    selInvLipUniversal kminP kh khat ell L ≤ selInvLipUniversal kminP kh khat ell' L' := by
  have hkh0' : 0 ≤ kh := hkh0.le
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 hsq
  have hPv : (0 : ℝ) < 2 * Real.pi / kh := by positivity
  have hrr : (0 : ℝ) ≤ 2 * Real.pi / kminP * (kh / (1 - kh ^ 2)) := by positivity
  refine selInvFrontLip_mono (by positivity) hkh0' hkh1 (by positivity) (by positivity)
    (SelInvPathGaugeC2.pathPv0_pos hPv hkh0' hkhat hrr).le hkhat
    (jacobiSourceConst_nonneg hPv) hell hL hlee hleL

/-! ### The global estimate with the perimeters bounded -/

/-- **The selected inverse is Lipschitz for the pinched pseudometric**, with a
constant depending only on the geometry, as soon as the perimeter of the
selected inverse of an admissible curve is bounded by `E`. -/
theorem dist_selInv_le_pinchedDist_of_perim_le {E : ℝ}
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hkh1 : kh < 1) (hkminP : 0 < kminP) (hkhat : rearKappa1 kh ≤ khat) (hkhat0 : 0 ≤ khat)
    (hE : ∀ a : Data, IsPinchedCurve kminP kh a → (∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u) →
      perim (SelectedInverseMap.selInv kh a) ≤ E)
    (hne : (pinchedSet kminP kh p q).Nonempty) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ selInvLipUniversal kminP kh khat E E * pinchedDist kminP kh p q := by
  have hkh0 : 0 < kh := by
    obtain ⟨c, Γ, -, hΓ⟩ := hne
    exact lt_of_lt_of_le hkminP (le_trans (hΓ.kmin 0 0) (hΓ.kmax 0 0))
  refine dist_selInv_le_pinchedDist_uniformLip hpd hpd2 hqd hqd2 hkh1 hkminP hkhat
    (fun a b ha hb hfa hfb => ?_) hne
  exact selInvLipUniversal_mono hkminP hkh0 hkh1 hkhat0 (norm_nonneg _) (norm_nonneg _)
    (hE a ha hfa) (hE b hb hfb)

end PinchedPath
