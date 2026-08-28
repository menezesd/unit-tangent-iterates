import Mathlib
import UnitTangentIterates.GaugeRearFamilyFromFront
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed
import UnitTangentIterates.SelectedInverseMap
import UnitTangentIterates.MarkedComparisonC2
import UnitTangentIterates.SelInvTerminalLift
import UnitTangentIterates.GaugeFlowVariablePeriod
import UnitTangentIterates.SecondOrderBounds

/-!
# Variable-speed interpolation-to-selected-inverse comparison

The rear family produced from the raw curvature interpolation is read in the
nonaffine normal-gauge marking.  Consequently its terminal marked datum need
not literally equal the canonically, affinely marked selected inverse.  This
file isolates exactly that discrepancy.

No constant-speed or tube-membership hypothesis is needed for the rear path:
`dist_le_cost_variableSpeed` applies directly.  The only remaining endpoint
input is the marked `C²` distance from the gauge endpoint to the canonical
selected inverse.  This is precisely the marking-defect term estimated by
`MarkingFlowDefectC2` in the downstream comparison modules.
-/

noncomputable section

open MarkedSpace PathMetric PathMetric.NormalPath
open Set Function MeasureTheory UniformFrameBounds
open scoped NNReal

namespace InterpolationVariableSpeedSelInvAdapter

open NormalPathC2IncrementVariableSpeed

/-- Uniform coefficient which linearizes the canonical marking correction on
the cost interval `[0,M]`. -/
def canonicalMarkingLinearConst
    (Qmax ell kappa kappa2 M L kb kL : ℝ) : ℝ :=
  let A := 2 * Qmax * kappa
  let B := ell * kappa * (Real.exp (kappa * M) + 1)
  let D := ell ^ 2 * Real.exp (2 * kappa * M) * kappa2
  max A (max (B + L * kb * A)
    (D + kb * B * (2 * L + B * M) + L ^ 2 * (kL + kb ^ 2) * A))

theorem markingC2Bound_flow_le_linear
    {Qmax ell kappa kappa2 M L kb kL x : ℝ}
    (hQ : 0 ≤ Qmax) (hell : 0 ≤ ell) (hk : 0 ≤ kappa)
    (hk2 : 0 ≤ kappa2) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hkb : 0 ≤ kb) (hkL : 0 ≤ kL) (hx0 : 0 ≤ x) (hxM : x ≤ M) :
    MarkingDeviationC2.markingC2Bound
        (2 * Qmax * kappa * x)
        (MarkingFlowDefectC2.flowDefectC1Int ell (kappa * x))
        (MarkingFlowDefectC2.flowDefectC2Int ell (kappa * x) (kappa2 * x))
        L kb kL ≤
      canonicalMarkingLinearConst Qmax ell kappa kappa2 M L kb kL * x := by
  let A := 2 * Qmax * kappa
  let B := ell * kappa * (Real.exp (kappa * M) + 1)
  let D := ell ^ 2 * Real.exp (2 * kappa * M) * kappa2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨h1, h2⟩ := MarkingFlowDefectC2.flowDefectInt_linear_bounds
    hell hk hk2 hx0 hxM
  have he0 : 0 ≤ A * x := mul_nonneg hA hx0
  have he1 : 0 ≤ MarkingFlowDefectC2.flowDefectC1Int ell (kappa * x) :=
    MarkingFlowDefectC2.flowDefectC1Int_nonneg hell (mul_nonneg hk hx0)
  have he2 : 0 ≤ MarkingFlowDefectC2.flowDefectC2Int ell
      (kappa * x) (kappa2 * x) := by
    simp only [MarkingFlowDefectC2.flowDefectC2Int]
    positivity
  simpa only [canonicalMarkingLinearConst, A, B, D] using
    MarkingDeviationC2.markingC2Bound_le_mul_of_component_linear
      hx0 hxM hA hB hD hL hkb hkL he0 he1 le_rfl h1 h2

theorem canonicalMarkingLinearConst_nonneg
    {Qmax ell kappa kappa2 M L kb kL : ℝ}
    (hQ : 0 ≤ Qmax) (hk : 0 ≤ kappa) :
    0 ≤ canonicalMarkingLinearConst Qmax ell kappa kappa2 M L kb kL := by
  have hA : (0:ℝ) ≤ 2 * Qmax * kappa :=
    mul_nonneg (mul_nonneg (by norm_num) hQ) hk
  refine le_trans hA ?_
  simp only [canonicalMarkingLinearConst]
  exact le_max_left _ _

/-- The complete canonical terminal certificate consumed by the gauge-marking
comparison.  The constants are the sharp selected-strip constants. -/
structure TerminalCertificate (kh : ℝ) (q : Data) where
  dR : ℝ
  dR_pos : 0 < dR
  terminalLower : ℝ
  tube : IsTubeMember (perim (SelectedInverseMap.selInv kh q))
    terminalLower dR (SelectedInverseMap.selInv kh q)
  terminalLower_pos : 0 < terminalLower
  hasDeriv_curve : ∀ u, HasDerivAt
    (⇑(SelectedInverseMap.selInv kh q).1)
    ((SelectedInverseMap.selInv kh q).2.1 u) u
  hasDeriv_vel : ∀ u, HasDerivAt
    (⇑(SelectedInverseMap.selInv kh q).2.1)
    ((SelectedInverseMap.selInv kh q).2.2 u) u
  Theta : ℝ → ℝ
  curvature : ℝ → ℝ
  hasDeriv_curve_angle : ∀ s, HasDerivAt (ev (SelectedInverseMap.selInv kh q))
    (Complex.exp (Complex.I * (Theta s : ℂ))) s
  hasDeriv_angle : ∀ s, HasDerivAt Theta (curvature s) s
  curvature_bound : ∀ s,
    |curvature s| ≤ kh / Real.sqrt (1 - kh ^ 2)
  curvature_lipschitz : ∀ s t,
    |curvature s - curvature t|
      ≤ 2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3 * |s - t|

/-- The selected-inverse specification and terminal-lift theorem together
discharge every geometric hypothesis about the canonical terminal endpoint. -/
theorem exists_terminalCertificate
    {q : Data} {c kmin dlt kh : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hq : IsTubeMember c kmin dlt q)
    (hub : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im
      ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hinjR : ∀ Theta K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q)
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) →
      (∀ s, HasDerivAt Theta (K s) s) →
      Function.Periodic dl (perim q) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (RearTrack.rearTrack (ev q) Theta dl) (Ico 0 (perim q))) :
    Nonempty (TerminalCertificate kh q) := by
  obtain ⟨dR, hdR, hmem, -, -, -⟩ :=
    SelectedInverseMap.selInv_spec hc hkmin hkh1 hq hub hinjR
  obtain ⟨Theta, k, hev, hTheta, hk, hklip⟩ :=
    SelInvTerminalLift.exists_tangent_lift_selInv
      hc hkmin hkh0 hkh1 hq hub hinjR
  have hkmin1 : kmin < 1 := by
    have h1 := hq.curv_lb 0
    have h2 := hub 0
    have hs : 0 < ‖q.2.1 0‖ ^ 3 := by
      have : 0 < ‖q.2.1 0‖ := lt_of_lt_of_le hc (hq.speed_lb 0)
      positivity
    nlinarith
  have hlower : 0 < kmin / Real.sqrt (1 - kmin ^ 2) :=
    div_pos hkmin (Real.sqrt_pos.2 (by nlinarith))
  refine ⟨?_⟩
  exact
    { dR := dR
      dR_pos := hdR
      terminalLower := kmin / Real.sqrt (1 - kmin ^ 2)
      tube := hmem
      terminalLower_pos := hlower
      hasDeriv_curve := hmem.hasDerivAt_curve
      hasDeriv_vel := hmem.hasDerivAt_vel
      Theta := Theta
      curvature := k
      hasDeriv_curve_angle := hev
      hasDeriv_angle := hTheta
      curvature_bound := hk
      curvature_lipschitz := hklip }

/-- **Capstone for a variable-speed selected-rear interpolation.**

Once the explicit interpolation construction supplies a variable-speed normal
path from the initial canonical selected inverse to its gauge-marked terminal
rear, the canonical selected inverses are separated by only

* the terminal marking defect `E`, and
* the explicit variable-speed path cost.

Thus the large qualitative and tube hypothesis blocks of the older
constant-speed adapters are absent. -/
theorem dist_selInv_le_terminalDefect_add_variableSpeedCost
    {p q q' : Data} {kh P0 P1 khat G1 Cg E : ℝ}
    (Γ' : NormalPath (SelectedInverseMap.selInv kh p) q')
    (hpd : ∀ u, HasDerivAt
      (⇑(SelectedInverseMap.selInv kh p).1)
      ((SelectedInverseMap.selInv kh p).2.1 u) u)
    (hpv : ∀ u, HasDerivAt
      (⇑(SelectedInverseMap.selInv kh p).2.1)
      ((SelectedInverseMap.selInv kh p).2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u)
    (hqv : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u)
    (hvar : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ')
    (hterminal : dist (SelectedInverseMap.selInv kh q) q' ≤ E) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ E + c2ConstVar P0 P1 khat G1 Cg * cost Γ' := by
  have hpath : dist q' (SelectedInverseMap.selInv kh p)
      ≤ c2ConstVar P0 P1 khat G1 Cg * cost Γ' := by
    rw [dist_comm]
    exact dist_le_cost_variableSpeed Γ' hpd hqd hpv hqv hvar
  exact (dist_triangle _ q' _).trans (add_le_add hterminal hpath)

/-- Integral-cost form consumed by
`GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`.
That construction identifies the rear-path cost with `∫₀ᵀ m`; after this
rewrite, the sole comparison remainder is the terminal marking defect. -/
theorem dist_selInv_le_terminalDefect_add_integralCost
    {p q q' : Data} {kh P0 P1 khat G1 Cg E T : ℝ} {m : ℝ → ℝ}
    (Γ' : NormalPath (SelectedInverseMap.selInv kh p) q')
    (hpd : ∀ u, HasDerivAt
      (⇑(SelectedInverseMap.selInv kh p).1)
      ((SelectedInverseMap.selInv kh p).2.1 u) u)
    (hpv : ∀ u, HasDerivAt
      (⇑(SelectedInverseMap.selInv kh p).2.1)
      ((SelectedInverseMap.selInv kh p).2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u)
    (hqv : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u)
    (hvar : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ')
    (hcost : cost Γ' = ∫ t in (0 : ℝ)..T, m t)
    (hterminal : dist (SelectedInverseMap.selInv kh q) q' ≤ E) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ E + c2ConstVar P0 P1 khat G1 Cg * ∫ t in (0 : ℝ)..T, m t := by
  rw [← hcost]
  exact dist_selInv_le_terminalDefect_add_variableSpeedCost
    Γ' hpd hpv hqd hqv hvar hterminal

/-- **The terminal marking defect is generated from the interpolation gauge
flow.**  This is the selected-inverse specialization of
`MarkedComparisonC2.dist_le_of_marking_and_variableSpeed`: the terminal
distance premise of the two preceding lemmas is replaced by the actual gauge
ODE, its first two spatial derivatives, and their cost-density bounds.

The path `Γ` controls the nonaffine marking, while `Γ'` is the variable-speed
path of selected rears produced by `GaugeRearFamilyFromFront`.  They need not
have the same parametrized slices. -/
theorem dist_selInv_le_of_gaugeFlow_and_variableSpeed
    {p q q' : Data} {kh : ℝ} (Γ : NormalPath p q)
    (Γ' : NormalPath (SelectedInverseMap.selInv kh p) q')
    {R Rx Rxx : ℝ → ℝ → ℝ} {C C2 : ℝ → ℝ} {Phi : ℝ → ℝ → ℝ}
    {Klip : ℝ≥0}
    {K2 L0 Lmax kappa kappa2 L kb kL cq kminq dltq : ℝ}
    {Theta k : ℝ → ℝ} {P0 P1 khat G1 Cg : ℝ}
    (hlip : ∀ t, LipschitzWith Klip (R t))
    (hRcont : Continuous (uncurry R))
    (hd : ∀ u t, HasDerivAt (fun s => Phi s u) (R t (Phi t u)) t)
    (hdc : ∀ u, Continuous fun t => R t (Phi t u))
    (hRx : ∀ s x, HasDerivAt (R s) (Rx s x) x)
    (hRxcont : Continuous (uncurry Rx))
    (hRxx : ∀ s x, HasDerivAt (Rx s) (Rxx s x) x)
    (hRxxcont : Continuous (uncurry Rxx))
    (hK2 : ∀ s x, |Rxx s x| ≤ K2)
    (hCcont : Continuous C) (hgrow : ∀ t x, |R t x| ≤ C t * |x|)
    (hCnn : ∀ t, 0 ≤ C t) (hRxbd : ∀ s x, |Rx s x| ≤ C s)
    (hC2cont : Continuous C2) (hRxxbd : ∀ s x, |Rxx s x| ≤ C2 s)
    (hcost : ∀ t, C t ≤ kappa * Γ.m t)
    (hcost2 : ∀ t, C2 t ≤ kappa2 * Γ.m t)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0)
    (hbase : ∀ t, Phi t 0 = 0)
    (hper : ∀ t u, Phi t (u + 1) = Phi t u + Phi t 1)
    (hLmax : ∀ t, Phi t 1 ≤ Lmax) (hPhiT : Phi Γ.T 1 = L)
    (hcq : 0 < cq)
    (hb : IsTubeMember cq kminq dltq (SelectedInverseMap.selInv kh q))
    (hLb : perim (SelectedInverseMap.selInv kh q) = L)
    (hev : ∀ s, HasDerivAt (ev (SelectedInverseMap.selInv kh q))
      (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hTheta : ∀ s, HasDerivAt Theta (k s) s)
    (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hq'1 : ∀ u, q'.1 u = ev (SelectedInverseMap.selInv kh q) (Phi Γ.T u))
    (hq'd : ∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u)
    (hq'v : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u)
    (hpd : ∀ u, HasDerivAt
      (⇑(SelectedInverseMap.selInv kh p).1)
      ((SelectedInverseMap.selInv kh p).2.1 u) u)
    (hpv : ∀ u, HasDerivAt
      (⇑(SelectedInverseMap.selInv kh p).2.1)
      ((SelectedInverseMap.selInv kh p).2.2 u) u)
    (hvar : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ') :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ MarkingDeviationC2.markingC2Bound (2 * Lmax * kappa * cost Γ)
          (MarkingFlowDefectC2.flowDefectC1Int L0 (kappa * cost Γ))
          (MarkingFlowDefectC2.flowDefectC2Int L0 (kappa * cost Γ)
            (kappa2 * cost Γ)) L kb kL
        + c2ConstVar P0 P1 khat G1 Cg * cost Γ' := by
  exact MarkedComparisonC2.dist_le_of_marking_and_variableSpeed
    Γ Γ' hlip hRcont hd hdc hRx hRxcont hRxx hRxxcont hK2 hCcont hgrow hCnn
    hRxbd hC2cont hRxxbd hcost hcost2 h0 hL0 hbase hper hLmax hPhiT hcq hb
    hLb hev hTheta hkb hklip hq'1 hq'd hq'v hpd hpv hvar

/-- **Concrete selected-rear gauge specialization.**

The same variable-speed rear path controls both terms of the terminal
comparison.  The gauge field is the actual `-xi` produced by the selected-rear
construction.  Its sharp first and second derivative bounds yield all flow
constants; quasi-periodicity of `xi` yields transport of one rear period by
`Phi`.  Canonical endpoint geometry is read from `TerminalCertificate`.

This is the form to feed into the marked pullback-limit step. -/
theorem dist_selInv_le_of_selectedRear_gauge
    {p q q' : Data} {kh P0 P1 khat G1 Cg : ℝ}
    (Gamma : NormalPath (SelectedInverseMap.selInv kh p) q')
    (hp : TerminalCertificate kh p) (hq : TerminalCertificate kh q)
    {xi Phi : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ} {Qmax : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hxiC2 : ContDiff ℝ (2 : ℕ) (uncurry xi))
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u)
    (hbase : ∀ t, Phi t 0 = 0)
    (hflow : ∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t)
    (hxi0 : ∀ t, xi t 0 = 0)
    (hQpos : ∀ t, 0 < Q t)
    (hQmax : ∀ t, Q t ≤ Qmax)
    (hRxbd : ∀ t x, |partialX xi t x|
      ≤ GaugeMarkedDataOfRearFamily.rearKappa1 kh * Gamma.m t)
    (hRxxbd : ∀ t x, |partialX (partialX xi) t x|
      ≤ GaugeMarkedDataOfRearFamily.rearKappa2 kh * Gamma.m t)
    (hperim : perim (SelectedInverseMap.selInv kh q) = Q Gamma.T)
    (hperim_pos : 0 < perim (SelectedInverseMap.selInv kh q))
    (hq'1 : ∀ u, q'.1 u = ev (SelectedInverseMap.selInv kh q) (Phi Gamma.T u))
    (hq'd : ∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u)
    (hq'v : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u)
    (hvar : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ MarkingDeviationC2.markingC2Bound
          (2 * Qmax * GaugeMarkedDataOfRearFamily.rearKappa1 kh * cost Gamma)
          (MarkingFlowDefectC2.flowDefectC1Int (Q 0)
            (GaugeMarkedDataOfRearFamily.rearKappa1 kh * cost Gamma))
          (MarkingFlowDefectC2.flowDefectC2Int (Q 0)
            (GaugeMarkedDataOfRearFamily.rearKappa1 kh * cost Gamma)
            (GaugeMarkedDataOfRearFamily.rearKappa2 kh * cost Gamma))
          (Q Gamma.T) (kh / Real.sqrt (1 - kh ^ 2))
          (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)
        + c2ConstVar P0 P1 khat G1 Cg * cost Gamma := by
  let R : ℝ → ℝ → ℝ := fun t x => -xi t x
  let Rx : ℝ → ℝ → ℝ := fun t x => -partialX xi t x
  let Rxx : ℝ → ℝ → ℝ := fun t x => -partialX (partialX xi) t x
  have hRxC : ContDiff ℝ (1 : ℕ) (uncurry (partialX xi)) :=
    contDiff_partialX (n := 1) hxiC2
  have hRd : ∀ t x, HasDerivAt (R t) (Rx t x) x := fun t x => by
    simpa [R, Rx] using
      (hasDerivAt_partialX (hxiC2.of_le (by norm_num)) t x).neg
  have hRxd : ∀ t x, HasDerivAt (Rx t) (Rxx t x) x := fun t x => by
    simpa [Rx, Rxx] using (hasDerivAt_partialX hRxC t x).neg
  have hRxbd' : ∀ t x, |Rx t x|
      ≤ GaugeMarkedDataOfRearFamily.rearKappa1 kh * Gamma.m t := fun t x => by
    simpa [Rx] using hRxbd t x
  have hRxxbd' : ∀ t x, |Rxx t x|
      ≤ GaugeMarkedDataOfRearFamily.rearKappa2 kh * Gamma.m t := fun t x => by
    simpa [Rxx] using hRxxbd t x
  obtain ⟨B, hB0, hBm, hlip, hK2⟩ :=
    GaugeRearFamilyFundamental.selectedRear_gaugeField_global_bounds
      Gamma hkh0 hkh1 hRd hRxbd' hRxxbd'
  have htrans : ∀ u t, Phi t (u + 1) = Phi t u + Q t := by
    intro u t
    exact GaugeFlowVariablePeriod.flow_translation_var hlip hQd
      (fun a x => by simp [R, hxiqp a x]; ring)
      (fun v a => by simpa [R] using hflow v a) hPhi0 u t
  have hPhi1 : ∀ t, Phi t 1 = Q t := by
    intro t
    have h := htrans 0 t
    simpa [hbase t] using h
  have hRcont : Continuous (uncurry R) := hxiC2.continuous.neg
  have hRxcont : Continuous (uncurry Rx) := hRxC.continuous.neg
  have hRxxcont : Continuous (uncurry Rxx) :=
    (contDiff_partialX (n := 0) hRxC).continuous.neg
  let C : ℝ → ℝ := fun t =>
    GaugeMarkedDataOfRearFamily.rearKappa1 kh * Gamma.m t
  let C2 : ℝ → ℝ := fun t =>
    GaugeMarkedDataOfRearFamily.rearKappa2 kh * Gamma.m t
  have hk1 := GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkh0 hkh1
  have hk2 := GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hkh0 hkh1
  have hCcont : Continuous C := continuous_const.mul Gamma.cont_m
  have hC2cont : Continuous C2 := continuous_const.mul Gamma.cont_m
  have hCnn : ∀ t, 0 ≤ C t := fun t => mul_nonneg hk1 (Gamma.m_nonneg t)
  have hgrow : ∀ t x, |R t x| ≤ C t * |x| := by
    intro t x
    have hs := SecondOrderBounds.abs_sub_le_of_deriv_bound
      (hRd t) (hRxbd' t) x 0
    have hR0 : R t 0 = 0 := by simp [R, hxi0 t]
    simpa [hR0, C] using hs
  have hdc : ∀ u, Continuous fun t => R t (Phi t u) := by
    intro u
    have hPhic : Continuous fun t => Phi t u :=
      continuous_iff_continuousAt.2 fun t => (hflow u t).continuousAt
    exact hRcont.comp (continuous_id.prodMk hPhic)
  exact MarkedComparisonC2.dist_le_of_marking_and_variableSpeed
    Gamma Gamma hlip hRcont (fun u t => by simpa [R] using hflow u t) hdc
    hRd hRxcont hRxd hRxxcont hK2 hCcont hgrow hCnn hRxbd' hC2cont hRxxbd'
    (fun _ => le_rfl) (fun _ => le_rfl) hPhi0 (hQpos 0)
    hbase (fun t u => by rw [htrans u t, hPhi1 t])
    (fun t => by rw [hPhi1 t]; exact hQmax t) (hPhi1 Gamma.T) (by simpa using hperim_pos) hq.tube hperim
    hq.hasDeriv_curve_angle hq.hasDeriv_angle hq.curvature_bound
    hq.curvature_lipschitz hq'1 hq'd hq'v hp.hasDeriv_curve hp.hasDeriv_vel hvar

end InterpolationVariableSpeedSelInvAdapter
