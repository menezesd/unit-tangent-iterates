import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfJacobi
import UnitTangentIterates.GaugeMarkedDataOfNormalRateCircle

/-!
# Non-vacuity of the Jacobi form of the construction

`GaugeMarkedDataOfJacobi.exists_variableSpeed_normalPath_of_jacobi` produces the
path `Γ'` of the `C²` comparison from the inverse Jacobi ODE of a family of
rears.  This file checks that its hypothesis block is satisfiable, on the
drifting circle: its normal rate vanishes and so does the inhomogeneity of the
ODE, the numerical conditions holding with `r = 1/2` and `c = d = 0`.

Main result: `exists_variableSpeed_normalPath_driftingCircle_of_jacobi`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfJacobiCircle

open GaugeFlowVariableSpeedPath GaugeFlowVariableSpeedPathCircle GaugeMarkedDataOfJacobi
  GaugeMarkedDataOfNormalRateCircle NormalPathC2IncrementVariableSpeed PathMetricCircle

/-- **The drifting circle satisfies the Jacobi form of the hypothesis block**,
and hence produces the normal path with slices of variable speed. -/
theorem exists_variableSpeed_normalPath_driftingCircle_of_jacobi :
    ∃ Γ : NormalPath (circleData 1) (circleData 1), Γ.T = 1 ∧
      Γ.m = (fun t => 2 * w t) ∧ cost Γ = (∫ t in (0 : ℝ)..1, 2 * w t) ∧
      IsVariableSpeedNormalPath 1 (2 * Real.pi) 1 0 0 Γ :=
  exists_variableSpeed_normalPath_of_jacobi (Y := Ydrift) (alpha := alphaDrift)
    (k := fun _ _ => 1) (en := fun _ _ => 0) (enS := fun _ _ => 0) (enSS := fun _ _ => 0)
    (g := fun _ _ => 0) (gS := fun _ _ => 0) (h := fun t _ => -w t) (hx := fun _ _ => 0)
    (hxx := fun _ _ => 0) (Phi := PhiDrift) (alphaT := fun t _ => w t)
    (kT := fun _ _ => 0) (kX := fun _ _ => 0) (C := fun _ => 0) (C2 := fun _ => 0)
    (Kx := fun _ => 0) (Rb := w) (S0 := fun _ => 0) (D := fun _ => 0)
    (K := 0) (K2 := 0) (ell := 2 * Real.pi) (c := 0) (d := 0) (r := 1 / 2) (kx := 0)
    driftingCircleData.hYC1 driftingCircleData.hY driftingCircleData.hYt
    driftingCircleData.halpha driftingCircleData.hlip driftingCircleData.hcont
    driftingCircleData.hPhid driftingCircleData.hell driftingCircleData.hPhi0
    driftingCircleData.hxd driftingCircleData.hxcont driftingCircleData.hxxd
    driftingCircleData.hxxcont driftingCircleData.hxxK driftingCircleData.hP1
    driftingCircleData.hG1 driftingCircleData.hk driftingCircleData.hC
    driftingCircleData.hC2 driftingCircleData.hCnn driftingCircleData.hC2nn
    driftingCircleData.hcost driftingCircleData.hcost2 driftingCircleData.halphaC1
    driftingCircleData.hkC1 driftingCircleData.halphaT driftingCircleData.hkT
    driftingCircleData.hkX driftingCircleData.halphaTc driftingCircleData.hkTc
    driftingCircleData.hkXc driftingCircleData.hkc driftingCircleData.hKxbd
    driftingCircleData.hRbd driftingCircleData.hKxnn
    (fun t x => hasDerivAt_const x (0 : ℝ)) (fun t x => hasDerivAt_const x (0 : ℝ))
    (fun t s => hasDerivAt_const s (w t)) mixed_driftingCircle
    (fun t x => hasDerivAt_const x (0 : ℝ))
    (fun t x => by simpa using hasDerivAt_const x (0 : ℝ))
    (fun t x => by norm_num) (fun t x => by norm_num) (fun t x => by norm_num)
    (fun t => by norm_num) (fun t => by norm_num)
    (fun t => by have := w_nonneg t; linarith) (fun t => le_rfl) (by norm_num)
    (fun t => by have := w_nonneg t; linarith) (by norm_num) (by norm_num)
    driftingCircleData.hT driftingCircleData.hencont driftingCircleData.hstart
    driftingCircleData.hfinish driftingCircleData.hmc driftingCircleData.hmstop
    driftingCircleData.hmbd driftingCircleData.hmsup

end GaugeMarkedDataOfJacobiCircle
