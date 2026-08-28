import UnitTangentIterates.ConfiguredApproximateDefectPathConstructor
import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariable
import UnitTangentIterates.ModelDefectSummable
import UnitTangentIterates.MatchingPathDist

/-!
# Configured defect paths with row-dependent ceilings

The interpolation speed scale grows with the configured separation.  Hence
the correct recursive interface uses the exact finite constants of each row,
not global dominators over all rows.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace ConfiguredApproximateDefectPathRowwise

open ModelOrbitDefect CurvatureInterpolation InterpolationEstimate
  InterpolationPathDist InterpolationVariableSpeedConstants
  InterpolationControlledJunctionFinal ProfiledInterpolationFields
  ProfiledInterpolationBoundsConstructor
  PathMetric.WeightedMarkedDefectThreshold RearTrack

/-- Curvature mismatch of configured edge `n`. -/
def edgeEps (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  curvDist
    (modelCurvature (D.model.configs n).yu
      (D.model.configs n).yu' (D.Hs n))
    (D.model.configs n).kH (D.Hs n)

/-- The matching majorant attached to the actual configured model, rather
than to an auxiliary fixed-scale defect. -/
def edgeMajorant (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  matchConst D.model.a D.model.C D.model.CK D.model.CU D.model.DU
      D.model.Km D.model.Kd D.model.au D.model.alpha D.model.beta D.model.Bcell
    * Real.exp (-(D.model.beta * D.Hs (n + 1)))

/-- The concrete curvature mismatch is exponentially small with the
coefficient and exponent of the configured matching theorem. -/
theorem edgeEps_le_edgeMajorant
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    edgeEps D n ≤ edgeMajorant D n := by
  let c := D.model.configs n
  have hxH : ∀ t, HasDerivAt (modelRearArclength c.Y)
      (Real.sqrt (1 - (c.Y t) ^ 2)) t := fun t => by
    rw [show Real.sqrt (1 - (c.Y t) ^ 2) = Real.cos (modelSteering c.Y t)
      from (cos_modelSteering (Y := c.Y) (s := t)).symm]
    exact hasDerivAt_rearArclength c.continuous_dl t
  have hx0 : modelRearArclength c.Y 0 = c.x 0 := by
    rw [c.hx0]
    simp [modelRearArclength, RearTrack.rearArclength]
  have h := MatchingPathDist.curvDist_le_of_matching
    (Y := c.Y) (y := c.y) (xH := modelRearArclength c.Y) (x := c.x)
    (Kstar := c.Kstar) (Kstar' := c.Kstar') (kH := c.kH) (Kbar := c.Kbar)
    (KP := modelCurvature c.yu c.yu' (D.Hs n)) (yu := c.yu) (yu' := c.yu')
    c.ha c.hy0 c.hyb c.hH c.hq2 c.hYdef c.ha0 c.ha1 c.continuous_Y c.continuous_y
    c.hYa c.abs_y_le_strip hxH c.hx hx0 c.hid c.abs_Kstar_le c.hKderiv
    c.abs_Kstar'_le c.continuous_Kstar c.hbeta0 c.hbeta c.hk
    c.continuous_kH_sub_Kbar c.hKbar c.intervalIntegrable_puncturedSum
    c.intervalIntegrable_kH_sub c.intervalIntegrable_Kbar_sub c.rearArclength_period c.Ppos
    c.integrable_Kstar c.Kstar_nonneg c.abs_Kstar_le_exp c.rearArclength_left_nonpos
    c.rearArclength_right_nonneg c.hpB c.hqB c.hhalf c.continuous_yu c.hyu'c c.hyu0
    c.hyub c.hDU c.hyu'b c.hau0 c.hau1 c.hYau c.hKstaru (fun _ => rfl) c.hPH
    c.periodic_kH c.periodic_KP
  simpa [edgeEps, edgeMajorant, c, curvDist, abs_sub_comm, matchConst] using h

def edgeCoefficient (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  matchConst D.model.a D.model.C D.model.CK D.model.CU D.model.DU
    D.model.Km D.model.Kd D.model.au D.model.alpha D.model.beta D.model.Bcell

theorem edgeEps_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ edgeEps D n := by
  simpa [edgeEps] using InterpolationNormal.integral_abs_sub_nonneg
    (D.model.configs n).continuous_KP (D.model.configs n).continuous_kH
    (D.model.separation_pos n).le

theorem edgeCoefficient_nonneg (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ edgeCoefficient D := by
  have he := edgeEps_nonneg D 0
  have hb := edgeEps_le_edgeMajorant D 0
  have hE := Real.exp_pos (-(D.model.beta * D.Hs (0 + 1)))
  simp only [edgeMajorant, edgeCoefficient] at hb ⊢
  nlinarith

/-- The growing polynomial defect scale which is actually used in marked
`C²` comparison.  In particular, the perimeter factor is not replaced by
the dimensionally false constant `1`. -/
def rowModelDefect (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  CurvatureStabilityL1.l1Modulus (2 * D.kd) (edgeEps D n) (D.Hs n) *
    (2 * D.Hs n) ^ 2 * (1 + D.kstar * (2 * D.Hs n))

theorem edgeEps_le_exp_at_row
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    edgeEps D n ≤ edgeCoefficient D *
      Real.exp (-(D.model.beta * D.Hs n)) := by
  have hb := edgeEps_le_edgeMajorant D n
  have hbeta : 0 < D.model.beta := (D.model.configs n).hbeta0
  have hmono : Real.exp (-(D.model.beta * D.Hs (n + 1))) ≤
      Real.exp (-(D.model.beta * D.Hs n)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [D.separation_step n, D.deltaStep_pos]
  simpa [edgeMajorant, edgeCoefficient] using
    hb.trans (mul_le_mul_of_nonneg_left hmono (edgeCoefficient_nonneg D))

/-- Weighted summability of the honest polynomial marked-comparison scale.
The quarter exponent is the loss from the `L¹` square-root modulus and
absorption of the quadratic/cubic separation factors. -/
theorem summable_weighted_rowModelDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) {K : ℝ}
    (hK : 0 ≤ K)
    (hthreshold : K * Real.exp (-((D.model.beta / 4) * D.deltaStep)) < 1) :
    Summable (PathMetric.WeightedRecursiveDefect.weightedDefect K
      (rowModelDefect D)) := by
  let b := D.model.beta
  let Cm := edgeCoefficient D
  let A := ModelDefectSummable.modelDefectConst
    (2 * D.kd) D.kstar Cm (D.Hs 0) b
  let q := Real.exp (-((b / 4) * D.deltaStep))
  let A0 := A * Real.exp (-((b / 4) * D.Hs 0))
  have hb : 0 < b := by simpa [b] using (D.model.configs 0).hbeta0
  have hCm : 0 ≤ Cm := by simpa [Cm] using edgeCoefficient_nonneg D
  have hA : 0 ≤ A := by
    exact ModelDefectSummable.modelDefectConst_nonneg hCm D.kstar_nonneg
      D.separation_zero_pos hb
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hrow : ∀ n, rowModelDefect D n ≤
      A * Real.exp (-((b / 4) * D.Hs n)) := by
    intro n
    simpa [rowModelDefect, A, b, Cm] using
      (ModelDefectSummable.model_defect_le
        (M := 2 * D.kd) (kb := D.kstar) (Cm := edgeCoefficient D)
        (P0 := D.Hs 0) (beta := D.model.beta)
        (Hs := D.Hs) (eps := edgeEps D) (P := D.Hs)
        hb (mul_nonneg (by norm_num) D.kd_nonneg) (edgeCoefficient_nonneg D) D.kstar_nonneg
        D.separation_zero_pos D.separation_lower
        (fun i => (D.model.separation_pos i).le) (edgeEps_nonneg D)
        (edgeEps_le_exp_at_row D) n)
  have hexp : ∀ n, Real.exp (-((b / 4) * D.Hs n)) ≤
      Real.exp (-((b / 4) * D.Hs 0)) * q ^ n := by
    intro n
    have hle : Real.exp (-((b / 4) * D.Hs n)) ≤
        Real.exp (-((b / 4) * (D.Hs 0 + n * D.deltaStep))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [D.separation_linear n]
    have heq : Real.exp (-((b / 4) * (D.Hs 0 + n * D.deltaStep))) =
        Real.exp (-((b / 4) * D.Hs 0)) * q ^ n := by
      dsimp [q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      ring
    exact hle.trans_eq heq
  have hdgeo : ∀ n, rowModelDefect D n ≤ A0 * q ^ n := by
    intro n
    exact (hrow n).trans <| by
      calc
        A * Real.exp (-((b / 4) * D.Hs n))
            ≤ A * (Real.exp (-((b / 4) * D.Hs 0)) * q ^ n) :=
          mul_le_mul_of_nonneg_left (hexp n) hA
        _ = A0 * q ^ n := by dsimp [A0]; ring
  have hd0 : ∀ n, 0 ≤ rowModelDefect D n := by
    intro n
    unfold rowModelDefect
    have hH := (D.model.separation_pos n).le
    have h2H : 0 ≤ 2 * D.Hs n := mul_nonneg (by norm_num) hH
    have hk : 0 ≤ 1 + D.kstar * (2 * D.Hs n) :=
      add_nonneg zero_le_one (mul_nonneg D.kstar_nonneg h2H)
    exact mul_nonneg
      (mul_nonneg (CurvatureStabilityL1.l1Modulus_nonneg _ _ _) (sq_nonneg _)) hk
  exact PathMetric.WeightedRecursiveDefect.summable_weightedDefect_of_geometric
    hK hA0 hq0 (by simpa [q, b] using hthreshold) hd0 hdgeo

/-- Exact lower speed constant of row `n`. -/
def rowP0 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  interpolationP0 D.kstar D.kd (D.Hs n) (edgeEps D n)

/-- Exact upper speed constant of row `n`. -/
def rowP1 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  costFac D.kstar (D.Hs n) (edgeEps D n)

/-- Exact spatial speed-derivative ceiling of row `n`. -/
def rowG1 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  interpolationG1 D.kstar D.kd (D.Hs n) (edgeEps D n)

/-- Exact mixed derivative ceiling of row `n`. -/
def rowCg (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  interpolationCgFinal D.kstar D.kd (D.Hs n) (edgeEps D n)

/-- Sup curvature mismatch used by the explicit interpolation estimate. -/
def rowDsup (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  CurvatureStabilityL1.l1Modulus (2 * D.kd) (edgeEps D n) (D.Hs n)

/-- The honest defect of row `n`: the full cost of the constructed
interpolation path, including its growing separation factors. -/
def rowDefect (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  interpPathCost D.kstar D.kd (rowDsup D n) (D.Hs n) (edgeEps D n)

/-- Once the explicit interpolation-cost comparison is supplied, weighted
summability of the actual constructed path cost follows from the honest
polynomial scale above.  This isolates the sole remaining analytic estimate;
there is no comparison to the obsolete fixed-scale canonical defect. -/
theorem summable_weighted_rowDefect_of_modelScale
    (D : ConstructedConfiguredSequenceWeighted.Data) {K Ccost : ℝ}
    (hK : 0 ≤ K) (hCcost : 0 ≤ Ccost)
    (hcost : ∀ n, rowDefect D n ≤ Ccost * rowModelDefect D n)
    (hthreshold : K * Real.exp (-((D.model.beta / 4) * D.deltaStep)) < 1) :
    Summable (PathMetric.WeightedRecursiveDefect.weightedDefect K
      (rowDefect D)) := by
  have hs := (summable_weighted_rowModelDefect D hK hthreshold).mul_left Ccost
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · unfold PathMetric.WeightedRecursiveDefect.weightedDefect rowDefect rowDsup
    exact mul_nonneg (pow_nonneg hK n)
      (interpPathCost_nonneg D.kstar_nonneg D.kd_nonneg
        (CurvatureStabilityL1.l1Modulus_nonneg _ _ _)
        (D.model.separation_pos n).le (edgeEps_nonneg D n))
  · unfold PathMetric.WeightedRecursiveDefect.weightedDefect
    exact (mul_le_mul_of_nonneg_left (hcost n) (pow_nonneg hK n)).trans_eq (by ring)

/-- Only the facts not retained by the configured smooth model data: the
actual marked rear endpoint and the comparison of the explicit interpolation
cost with the chosen paper defect. -/
structure Residual
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (B : Data → Data) (Q : ℕ → Data) : Prop where
  rear_endpoint : ∀ n (Phi : ℝ → ℝ → ℝ),
    (∀ u, Phi 0 u = 2 * D.Hs n * u) →
    (∀ u t, HasDerivAt (fun r ↦ Phi r u)
      (InterpolationGauge.gaugeField
        (modelCurvature (D.model.configs n).yu
          (D.model.configs n).yu' (D.Hs n))
        (D.model.configs n).kH D.model.thetaBase (D.Hs n) t (Phi t u)) t) →
    ∀ u, (B (Q (n + 1))).1 u =
      interpCurve (D.model.configs n).kH D.model.thetaBase
        (D.Hs n) (Phi 1 u)

set_option maxHeartbeats 2000000 in
/-- One configured edge produces a defect path in its exact rowwise
variable-speed class.  All configured curvature smoothness is read directly
from `D.model`. -/
theorem exists_approx_defect_path
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {B : Data → Data} {Q : ℕ → Data}
    (R : Residual D B Q)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
      cost Lambda ≤ rowDefect D n + eta ∧
      IsVariableSpeedNormalPath (rowP0 D n) (rowP1 D n) D.kstar
        (rowG1 D n) (rowCg D n) Lambda := by
  let c := D.model.configs n
  let L := D.Hs n
  let k0 := modelCurvature c.yu c.yu' L
  let k1 := c.kH
  let k0' := c.KP'
  let k1' := kHderiv c.Y
    (modelCurvature c.y c.yd (D.Hs (n + 1))) c.sf
  let eps := curvDist k0 k1 L
  let dsup := CurvatureStabilityL1.l1Modulus (2 * D.kd) eps L
  have hL : 0 < L := D.model.separation_pos n
  have hkd : 0 < D.kd := by
    simpa [c, D.model_kd] using c.hkd
  have hk0c : Continuous k0 := by
    simpa [c, L, k0] using c.continuous_KP
  have hk1c : Continuous k1 := by
    simpa [c, k1] using c.continuous_kH
  have hk0'c : Continuous k0' := by
    simpa [c, k0'] using c.continuous_KP'
  have hk1'c : Continuous k1' := by
    simpa [c, k1'] using c.continuous_kHderiv
  have hper0 : Periodic k0 L := by
    simpa [c, L, k0] using c.periodic_KP
  have hper1 : Periodic k1 L := by
    simpa [c, L, k1] using c.periodic_kH
  have htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi := by
    simpa [c, L, k0] using c.integral_KP_eq_pi
  have htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi := by
    simpa [c, L, k1] using c.integral_kH_eq_pi
  have hd0 : ∀ r, HasDerivAt k0 (k0' r) r := by
    intro r
    simpa [c, L, k0, k0'] using c.hd1 r
  have hd1 : ∀ r, HasDerivAt k1 (k1' r) r := by
    intro r
    simpa [c, k1, k1'] using c.hasDerivAt_kH r
  have hkd0 : ∀ r, |k0' r| ≤ D.kd := by
    intro r
    simpa [c, k0', D.model_kd] using c.abs_KP'_le r
  have hkd1 : ∀ r, |k1' r| ≤ D.kd := by
    intro r
    simpa [c, k1', D.model_kd] using c.abs_kHderiv_le r
  have hk0nn : ∀ r, 0 ≤ k0 r := by
    intro r
    simpa [c, L, k0] using c.KP_nonneg r
  have hk1nn : ∀ r, 0 ≤ k1 r := by
    intro r
    simpa [c, k1] using c.kH_nonneg r
  have hk0le : ∀ r, k0 r ≤ D.kstar := by
    intro r
    simpa [c, L, k0, D.model_kstar] using c.KP_le r
  have hk1le : ∀ r, k1 r ≤ D.kstar := by
    intro r
    simpa [c, k1, D.model_kstar] using c.kH_le r
  have hdsup : ∀ r, |k1 r - k0 r| ≤ dsup := by
    intro r
    exact InterpolationPathDistL1.sup_le_of_curvDist hL hkd hper0 hper1
      hd0 hd1 hkd0 hkd1 r
  obtain ⟨Phi, phi1, phi2, hPhi0, hPhid, htrans, _hphi1, _hphi2,
      _hPc, _hphi1c, _hphi2c, hF, hnormal⟩ :=
    exists_smooth_flow_with_residual hk0c hk1c hk0'c hk1'c hper0 hper1
      htot0 htot1 hL hd0 hd1 hk0nn hk1nn hk0le hk1le hkd0 hkd1
  have hQcert : Certificate k0 k1 k0' k1' D.model.thetaBase L Phi :=
    ProfiledInterpolationFields.exists_certificate
      (by simpa [c, L, k0] using D.model_KP_C2 n)
      (by simpa [c, k1] using D.model_kH_C2 n)
      hk0'c hk1'c hd0 hd1 hper0 hper1 htot0 htot1 hPhid hPhi0 htrans
  have hp : ∀ u, (Q n).1 u =
      interpCurve k0 D.model.thetaBase L (2 * L * u) := by
    intro u
    have hLne : 2 * L ≠ 0 := mul_ne_zero (by norm_num) hL.ne'
    calc
      (Q n).1 u = ev (Q n) (2 * L * u) := by
        simp [ev, (hQ n).1, L, hLne]
      _ = TwoCapPairsAssembly.front (D.kappas n) D.model.thetaBase
            (D.Hs n) (2 * L * u) := by rw [(hQ n).2]
      _ = interpCurve k0 D.model.thetaBase L (2 * L * u) := by
        rw [D.model.curvature_eq n]
        rfl
  have hq : ∀ u, (B (Q (n + 1))).1 u =
      interpCurve k1 D.model.thetaBase L (Phi 1 u) := by
    simpa [c, L, k0, k1] using R.rear_endpoint n Phi
      (by simpa [L] using hPhi0) (by simpa [k0, k1, L] using hPhid)
  obtain ⟨Dbounds, _hK, _hK2, _hc1, hm⟩ :=
    exists_bounds_of_curvature_data hQcert hk0c hk1c hk0'c hk1'c
      hper0 hper1 htot0 htot1 hL hd0 hd1 hdsup hkd0 hkd1
      hk0nn hk1nn hk0le hk1le hPhi0 hPhid hnormal hp hq hF
  obtain ⟨Gamma, _hT, _hX, _hetaGamma, _hmGamma, hcost, hvar⟩ :=
    ProfiledInterpolationBounds.exists_path hQcert Dbounds hL
  have hcostEdge : cost Gamma ≤ interpPathCost D.kstar D.kd dsup L eps := by
    calc
      cost Gamma = (∫ t in (0 : ℝ)..1, Dbounds.m t) := hcost
      _ ≤ interpPathCost D.kstar D.kd dsup L eps := Dbounds.hcostIntegral
  refine ⟨Gamma, ?_, ?_⟩
  · calc
      cost Gamma ≤ interpPathCost D.kstar D.kd dsup L eps := hcostEdge
      _ = rowDefect D n := by
        simp [rowDefect, rowDsup, edgeEps, c, L, k0, k1, eps, dsup]
      _ ≤ rowDefect D n + eta := by linarith
  · simpa [rowP0, rowP1, rowG1, rowCg, edgeEps, c, L, k0, k1, eps] using hvar

/-- Family form suitable for rowwise recursive construction. -/
theorem hdefect
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {B : Data → Data} {Q : ℕ → Data}
    (R : Residual D B Q)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n)) :
    ∀ n : ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
        cost Lambda ≤ rowDefect D n + eta ∧
        IsVariableSpeedNormalPath (rowP0 D n) (rowP1 D n) D.kstar
          (rowG1 D n) (rowCg D n) Lambda :=
  fun n eta heta => exists_approx_defect_path D R hQ n eta heta

end ConfiguredApproximateDefectPathRowwise
