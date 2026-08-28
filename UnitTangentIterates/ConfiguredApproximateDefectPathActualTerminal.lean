import UnitTangentIterates.ConfiguredApproximateDefectPathRowwise
import UnitTangentIterates.NormalizedTerminalMarkingComposition
import UnitTangentIterates.MarkedShift
import UnitTangentIterates.GaugeRearEndpointCurvature
import UnitTangentIterates.PeriodicSupNormFunctionalIntegrable
import UnitTangentIterates.SelectedInverseShiftEquivariance
import UnitTangentIterates.RearOwnDriftFundamental
import UnitTangentIterates.MarkedMetricRigidTransport

/-!
# Actual terminals of configured interpolation paths

The interpolation flow does not end in the canonical affine marking of the
physical rear.  This module retains its actual terminal datum and the normalized
`C2` marking relating it to a shifted constant-speed representative.  No
endpoint equality with `SelectedInverseMap.selInv` is asserted.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace ConfiguredApproximateDefectPathActualTerminal

open ModelOrbitDefect CurvatureInterpolation InterpolationEstimate
  InterpolationPathDist InterpolationVariableSpeedConstants
  InterpolationControlledJunctionFinal ProfiledInterpolationFields
  ProfiledInterpolationBoundsConstructor GaugeRearEndpointCurvature
  ConfiguredApproximateDefectPathRowwise
  NormalizedTerminalMarkingComposition

/-- First-jet distortion of the actual interpolation marking. -/
def baseGaugeC1 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  InterpolationGauge.interpolationSmoothC1 D.kstar (D.Hs n) (edgeEps D n)

/-- Second-jet distortion of the actual interpolation marking. -/
def baseGaugeC2 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  InterpolationGauge.interpolationSmoothC2 D.kstar D.kd (D.Hs n) (edgeEps D n)

def baseMarkingE1 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  let ell := 2 * D.Hs n
  ell * (Real.exp (baseGaugeC1 D n) - Real.exp (-(baseGaugeC1 D n)))

def baseMarkingE2 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  let ell := 2 * D.Hs n
  baseGaugeC2 D n * ell ^ 2 * Real.exp (2 * baseGaugeC1 D n)

/-- Exact marked `C2` endpoint modulus retained before the interpolation
source is erased. -/
def baseMarkingBound (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  MarkingDeviationC2.markingC2Bound
    (baseMarkingE1 D n) (baseMarkingE1 D n) (baseMarkingE2 D n)
    (2 * D.Hs n) D.kstar D.kd

/-- Reanchoring the terminal marking at an arbitrary phase replaces the
position defect by the difference of two defects, hence the factor two. -/
def baseTransportMarkingBound
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  MarkingDeviationC2.markingC2Bound
    (2 * baseMarkingE1 D n) (baseMarkingE1 D n) (baseMarkingE2 D n)
    (2 * D.Hs n) D.kstar D.kd

/-- A constant-speed carrier of the configured rear curvature.  Its geometric
identification with the physical selected rear is deliberately separate from
this analytic construction. -/
structure RearCarrier
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) where
  data : Data
  c : ℝ
  dlt : ℝ
  c_pos : 0 < c
  dlt_pos : 0 < dlt
  tube : IsTubeMember c 0 dlt data
  perim_eq : perim data = 2 * D.Hs n
  curve_eq : ev data = interpCurve (D.model.configs n).kH
    D.model.thetaBase (D.Hs n)

/-- The two endpoint curvatures and their spatial derivatives used by the
configured interpolation.  These names keep the analytic source data visible
after the local interpolation proof has returned. -/
def sourceK0 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ → ℝ :=
  modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n)

def sourceK1 (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ → ℝ :=
  (D.model.configs n).kH

def sourceK0' (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ → ℝ :=
  (D.model.configs n).KP'

def sourceK1' (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ → ℝ :=
  kHderiv (D.model.configs n).Y
    (modelCurvature (D.model.configs n).y (D.model.configs n).yd (D.Hs (n + 1)))
    (D.model.configs n).sf

/-- The exact output of one configured interpolation edge.  `terminalBase` is
a shift of the supplied constant-speed carrier chosen so that the marking is
anchored at zero. -/
structure Output
    (D : ConstructedConfiguredSequenceWeighted.Data) (Q : ℕ → Data)
    (n : ℕ) (A : RearCarrier D n) where
  rear : Data
  terminalBase : Data
  baseShift : ℝ
  terminalBase_eq : terminalBase = MarkedShift.shiftData baseShift A.data
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  marking : NormalizedC2Marking terminalBase rear lambda Lambda
  increment : NormalPath (Q n) rear
  increment_time_one : increment.T = 1
  increment_c2 : C2NormalPathData increment
  increment_eta_cont : Continuous (Function.uncurry increment.eta)
  increment_eta1_cont : Continuous (Function.uncurry increment_c2.eta1)
  increment_eta2_cont : Continuous (Function.uncurry increment_c2.eta2)
  increment_functional :
    ControlledJunctionPathFunctionalBounds.FunctionalIntegrable increment.eta
  increment_cost : cost increment ≤ rowDefect D n
  increment_geometry : IsVariableSpeedNormalPath
    (rowP0 D n) (rowP1 D n) D.kstar (rowG1 D n) (rowCg D n) increment
  /-- The actual nonaffine gauge flow and its two spatial jets. -/
  sourcePhi : ℝ → ℝ → ℝ
  sourcePhi1 : ℝ → ℝ → ℝ
  sourcePhi2 : ℝ → ℝ → ℝ
  sourcePhi_space : ∀ t u, HasDerivAt (sourcePhi t) (sourcePhi1 t u) u
  sourcePhi1_space : ∀ t u, HasDerivAt (sourcePhi1 t) (sourcePhi2 t u) u
  sourcePhi_joint : Continuous (Function.uncurry sourcePhi)
  sourcePhi1_joint : Continuous (Function.uncurry sourcePhi1)
  sourcePhi2_joint : Continuous (Function.uncurry sourcePhi2)
  /-- The full qualitative profiled interpolation certificate retained before
  construction of the selected rear family. -/
  sourceCertificate : ProfiledInterpolationFields.Certificate
    (sourceK0 D n) (sourceK1 D n) (sourceK0' D n) (sourceK1' D n)
    D.model.thetaBase (D.Hs n) sourcePhi
  /-- The matching quantitative bounds that produced this exact increment. -/
  sourceBounds : ProfiledInterpolationBounds.Bounds (Q n) rear
    (sourceK0 D n) (sourceK1 D n) (sourceK0' D n) (sourceK1' D n)
    D.model.thetaBase (D.Hs n) D.kstar D.kd (rowDsup D n) (edgeEps D n)
    sourcePhi
  source_density_eq : increment.m = sourceBounds.m
  source_c1_eq : sourceBounds.c1 =
    1 / InterpolationPathDist.costFac D.kstar (D.Hs n) (edgeEps D n)
  source_eta_eq : increment.eta = InterpolationPathDist.pathEta
    (sourceK0 D n) (sourceK1 D n) D.model.thetaBase (D.Hs n) sourcePhi
  endpoint_dist : dist rear terminalBase ≤ baseMarkingBound D n
  transported_endpoint_dist : ∀ q a w, ‖w‖ = 1 →
    dist (MarkedRigid.rigidData a w (MarkedShift.shiftData q rear))
      (MarkedRigid.rigidData a w
        (MarkedShift.shiftData (marking.marking.psi q) terminalBase)) ≤
      baseTransportMarkingBound D n
  rear_curve_deriv : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u
  rear_vel_deriv : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u
  rear_periodic : Periodic (⇑rear.1) 1
  rear_curvature_nonnegative : ∀ u, 0 ≤
    ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im

set_option maxHeartbeats 4000000 in
/-- One configured edge, with the actual flow terminal and exact cost. -/
theorem exists_output
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {Q : ℕ → Data}
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (n : ℕ) (A : RearCarrier D n) : Nonempty (Output D Q n A) := by
  let c := D.model.configs n
  let L := D.Hs n
  let k0 := sourceK0 D n
  let k1 := sourceK1 D n
  let k0' := sourceK0' D n
  let k1' := sourceK1' D n
  let eps := curvDist k0 k1 L
  let dsup := CurvatureStabilityL1.l1Modulus (2 * D.kd) eps L
  have hL : 0 < L := D.model.separation_pos n
  have hkd : 0 < D.kd := by
    simpa [c, D.model_kd] using c.hkd
  have hk0c : Continuous k0 := by simpa [c, L, k0] using c.continuous_KP
  have hk1c : Continuous k1 := by simpa [c, k1] using c.continuous_kH
  have hk0'c : Continuous k0' := by simpa [c, k0'] using c.continuous_KP'
  have hk1'c : Continuous k1' := by simpa [c, k1'] using c.continuous_kHderiv
  have hper0 : Periodic k0 L := by simpa [c, L, k0] using c.periodic_KP
  have hper1 : Periodic k1 L := by simpa [c, L, k1] using c.periodic_kH
  have htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi := by
    simpa [c, L, k0] using c.integral_KP_eq_pi
  have htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi := by
    simpa [c, L, k1] using c.integral_kH_eq_pi
  have hd0 : ∀ r, HasDerivAt k0 (k0' r) r := fun r => by
    simpa [c, L, k0, k0'] using c.hd1 r
  have hd1 : ∀ r, HasDerivAt k1 (k1' r) r := fun r => by
    simpa [c, k1, k1'] using c.hasDerivAt_kH r
  have hkd0 : ∀ r, |k0' r| ≤ D.kd := fun r => by
    simpa [c, k0', D.model_kd] using c.abs_KP'_le r
  have hkd1 : ∀ r, |k1' r| ≤ D.kd := fun r => by
    simpa [c, k1', D.model_kd] using c.abs_kHderiv_le r
  have hk0nn : ∀ r, 0 ≤ k0 r := fun r => by
    simpa [c, L, k0] using c.KP_nonneg r
  have hk1nn : ∀ r, 0 ≤ k1 r := fun r => by
    simpa [c, k1] using c.kH_nonneg r
  have hk0le : ∀ r, k0 r ≤ D.kstar := fun r => by
    simpa [c, L, k0, D.model_kstar] using c.KP_le r
  have hk1le : ∀ r, k1 r ≤ D.kstar := fun r => by
    simpa [c, k1, D.model_kstar] using c.kH_le r
  have hdsup : ∀ r, |k1 r - k0 r| ≤ dsup := fun r =>
    InterpolationPathDistL1.sup_le_of_curvDist hL hkd hper0 hper1
      hd0 hd1 hkd0 hkd1 r
  obtain ⟨Phi, phi1, phi2, hPhi0, hPhid, htrans, hphi1, hphi2,
      hPhic, hphi1c, hphi2c, hb1, hb2, hphi1eq, hphi2eq,
      hPhiJoint, hphi1Joint, hphi2Joint, hnormal⟩ :=
    InterpolationGauge.exists_interpolation_gauge_flow_smooth_specialized_full
      hk0c hk1c hk0'c hk1'c hper0 hper1 htot0 htot1 hL hd0 hd1
      hk0nn hk1nn hk0le hk1le hkd0 hkd1
  have hF : FlowResidual k0 k1 k0' k1' D.model.thetaBase L D.kstar D.kd eps Phi :=
    flowResidual_of_smooth_data hk0c hk1c hk0'c hk1'c D.kstar_nonneg
      D.kd_nonneg hL.le (ConfiguredApproximateDefectPathRowwise.edgeEps_nonneg D n)
      hPhid (fun t u => (hb1 t u).2) hb2 hphi1eq hphi2eq
  let den : ℝ := 2 * L
  let b : ℝ := Phi 1 0 / den
  let psi : ℝ → ℝ := fun u => Phi 1 u / den - b
  let dpsi : ℝ → ℝ := fun u => phi1 1 u / den
  let ddpsi : ℝ → ℝ := fun u => phi2 1 u / den
  let base := MarkedShift.shiftData b A.data
  have hden : 0 < den := by dsimp [den]; positivity
  have hpsid : ∀ u, HasDerivAt psi (dpsi u) u := fun u => by
    dsimp [psi, dpsi]
    exact ((hphi1 1 u).div_const den).sub_const b
  have hdpsid : ∀ u, HasDerivAt dpsi (ddpsi u) u := fun u => by
    dsimp [dpsi, ddpsi]
    exact (hphi2 1 u).div_const den
  have hdpsic : Continuous dpsi := by dsimp [dpsi]; exact (hphi1c 1).div_const den
  have hddpsic : Continuous ddpsi := by dsimp [ddpsi]; exact (hphi2c 1).div_const den
  let C1 := InterpolationGauge.interpolationSmoothC1 D.kstar L eps
  let C2 := InterpolationGauge.interpolationSmoothC2 D.kstar D.kd L eps
  let lo : ℝ := Real.exp (-C1)
  let hi : ℝ := Real.exp C1
  have hlopos : 0 < lo := by dsimp [lo]; positivity
  have hdlo : ∀ u, lo ≤ dpsi u := by
    intro u
    have h := (hb1 1 u).1
    dsimp [lo, dpsi, C1, den]
    norm_num at h
    exact (le_div_iff₀ (by positivity : 0 < 2 * L)).2
      (by simpa [eps, mul_comm] using h)
  have hdhi : ∀ u, dpsi u ≤ hi := by
    intro u
    have h := (hb1 1 u).2
    dsimp [hi, dpsi, C1, den]
    norm_num at h
    exact (div_le_iff₀ (by positivity : 0 < 2 * L)).2
      (by simpa [eps, mul_comm] using h)
  have hA1 : ∀ u, |dpsi u| ≤ hi := by
    intro u
    rw [abs_of_pos (lt_of_lt_of_le hlopos (hdlo u))]
    exact hdhi u
  have hA2 : ∀ u, |ddpsi u| ≤
      (C2 * den ^ 2 * Real.exp (2 * C1)) / den := by
    intro u
    dsimp [ddpsi]
    rw [abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_right _ hden.le
    have h := hb2 1 u
    norm_num at h
    simpa [C1, C2, den] using h
  have hbase1 : ∀ u, HasDerivAt (⇑base.1) (base.2.1 u) u :=
    (MarkedShift.isTubeMember_shiftData A.tube b).hasDerivAt_curve
  have hbase2 : ∀ u, HasDerivAt (⇑base.2.1) (base.2.2 u) u :=
    (MarkedShift.isTubeMember_shiftData A.tube b).hasDerivAt_vel
  obtain ⟨rear, hrearPos, hrearVel, hrearAcc, hrear1, hrear2⟩ :=
    MarkedDataOfMarking.exists_data_of_marking hbase1 hbase2 hpsid hdpsid
      hdpsic hddpsic hA1 hA2
  have hbasePosition : ∀ u, base.1 (psi u) = A.data.1 (Phi 1 u / den) := by
    intro u
    dsimp [base, psi, b]
    apply congrArg (fun x : ℝ => A.data.1 x)
    ring
  have hrearPosition : ∀ u, rear.1 u =
      interpCurve k1 D.model.thetaBase L (Phi 1 u) := by
    intro u
    rw [hrearPos u, hbasePosition u]
    have hperA : perim A.data = den := by simpa [den, L] using A.perim_eq
    calc
      A.data.1 (Phi 1 u / den) = ev A.data (Phi 1 u) := by
        simp [ev, hperA, hden.ne']
      _ = interpCurve k1 D.model.thetaBase L (Phi 1 u) := by
        rw [A.curve_eq]
        rfl
  have hp : ∀ u, (Q n).1 u =
      interpCurve k0 D.model.thetaBase L (2 * L * u) := by
    intro u
    have hne : 2 * L ≠ 0 := by positivity
    calc
      (Q n).1 u = ev (Q n) (2 * L * u) := by simp [ev, (hQ n).1, L, hne]
      _ = TwoCapPairsAssembly.front (D.kappas n) D.model.thetaBase
          (D.Hs n) (2 * L * u) := by rw [(hQ n).2]
      _ = interpCurve k0 D.model.thetaBase L (2 * L * u) := by
        rw [D.model.curvature_eq n]
        rfl
  have hQcert : Certificate k0 k1 k0' k1' D.model.thetaBase L Phi :=
    ProfiledInterpolationFields.exists_certificate
      (by simpa [c, L, k0] using D.model_KP_C2 n)
      (by simpa [c, k1] using D.model_kH_C2 n)
      hk0'c hk1'c hd0 hd1 hper0 hper1 htot0 htot1 hPhid hPhi0 htrans
  have hDbounds :=
    exists_bounds_of_curvature_data hQcert hk0c hk1c hk0'c hk1'c
      hper0 hper1 htot0 htot1 hL hd0 hd1 hdsup hkd0 hkd1
      hk0nn hk1nn hk0le hk1le hPhi0 hPhid hnormal hp hrearPosition hF
  let Dbounds := Classical.choose hDbounds
  have hDboundsC1 := (Classical.choose_spec hDbounds).2.2.1
  obtain ⟨Gamma, hGammaT, -, hGammaEta, hGammaM, hcost, hvar⟩ :=
    ProfiledInterpolationBounds.exists_path hQcert Dbounds hL
  let Ceta : PathEtaSpatialC2Certificate
      k0 k1 D.model.thetaBase L Phi :=
    pathEtaSpatialC2Certificate_of_smoothPhi
      (theta0 := D.model.thetaBase)
    hk0c hk1c hk0'c hk1'c hper0 hper1 htot0 htot1 hd0 hd1 htrans
    hphi1 hphi2 hphi2c
  have hGammaEtaEq : Gamma.eta = pathEta k0 k1 D.model.thetaBase L Phi := by
    funext t u
    simpa [ProfiledInterpolationFields.en, ProfiledInterpolationFields.PhiB,
      pathEta] using hGammaEta t u
  let GammaC2 : C2NormalPathData Gamma :=
    c2NormalPathData_of_smoothPathEta
      (k0' := k0') (k1' := k1') (phi1 := phi1) (phi2 := phi2)
      Ceta hGammaEtaEq
  have hGammaEtaCont : Continuous (Function.uncurry Gamma.eta) := by
    rw [hGammaEtaEq]
    exact continuous_uncurry_pathEta_of_jointPhi hk0c hk1c hPhiJoint
  have hGammaEta1Cont : Continuous (Function.uncurry GammaC2.eta1) := by
    simpa [GammaC2, c2NormalPathData_of_smoothPathEta, Ceta,
      pathEtaSpatialC2Certificate_of_smoothPhi] using
      (continuous_uncurry_smoothPathEta1 (theta0 := D.model.thetaBase) (L := L)
        hk0c hk1c hPhiJoint hphi1Joint)
  have hGammaEta2Cont : Continuous (Function.uncurry GammaC2.eta2) := by
    simpa [GammaC2, c2NormalPathData_of_smoothPathEta, Ceta,
      pathEtaSpatialC2Certificate_of_smoothPhi] using
      (continuous_uncurry_smoothPathEta2 (theta0 := D.model.thetaBase) (L := L)
        hk0c hk1c hk0'c hk1'c
        hPhiJoint hphi1Joint hphi2Joint)
  let GammaFunctional :=
    PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      GammaC2 hGammaEtaCont hGammaEta1Cont hGammaEta2Cont
  have hcostEdge : cost Gamma ≤ interpPathCost D.kstar D.kd dsup L eps := by
    calc
      cost Gamma = (∫ t in (0 : ℝ)..1, Dbounds.m t) := hcost
      _ ≤ interpPathCost D.kstar D.kd dsup L eps := Dbounds.hcostIntegral
  have htranslate : ∀ u, psi (u + 1) = psi u + 1 := by
    intro u
    dsimp [psi, den]
    rw [htrans 1 u]
    field_simp [hL.ne']
    ring
  have hvelocity : ∀ u, rear.2.1 u = (dpsi u : ℂ) * base.2.1 (psi u) := hrearVel
  let R : GaugeRearFamilyVariableTerminal.OrientedReparametrization
      base rear lo hi :=
    { psi := psi
      dpsi := dpsi
      position := hrearPos
      velocity := hvelocity
      translate := htranslate
      lower := hdlo
      upper := hdhi }
  let N : NormalizedC2Marking base rear lo hi :=
    { lambda_pos := hlopos
      marking := R
      ddpsi := ddpsi
      psi_deriv := hpsid
      dpsi_deriv := hdpsid
      ddpsi_cont := hddpsic
      psi_zero := by dsimp [R, psi, b]; ring }
  have hcurv : ∀ u, 0 ≤
      ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im := by
    apply GaugeRearEndpointCurvature.orientedCurvature_nonnegative
      (Y := interpCurve k1 D.model.thetaBase L)
      (α := tangentAngle k1 D.model.thetaBase) (k := k1)
      (phi := fun u => Phi 1 u) (phi1 := fun u => phi1 1 u)
      (phi2 := fun u => phi2 1 u)
    · exact fun s => by
        simpa [SelectedInverseCarrier.tau_eq_exp] using
          (hasDerivAt_interpCurve (kappa := k1) (θ₀ := D.model.thetaBase)
            (L := L) hk1c s)
    · exact fun s => hasDerivAt_tangentAngle hk1c s
    · exact hrearPosition
    · exact hrear1
    · exact hrear2
    · exact hphi1 1
    · exact hphi2 1
    · intro u
      exact (lt_of_lt_of_le (mul_pos (by positivity : 0 < 2 * L)
        (Real.exp_pos (-C1))) (by simpa [C1] using (hb1 1 u).1)).le
    · exact hk1nn
  have hbaseTube : IsTubeMember A.c 0 A.dlt base :=
    MarkedShift.isTubeMember_shiftData A.tube b
  have hbasePerim : perim base = den := by
    simpa [den, L] using
      (SelectedInverseShiftEquivariance.perim_shiftData A.tube b).trans A.perim_eq
  let q0 : ℝ := Phi 1 0
  let Theta : ℝ → ℝ := fun s => tangentAngle k1 D.model.thetaBase (s + q0)
  let kbase : ℝ → ℝ := fun s => k1 (s + q0)
  have hevbase : ∀ s, HasDerivAt (ev base)
      (Complex.exp (Complex.I * (Theta s : ℂ))) s := by
    intro s
    have hinner : HasDerivAt (fun x : ℝ => x + q0) 1 s := by
      simpa using (hasDerivAt_id s).add_const q0
    have hevEq : ev base s = interpCurve k1 D.model.thetaBase L (s + q0) := by
      rw [SelectedInverseShiftEquivariance.ev_shiftData A.tube
        (by rw [A.perim_eq]; positivity) b s, A.curve_eq]
      congr 2
      rw [A.perim_eq]
      dsimp [q0, b, den, L]
      field_simp [show D.Hs n ≠ 0 by simpa [L] using hL.ne']
    have hfun : ev base = fun x => interpCurve k1 D.model.thetaBase L (x + q0) := by
      funext x
      rw [SelectedInverseShiftEquivariance.ev_shiftData A.tube
        (by rw [A.perim_eq]; positivity) b x, A.curve_eq]
      congr 2
      rw [A.perim_eq]
      dsimp [q0, b, den, L]
      field_simp [show D.Hs n ≠ 0 by simpa [L] using hL.ne']
    rw [hfun]
    simpa [Theta, Function.comp_def, SelectedInverseCarrier.tau_eq_exp] using
      (hasDerivAt_interpCurve (kappa := k1) (θ₀ := D.model.thetaBase)
        (L := L) hk1c (s + q0)).scomp s hinner
  have hThetad : ∀ s, HasDerivAt Theta (kbase s) s := by
    intro s
    have hinner : HasDerivAt (fun x : ℝ => x + q0) 1 s := by
      simpa using (hasDerivAt_id s).add_const q0
    simpa [Theta, kbase, Function.comp_def] using
      (hasDerivAt_tangentAngle hk1c (s + q0)).scomp s hinner
  have hkbase : ∀ s, |kbase s| ≤ D.kstar := by
    intro s
    rw [abs_of_nonneg (hk1nn (s + q0))]
    exact hk1le (s + q0)
  have hkbaseLip : ∀ s t, |kbase s - kbase t| ≤ D.kd * |s - t| := by
    intro s t
    have hmvt := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := k1) (f' := k1')
      (fun x _ => (hd1 x).hasDerivWithinAt)
      (fun x _ => by simpa [Real.norm_eq_abs] using hkd1 x)
      (Set.mem_univ (s + q0)) (Set.mem_univ (t + q0))
    simpa [kbase, Real.norm_eq_abs, abs_sub_comm] using hmvt
  have heps0 : 0 ≤ eps := by
    simpa [eps, edgeEps, c, k0, k1] using edgeEps_nonneg D n
  have hC10 : 0 ≤ C1 := by
    dsimp [C1, InterpolationGauge.interpolationSmoothC1]
    exact mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg)
      (mul_nonneg (mul_nonneg (by norm_num) hL.le) heps0)
  have hE1 : ∀ u, |den * dpsi u - den| ≤
      den * (Real.exp C1 - Real.exp (-C1)) := by
    intro u
    have hlo := (hb1 1 u).1
    have hhi := (hb1 1 u).2
    have helo : Real.exp (-C1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hehi : 1 ≤ Real.exp C1 := Real.one_le_exp hC10
    have hd : den * dpsi u = phi1 1 u := by
      dsimp [dpsi]
      field_simp [hden.ne']
    rw [abs_le]
    constructor
    · rw [hd]
      norm_num at hlo hhi
      nlinarith
    · rw [hd]
      norm_num at hlo hhi
      nlinarith
  let f : ℝ → ℝ := fun u => den * psi u - den * u
  have hfderiv : ∀ u, HasDerivAt f (den * dpsi u - den) u := by
    intro u
    simpa [f] using ((hpsid u).const_mul den).sub ((hasDerivAt_id u).const_mul den)
  have hfperiodic : Function.Periodic f 1 := by
    intro u
    dsimp [f]
    rw [htranslate u]
    ring
  have hfzero : f 0 = 0 := by dsimp [f, psi, b]; ring
  have hE0 : ∀ u, |den * psi u - den * u| ≤
      den * (Real.exp C1 - Real.exp (-C1)) := by
    intro u
    obtain ⟨x, hx, hux⟩ : ∃ x ∈ Set.Icc (0 : ℝ) 1, f u = f x := by
      have hu : f u ∈ Set.range f := ⟨u, rfl⟩
      rw [← hfperiodic.image_Icc one_pos 0] at hu
      obtain ⟨x, hx, hxu⟩ := hu
      exact ⟨x, by simpa using hx, hxu.symm⟩
    rw [show den * psi u - den * u = f u by rfl, hux]
    exact RearOwnDriftFundamental.abs_le_of_deriv_le_on_Icc
      zero_le_one hfderiv hfzero hE1 hx |>.trans_eq (one_mul _)
  have hE2 : ∀ u, |den * ddpsi u| ≤
      C2 * den ^ 2 * Real.exp (2 * C1) := by
    intro u
    have h := hb2 1 u
    norm_num at h
    have hd : den * ddpsi u = phi2 1 u := by
      dsimp [ddpsi]
      field_simp [hden.ne']
    rw [hd]
    simpa [C1, C2, den] using h
  have hendpoint : dist rear base ≤ baseMarkingBound D n := by
    apply MarkingDeviationC2.dist_le_of_marking_defect_c2
      (phi := fun u => den * psi u) (phi1 := fun u => den * dpsi u)
      (phi2 := fun u => den * ddpsi u) (Θ := Theta) (k := kbase)
      A.c_pos hbaseTube hbasePerim hevbase hThetad hkbase hkbaseLip
    · intro u
      rw [hrearPos u, ev, hbasePerim]
      congr 1
      field_simp [hden.ne']
    · exact hrear1
    · exact hrear2
    · intro u
      simpa using (hpsid u).const_mul den
    · intro u
      simpa using (hdpsid u).const_mul den
    · simpa [baseMarkingBound, baseMarkingE1, baseMarkingE2,
        baseGaugeC1, baseGaugeC2, C1, C2, den, L] using hE0
    · simpa [baseMarkingBound, baseMarkingE1, baseMarkingE2,
        baseGaugeC1, baseGaugeC2, C1, C2, den, L] using hE1
    · simpa [baseMarkingBound, baseMarkingE1, baseMarkingE2,
        baseGaugeC1, baseGaugeC2, C1, C2, den, L] using hE2
  have hendpointPhase : ∀ q, dist (MarkedShift.shiftData q rear)
      (MarkedShift.shiftData (psi q) base) ≤ baseTransportMarkingBound D n := by
    intro q
    let rearq := MarkedShift.shiftData q rear
    let baseq := MarkedShift.shiftData (psi q) base
    let phiq : ℝ → ℝ := fun u => den * (psi (u + q) - psi q)
    let phiq1 : ℝ → ℝ := fun u => den * dpsi (u + q)
    let phiq2 : ℝ → ℝ := fun u => den * ddpsi (u + q)
    let Thetaq : ℝ → ℝ := fun s => Theta (s + psi q * den)
    let kbaseq : ℝ → ℝ := fun s => kbase (s + psi q * den)
    have hbaseqTube : IsTubeMember A.c 0 A.dlt baseq :=
      MarkedShift.isTubeMember_shiftData hbaseTube (psi q)
    have hbaseqPerim : perim baseq = den := by
      simpa [baseq, hbasePerim] using
        SelectedInverseShiftEquivariance.perim_shiftData hbaseTube (psi q)
    have hevbaseq : ∀ s, HasDerivAt (ev baseq)
        (Complex.exp (Complex.I * (Thetaq s : ℂ))) s := by
      intro s
      have hi : HasDerivAt (fun x : ℝ => x + psi q * den) 1 s := by
        simpa using (hasDerivAt_id s).add_const (psi q * den)
      have heq : ev baseq = fun x => ev base (x + psi q * den) := by
        funext x
        simpa [baseq, hbasePerim] using
          SelectedInverseShiftEquivariance.ev_shiftData hbaseTube
            (by rw [hbasePerim]; exact hden.ne')
            (psi q) x
      rw [heq]
      simpa [Thetaq, Function.comp_def] using
        (hevbase (s + psi q * den)).scomp s hi
    have hThetaqd : ∀ s, HasDerivAt Thetaq (kbaseq s) s := by
      intro s
      have hi : HasDerivAt (fun x : ℝ => x + psi q * den) 1 s := by
        simpa using (hasDerivAt_id s).add_const (psi q * den)
      simpa [Thetaq, kbaseq, Function.comp_def] using
        (hThetad (s + psi q * den)).scomp s hi
    have hkbaseq : ∀ s, |kbaseq s| ≤ D.kstar := fun s => by
      simpa [kbaseq] using hkbase (s + psi q * den)
    have hkbaseqLip : ∀ s t, |kbaseq s - kbaseq t| ≤
        D.kd * |s - t| := by
      intro s t
      simpa [kbaseq] using hkbaseLip (s + psi q * den) (t + psi q * den)
    have hrearq1 : ∀ u, HasDerivAt (⇑rearq.1) (rearq.2.1 u) u := by
      intro u
      have hi : HasDerivAt (fun x : ℝ => x + q) 1 u := by
        simpa using (hasDerivAt_id u).add_const q
      simpa [rearq, Function.comp_def] using (hrear1 (u + q)).scomp u hi
    have hrearq2 : ∀ u, HasDerivAt (⇑rearq.2.1) (rearq.2.2 u) u := by
      intro u
      have hi : HasDerivAt (fun x : ℝ => x + q) 1 u := by
        simpa using (hasDerivAt_id u).add_const q
      simpa [rearq, Function.comp_def] using (hrear2 (u + q)).scomp u hi
    have hphiq : ∀ u, HasDerivAt phiq (phiq1 u) u := by
      intro u
      have hi : HasDerivAt (fun x : ℝ => x + q) 1 u := by
        simpa using (hasDerivAt_id u).add_const q
      simpa [phiq, phiq1, Function.comp_def] using
        (((hpsid (u + q)).scomp u hi).sub_const (psi q)).const_mul den
    have hphiq1 : ∀ u, HasDerivAt phiq1 (phiq2 u) u := by
      intro u
      have hi : HasDerivAt (fun x : ℝ => x + q) 1 u := by
        simpa using (hasDerivAt_id u).add_const q
      simpa [phiq1, phiq2, Function.comp_def] using
        ((hdpsid (u + q)).scomp u hi).const_mul den
    have hposition : ∀ u, rearq.1 u = ev baseq (phiq u) := by
      intro u
      rw [show rearq.1 u = rear.1 (u + q) by rfl, hrearPos]
      rw [SelectedInverseShiftEquivariance.ev_shiftData hbaseTube
          (by rw [hbasePerim]; exact hden.ne'),
        ev, hbasePerim]
      congr 1
      dsimp [phiq]
      field_simp [hden.ne']
      ring
    have hE0q : ∀ u, |phiq u - den * u| ≤
        2 * (den * (Real.exp C1 - Real.exp (-C1))) := by
      intro u
      have hu := hE0 (u + q)
      have hq := hE0 q
      have htri : |(den * psi (u + q) - den * (u + q)) -
          (den * psi q - den * q)| ≤
          |den * psi (u + q) - den * (u + q)| +
            |den * psi q - den * q| := abs_sub _ _
      dsimp [phiq]
      rw [show den * (psi (u + q) - psi q) - den * u =
        (den * psi (u + q) - den * (u + q)) -
          (den * psi q - den * q) by ring]
      linarith
    have hE1q : ∀ u, |phiq1 u - den| ≤
        den * (Real.exp C1 - Real.exp (-C1)) := by
      intro u
      simpa [phiq1] using hE1 (u + q)
    have hE2q : ∀ u, |phiq2 u| ≤
        C2 * den ^ 2 * Real.exp (2 * C1) := by
      intro u
      simpa [phiq2] using hE2 (u + q)
    apply MarkingDeviationC2.dist_le_of_marking_defect_c2
      (phi := phiq) (phi1 := phiq1) (phi2 := phiq2)
      (Θ := Thetaq) (k := kbaseq)
      A.c_pos hbaseqTube hbaseqPerim hevbaseq hThetaqd hkbaseq hkbaseqLip
    · exact hposition
    · exact hrearq1
    · exact hrearq2
    · exact hphiq
    · exact hphiq1
    · simpa [baseTransportMarkingBound, baseMarkingE1, baseMarkingE2,
        baseGaugeC1, baseGaugeC2, C1, C2, den, L] using hE0q
    · simpa [baseTransportMarkingBound, baseMarkingE1, baseMarkingE2,
        baseGaugeC1, baseGaugeC2, C1, C2, den, L] using hE1q
    · simpa [baseTransportMarkingBound, baseMarkingE1, baseMarkingE2,
        baseGaugeC1, baseGaugeC2, C1, C2, den, L] using hE2q
  have hendpointTransport : ∀ q a w, ‖w‖ = 1 →
      dist (MarkedRigid.rigidData a w (MarkedShift.shiftData q rear))
        (MarkedRigid.rigidData a w (MarkedShift.shiftData (N.marking.psi q) base)) ≤
        baseTransportMarkingBound D n := by
    intro q a w hw
    rw [MarkedRigid.dist_rigidData hw]
    simpa [N, R] using hendpointPhase q
  refine ⟨{
    rear := rear
    terminalBase := base
    baseShift := b
    terminalBase_eq := rfl
    lambda := lo
    Lambda := hi
    lambda_pos := hlopos
    marking := N
    increment := Gamma
    increment_time_one := hGammaT
    increment_c2 := GammaC2
    increment_eta_cont := hGammaEtaCont
    increment_eta1_cont := hGammaEta1Cont
    increment_eta2_cont := hGammaEta2Cont
    increment_functional := GammaFunctional
    increment_cost := ?_
    increment_geometry := ?_
    sourcePhi := Phi
    sourcePhi1 := phi1
    sourcePhi2 := phi2
    sourcePhi_space := hphi1
    sourcePhi1_space := hphi2
    sourcePhi_joint := hPhiJoint
    sourcePhi1_joint := hphi1Joint
    sourcePhi2_joint := hphi2Joint
    sourceCertificate := by
      simpa [k0, k1, k0', k1', L] using hQcert
    sourceBounds := by
      simpa [k0, k1, k0', k1', L, dsup, eps, rowDsup, edgeEps] using Dbounds
    source_density_eq := by
      simpa [k0, k1, k0', k1', L, dsup, eps, rowDsup, edgeEps] using hGammaM
    source_c1_eq := by
      simpa [Dbounds, L, k0, k1, eps, edgeEps] using hDboundsC1
    source_eta_eq := by
      simpa [k0, k1, L] using hGammaEtaEq
    endpoint_dist := hendpoint
    transported_endpoint_dist := hendpointTransport
    rear_curve_deriv := hrear1
    rear_vel_deriv := hrear2
    rear_periodic := by
      intro u
      rw [N.marking.position (u + 1), N.marking.translate u,
        (MarkedShift.isTubeMember_shiftData A.tube b).periodic,
        ← N.marking.position u]
    rear_curvature_nonnegative := hcurv }⟩
  · simpa [rowDefect, rowDsup, edgeEps, c, L, k0, k1, eps, dsup] using hcostEdge
  · simpa [rowP0, rowP1, rowG1, rowCg, edgeEps, c, L, k0, k1, eps] using hvar

end ConfiguredApproximateDefectPathActualTerminal
