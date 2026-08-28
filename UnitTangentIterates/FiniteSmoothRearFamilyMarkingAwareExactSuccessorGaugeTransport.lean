import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
import UnitTangentIterates.RearOwnFrameGaugeFlowReanchoring

/-! Generic gauge transport of an exact C1 successor pretransport. -/

noncomputable section

open Function RearTrack RearOwnArclength RearFamilyFrame RearOwnHigherRegularity
  MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax kap : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {S : ExactSelected A (kap := kap)}

variable (R : PreTransport S)

abbrev xi : ℝ → ℝ → ℝ := frameTangential R.Ydot S.psi
def qRate (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) (t : ℝ) : ℝ :=
  -xi R t (G.q t)
abbrev shiftedRear (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) :=
  TimeDependentSpatialReanchoring.shift S.rear G.q
abbrev shiftedPsi (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) :=
  RearOwnFrameGaugeFlowReanchoring.shiftedPsi S.psi G.q
abbrev shiftedKappa (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) :=
  TimeDependentSpatialReanchoring.shift S.kappa G.q
abbrev shiftedSource (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) :=
  TimeDependentSpatialReanchoring.shift S.source G.q
abbrev shiftedCurvatureSpatial
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) :=
  TimeDependentSpatialReanchoring.shift S.curvatureSpatial G.q
def Ydot (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) :=
  RearOwnFrameGaugeFlowReanchoring.shiftedYdot R.Ydot S.psi (xi R) G.q
def alphaT (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) := fun t x =>
  TimeDependentSpatialReanchoring.shift R.alphaT G.q t x +
    qRate R G t * shiftedKappa R G t x
def kT (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) := fun t x =>
  TimeDependentSpatialReanchoring.shift R.kT G.q t x +
    qRate R G t * shiftedCurvatureSpatial R G t x
abbrev gS (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) :=
  TimeDependentSpatialReanchoring.shift R.gS G.q

structure ShiftedTransport
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)) where
  Ydot_continuous : Continuous (uncurry (Ydot R G))
  gS_continuous : Continuous (uncurry (gS R G))
  rear_time : ∀ t x, HasDerivAt (fun r => shiftedRear R G r x) (Ydot R G t x) t
  anchor_flow : ∀ t, HasDerivAt (fun _ : ℝ => (0 : ℝ))
    (-frameTangential (Ydot R G) (shiftedPsi R G) t 0) t
  jacobi : ∀ t x, HasDerivAt (frameNormal (Ydot R G) (shiftedPsi R G) t)
    (shiftedSource R G t x - frameNormal (Ydot R G) (shiftedPsi R G) t x) x
  gS_deriv : ∀ t x, HasDerivAt (shiftedSource R G t) (gS R G t x) x
  curvatureSpatial_deriv : ∀ t x, HasDerivAt (shiftedKappa R G t)
    (shiftedCurvatureSpatial R G t x) x
  rear_angle_time_deriv : ∀ t x, HasDerivAt
    (fun r => shiftedPsi R G r x) (alphaT R G t x) t
  rear_curvature_time_deriv : ∀ t x, HasDerivAt
    (fun r => shiftedKappa R G r x) (kT R G t x) t
  rear_angle_time_continuous : Continuous (uncurry (alphaT R G))
  rear_curvature_time_continuous : Continuous (uncurry (kT R G))
  rear_angle_time_spatial : ∀ t x, HasDerivAt (alphaT R G t) (kT R G t x) x
  mixed : ∀ t x, ∃ Z : ℂ,
    HasDerivAt (fun r => Complex.exp (Complex.I * (shiftedPsi R G r x : ℂ))) Z t ∧
    HasDerivAt (fun y =>
      (frameTangential (Ydot R G) (shiftedPsi R G) t y : ℂ) *
          Complex.exp (Complex.I * (shiftedPsi R G t y : ℂ)) +
      (frameNormal (Ydot R G) (shiftedPsi R G) t y : ℂ) *
          (Complex.I * Complex.exp (Complex.I * (shiftedPsi R G t y : ℂ)))) Z x

section Proofs

variable (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))

theorem rear_time (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) :
    HasDerivAt (fun r => shiftedRear R G r x) (Ydot R G t x) t := by
  have hcomp := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    (S.rear_contDiff.differentiable (by norm_num))
    ((hasDerivAt_const t x).add (G.ode t))
  have hpt : partialTime S.rear t (x + G.q t) = R.Ydot t (x + G.q t) :=
    (hasDerivAt_partialTime (S.rear_contDiff.differentiable (by norm_num)) t _).unique
      (R.rear_time t _)
  have hpx : partialArc S.rear t (x + G.q t) =
      Complex.exp (Complex.I * (S.psi t (x + G.q t) : ℂ)) :=
    (hasDerivAt_partialArc (S.rear_contDiff.differentiable (by norm_num)) t _).unique
      (by
        simpa [RearOwnArclength.rearOwnTangent] using
          hasDerivAt_rearOwn_space
            (MarkingAwareSource.successorFrontCore A).front_frenet
            (MarkingAwareSource.successorFrontCore A).angle_frenet S.steering S.sf_deriv
            (fun a s => by
              exact ne_of_gt (SelectedPathData.cos_steering_pos
                hkap0 hkap1
                (S.strip_nonnegative a) (S.strip_le a) s)) t _)
  simp only [Pi.add_apply, zero_add] at hcomp
  rw [hpt, hpx] at hcomp
  convert hcomp using 1 <;>
    simp [shiftedRear, Ydot, RearOwnFrameGaugeFlowReanchoring.shiftedYdot,
      shiftedPsi, xi, qRate, TimeDependentSpatialReanchoring.shift,
      Complex.real_smul]

theorem rear_angle_time_deriv (t x : ℝ) : HasDerivAt
    (fun r => shiftedPsi R G r x) (alphaT R G t x) t := by
  have hcomp := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    (S.psi_contDiff.differentiable (by norm_num))
    ((hasDerivAt_const t x).add (G.ode t))
  have hpt : partialTime S.psi t (x + G.q t) = R.alphaT t (x + G.q t) :=
    (hasDerivAt_partialTime (S.psi_contDiff.differentiable (by norm_num)) t _).unique
      (R.rear_angle_time_deriv t _)
  have hpx : partialArc S.psi t (x + G.q t) = S.kappa t (x + G.q t) :=
    (hasDerivAt_partialArc (S.psi_contDiff.differentiable (by norm_num)) t _).unique
      (S.psi_spatial t _)
  simp only [Pi.add_apply, zero_add] at hcomp
  rw [hpt, hpx] at hcomp
  convert hcomp using 1 <;>
    simp [shiftedPsi, alphaT, shiftedKappa, qRate, xi,
      RearOwnFrameGaugeFlowReanchoring.shiftedPsi,
      TimeDependentSpatialReanchoring.shift, smul_eq_mul]

theorem rear_curvature_time_deriv
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) : HasDerivAt
    (fun r => shiftedKappa R G r x) (kT R G t x) t := by
  have hkC := S.kappa_contDiff hkap0 hkap1
  have hcomp := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    (hkC.differentiable (by norm_num)) ((hasDerivAt_const t x).add (G.ode t))
  have hpt : partialTime S.kappa t (x + G.q t) = R.kT t (x + G.q t) :=
    (hasDerivAt_partialTime (hkC.differentiable (by norm_num)) t _).unique
      (R.rear_curvature_time_deriv t _)
  have hpx : partialArc S.kappa t (x + G.q t) =
      S.curvatureSpatial t (x + G.q t) :=
    (hasDerivAt_partialArc (hkC.differentiable (by norm_num)) t _).unique
      (R.curvatureSpatial_deriv t _)
  simp only [Pi.add_apply, zero_add] at hcomp
  rw [hpt, hpx] at hcomp
  convert hcomp using 1 <;>
    simp [shiftedKappa, shiftedCurvatureSpatial, kT, qRate, xi,
      TimeDependentSpatialReanchoring.shift, smul_eq_mul]

theorem curvatureSpatial_deriv (t x : ℝ) : HasDerivAt
    (shiftedKappa R G t) (shiftedCurvatureSpatial R G t x) x :=
  TimeDependentSpatialReanchoring.shift_spatial_deriv R.curvatureSpatial_deriv t x

theorem gS_deriv (t x : ℝ) :
    HasDerivAt (shiftedSource R G t) (gS R G t x) x :=
  TimeDependentSpatialReanchoring.shift_spatial_deriv R.gS_deriv t x

theorem rear_angle_time_spatial (t x : ℝ) :
    HasDerivAt (alphaT R G t) (kT R G t x) x := by
  have h1 := TimeDependentSpatialReanchoring.shift_spatial_deriv
    (q := G.q) R.rear_angle_time_spatial t x
  have h2 := (TimeDependentSpatialReanchoring.shift_spatial_deriv
    (q := G.q) R.curvatureSpatial_deriv t x).const_mul (qRate R G t)
  simpa [alphaT, kT, shiftedKappa, shiftedCurvatureSpatial,
    TimeDependentSpatialReanchoring.shift] using h1.add h2

theorem jacobi (t x : ℝ) : HasDerivAt
    (frameNormal (Ydot R G) (shiftedPsi R G) t)
    (shiftedSource R G t x - frameNormal (Ydot R G) (shiftedPsi R G) t x) x := by
  have h := TimeDependentSpatialReanchoring.shift_spatial_deriv
    (q := G.q) R.jacobi t x
  have heq : frameNormal (Ydot R G) (shiftedPsi R G) t =
      TimeDependentSpatialReanchoring.shift (frameNormal R.Ydot S.psi) G.q t := by
    funext y
    exact RearOwnFrameGaugeFlowReanchoring.frameNormal_shiftedYdot
      R.Ydot S.psi G.q t y
  rw [heq]
  apply h.congr_deriv
  simp [shiftedSource, Ydot, shiftedPsi,
    RearOwnFrameGaugeFlowReanchoring.frameNormal_shiftedYdot,
    TimeDependentSpatialReanchoring.shift]

theorem anchor_flow (t : ℝ) : HasDerivAt (fun _ : ℝ => (0 : ℝ))
    (-frameTangential (Ydot R G) (shiftedPsi R G) t 0) t := by
  have hz := RearOwnFrameGaugeFlowReanchoring.frameTangential_shiftedYdot_zero
    R.Ydot S.psi G.q t
  unfold Ydot shiftedPsi
  rw [hz]
  simpa using hasDerivAt_const t (0 : ℝ)

theorem rearAngleTime_continuous : Continuous (uncurry (alphaT R G)) := by
  have hC := TimeDependentSpatialReanchoring.shift_contDiff S.psi_contDiff G.contDiff
  have heq : alphaT R G = partialTime (shiftedPsi R G) := by
    funext t x
    exact (rear_angle_time_deriv R G t x).unique
      (hasDerivAt_partialTime (hC.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) hC).continuous

theorem rearCurvatureTime_continuous
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) : Continuous (uncurry (kT R G)) := by
  have hC := TimeDependentSpatialReanchoring.shift_contDiff
    (S.kappa_contDiff hkap0 hkap1) G.contDiff
  have heq : kT R G = partialTime (shiftedKappa R G) := by
    funext t x
    exact (rear_curvature_time_deriv R G hkap0 hkap1 t x).unique
      (hasDerivAt_partialTime (hC.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) hC).continuous

theorem Ydot_continuous (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    Continuous (uncurry (Ydot R G)) := by
  have hC := TimeDependentSpatialReanchoring.shift_contDiff S.rear_contDiff G.contDiff
  have heq : Ydot R G = partialTime (shiftedRear R G) := by
    funext t x
    exact (rear_time R G hkap0 hkap1 t x).unique
      (hasDerivAt_partialTime (hC.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) hC).continuous

theorem gS_continuous : Continuous (uncurry (gS R G)) := by
  have hpair : Continuous (fun z : ℝ × ℝ => (z.1, z.2 + G.q z.1)) :=
    continuous_fst.prodMk
      (continuous_snd.add (G.contDiff.continuous.comp continuous_fst))
  simpa [gS, TimeDependentSpatialReanchoring.shift, uncurry] using
    R.gS_continuous.comp hpair

theorem mixed (t x : ℝ) : ∃ Z : ℂ,
    HasDerivAt (fun r => Complex.exp (Complex.I * (shiftedPsi R G r x : ℂ))) Z t ∧
    HasDerivAt (fun y =>
      (frameTangential (Ydot R G) (shiftedPsi R G) t y : ℂ) *
          Complex.exp (Complex.I * (shiftedPsi R G t y : ℂ)) +
      (frameNormal (Ydot R G) (shiftedPsi R G) t y : ℂ) *
          (Complex.I * Complex.exp (Complex.I * (shiftedPsi R G t y : ℂ)))) Z x := by
  let Z := Complex.I * (alphaT R G t x : ℂ) *
    Complex.exp (Complex.I * (shiftedPsi R G t x : ℂ))
  refine ⟨Z, ?_, ?_⟩
  · have h := (((rear_angle_time_deriv R G t x).ofReal_comp.const_mul
      Complex.I).cexp)
    convert h using 1 <;> simp [Z] <;> ring
  · obtain ⟨Z0, hZ0t, hZ0s⟩ := R.mixed t (x + G.q t)
    have hbaseT := (((R.rear_angle_time_deriv t (x + G.q t)).ofReal_comp.const_mul
      Complex.I).cexp)
    have hZ0 : Z0 = Complex.I * (R.alphaT t (x + G.q t) : ℂ) *
        Complex.exp (Complex.I * (S.psi t (x + G.q t) : ℂ)) :=
      hZ0t.unique (by convert hbaseT using 1 <;> ring)
    have hframe : (fun y =>
        (frameTangential R.Ydot S.psi t y : ℂ) *
            Complex.exp (Complex.I * (S.psi t y : ℂ)) +
        (frameNormal R.Ydot S.psi t y : ℂ) *
            (Complex.I * Complex.exp (Complex.I * (S.psi t y : ℂ)))) = R.Ydot t := by
      funext y
      rw [← frame_reconstruct (R.Ydot t y) (S.psi t y)]
      simp [frameTangential, frameNormal]
      ring
    rw [hframe] at hZ0s
    have hshift := (hasDerivAt_id x).add_const (G.q t)
    have hbase := hZ0s.scomp x hshift
    rw [hZ0] at hbase
    have hpsi := (S.psi_spatial t (x + G.q t)).comp x hshift
    have hE := ((hpsi.ofReal_comp.const_mul Complex.I).cexp).const_mul
      ((qRate R G t : ℝ) : ℂ)
    have hsum := hbase.add hE
    have hYspace : HasDerivAt (Ydot R G t) Z x := by
      convert hsum using 1 <;>
        simp [Ydot, RearOwnFrameGaugeFlowReanchoring.shiftedYdot, shiftedPsi,
          shiftedKappa, alphaT, qRate,
          RearOwnFrameGaugeFlowReanchoring.shiftedPsi,
          TimeDependentSpatialReanchoring.shift, Z] <;> ring
    have hreconstruct : (fun y =>
        (frameTangential (Ydot R G) (shiftedPsi R G) t y : ℂ) *
            Complex.exp (Complex.I * (shiftedPsi R G t y : ℂ)) +
        (frameNormal (Ydot R G) (shiftedPsi R G) t y : ℂ) *
            (Complex.I * Complex.exp (Complex.I * (shiftedPsi R G t y : ℂ)))) =
        Ydot R G t := by
      funext y
      rw [← frame_reconstruct (Ydot R G t y) (shiftedPsi R G t y)]
      simp [frameTangential, frameNormal]
      ring
    rw [hreconstruct]
    exact hYspace

def exact (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) : ShiftedTransport R G where
  Ydot_continuous := Ydot_continuous R G hkap0 hkap1
  gS_continuous := gS_continuous R G
  rear_time := rear_time R G hkap0 hkap1
  anchor_flow := anchor_flow R G
  jacobi := jacobi R G
  gS_deriv := gS_deriv R G
  curvatureSpatial_deriv := curvatureSpatial_deriv R G
  rear_angle_time_deriv := rear_angle_time_deriv R G
  rear_curvature_time_deriv := rear_curvature_time_deriv R G hkap0 hkap1
  rear_angle_time_continuous := rearAngleTime_continuous R G
  rear_curvature_time_continuous := rearCurvatureTime_continuous R G hkap0 hkap1
  rear_angle_time_spatial := rear_angle_time_spatial R G
  mixed := mixed R G

end Proofs

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
