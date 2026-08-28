import UnitTangentIterates.ConfiguredBaseExactSelectedPreTransport
import UnitTangentIterates.ConfiguredBaseProfiledSelectedRearGaugeReanchoring

/-!
# Gauge transport of the exact selected rear C1 data

The phase certificate is consumed, not constructed, here.  All analytic
transport identities are expressed against spatial shifts of the pretransport
fields, so the configured geometric reanchoring can identify them directly.
-/

noncomputable section

open Function RearTrack

namespace ConfiguredBaseExactSelectedGaugeTransport

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseProfiledResidualConstructor.ExactSelected
  ConfiguredBaseExactSelectedPreTransport
  ConfiguredBaseProfiledSelectedRearReanchoring
  RearOwnArclength RearFamilyFrame RearOwnHigherRegularity


variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}
  {H : ConfiguredActualSubunitCurvature.Certificate D}

section Definitions

variable {W : Output D Q n A} {S : ExactSelected (n := n) H}
  (P : PreTransport W H S)

abbrev xi : ℝ → ℝ → ℝ := frameTangential P.Ydot (psiR W S)

def qRate (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) (t : ℝ) : ℝ := -xi P t (G.q t)

abbrev shiftedRear (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) : ℝ → ℝ → ℂ :=
  TimeDependentSpatialReanchoring.shift (rearR W S) G.q

abbrev shiftedPsi (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) : ℝ → ℝ → ℝ :=
  RearOwnFrameGaugeFlowReanchoring.shiftedPsi (psiR W S) G.q

abbrev shiftedKappa (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (kappaR W S) G.q

abbrev shiftedJacobiSource (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (jacobiSource W S) G.q

abbrev shiftedCurvatureSpatial (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift (curvatureSpatial W S) G.q

def Ydot (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) : ℝ → ℝ → ℂ :=
  RearOwnFrameGaugeFlowReanchoring.shiftedYdot P.Ydot (psiR W S) (xi P) G.q

def alphaT (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) : ℝ → ℝ → ℝ := fun t x ↦
  TimeDependentSpatialReanchoring.shift P.alphaT G.q t x + qRate P G t * shiftedKappa P G t x

def kT (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) : ℝ → ℝ → ℝ := fun t x ↦
  TimeDependentSpatialReanchoring.shift P.kT G.q t x + qRate P G t * shiftedCurvatureSpatial P G t x

abbrev gS (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) : ℝ → ℝ → ℝ := TimeDependentSpatialReanchoring.shift P.gS G.q

/-- Every field of the configured transport, stated before identifying the
shifted geometry package.  The anchor coordinate is the constant zero map. -/
structure ShiftedTransport (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) where
  Ydot_continuous : Continuous (uncurry (Ydot P G))
  gS_continuous : Continuous (uncurry (gS P G))
  rear_time : ∀ t x, HasDerivAt (fun r ↦ shiftedRear P G r x) (Ydot P G t x) t
  anchor_flow : ∀ t, HasDerivAt (fun _r : ℝ ↦ (0 : ℝ))
    (-frameTangential (Ydot P G) (shiftedPsi P G) t 0) t
  jacobi : ∀ t x, HasDerivAt
    (fun y ↦ frameNormal (Ydot P G) (shiftedPsi P G) t y)
    (shiftedJacobiSource P G t x -
      frameNormal (Ydot P G) (shiftedPsi P G) t x) x
  gS_deriv : ∀ t x, HasDerivAt (shiftedJacobiSource P G t) (gS P G t x) x
  curvatureSpatial_deriv : ∀ t x,
    HasDerivAt (shiftedKappa P G t) (shiftedCurvatureSpatial P G t x) x
  rear_angle_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ shiftedPsi P G r x) (alphaT P G t x) t
  rear_curvature_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ shiftedKappa P G r x) (kT P G t x) t
  rear_angle_time_continuous : Continuous (uncurry (alphaT P G))
  rear_curvature_time_continuous : Continuous (uncurry (kT P G))
  rear_angle_time_spatial : ∀ t x,
    HasDerivAt (alphaT P G t) (kT P G t x) x
  mixed : ∀ t x, ∃ Z : ℂ,
    HasDerivAt
      (fun r ↦ Complex.exp (Complex.I * (shiftedPsi P G r x : ℂ))) Z t ∧
    HasDerivAt
      (fun y ↦
        (frameTangential (Ydot P G) (shiftedPsi P G) t y : ℂ) *
            Complex.exp (Complex.I * (shiftedPsi P G t y : ℂ)) +
        (frameNormal (Ydot P G) (shiftedPsi P G) t y : ℂ) *
            (Complex.I * Complex.exp
              (Complex.I * (shiftedPsi P G t y : ℂ)))) Z x

end Definitions

section Proofs

variable {W : Output D Q n A} {S : ExactSelected (n := n) H}
  (P : PreTransport W H S) (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P))

private theorem rear_contDiff : ContDiff ℝ 1 (uncurry (rearR W S)) :=
  contDiff_one_rearOwn (geometry W).front_contDiff (geometry W).angle_contDiff
    (deltaR_contDiff W S) (sfR_contDiff W S)

private theorem rear_space (t x : ℝ) : HasDerivAt (rearR W S t)
    (Complex.exp (Complex.I * (psiR W S t x : ℂ))) x := by
  simpa [RearOwnArclength.rearOwnTangent] using
    (hasDerivAt_rearOwn_space (geometry W).front_frenet
      (geometry W).angle_frenet (deltaR_steering W S) (sfR_deriv W S)
      (deltaR_cos_ne_zero W S) t x)

theorem rear_time (t x : ℝ) :
    HasDerivAt (fun r ↦ shiftedRear P G r x) (Ydot P G t x) t := by
  have hcomp := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    ((rear_contDiff (W := W) (S := S)).differentiable (by norm_num))
      ((hasDerivAt_const t x).add (G.ode t))
  have hpt : partialTime (rearR W S) t (x + G.q t) = P.Ydot t (x + G.q t) :=
    (hasDerivAt_partialTime
      ((rear_contDiff (W := W) (S := S)).differentiable (by norm_num)) t _).unique
      (P.rear_time t _)
  have hpx : partialArc (rearR W S) t (x + G.q t) =
      Complex.exp (Complex.I * (psiR W S t (x + G.q t) : ℂ)) :=
    (hasDerivAt_partialArc
      ((rear_contDiff (W := W) (S := S)).differentiable (by norm_num)) t _).unique
      (rear_space (W := W) (S := S) t _)
  simp only [Pi.add_apply, zero_add] at hcomp
  rw [hpt, hpx] at hcomp
  convert hcomp using 1 <;>
    simp [shiftedRear, Ydot, RearOwnFrameGaugeFlowReanchoring.shiftedYdot, RearOwnFrameGaugeFlowReanchoring.shiftedPsi, xi, qRate,
      TimeDependentSpatialReanchoring.shift, Complex.real_smul]

theorem rear_angle_time_deriv (t x : ℝ) :
    HasDerivAt (fun r ↦ shiftedPsi P G r x) (alphaT P G t x) t := by
  have hcomp := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    ((psiR_contDiff W S).differentiable (by norm_num))
      ((hasDerivAt_const t x).add (G.ode t))
  have hpt : partialTime (psiR W S) t (x + G.q t) = P.alphaT t (x + G.q t) :=
    (hasDerivAt_partialTime ((psiR_contDiff W S).differentiable (by norm_num))
      t _).unique (P.rear_angle_time_deriv t _)
  have hpx : partialArc (psiR W S) t (x + G.q t) = kappaR W S t (x + G.q t) :=
    (hasDerivAt_partialArc ((psiR_contDiff W S).differentiable (by norm_num))
      t _).unique (psiR_spatial W S t _)
  simp only [Pi.add_apply, zero_add] at hcomp
  rw [hpt, hpx] at hcomp
  convert hcomp using 1 <;>
    simp [shiftedPsi, alphaT, shiftedKappa, qRate, xi, RearOwnFrameGaugeFlowReanchoring.shiftedPsi,
      TimeDependentSpatialReanchoring.shift, smul_eq_mul]

theorem rear_curvature_time_deriv (t x : ℝ) :
    HasDerivAt (fun r ↦ shiftedKappa P G r x) (kT P G t x) t := by
  have hkC := rear_curvature_contDiff W S
  have hcomp := RearArclengthInverseTimeSpatial.hasDerivAt_comp_partials
    (hkC.differentiable (by norm_num))
      ((hasDerivAt_const t x).add (G.ode t))
  have hpt : partialTime (kappaR W S) t (x + G.q t) = P.kT t (x + G.q t) :=
    (hasDerivAt_partialTime (hkC.differentiable (by norm_num)) t _).unique
      (P.rear_curvature_time_deriv t _)
  have hpx : partialArc (kappaR W S) t (x + G.q t) =
      curvatureSpatial W S t (x + G.q t) :=
    (hasDerivAt_partialArc (hkC.differentiable (by norm_num)) t _).unique
      (P.curvatureSpatial_deriv t _)
  simp only [Pi.add_apply, zero_add] at hcomp
  rw [hpt, hpx] at hcomp
  convert hcomp using 1 <;>
    simp [shiftedKappa, shiftedCurvatureSpatial, kT, qRate, xi, TimeDependentSpatialReanchoring.shift,
      smul_eq_mul]

theorem curvatureSpatial_deriv (t x : ℝ) :
    HasDerivAt (shiftedKappa P G t) (shiftedCurvatureSpatial P G t x) x :=
  TimeDependentSpatialReanchoring.shift_spatial_deriv P.curvatureSpatial_deriv t x

theorem gS_deriv (t x : ℝ) :
    HasDerivAt (shiftedJacobiSource P G t) (gS P G t x) x :=
  TimeDependentSpatialReanchoring.shift_spatial_deriv P.gS_deriv t x

theorem rear_angle_time_spatial (t x : ℝ) :
    HasDerivAt (alphaT P G t) (kT P G t x) x := by
  have h1 := TimeDependentSpatialReanchoring.shift_spatial_deriv
    (q := G.q) P.rear_angle_time_spatial t x
  have h2 := (TimeDependentSpatialReanchoring.shift_spatial_deriv
    (q := G.q) P.curvatureSpatial_deriv t x).const_mul
    (qRate P G t)
  simpa [alphaT, kT, shiftedKappa, shiftedCurvatureSpatial, TimeDependentSpatialReanchoring.shift] using h1.add h2

theorem jacobi (t x : ℝ) : HasDerivAt
    (fun y ↦ frameNormal (Ydot P G) (shiftedPsi P G) t y)
    (shiftedJacobiSource P G t x -
      frameNormal (Ydot P G) (shiftedPsi P G) t x) x := by
  have h := TimeDependentSpatialReanchoring.shift_spatial_deriv
    (q := G.q) P.jacobi t x
  have hnormal : (fun y ↦ frameNormal (Ydot P G) (shiftedPsi P G) t y) =
      TimeDependentSpatialReanchoring.shift
        (frameNormal P.Ydot (psiR W S)) G.q t := by
    funext y
    exact RearOwnFrameGaugeFlowReanchoring.frameNormal_shiftedYdot
      P.Ydot (psiR W S) G.q t y
  rw [hnormal]
  apply h.congr_deriv
  simp only [shiftedJacobiSource, TimeDependentSpatialReanchoring.shift]
  unfold Ydot shiftedPsi
  rw [RearOwnFrameGaugeFlowReanchoring.frameNormal_shiftedYdot
    P.Ydot (psiR W S) G.q t x]
  rfl

theorem anchor_flow (t : ℝ) : HasDerivAt (fun _r : ℝ ↦ (0 : ℝ))
    (-frameTangential (Ydot P G) (shiftedPsi P G) t 0) t := by
  have hz := RearOwnFrameGaugeFlowReanchoring.frameTangential_shiftedYdot_zero P.Ydot (psiR W S) G.q t
  unfold Ydot shiftedPsi
  rw [hz]
  simpa using (hasDerivAt_const t (0 : ℝ))

theorem rearAngleTime_continuous : Continuous (uncurry (alphaT P G)) := by
  have hpsiC := TimeDependentSpatialReanchoring.shift_contDiff (psiR_contDiff W S) G.contDiff
  have heq : alphaT P G = partialTime (shiftedPsi P G) := by
    funext t x
    exact (rear_angle_time_deriv P G t x).unique
      (hasDerivAt_partialTime (hpsiC.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) hpsiC).continuous

theorem rearCurvatureTime_continuous : Continuous (uncurry (kT P G)) := by
  have hkC := TimeDependentSpatialReanchoring.shift_contDiff (rear_curvature_contDiff W S) G.contDiff
  have heq : kT P G = partialTime (shiftedKappa P G) := by
    funext t x
    exact (rear_curvature_time_deriv P G t x).unique
      (hasDerivAt_partialTime (hkC.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) hkC).continuous

theorem Ydot_continuous : Continuous (uncurry (Ydot P G)) := by
  have hrearC := TimeDependentSpatialReanchoring.shift_contDiff
    (rear_contDiff (W := W) (S := S)) G.contDiff
  have heq : Ydot P G = partialTime (shiftedRear P G) := by
    funext t x
    exact (rear_time P G t x).unique
      (hasDerivAt_partialTime (hrearC.differentiable (by norm_num)) t x)
  rw [heq]
  exact (contDiff_partialTime_self (n := 0) hrearC).continuous

theorem gS_continuous : Continuous (uncurry (gS P G)) := by
  have hpair : Continuous (fun p : ℝ × ℝ ↦ (p.1, p.2 + G.q p.1)) :=
    continuous_fst.prodMk
      (continuous_snd.add (G.contDiff.continuous.comp continuous_fst))
  simpa [gS, TimeDependentSpatialReanchoring.shift, uncurry] using P.gS_continuous.comp hpair

theorem mixed (t x : ℝ) : ∃ Z : ℂ,
    HasDerivAt
      (fun r ↦ Complex.exp (Complex.I * (shiftedPsi P G r x : ℂ))) Z t ∧
    HasDerivAt
      (fun y ↦
        (frameTangential (Ydot P G) (shiftedPsi P G) t y : ℂ) *
            Complex.exp (Complex.I * (shiftedPsi P G t y : ℂ)) +
        (frameNormal (Ydot P G) (shiftedPsi P G) t y : ℂ) *
            (Complex.I * Complex.exp
              (Complex.I * (shiftedPsi P G t y : ℂ)))) Z x := by
  let Z := Complex.I * (alphaT P G t x : ℂ) *
    Complex.exp (Complex.I * (shiftedPsi P G t x : ℂ))
  refine ⟨Z, ?_, ?_⟩
  · have h := (((rear_angle_time_deriv P G t x).ofReal_comp.const_mul
      Complex.I).cexp)
    convert h using 1 <;> simp [Z] <;> ring
  · obtain ⟨Z0, hZ0t, hZ0s⟩ := P.mixed t (x + G.q t)
    have hbaseT := (((P.rear_angle_time_deriv t (x + G.q t)).ofReal_comp.const_mul
      Complex.I).cexp)
    have hZ0 : Z0 = Complex.I * (P.alphaT t (x + G.q t) : ℂ) *
        Complex.exp (Complex.I * (psiR W S t (x + G.q t) : ℂ)) := by
      exact hZ0t.unique (by convert hbaseT using 1 <;> ring)
    have hframe : (fun y ↦
        (frameTangential P.Ydot (psiR W S) t y : ℂ) *
            Complex.exp (Complex.I * (psiR W S t y : ℂ)) +
        (frameNormal P.Ydot (psiR W S) t y : ℂ) *
            (Complex.I * Complex.exp (Complex.I * (psiR W S t y : ℂ)))) =
        P.Ydot t := by
      funext y
      rw [← frame_reconstruct (P.Ydot t y) (psiR W S t y)]
      simp [frameTangential, frameNormal]
      ring
    rw [hframe] at hZ0s
    have hshift : HasDerivAt (fun y : ℝ ↦ y + G.q t) 1 x :=
      (hasDerivAt_id x).add_const (G.q t)
    have hbase := hZ0s.scomp x hshift
    rw [hZ0] at hbase
    have hpsi := (psiR_spatial W S t (x + G.q t)).comp x hshift
    have hE := ((hpsi.ofReal_comp.const_mul Complex.I).cexp).const_mul
      ((qRate P G t : ℝ) : ℂ)
    have hsum := hbase.add hE
    have hYspace : HasDerivAt (Ydot P G t) Z x := by
      convert hsum using 1 <;>
        simp [Ydot, RearOwnFrameGaugeFlowReanchoring.shiftedYdot, shiftedPsi, shiftedKappa, alphaT, qRate,
          RearOwnFrameGaugeFlowReanchoring.shiftedPsi, TimeDependentSpatialReanchoring.shift, Z] <;> ring
    have hreconstruct : (fun y ↦
        (frameTangential (Ydot P G) (shiftedPsi P G) t y : ℂ) *
            Complex.exp (Complex.I * (shiftedPsi P G t y : ℂ)) +
        (frameNormal (Ydot P G) (shiftedPsi P G) t y : ℂ) *
            (Complex.I * Complex.exp
              (Complex.I * (shiftedPsi P G t y : ℂ)))) = Ydot P G t := by
      funext y
      rw [← frame_reconstruct (Ydot P G t y) (shiftedPsi P G t y)]
      simp [frameTangential, frameNormal]
      ring
    rw [hreconstruct]
    exact hYspace

/-- Gauge transport of every exact C1 field, including the now-valid anchor
flow at the shifted origin. -/
def exact : ShiftedTransport P G where
  Ydot_continuous := Ydot_continuous P G
  gS_continuous := gS_continuous P G
  rear_time := rear_time P G
  anchor_flow := anchor_flow P G
  jacobi := jacobi P G
  gS_deriv := gS_deriv P G
  curvatureSpatial_deriv := curvatureSpatial_deriv P G
  rear_angle_time_deriv := rear_angle_time_deriv P G
  rear_curvature_time_deriv := rear_curvature_time_deriv P G
  rear_angle_time_continuous := rearAngleTime_continuous P G
  rear_curvature_time_continuous := rearCurvatureTime_continuous P G
  rear_angle_time_spatial := rear_angle_time_spatial P G
  mixed := mixed P G

theorem exists_shiftedTransport : Nonempty (ShiftedTransport P G) := ⟨exact P G⟩

end Proofs

end ConfiguredBaseExactSelectedGaugeTransport
