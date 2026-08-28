import UnitTangentIterates.ConfiguredCompatiblePhysicalRearSequence
import UnitTangentIterates.ConfiguredFiniteBasePhysicalRearCertificate

/-!
# Configured adapter to compatible physical pair sources

An aligned configured carrier family already contains the normalized `kH`
carrier, both ordinary tube certificates, and the unshifted physical pair.
This module proves rigid equivariance of the full pointwise kinematic structure
and then forgets the aligned package to `PairSource` without an extra callback.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredPairSourceAdapter

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredCompatiblePhysicalRearSequence
  ConfiguredFiniteBasePhysicalRearCertificate

/-- Common orientation-preserving rigid motions preserve the complete physical
rear kinematic package.  The steering and rear arclength are unchanged; the
initial physical tangent angle is increased by `arg w`. -/
def physicalRearLimitKinematics_rigid
    {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    PhysicalRearLimitKinematics kh
      (MarkedRigid.rigidData a w rear)
      (MarkedRigid.rigidData a w front) := by
  let phi : ℝ := Complex.arg w
  have hperim (p : Data) :
      perim (MarkedRigid.rigidData a w p) = perim p := by
    simp [perim, hw]
  have hev (p : Data) (s : ℝ) :
      ev (MarkedRigid.rigidData a w p) s = a + w * ev p s := by
    simp [ev, hperim]
  have hphase : Complex.exp ((phi : ℂ) * Complex.I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at h
    simpa [phi] using h
  have htheta (P s : ℝ) :
      NormalizedSteeringPhysicalRescaling.thetaPhys K.steering P
          (K.theta0 + phi) s =
        phi + NormalizedSteeringPhysicalRescaling.thetaPhys K.steering P
          K.theta0 s := by
    simp [NormalizedSteeringPhysicalRescaling.thetaPhys]
    ring
  have hexp_add (t : ℝ) :
      Complex.exp (Complex.I * (((phi + t : ℝ) : ℂ))) =
        w * Complex.exp (Complex.I * ((t : ℝ) : ℂ)) := by
    have hcast : (((phi + t : ℝ) : ℂ)) = (phi : ℂ) + (t : ℂ) := by
      norm_num
    rw [hcast, mul_add, Complex.exp_add]
    rw [show Complex.I * (phi : ℂ) = (phi : ℂ) * Complex.I by ring,
      hphase]
  refine
    { theta0 := K.theta0 + phi
      steering := K.steering
      sf := K.sf
      curvature_continuous := K.curvature_continuous
      arclength_rightInverse := ?_
      front_frenet := ?_
      rear_track := ?_
      rear_perimeter := ?_
      steering_nonzero := ?_ }
  · intro x
    simpa [hperim] using K.arclength_rightInverse x
  · intro s
    have hd := ((K.front_frenet s).const_mul w).const_add a
    have hexp :
        Complex.exp (Complex.I *
          (NormalizedSteeringPhysicalRescaling.thetaPhys K.steering
            (perim front) (K.theta0 + phi) s : ℂ)) =
          w * Complex.exp (Complex.I *
            (NormalizedSteeringPhysicalRescaling.thetaPhys K.steering
              (perim front) K.theta0 s : ℂ)) := by
      rw [htheta, hexp_add]
    rw [funext (hev front), hperim, hexp]
    simpa [add_comm] using hd
  · intro x
    have hrearExp :
        Complex.exp (Complex.I *
          ((NormalizedSteeringPhysicalRescaling.thetaPhys K.steering
              (perim front) (K.theta0 + phi) (K.sf x) -
            NormalizedSteeringPhysicalRescaling.deltaPhys K.steering
              (perim front) (K.sf x) : ℝ) : ℂ)) =
          w * Complex.exp (Complex.I *
            ((NormalizedSteeringPhysicalRescaling.thetaPhys K.steering
                (perim front) K.theta0 (K.sf x) -
              NormalizedSteeringPhysicalRescaling.deltaPhys K.steering
                (perim front) (K.sf x) : ℝ) : ℂ)) := by
      rw [htheta]
      convert hexp_add
        (NormalizedSteeringPhysicalRescaling.thetaPhys K.steering
          (perim front) K.theta0 (K.sf x) -
        NormalizedSteeringPhysicalRescaling.deltaPhys K.steering
          (perim front) (K.sf x)) using 1 <;> ring
    rw [hev, K.rear_track]
    simp only [RearTrack.rearTrack, RearTrack.rearAngle, hperim]
    rw [hev, hrearExp]
    ring
  · simpa [hperim] using K.rear_perimeter
  · simpa [hperim] using K.steering_nonzero

/-- Forget an aligned configured physical carrier family to the pointwise pair
source consumed by the compatible-marking recursion.  No new model, tube,
regularity, or alignment callback is introduced. -/
def pairSource
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt : ℝ}
    (F : AlignedPhysicalCarrierFamily D Q kh c dlt) : PairSource D kh c dlt where
  normalized := F.carrier
  rear := fun n => (F.carrier n).data
  front := fun n => Q (n + 1)
  rear_regular := by
    intro n
    exact lt_of_lt_of_le (F.carrier n).c_pos
      ((F.carrier n).tube.speed_lb 0)
  rear_tube := by
    intro n
    exact ⟨(F.carrier n).c, (F.carrier n).dlt,
      (F.carrier n).c_pos, (F.carrier n).dlt_pos, (F.carrier n).tube⟩
  front_tube := F.front_tube
  normalized_alignment := by
    intro n
    refine ⟨0, 1, 0, norm_one, ?_⟩
    simp
  physical_rigid := by
    intro n a w hw
    let K : PhysicalRearLimitKinematics kh (F.carrier n).data (Q (n + 1)) :=
      Nonempty.some (by simpa using F.physical_shift n 0)
    exact ⟨physicalRearLimitKinematics_rigid K a w hw⟩

/-- The corresponding coherent all-level compatible sequence. -/
def compatibleSequence
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt : ℝ}
    (F : AlignedPhysicalCarrierFamily D Q kh c dlt) (q0 : Data)
    (hc : 0 < c) (hq0 : IsTubeMember c 0 dlt q0) :
    (pairSource F).Output q0 :=
  (pairSource F).compatibleSequence q0 hc hq0

end ConfiguredPairSourceAdapter
