import Mathlib
import UnitTangentIterates.RearArclengthInverseBridge
import UnitTangentIterates.RearFrenetLimitStrictness
import UnitTangentIterates.NormalizedSteeringPhysicalRescaling

noncomputable section

open Function Set

namespace SelectedRearFrenetChain

open RearTrack NormalizedSelectedRearClosure
open NormalizedSteeringPhysicalRescaling

def rearPsi {kap : ℝ} (d : SteeringData kap) (P theta0 : ℝ)
    (sf : ℝ → ℝ) : ℝ → ℝ :=
  fun x => thetaPhys d P theta0 (sf x) - deltaPhys d P (sf x)

def rearK {kap : ℝ} (d : SteeringData kap) (P : ℝ)
    (sf : ℝ → ℝ) : ℝ → ℝ :=
  fun x => Real.tan (deltaPhys d P (sf x))

def rearK' {kap : ℝ} (d : SteeringData kap) (P : ℝ)
    (sf : ℝ → ℝ) : ℝ → ℝ := fun x =>
  (1 / Real.cos (deltaPhys d P (sf x)) ^ 2) *
    (curvaturePhys d P (sf x) - Real.sin (deltaPhys d P (sf x))) *
      (1 / Real.cos (deltaPhys d P (sf x)))

/-- Frenet data obtained from the physical selected-rear reconstruction,
excluding only the curvature inequality for the next unit-tangent track. -/
structure RearFrenetCoreCertificate (q : MarkedSpace.Data) where
  psi : ℝ → ℝ
  k : ℝ → ℝ
  k' : ℝ → ℝ
  curve_deriv : ∀ s, HasDerivAt (MarkedSpace.ev q)
    (Complex.exp (Complex.I * (psi s : ℂ))) s
  angle_deriv : ∀ s, HasDerivAt psi (k s) s
  curvature_deriv : ∀ s, HasDerivAt k (k' s) s
  curvature_periodic : Periodic k (MarkedSpace.perim q)
  curvature_nonnegative : ∀ s, 0 ≤ k s
  curvature_nonzero : ∃ s, k s ≠ 0

/-- Physical rear-track formulas give the Frenet core in rear arclength. -/
def rearFrenetCore_of_physicalRear
    {kap P theta0 : ℝ} (d : SteeringData kap) {sf : ℝ → ℝ}
    {p q : MarkedSpace.Data}
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hP : 0 < P) (hK : Continuous d.K)
    (D : RearArclengthInverseBridge.Data (deltaPhys d P) sf P)
    (hfront : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I * (thetaPhys d P theta0 s : ℂ))) s)
    (hrear : ∀ x, MarkedSpace.ev q x = RearTrack.rearTrack
      (MarkedSpace.ev p) (thetaPhys d P theta0)
        (deltaPhys d P) (sf x))
    (hper : MarkedSpace.perim q = D.rearPeriod)
    (hk0 : ∀ x, 0 ≤ rearK d P sf x)
    (hkne : ∃ x, rearK d P sf x ≠ 0) :
    RearFrenetCoreCertificate q := by
  have htheta := hasDerivAt_thetaPhys (P := P) (theta0 := theta0) d hK
  have hdelta := hasDerivAt_deltaPhys d hP
  refine
    { psi := rearPsi d P theta0 sf
      k := rearK d P sf
      k' := rearK' d P sf
      curve_deriv := ?_
      angle_deriv := ?_
      curvature_deriv := ?_
      curvature_periodic := ?_
      curvature_nonnegative := hk0
      curvature_nonzero := hkne }
  · intro x
    have hr := (RearTrack.hasDerivAt_rearTrack (hfront (sf x))
      (htheta (sf x)) (hdelta (sf x))).scomp x (D.sf_deriv x)
    have hc : Real.cos (deltaPhys d P (sf x)) ≠ 0 := by
      have hm := deltaPhys_mem d (P := P) (sf x)
      exact ne_of_gt (RearTrack.rear_speed_ge hkap1 hkap0 hm.1 hm.2)
    rw [show MarkedSpace.ev q = fun x => RearTrack.rearTrack
      (MarkedSpace.ev p) (thetaPhys d P theta0)
        (deltaPhys d P) (sf x) from funext hrear]
    convert hr using 1 <;>
      simp [rearPsi, RearTrack.rearAngle, one_div, hc, Complex.ofReal_inv]
    have hcC : (Complex.cos ((deltaPhys d P (sf x) : ℝ) : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_cos]
      exact_mod_cast hc
    field_simp
  · intro x
    have hr := (RearTrack.hasDerivAt_rearAngle (htheta (sf x))
      (hdelta (sf x))).comp x (D.sf_deriv x)
    have hc : Real.cos (deltaPhys d P (sf x)) ≠ 0 := by
      have hm := deltaPhys_mem d (P := P) (sf x)
      exact ne_of_gt (RearTrack.rear_speed_ge hkap1 hkap0 hm.1 hm.2)
    convert hr using 1 <;>
      simp [rearPsi, rearK, Real.tan_eq_sin_div_cos, one_div, hc]
    rw [div_eq_mul_inv]
  · intro x
    have hc : Real.cos (deltaPhys d P (sf x)) ≠ 0 := by
      have hm := deltaPhys_mem d (P := P) (sf x)
      exact ne_of_gt (RearTrack.rear_speed_ge hkap1 hkap0 hm.1 hm.2)
    have hdcomp := (hdelta (sf x)).comp x (D.sf_deriv x)
    have htan := (Real.hasDerivAt_tan hc).comp x hdcomp
    convert htan using 1 <;> simp [rearK, rearK', one_div]; ring
  · rw [hper]
    change Periodic (fun x => Real.tan (deltaPhys d P (sf x))) D.rearPeriod
    intro x
    have h := RearArclengthInverseBridge.periodic_comp_sf D
      (fun s => deltaPhys_periodic (P := P) d s) x
    exact congrArg Real.tan h

/-- Add precisely the successor-curvature inequality to obtain the capstone
Frenet certificate. -/
def RearFrenetCoreCertificate.toRearFrenetCertificate
    {q : MarkedSpace.Data} (F : RearFrenetCoreCertificate q)
    (hnext : ∀ s,
      0 ≤ (F.k s + F.k' s / (1 + F.k s ^ 2)) /
        Real.sqrt (1 + F.k s ^ 2)) :
    PhysicalSelectedRearStrictnessAdapter.RearFrenetCertificate q where
  psi := F.psi
  k := F.k
  k' := F.k'
  curve_deriv := F.curve_deriv
  angle_deriv := F.angle_deriv
  curvature_deriv := F.curvature_deriv
  curvature_periodic := F.curvature_periodic
  curvature_nonnegative := F.curvature_nonnegative
  next_nonnegative := hnext
  curvature_nonzero := F.curvature_nonzero

/-- For the selected rear, the scalar curvature of its unit-tangent transform
is literally the physical curvature of the reconstructed front.  Thus the
closed-tube nonnegativity needed at the successor is not an additional
differential inequality on the rear. -/
theorem rear_transform_curvature_eq_front
    {kap P : ℝ} (d : SteeringData kap) (sf : ℝ → ℝ)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (s : ℝ) :
    (rearK d P sf s + rearK' d P sf s /
        (1 + rearK d P sf s ^ 2)) /
      Real.sqrt (1 + rearK d P sf s ^ 2) =
        curvaturePhys d P (sf s) := by
  let a := deltaPhys d P (sf s)
  let K := curvaturePhys d P (sf s)
  have hm := deltaPhys_mem d (P := P) (sf s)
  have hcpos : 0 < Real.cos a := by
    exact RearTrack.rear_speed_ge hkap1 hkap0 hm.1 hm.2
  have hc : Real.cos a ≠ 0 := ne_of_gt hcpos
  have htrig : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq a
  have hsquare : (1 / Real.cos a) ^ 2 =
      1 + (Real.tan a) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith
  have hsqrt : Real.sqrt (1 + Real.tan a ^ 2) = 1 / Real.cos a := by
    have hs0 : 0 ≤ Real.sqrt (1 + Real.tan a ^ 2) := Real.sqrt_nonneg _
    have hi0 : 0 ≤ 1 / Real.cos a := (one_div_pos.mpr hcpos).le
    have hs2 := Real.sq_sqrt (show 0 ≤ 1 + Real.tan a ^ 2 by positivity)
    nlinarith
  change (Real.tan a +
      ((1 / Real.cos a ^ 2) * (K - Real.sin a) *
        (1 / Real.cos a)) / (1 + Real.tan a ^ 2)) /
      Real.sqrt (1 + Real.tan a ^ 2) = K
  rw [hsqrt, Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination (Real.sin a - K) * htrig

/-- Successor nonnegative curvature completes the selected-rear Frenet
certificate. -/
def RearFrenetCoreCertificate.complete_of_front_curvature_nonnegative
    {kap P : ℝ} (d : SteeringData kap) (sf : ℝ → ℝ)
    {q : MarkedSpace.Data} (F : RearFrenetCoreCertificate q)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hk : F.k = rearK d P sf) (hk' : F.k' = rearK' d P sf)
    (hfront0 : ∀ s, 0 ≤ curvaturePhys d P (sf s)) :
    PhysicalSelectedRearStrictnessAdapter.RearFrenetCertificate q := by
  apply F.toRearFrenetCertificate
  intro s
  rw [hk, hk', rear_transform_curvature_eq_front d sf hkap0 hkap1 s]
  exact hfront0 s

/-- The corresponding capstone datum, with the transformed-curvature field
discharged by the successor's physical curvature nonnegativity. -/
def RearFrenetCoreCertificate.limitStrictness_of_front_curvature_nonnegative
    {kap P : ℝ} (d : SteeringData kap) (sf : ℝ → ℝ)
    {q : MarkedSpace.Data} (F : RearFrenetCoreCertificate q)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hk : F.k = rearK d P sf) (hk' : F.k' = rearK' d P sf)
    (hfront0 : ∀ s, 0 ≤ curvaturePhys d P (sf s)) :
    UnconditionalAssembly.LimitStrictnessData q :=
  (F.complete_of_front_curvature_nonnegative d sf hkap0 hkap1 hk hk'
    hfront0).toLimitStrictnessData

end SelectedRearFrenetChain
