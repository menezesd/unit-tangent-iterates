import Mathlib
import UnitTangentIterates.NormalizedSteeringPhysicalRescaling
import UnitTangentIterates.NormalizedSelectedRearClosure
import UnitTangentIterates.UnitTangentSpeed

/-! # Physical selected-rear closure and strictness -/

noncomputable section

open Set

namespace PhysicalSelectedRearStrictnessAdapter

open NormalizedSelectedRearClosure NormalizedSteeringPhysicalRescaling

/-- Sound replacement for the capstone's limit-strictness datum. -/
structure PhysicalLimitStrictnessData
    (kap : ℝ) (p q : MarkedSpace.Data) (P : ℝ)
    (d : SteeringData kap) (theta0 : ℝ) (k k' : ℝ → ℝ) : Prop where
  canonical : q = SelectedInverseMap.selInv kap p
  curvature_pos : ∀ s, 0 < k s
  rear_C3 : ContDiff ℝ (3 : ℕ)
    (fun x => ∫ t in (0 : ℝ)..x,
      Complex.exp (((thetaPhys d P theta0 t - deltaPhys d P t : ℝ) : ℂ) * Complex.I))

/-- Physical steering gives the rear-angle ODE required by the regularity
gain, without forcing the physical period back into a period-one structure. -/
theorem rear_C3_of_physical_steering
    {kap P theta0 : ℝ} (d : SteeringData kap)
    (hP : 0 < P) (hK : Continuous d.K) :
    ContDiff ℝ (3 : ℕ)
      (fun x => ∫ t in (0 : ℝ)..x,
        Complex.exp (((thetaPhys d P theta0 t - deltaPhys d P t : ℝ) : ℂ) *
          Complex.I)) := by
  have htheta : ContDiff ℝ (1 : ℕ) (thetaPhys d P theta0) := by
    have hderiv : deriv (thetaPhys d P theta0) = curvaturePhys d P :=
      funext fun x => (hasDerivAt_thetaPhys (P := P) (theta0 := theta0) d hK x).deriv
    have h1 : ContDiff ℝ (1 : WithTop ℕ∞) (thetaPhys d P theta0) := by
      rw [contDiff_one_iff_deriv]
      refine ⟨fun x =>
        (hasDerivAt_thetaPhys (P := P) (theta0 := theta0) d hK x).differentiableAt, ?_⟩
      rw [hderiv]
      exact continuous_curvaturePhys (P := P) d hK
    exact_mod_cast h1
  have hrear : ∀ s, HasDerivAt
      (fun t => thetaPhys d P theta0 t - deltaPhys d P t)
      (Real.sin (thetaPhys d P theta0 s -
        (thetaPhys d P theta0 s - deltaPhys d P s))) s := by
    intro s
    have ht := hasDerivAt_thetaPhys (P := P) (theta0 := theta0) d hK s
    have hd := hasDerivAt_deltaPhys d hP s
    convert ht.sub hd using 1 <;> ring
  simpa using RearRegularity.rear_contDiff 1 htheta hrear

/-- Corrected closure-to-strictness adapter.  All steering quantities passed
to `packagedRear_eq_selInv` are in physical arclength. -/
theorem physicalLimitStrictnessData_of_packagedRear
    {kap c kmin dlt cR kR dR P theta0 L : ℝ}
    {p q : MarkedSpace.Data} {sf k k' : ℝ → ℝ}
    (d : SteeringData kap)
    (hc : 0 < c) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hP : 0 < P) (hPperim : P = MarkedSpace.perim p) (hK : Continuous d.K)
    (hp : MarkedSpace.IsTubeMember c kmin dlt p)
    (hq : MarkedSpace.IsTubeMember cR kR dR q)
    (hfront : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I * (thetaPhys d P theta0 s : ℂ))) s)
    (hsf : ∀ x, RearTrack.rearArclength (deltaPhys d P) (sf x) = x)
    (hperim : MarkedSpace.perim q =
      RearTrack.rearArclength (deltaPhys d P) (MarkedSpace.perim p))
    (hrear : ∀ x, MarkedSpace.ev q x = RearTrack.rearTrack
      (MarkedSpace.ev p) (thetaPhys d P theta0) (deltaPhys d P) (sf x))
    (hL : 0 < L) (hkper : Function.Periodic k L)
    (hk : ∀ s, HasDerivAt k (k' s) s) (hk0 : ∀ s, 0 ≤ k s)
    (hnext : ∀ s,
      0 ≤ (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2))
    (hkne : ∃ s, k s ≠ 0) :
    PhysicalLimitStrictnessData kap p q P d theta0 k k' := by
  subst P
  obtain ⟨hdeltaPer, hdeltaMem, hdelta, htheta⟩ :=
    physical_steering_data d hP hK
  have hcanonical : q = SelectedInverseMap.selInv kap p :=
    packagedRear_eq_selInv hc hkap0 hkap1 hp hq hfront htheta
      hdeltaPer hdeltaMem hdelta hsf hperim hrear
  have hkpos := UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg
    hL hkper hk hk0 hnext hkne
  exact ⟨hcanonical, hkpos, rear_C3_of_physical_steering d hP hK⟩

/-- The smallest bridge from a closure-limit reconstruction to capstone-ready
strictness: provide its physical rear packaging and the intrinsic next-track
curvature inequality. -/
theorem physical_limit_is_canonical_strict
    {kap c kmin dlt cR kR dR P theta0 L : ℝ}
    {p q : MarkedSpace.Data} {sf k k' : ℝ → ℝ}
    (d : SteeringData kap)
    (hc : 0 < c) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hP : 0 < P) (hPperim : P = MarkedSpace.perim p) (hK : Continuous d.K)
    (hp : MarkedSpace.IsTubeMember c kmin dlt p)
    (hq : MarkedSpace.IsTubeMember cR kR dR q)
    (hfront : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I * (thetaPhys d P theta0 s : ℂ))) s)
    (hsf : ∀ x, RearTrack.rearArclength (deltaPhys d P) (sf x) = x)
    (hperim : MarkedSpace.perim q =
      RearTrack.rearArclength (deltaPhys d P) (MarkedSpace.perim p))
    (hrear : ∀ x, MarkedSpace.ev q x = RearTrack.rearTrack
      (MarkedSpace.ev p) (thetaPhys d P theta0) (deltaPhys d P) (sf x))
    (hL : 0 < L) (hkper : Function.Periodic k L)
    (hk : ∀ s, HasDerivAt k (k' s) s) (hk0 : ∀ s, 0 ≤ k s)
    (hnext : ∀ s,
      0 ≤ (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2))
    (hkne : ∃ s, k s ≠ 0) :
    q = SelectedInverseMap.selInv kap p ∧ (∀ s, 0 < k s) := by
  have H := physicalLimitStrictnessData_of_packagedRear d hc hkap0 hkap1 hP hPperim hK
    hp hq hfront hsf hperim hrear hL hkper hk hk0 hnext hkne
  exact ⟨H.canonical, H.curvature_pos⟩

end PhysicalSelectedRearStrictnessAdapter
