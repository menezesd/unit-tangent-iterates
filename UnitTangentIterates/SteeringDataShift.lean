import UnitTangentIterates.NormalizedSelectedRearClosure
import UnitTangentIterates.NormalizedSteeringPhysicalRescaling

noncomputable section
open Function Set
namespace NormalizedSelectedRearClosure.SteeringData

open NormalizedSteeringPhysicalRescaling

/-- Translation of the normalized front parameter preserves the selected
steering ODE and its unit period. -/
def shift {kap b : ℝ} (S : SteeringData kap) : SteeringData kap where
  K := fun u => S.K (u + b)
  delta := fun u => S.delta (u + b)
  K_periodic := by
    intro u
    change S.K (u + 1 + b) = S.K (u + b)
    rw [show u + 1 + b = (u + b) + 1 by ring, S.K_periodic]
  delta_periodic := by
    intro u
    change S.delta (u + 1 + b) = S.delta (u + b)
    rw [show u + 1 + b = (u + b) + 1 by ring, S.delta_periodic]
  delta_mem := fun u => S.delta_mem (u + b)
  steering := by
    intro u
    have hi : HasDerivAt (fun x : ℝ => x + b) 1 u := by
      simpa using (hasDerivAt_id u).add_const b
    simpa [Function.comp_def] using (S.steering (u + b)).scomp u hi

theorem curvaturePhys_shift {kap P b : ℝ} (S : SteeringData kap)
    (hP : P ≠ 0) (s : ℝ) :
    curvaturePhys (S.shift (b := b)) P s = curvaturePhys S P (s + P * b) := by
  unfold curvaturePhys shift
  have harg : (s + P * b) / P = s / P + b := by field_simp
  rw [harg]

/-- Choosing the new marked angle at the translated origin makes the entire
physical tangent-angle primitive translate by `P*b`. -/
theorem thetaPhys_shift {kap P theta0 b : ℝ} (S : SteeringData kap)
    (hP : P ≠ 0) (hK : Continuous S.K) (s : ℝ) :
    thetaPhys (S.shift (b := b)) P (thetaPhys S P theta0 (P * b)) s =
      thetaPhys S P theta0 (s + P * b) := by
  have hc : Continuous (curvaturePhys S P) :=
    continuous_curvaturePhys S hK
  have hpoint : (fun r => curvaturePhys (S.shift (b := b)) P r) =
      fun r => curvaturePhys S P (r + P * b) := by
    funext r
    exact curvaturePhys_shift S hP r
  unfold thetaPhys
  rw [hpoint, intervalIntegral.integral_comp_add_right, zero_add]
  rw [add_assoc]
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]

end NormalizedSelectedRearClosure.SteeringData
