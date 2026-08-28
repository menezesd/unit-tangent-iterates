import UnitTangentIterates.VariableMarkedTubeGeometry

/-!
# Physical length under variable markings

For nonaffine marked data, `MarkedSpace.perim` is only the speed at the marked
basepoint.  The geometric perimeter is instead the integral of the speed.
This file records its Lipschitz dependence on marked `C2` data.
-/

noncomputable section

open Set Function

namespace VariableMarkedPhysicalLength

open MarkedSpace MarkedReparam

/-- Physical total length is `1`-Lipschitz for the marked product metric. -/
theorem abs_totalLength_sub_le_dist (p q : Data) :
    |totalLength (fun u => p.2.1 u) - totalLength (fun u => q.2.1 u)| ≤
      dist p q := by
  let d := dist p q
  have hpq : ∀ u, ‖p.2.1 u‖ ≤ ‖q.2.1 u‖ + d := by
    intro u
    calc
      ‖p.2.1 u‖ ≤ ‖q.2.1 u‖ + ‖p.2.1 u - q.2.1 u‖ := by
        simpa [add_comm] using
          (norm_le_norm_add_norm_sub' (p.2.1 u) (q.2.1 u))
      _ ≤ ‖q.2.1 u‖ + d := by
        linarith [MarkedSpace.dist_vel_apply_le p q u]
  have hqp : ∀ u, ‖q.2.1 u‖ ≤ ‖p.2.1 u‖ + d := by
    intro u
    calc
      ‖q.2.1 u‖ ≤ ‖p.2.1 u‖ + ‖q.2.1 u - p.2.1 u‖ := by
        simpa [add_comm] using
          (norm_le_norm_add_norm_sub' (q.2.1 u) (p.2.1 u))
      _ ≤ ‖p.2.1 u‖ + d := by
        have h := MarkedSpace.dist_vel_apply_le p q u
        rw [norm_sub_rev]
        linarith
  have hpInt : totalLength (fun u => p.2.1 u) ≤
      totalLength (fun u => q.2.1 u) + d := by
    have hqcont : Continuous (fun u : ℝ => ‖q.2.1 u‖ + d) :=
      q.2.1.continuous.norm.add continuous_const
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (show (0 : ℝ) ≤ 1 by norm_num)
      ((p.2.1.continuous.norm).intervalIntegrable 0 1)
      (hqcont.intervalIntegrable 0 1)
      (fun u _ => hpq u)
    calc
      totalLength (fun u => p.2.1 u) ≤
          ∫ u in (0 : ℝ)..1, (‖q.2.1 u‖ + d) := by
        simpa [totalLength] using hmono
      _ = totalLength (fun u => q.2.1 u) + d := by
        rw [intervalIntegral.integral_add
          (q.2.1.continuous.norm.intervalIntegrable 0 1)
          intervalIntegral.intervalIntegrable_const]
        simp [totalLength]
  have hqInt : totalLength (fun u => q.2.1 u) ≤
      totalLength (fun u => p.2.1 u) + d := by
    have hpcont : Continuous (fun u : ℝ => ‖p.2.1 u‖ + d) :=
      p.2.1.continuous.norm.add continuous_const
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (show (0 : ℝ) ≤ 1 by norm_num)
      ((q.2.1.continuous.norm).intervalIntegrable 0 1)
      (hpcont.intervalIntegrable 0 1)
      (fun u _ => hqp u)
    calc
      totalLength (fun u => q.2.1 u) ≤
          ∫ u in (0 : ℝ)..1, (‖p.2.1 u‖ + d) := by
        simpa [totalLength] using hmono
      _ = totalLength (fun u => p.2.1 u) + d := by
        rw [intervalIntegral.integral_add
          (p.2.1.continuous.norm.intervalIntegrable 0 1)
          intervalIntegral.intervalIntegrable_const]
        simp [totalLength]
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- For an ordinary tube member, physical length is its marked perimeter. -/
theorem totalLength_eq_perim_of_tube
    {c kmin dlt : ℝ} {p : Data} (hp : IsTubeMember c kmin dlt p) :
    totalLength (fun u => p.2.1 u) = perim p := by
  have hconst : (fun u => ‖p.2.1 u‖) = fun _ : ℝ => perim p := by
    funext u
    exact norm_vel_eq_perim hp u
  rw [totalLength, hconst, intervalIntegral.integral_const]
  simp

/-- Distance from an ordinary model controls the physical perimeter of an
arbitrarily marked endpoint. -/
theorem abs_totalLength_sub_perim_le_dist
    {c kmin dlt : ℝ} {base p : Data}
    (hbase : IsTubeMember c kmin dlt base) :
    |totalLength (fun u => p.2.1 u) - perim base| ≤ dist base p := by
  rw [← totalLength_eq_perim_of_tube hbase]
  simpa [abs_sub_comm, dist_comm] using abs_totalLength_sub_le_dist base p

end VariableMarkedPhysicalLength
