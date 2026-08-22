import Mathlib
import UnitTangentIterates.MarkingFlowDefectC2
import UnitTangentIterates.MarkedShift
import UnitTangentIterates.SelectedInverseTubeCircle

/-!
# Non-vacuity of the `C²` marking defect

`MarkingFlowDefectC2.dist_le_of_flow_marking_int` bounds the marked distance
between a member of the tube and the same curve read in a gauge marking
produced by a flow.  This file checks that its hypothesis block is satisfiable,
on the simplest nontrivial marking: the circle of radius `ρ`, read in the
marking flowed at the constant rate `a`,

```
  Φ(t, u) = 2πρ·u + a t ,
```

the flow of the constant field `h(t,x) = a`.  The field has vanishing space
derivatives, so both flow defects vanish, while the marking is not the affine
one: it is the affine marking shifted by `aT`, and the curve it reads is the
circle with its marking rotated by `aT/(2πρ)`.  The bound of the general
statement therefore reads

```
  dist (shift (aT/2πρ) (circle ρ)) (circle ρ) ≤ markingC2Bound (|a|T) 0 0 (2πρ) (1/ρ) 0 ,
```

which is `marking_defect_c2_circle`.

Main result: `marking_defect_c2_circle`.
-/

noncomputable section

open Set Function

namespace MarkingDeviationC2Circle

open MarkedSpace MarkedShift MarkingDeviationC2 MarkingFlowDefectC2
  SelectedInverseCircle SelectedInverseTubeCircle

/-- The marking flowed at the constant rate `a` from the affine marking of
period `ell`. -/
def driftMarking (ell a : ℝ) : ℝ → ℝ → ℝ := fun t u => ell * u + a * t

/-- **The hypothesis block of the `C²` marking defect is satisfiable.**  The
circle of radius `ρ`, read in the marking flowed at the constant rate `a` over
the time `T`, is the circle with its marking shifted by `aT/(2πρ)`, and the
general bound holds for it with both flow defects equal to zero. -/
theorem marking_defect_c2_circle {rho a T : ℝ} (hrho : 0 < rho) (hT : 0 ≤ T) :
    dist (shiftData (a * T / (2 * Real.pi * rho)) (circleData rho)) (circleData rho)
      ≤ markingC2Bound (|a| * T) 0 0 (2 * Real.pi * rho) (1 / rho) 0 := by
  set L : ℝ := 2 * Real.pi * rho with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  set q : Data := circleData rho with hq
  set r : Data := shiftData (a * T / L) (circleData rho) with hr
  have hqmem : IsTubeMember (2 * Real.pi * rho) (1 / rho) (4 * rho) q :=
    circleData_mem_tube hrho
  have hrmem : IsTubeMember (2 * Real.pi * rho) (1 / rho) (4 * rho) r :=
    isTubeMember_shiftData hqmem _
  have hperim : perim q = L := perim_circleData hrho
  -- the curve of the circle in arclength, its tangent angle and its curvature
  have hev : ∀ s, HasDerivAt (ev q)
      (Complex.exp (Complex.I * ((circleAngle rho s : ℝ) : ℂ))) s := by
    intro s
    rw [hq, ev_circleData hrho]
    exact hasDerivAt_circleFront hrho s
  have hangle : ∀ s, HasDerivAt (circleAngle rho) ((fun _ : ℝ => 1 / rho) s) s := fun s =>
    hasDerivAt_circleAngle s
  -- the flow of the constant field
  have hlip : ∀ t : ℝ, LipschitzWith 0 (fun _ : ℝ => a) := fun _ => LipschitzWith.const a
  have hPhid : ∀ u t : ℝ,
      HasDerivAt (fun s => driftMarking L a s u) ((fun _ _ : ℝ => a) t (driftMarking L a t u)) t := by
    intro u t
    have h : HasDerivAt (fun s : ℝ => L * u + a * s) a t := by
      simpa using ((hasDerivAt_id t).const_mul a).const_add (L * u)
    exact h
  have hPhi0 : ∀ u, driftMarking L a 0 u = L * u := by
    intro u; simp [driftMarking]
  have hxd : ∀ s x : ℝ, HasDerivAt (fun _ : ℝ => a) ((fun _ _ : ℝ => (0:ℝ)) s x) x := fun _ _ =>
    hasDerivAt_const _ _
  have hxxd : ∀ s x : ℝ, HasDerivAt ((fun _ _ : ℝ => (0:ℝ)) s) ((fun _ _ : ℝ => (0:ℝ)) s x) x :=
    fun _ _ => hasDerivAt_const _ _
  -- the reparametrized datum is the shifted circle
  have hr1 : ∀ u, r.1 u = ev q (driftMarking L a T u) := by
    intro u
    rw [hr, shiftData_curve, ev, hperim, driftMarking]
    congr 1
    field_simp
  have hdev : ∀ u, |driftMarking L a T u - L * u| ≤ |a| * T := by
    intro u
    have : driftMarking L a T u - L * u = a * T := by rw [driftMarking]; ring
    rw [this, abs_mul, abs_of_nonneg hT]
  have hperiod : driftMarking L a T 1 - driftMarking L a T 0 = L := by
    simp [driftMarking]
  -- the general bound
  have hmain := MarkingFlowDefectC2.dist_le_of_flow_marking_int
    (h := fun _ _ : ℝ => a) (hx := fun _ _ : ℝ => (0:ℝ)) (hxx := fun _ _ : ℝ => (0:ℝ))
    (K := 0) (ell := L) (Phi := driftMarking L a) (K2 := 0)
    (C := fun _ => (0:ℝ)) (C2 := fun _ => (0:ℝ)) (Θ := circleAngle rho)
    (k := fun _ => 1 / rho) (kb := 1 / rho) (kL := 0) (e0 := |a| * T)
    hlip continuous_const hPhid hLpos hPhi0 hxd continuous_const hxxd continuous_const
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) continuous_const
    (fun _ _ => by norm_num) continuous_const hT
    (by positivity) hqmem hperim hev hangle
    (fun _ => by rw [abs_of_pos (by positivity : (0:ℝ) < 1 / rho)])
    (fun s t => by simp)
    hr1 (fun u => hrmem.hasDerivAt_curve u) (fun u => hrmem.hasDerivAt_vel u) hdev hperiod
  simpa [flowDefectC1Int, flowDefectC2Int] using hmain

end MarkingDeviationC2Circle
