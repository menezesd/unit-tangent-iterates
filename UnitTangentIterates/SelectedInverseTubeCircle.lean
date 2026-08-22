import Mathlib
import UnitTangentIterates.SelectedInverseTube
import UnitTangentIterates.SelectedInverseCircle
import UnitTangentIterates.MarkedSpaceCircle

/-!
# The marked selected inverse of a circle

The hypotheses of `SelectedInverseTube.exists_tube_member_rear` — the theorem
that the selected inverse takes a marked curve to a marked curve — are not
vacuous.  This file checks them for the circle of radius `r > 1`, seen as a
member of the tube of marked curves (`MarkedSpaceCircle.lean`):

* `ev_circleData` : the arclength parametrization of the marked circle is the
  circle `s ↦ r e^{is/r}`;
* `circleData_curvature_le` : its curvature is exactly `1/r`, so the assumed
  upper bound holds with `κ̂ = 1/r < 1`;
* `injOn_rearTrack_evCircleData` : every rear track built from an admissible
  steering angle of the marked circle is embedded;
* `exists_tube_member_rear_circle` : hence the marked circle of radius `r > 1`
  **has a marked selected inverse** — a member of the tube whose unit-tangent
  transform retraces it.
-/

noncomputable section

open Set Function

namespace SelectedInverseTubeCircle

open MarkedSpace SelectedInverseCircle

/-- The arclength parametrization of the marked circle of radius `r` is the
circle `s ↦ r e^{is/r}`. -/
theorem ev_circleData {r : ℝ} (hr : 0 < r) : ev (circleData r) = circleFront r := by
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hpine : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  funext s
  show (circleData r).1 (s / perim (circleData r)) = circleFront r s
  rw [perim_circleData hr, circleData_fst, normExp]
  unfold circleFront
  congr 1
  have harg : (2 : ℂ) * (Real.pi : ℂ) * ((s / (2 * Real.pi * r) : ℝ) : ℂ) * Complex.I
      = Complex.I * ((s / r : ℝ) : ℂ) := by
    have h2 : ((s / (2 * Real.pi * r) : ℝ) : ℂ) = (s : ℂ) / (2 * (Real.pi : ℂ) * (r : ℂ)) := by
      push_cast; ring
    rw [h2]
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hrne
    have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpine
    push_cast
    field_simp
  rw [harg]

/-- The curvature of the marked circle of radius `r` is exactly `1/r`. -/
theorem circleData_curvature_le {r : ℝ} (hr : 0 < r) (u : ℝ) :
    ((starRingEnd ℂ) ((circleData r).2.1 u) * (circleData r).2.2 u).im
      ≤ (1 / r) * ‖(circleData r).2.1 u‖ ^ 3 := by
  have hpi := Real.pi_pos
  have hnorm : ‖(circleData r).2.1 u‖ = 2 * Real.pi * r := by
    rw [circleData_vel]
    simp [abs_of_pos hpi, abs_of_pos hr]
  have hconj : (starRingEnd ℂ) ((circleData r).2.1 u)
      = ((2 * Real.pi * r : ℝ) : ℂ) * (-Complex.I) * (starRingEnd ℂ) (normExp u) := by
    rw [circleData_vel, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have him : ((starRingEnd ℂ) ((circleData r).2.1 u) * (circleData r).2.2 u).im
      = 8 * Real.pi ^ 3 * r ^ 2 := by
    rw [hconj, circleData_acc]
    have hmul : (((2 * Real.pi * r : ℝ) : ℂ) * (-Complex.I) * (starRingEnd ℂ) (normExp u))
        * (-((4 * Real.pi ^ 2 * r : ℝ) : ℂ) * normExp u)
        = (((2 * Real.pi * r : ℝ) : ℂ) * ((4 * Real.pi ^ 2 * r : ℝ) : ℂ)) * Complex.I
          * ((starRingEnd ℂ) (normExp u) * normExp u) := by
      ring
    rw [hmul, conj_mul_normExp, mul_one]
    have hcast : (((2 * Real.pi * r : ℝ) : ℂ) * ((4 * Real.pi ^ 2 * r : ℝ) : ℂ))
        = ((8 * Real.pi ^ 3 * r ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    simp only [Complex.mul_I_im, Complex.ofReal_re]
  rw [him, hnorm]
  have : (1 / r) * (2 * Real.pi * r) ^ 3 = 8 * Real.pi ^ 3 * r ^ 2 := by
    field_simp
    ring
  rw [this]

/-- Every rear track built from an admissible steering angle of the marked
circle of radius `r > 1` is embedded on one period. -/
theorem injOn_rearTrack_evCircleData {r : ℝ} (hr : 1 < r) (Θ K dl : ℝ → ℝ)
    (hX : ∀ s, HasDerivAt (ev (circleData r)) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hdlper : Periodic dl (perim (circleData r)))
    (hdlmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin (1 / r)))
    (hdlode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) :
    InjOn (RearTrack.rearTrack (ev (circleData r)) Θ dl) (Ico 0 (perim (circleData r))) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hev := ev_circleData hr0
  have hperim := perim_circleData hr0
  have hppos : 0 < 2 * Real.pi * r := by positivity
  have hkap1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have hkmin : 0 < 1 / r := by positivity
  rw [hev] at hX ⊢
  rw [hperim] at hdlper ⊢
  -- the front's curvature is `1/r`
  have hXc : ∀ s, HasDerivAt (circleFront r)
      (Complex.exp (Complex.I * ((circleAngle r s : ℝ) : ℂ))) s := hasDerivAt_circleFront hr0
  have hKeq : ∀ s, K s = 1 / r := fun s =>
    SelectedInverseTube.curvature_unique hX hXc hΘ (fun t => hasDerivAt_circleAngle t) s
  -- the steering angle is the constant `arcsin (1/r)`
  set d0 : ℝ := Real.arcsin (1 / r) with hd0
  have hsin : Real.sin d0 = 1 / r := Real.sin_arcsin (by linarith) hkap1.le
  have hd0nonneg : 0 ≤ d0 := Real.arcsin_nonneg.mpr hkmin.le
  have hd0le : d0 ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hdlconst : dl = fun _ => d0 := by
    refine Shadowing.steering_unique (K := K) hppos hdlode ?_ hdlper (fun s => by simp) ?_ ?_
    · intro s
      have : K s - Real.sin d0 = 0 := by rw [hKeq s, hsin]; ring
      rw [this]
      exact hasDerivAt_const s d0
    · intro s
      exact ⟨by linarith [(hdlmem s).1], le_trans (hdlmem s).2 hd0le⟩
    · exact fun s => ⟨by linarith, hd0le⟩
  rw [hdlconst]
  -- the rear track only depends on the front's unit tangent
  have hexp : ∀ s, Complex.exp (Complex.I * (Θ s : ℂ))
      = Complex.exp (Complex.I * ((circleAngle r s : ℝ) : ℂ)) := fun s => (hX s).unique (hXc s)
  have hrear : RearTrack.rearTrack (circleFront r) Θ (fun _ => d0)
      = RearTrack.rearTrack (circleFront r) (circleAngle r) (fun _ => d0) := by
    funext s
    simp only [RearTrack.rearTrack, RearTrack.rearAngle]
    congr 1
    have hsplitΘ : ((Θ s - d0 : ℝ) : ℂ) = (Θ s : ℂ) + ((-d0 : ℝ) : ℂ) := by push_cast; ring
    have hsplitA : ((circleAngle r s - d0 : ℝ) : ℂ)
        = ((circleAngle r s : ℝ) : ℂ) + ((-d0 : ℝ) : ℂ) := by push_cast; ring
    rw [hsplitΘ, hsplitA, mul_add, mul_add, Complex.exp_add, Complex.exp_add, hexp s]
  rw [hrear]
  exact injOn_rearTrack_circle hr d0

/-- **The marked circle of radius `r > 1` has a marked selected inverse.**  An
instance of `SelectedInverseTube.exists_tube_member_rear`, showing that its
hypotheses are satisfiable. -/
theorem exists_tube_member_rear_circle {r : ℝ} (hr : 1 < r) :
    ∃ (q : Data) (LR dR : ℝ), 0 < LR ∧ 0 < dR ∧
      IsTubeMember LR ((1 / r) / Real.sqrt (1 - (1 / r) ^ 2)) dR q ∧
      perim q = LR ∧ perim q ≤ perim (circleData r) ∧
      MainTheoremConditional.IsOval (ev q) ∧
      (∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im
        ≤ (1 / r) / Real.sqrt (1 - (1 / r) ^ 2) * ‖q.2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev q)) = range (ev (circleData r)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hppos : 0 < 2 * Real.pi * r := by positivity
  have hkmin : 0 < 1 / r := by positivity
  have hkap1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  exact SelectedInverseTube.exists_tube_member_rear hppos hkmin hkap1
    (circleData_mem_tube hr0) (circleData_curvature_le hr0)
    (fun Θ K dl hX hΘ hdlper hdlmem hdlode =>
      injOn_rearTrack_evCircleData hr Θ K dl hX hΘ hdlper hdlmem hdlode)

end SelectedInverseTubeCircle
