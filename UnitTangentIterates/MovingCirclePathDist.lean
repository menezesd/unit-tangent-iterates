import Mathlib
import UnitTangentIterates.MovingCirclePath
import UnitTangentIterates.RearOwnPathDistFrameDrift

/-!
# A genuine instance of the path-distance assembly in which the rear length moves

`RearOwnPathDistFrameDrift.pathDist_le_of_front_frame_variable` bounds the path
pseudodistance of the selected rears of a path of fronts under hypotheses which
are all on the front data, and which no longer force the arclength period of the
rear to be constant along the path: it is only asked to depend differentiably on
the time.  `RearOwnPathDistCircleDrift.lean` checks that those hypotheses can all
be met, but by a *resting* circle, whose rear period does not move.

Here they are met by the family of `MovingCircleFront.lean`: the circle of
radius `1 / sin A(t)` with the steering profile `A` decreasing from `π/4` to
`π/6`, whose rear is the circle of length

```
  Q(t) = 2π cos A(t) / sin A(t) ,
```

so `Q(0) = 2π` and `Q(1) = 2π√3`: the length of the rear really moves
(`MovingCircle.rearPeriod_ne`).  The path of fronts is the normal path
`MovingCirclePath.movingPath`.

Main result: `movingCircle_instance_variable`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath RearTrack
  RearFamilyFrame RearOwnArclength RearOwnMotion MovingCircleProfile MovingCircle
  MovingCirclePath
open scoped BoundedContinuousFunction

namespace MovingCirclePathDist

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistFrameDrift

/-! ### The rear as a marked curve -/

/-- The selected rear at time `0`, in the normalized parameter. -/
def rearData0 : Data :=
  (BoundedContinuousFunction.ofNormedAddCommGroup
      (fun u => rearOwn Ff Th de sff 0 (2 * Real.pi * u))
      (by
        show Continuous fun u : ℝ =>
          Ff 0 (sff 0 (2 * Real.pi * u))
            - Complex.exp (Complex.I * (rearAngle (Th 0) (de 0) (sff 0 (2 * Real.pi * u)) : ℂ))
        simp only [Ff, Th, de, sff, rearAngle]
        fun_prop (disch := intros; simp [sA_ne, cA_ne]))
      (1 / sA 0 + 1) (fun u => norm_rearOwn_le 0 _), 0, 0)

theorem rearData0_apply (u : ℝ) :
    rearData0.1 u = rearOwn Ff Th de sff 0 (rearArclength (de 0) (Pp 0) * u) := by
  rw [rearPeriod_zero]
  rfl

/-! ### The rear period moves differentiably -/

theorem hasDerivAt_rearPeriod (t : ℝ) :
    HasDerivAt (fun r => rearArclength (de r) (Pp r))
      (-(2 * Real.pi) * profD t / (sA t) ^ 2) t := by
  have heq : (fun r => rearArclength (de r) (Pp r)) = fun r => 2 * Real.pi * cA r / sA r :=
    funext rearPeriod_eq
  rw [heq]
  have h := ((hasDerivAt_cA t).const_mul (2 * Real.pi)).div (hasDerivAt_sA t) (sA_ne t)
  refine h.congr_deriv ?_
  have hpy : (sA t) ^ 2 + (cA t) ^ 2 = 1 := by
    simp [sA, cA, Real.sin_sq_add_cos_sq]
  have hs := sA_ne t
  field_simp
  linear_combination (-(profD t)) * hpy

/-! ### The family is frozen outside the time window -/

theorem Ydot_clamp (a x : ℝ) : Ydotf a x = Ydotf (clampT 0 1 a) x := by
  rcases le_or_gt 0 a with h0 | h0
  · rcases le_or_gt a 1 with h1 | h1
    · rw [clampT_of_mem ⟨h0, h1⟩]
    · have hc : clampT 0 1 a = 1 := by
        rw [clampT, min_eq_right h1.le, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
      rw [hc, Ydot_eq_zero (profD_of_gt (by linarith)) x,
        Ydot_eq_zero (profD_of_gt (by norm_num)) x]
  · have hc : clampT 0 1 a = 0 := by
      rw [clampT, min_eq_left (by linarith : a ≤ (1:ℝ)), max_eq_left h0.le]
    rw [hc, Ydot_eq_zero (profD_of_lt (by linarith)) x,
      Ydot_eq_zero (profD_of_lt (by norm_num)) x]

theorem ang_clamp (a x : ℝ) :
    rearOwnAngle Th de sff a x = rearOwnAngle Th de sff (clampT 0 1 a) x := by
  rw [rearOwnAngle_eq, rearOwnAngle_eq, cA, cA, sA, sA, ← prof_clamp]

theorem frameNormal_rest {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) :
    (fun x => frameNormal Ydotf (rearOwnAngle Th de sff) t x) = fun _ => 0 := by
  funext x
  simp [frameNormal, Ydot_eq_zero (profD_eq_zero_outside ht) x]

/-! ### The assembly -/

/-- **The hypotheses of the path-distance assembly with the rear length free are
met by a family whose rear length really moves.**

The front is the circle of radius `1/sin A(t)`, `A` decreasing smoothly from
`π/4` to `π/6` between the times `0` and `1`; its selected rear is the circle of
length `2π cos A / sin A`, which moves from `2π` to `2π√3`.  Every hypothesis of
`RearOwnPathDistFrameDrift.pathDist_le_of_front_frame_variable` holds for it, and
the bound it gives is stated here with all the constants explicit. -/
theorem movingCircle_instance_variable :
    ∃ (rL rB : ℝ) (Phi : ℝ → ℝ → ℝ),
      rearArclength (de 0) (Pp 0) = 2 * Real.pi ∧
      rearArclength (de 1) (Pp 1) = 2 * Real.pi * Real.sqrt 3 ∧
      (∀ u, Phi 0 u = 2 * Real.pi * u) ∧
      (∀ u, rearData0.1 u = rearOwn Ff Th de sff 0 (2 * Real.pi * u)) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn Ff Th de sff 1 (Phi 1 u)) →
        pathDist rearData0 q' ≤
          gaugeJacobiConst (2 * Real.pi) (4 * Real.pi) (Real.sin (Real.pi / 4)) rL rB 1
            (2 * Real.pi) * cost movingPath := by
  have hpi := Real.pi_pos
  -- the curvature bound
  have harcsin : Real.arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 :=
    Real.arcsin_sin (by linarith) (by linarith)
  have hsin4 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hsin4pos : 0 ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  obtain ⟨rL, rB, Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_frame_variable
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
    (P := Pp) (Qf' := fun t => -(2 * Real.pi) * profD t / (sA t) ^ 2)
    (F := Ff) (Fdot := Fdotf) (Fdots := Fdotsf) (Ydot := Ydotf)
    (Θ := Th) (δ := de) (K := Kk) (etaF := etaFf) (etaFs := fun _ _ => 0)
    (sf := sff) (sft := sfft) (dt := ww) (Θdot := Thdot) (w := ww)
    (Θdots := Thdots) (ws := fun _ _ => 0)
    movingPath rearData0
    (by positivity) hsin4pos hsin4
    -- the two-sided bound for the front period
    (fun t => by
      rw [Pp, le_div_iff₀ (sA_pos t)]
      nlinarith [sA_le t, Real.sin_le_one (prof t), sA_pos t])
    (fun t => by
      rw [Pp, div_le_iff₀ (sA_pos t)]
      nlinarith [sA_ge t])
    hasDerivAt_Ff_space hasDerivAt_Th_space hasDerivAt_de_space
    (fun t s => (prof_pos t).le)
    (fun t s => by rw [harcsin]; exact prof_le t)
    de_periodic
    (fun t s => by
      rw [Kk, abs_of_pos (sA_pos t)]
      exact sA_le t)
    (fun t => continuous_const)
    Ff_periodic Th_periodic
    (contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_Th.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_de.of_le (by exact ENat.LEInfty.out))
    hasDerivAt_de_time
    (by
      show Continuous fun p : ℝ × ℝ => profD p.1
      exact contDiff_profD.continuous.comp continuous_fst)
    etaF_eq
    (fun t s => hasDerivAt_const s (etaFf t 0))
    (fun t => continuous_const)
    (fun t s => rfl)
    (fun t u => rfl)
    sff_inv hasDerivAt_sff_time hasDerivAt_Ff_time hasDerivAt_Th_time hasDerivAt_de_time
    hasDerivAt_Fdot_space hasDerivAt_Thdot_space hasDerivAt_ww_space
    (contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_Th.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_de.of_le (by exact ENat.LEInfty.out))
    (fun t x => rfl)
    hasDerivAt_rearPeriod
    (contDiff_uncurry_Ydot.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_ang.of_le (by exact ENat.LEInfty.out))
    Ydot_clamp ang_clamp
    (fun t ht => frameNormal_rest ht)
    (fun u => rearData0_apply u)
  refine ⟨rL, rB, Phi, rearPeriod_zero, rearPeriod_one, ?_, fun u => rfl, ?_⟩
  · intro u
    have h := hPhi0 u
    rwa [rearPeriod_zero] at h
  · intro q' hq'
    have h := hPhi q' hq'
    rwa [rearPeriod_zero] at h

end MovingCirclePathDist
