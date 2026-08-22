import Mathlib
import UnitTangentIterates.TurningNumber
import UnitTangentIterates.FrontFromPath

/-!
# The turning hypothesis of a normal path, produced from the curvature pinching

The statements of `FrontFromPath.lean` and of the path-distance files that rest
on it carry the hypothesis

`hturn : ∀ t, ∫_0^1 (conj V(t,u) · A(t,u)).im / P(t)² = 2π`,

that is, that each slice of the normal path has total turning `2π`.  This is
the turning-number normalization, the one global topological fact those files
assume.

`FrontFromPath.exists_int_turning` already shows that the increment of the
tangent angle over one period is `2πn` for an integer `n`: the tangent of a
closed slice is periodic, so the increment is quantized.  Since the increment
*is* the total turning of the slice, a two-sided bound on the slice curvature
pins `n` down:

* `turning_of_slice_of_pinched` — if the arclength curvature of the slice is
  pinched by `0 < kmin ≤ k ≤ kmax` with `kmax·P(t) < 4π`, then the total turning
  of that slice is exactly `2π`;
* `turning_of_path_of_pinched` — the hypothesis `hturn` itself, for a path all
  of whose slices are so pinched.

So for the curves the paper works with — closed convex slices, of curvature
pinched between two positive constants and of length below the threshold
`4π/kmax` — the turning hypothesis is no longer an assumption.
-/

noncomputable section

open Real Set Function MeasureTheory

namespace TurningNumberPath

open FrontFromPath

variable {V A : ℝ → ℝ → ℂ} {P : ℝ → ℝ}

/-- The total turning of the slice, in its own arclength, is the normalized
integral appearing in the hypothesis `hturn`. -/
theorem integral_curvOfPath_eq {t : ℝ} (hP : 0 < P t) :
    (∫ x in (0 : ℝ)..(P t), curvOfPath V A P t x)
      = ∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2 := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (curvOfPath V A P t) (P t)
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  have hu : P t * u / P t = u := by field_simp
  rw [curvOfPath, hu]
  field_simp

/-- **The total turning of a pinched closed slice is `2π`.**  The increment of
the tangent angle over one period is `2πn` (`FrontFromPath.exists_int_turning`)
and equals the total curvature of the slice, which lies in `(0, 4π)` under the
pinching `0 < kmin ≤ k ≤ kmax`, `kmax·P(t) < 4π`; hence `n = 1`. -/
theorem turning_of_slice_of_pinched {t kmin kmax : ℝ}
    (hA : ∀ u, HasDerivAt (V t) (A t u) u)
    (hVper : Periodic (V t) 1) (hAper : Periodic (A t) 1)
    (hVcont : Continuous (V t)) (hAcont : Continuous (A t))
    (hspeed : ∀ u, ‖V t u‖ = P t) (hP : 0 < P t)
    (hkmin : 0 < kmin) (hlow : ∀ s, kmin ≤ curvOfPath V A P t s)
    (hhigh : ∀ s, curvOfPath V A P t s ≤ kmax)
    (hsmall : kmax * P t < 4 * π) :
    (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2) = 2 * π := by
  have hcurvcont : Continuous (curvOfPath V A P t) := continuous_curvOfPath hVcont hAcont
  obtain ⟨n, hn⟩ := exists_int_turning hA hVper hAper hVcont hAcont hspeed hP
  -- the increment of the tangent angle over one period is the total curvature
  have hincr : angleOfPath V A P t (0 + P t) - angleOfPath V A P t 0
      = ∫ x in (0 : ℝ)..(P t), curvOfPath V A P t x := by
    simp [angleOfPath]
  have hval : (∫ x in (0 : ℝ)..(P t), curvOfPath V A P t x) = 2 * π * n := by
    rw [← hincr, hn 0]; ring
  -- two-sided bounds on the total curvature
  have hlb : kmin * P t ≤ ∫ x in (0 : ℝ)..(P t), curvOfPath V A P t x := by
    have := intervalIntegral.integral_mono_on (f := fun _ : ℝ => kmin)
      (g := curvOfPath V A P t) hP.le
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := kmin))
      (hcurvcont.intervalIntegrable 0 (P t)) (fun x _ => hlow x)
    simpa [mul_comm] using this
  have hub : (∫ x in (0 : ℝ)..(P t), curvOfPath V A P t x) ≤ kmax * P t := by
    have := intervalIntegral.integral_mono_on (f := curvOfPath V A P t)
      (g := fun _ : ℝ => kmax) hP.le (hcurvcont.intervalIntegrable 0 (P t))
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := kmax)) (fun x _ => hhigh x)
    simpa [mul_comm] using this
  have hpos : 0 < kmin * P t := by positivity
  have hpi : (0:ℝ) < π := Real.pi_pos
  -- hence `0 < 2πn < 4π`, so `n = 1`
  have hn1 : n = 1 := by
    rw [hval] at hlb hub
    have h1 : (0:ℝ) < (n:ℝ) := by nlinarith
    have h2 : (n:ℝ) < 2 := by nlinarith
    have h1' : (0:ℤ) < n := by exact_mod_cast h1
    have h2' : n < 2 := by exact_mod_cast h2
    omega
  rw [← integral_curvOfPath_eq hP, hval, hn1]
  push_cast
  ring

/-- **The turning hypothesis of a normal path, produced.**  If every slice is a
closed curve of constant speed whose arclength curvature is pinched by
`0 < kmin ≤ k ≤ kmax` with `kmax·P(t) < 4π`, then every slice has total turning
`2π` — which is the hypothesis `hturn` of `FrontFromPath.lean` and of the
path-distance statements built on it. -/
theorem turning_of_path_of_pinched {kmin kmax : ℝ}
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hVper : ∀ t, Periodic (V t) 1) (hAper : ∀ t, Periodic (A t) 1)
    (hVcont : ∀ t, Continuous (V t)) (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t) (hP : ∀ t, 0 < P t)
    (hkmin : 0 < kmin) (hlow : ∀ t s, kmin ≤ curvOfPath V A P t s)
    (hhigh : ∀ t s, curvOfPath V A P t s ≤ kmax)
    (hsmall : ∀ t, kmax * P t < 4 * π) :
    ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2) = 2 * π :=
  fun t => turning_of_slice_of_pinched (hA t) (hVper t) (hAper t) (hVcont t) (hAcont t)
    (hspeed t) (hP t) hkmin (hlow t) (hhigh t) (hsmall t)

end TurningNumberPath
