import Mathlib
import UnitTangentIterates.ModelPeriodContinuity

/-!
# The perimeter defect of one period is bounded below

The separations of the model pseudo-orbit are tied by `Q(H_{n+1}) = H_n`, `Q`
the rear period of the front of separation `H`.  For the sequence to escape to
infinity — the growth clause of the lemma *Large-separation threshold* — the
perimeter defect `H - Q(H)` of one period must be bounded below away from zero,
uniformly in `H`.

It is: `1 - √(1-z²) ≥ z²/2` on `[-1,1]`, the square of the periodized pulse
dominates the periodization of the square (the terms are nonnegative), and the
mass of a periodization over one period is the total mass of the pulse, so

`H - Q(H) = ∫₀^H (1 - cos δ_H) ≥ ½∫₀^H Y_H² ≥ ½∫_ℝ y²`,

a constant depending on the pulse alone (`rearPeriod_le_sub`).

-/

noncomputable section

open Real MeasureTheory Filter Topology Set

namespace ModelPeriodGrowth

open ModelOrbitDefect ModelPeriodContinuity

variable {y : ℝ → ℝ} {C Km alpha : ℝ}

/-- `1 - √(1-z²) ≥ z²/2` for `|z| ≤ 1`. -/
theorem half_sq_le_one_sub_sqrt {z : ℝ} (hz : z ^ 2 ≤ 1) :
    z ^ 2 / 2 ≤ 1 - Real.sqrt (1 - z ^ 2) := by
  have h0 : (0:ℝ) ≤ 1 - z ^ 2 := by linarith
  have hle : Real.sqrt (1 - z ^ 2) ≤ 1 - z ^ 2 / 2 := by
    have hnn : (0:ℝ) ≤ 1 - z ^ 2 / 2 := by nlinarith [sq_nonneg z]
    refine (Real.sqrt_le_left hnn).mpr ?_
    nlinarith [sq_nonneg z]
  linarith

/-- **The periodization of the square is dominated by the square of the
periodization**, the terms being nonnegative. -/
theorem tsum_sq_le_sq_tsum (ha : 0 < alpha) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|)) {H : ℝ} (hH : 0 < H) (s : ℝ) :
    (∑' m : ℤ, y (s - m * H) ^ 2) ≤ (∑' m : ℤ, y (s - m * H)) ^ 2 := by
  have hsum : Summable (fun m : ℤ => y (s - m * H)) :=
    PeriodizationDeriv.summable_periodization_of_le (s := s) ha hyb hH le_rfl
  set S : ℝ := ∑' m : ℤ, y (s - m * H) with hS
  have hle : ∀ m : ℤ, y (s - m * H) ≤ S := fun m =>
    hsum.le_tsum m fun j _ => hy0 _
  have hS0 : 0 ≤ S := tsum_nonneg fun m => hy0 _
  have hsum2 : Summable (fun m : ℤ => S * y (s - m * H)) := hsum.mul_left S
  have hsumsq : Summable (fun m : ℤ => y (s - m * H) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_) hsum2
    have h1 := hy0 (s - m * H)
    nlinarith [hle m]
  calc (∑' m : ℤ, y (s - m * H) ^ 2) ≤ ∑' m : ℤ, S * y (s - m * H) := by
        refine Summable.tsum_le_tsum (fun m => ?_) hsumsq hsum2
        have h1 := hy0 (s - m * H)
        nlinarith [hle m]
    _ = S * S := by rw [tsum_mul_left, ← hS]
    _ = S ^ 2 := by ring

/-- **The perimeter defect of one period is at least half the `L²` mass of the
pulse**, uniformly in the separation. -/
theorem rearPeriod_le_sub (ha : 0 < alpha) (hyc : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyKm : ∀ s, y s ≤ Km)
    (hyb : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|))
    (hsqint : Integrable fun s => y s ^ 2)
    {H : ℝ} (hH : 0 < H) (hYle : ∀ s, |periodizedPulse y H s| ≤ 1) :
    rearPeriod y H ≤ H - (∫ s, y s ^ 2) / 2 := by
  have hKm0 : 0 ≤ Km := le_trans (hy0 0) (hyKm 0)
  have hC0 : 0 ≤ C := PeriodizationDeriv.const_nonneg hyb
  -- the periodization and its continuity
  have hYc : Continuous (periodizedPulse y H) :=
    PeriodizedTurning.continuous_periodization (alpha := alpha) (P := H) (C := C)
      ha hH hyc hyb
  have hsqb : ∀ s, |y s ^ 2| ≤ (Km * C) * Real.exp (-alpha * |s|) := by
    intro s
    have h1 := hy0 s
    have h2 := hyKm s
    have h3 : |y s| ≤ C * Real.exp (-alpha * |s|) := hyb s
    rw [abs_of_nonneg (sq_nonneg _)]
    have h4 : y s ≤ C * Real.exp (-alpha * |s|) := by
      rw [abs_of_nonneg h1] at h3; exact h3
    nlinarith [Real.exp_pos (-alpha * |s|)]
  have hZc : Continuous fun s => ∑' m : ℤ, y (s - m * H) ^ 2 :=
    PeriodizedTurning.continuous_periodization (y := fun s => y s ^ 2) (alpha := alpha)
      (P := H) (C := Km * C) ha hH (hyc.pow 2) hsqb
  -- the mass of the periodized square over one period
  have hmass2 : (∫ u in (0:ℝ)..(0 + H), ∑' m : ℤ, y (u - m * H) ^ 2) = ∫ s, y s ^ 2 :=
    PeriodizedTurning.integral_periodization_eq_integral (y := fun s => y s ^ 2)
      hH hsqint (fun u => sq_nonneg _) 0
  -- the defect
  have hcosc : Continuous fun s => Real.cos (modelSteering (periodizedPulse y H) s) :=
    Real.continuous_cos.comp (continuous_modelSteering hYc)
  have hdef : H - rearPeriod y H
      = ∫ s in (0:ℝ)..H, (1 - Real.cos (modelSteering (periodizedPulse y H) s)) := by
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
      (hcosc.intervalIntegrable _ _), intervalIntegral.integral_const]
    simp [rearPeriod, modelRearArclength, RearTrack.rearArclength]
  have hpt : ∀ s, (∑' m : ℤ, y (s - m * H) ^ 2) / 2
      ≤ 1 - Real.cos (modelSteering (periodizedPulse y H) s) := by
    intro s
    rw [cos_modelSteering]
    have h1 : (periodizedPulse y H s) ^ 2 ≤ 1 := by
      have := hYle s
      nlinarith [abs_nonneg (periodizedPulse y H s), abs_le.mp this]
    have h2 := half_sq_le_one_sub_sqrt h1
    have h3 : (∑' m : ℤ, y (s - m * H) ^ 2) ≤ (periodizedPulse y H s) ^ 2 :=
      tsum_sq_le_sq_tsum ha hy0 hyb hH s
    linarith
  have hmono : (∫ s in (0:ℝ)..H, (∑' m : ℤ, y (s - m * H) ^ 2) / 2)
      ≤ ∫ s in (0:ℝ)..H, (1 - Real.cos (modelSteering (periodizedPulse y H) s)) := by
    refine intervalIntegral.integral_mono_on hH.le
      ((hZc.div_const 2).intervalIntegrable _ _)
      ((continuous_const.sub hcosc).intervalIntegrable _ _) (fun s _ => hpt s)
  have hhalf : (∫ s in (0:ℝ)..H, (∑' m : ℤ, y (s - m * H) ^ 2) / 2)
      = (∫ s, y s ^ 2) / 2 := by
    rw [intervalIntegral.integral_div]
    congr 1
    simpa using hmass2
  linarith [hdef, hmono, hhalf]

end ModelPeriodGrowth
