import UnitTangentIterates.GaugeRearFamilyFromFront
import UnitTangentIterates.ScaledCostDensity

/-!
# The numeric side conditions of the rear-family constructor are satisfiable
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real

namespace GaugeRearFamilyFromFront

/-- **The two numeric side conditions are consistent.**

The rear-family constructor closes with

    hnumA : 2 + 2 * khat * R           <= 1/P0
    hnumK : (d+2) + khat^2 + 2 * R * k <= 1/P0^2 + khat^2

where `R = rearDriftConst Qmax kh`.  Both are conditions on the *speed floor*
`P0` alone, and both hold once `P0` is small enough.  Making that explicit
matters for the same reason `exists_profileConstants` did: without it the
constructor could be vacuous, and every hypothesis discharged for it would be
discharged for nothing.

Note `khat^2` cancels in `hnumK`, so that condition does not constrain `khat` at
all - only `P0` against `d`, `k` and the drift constant. -/
theorem exists_speed_floor {khat kh Qmax d kx : ℝ} (hkhat : 0 ≤ khat)
    (hQ : 0 ≤ Qmax) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hd : 0 ≤ d) (hkx : 0 ≤ kx) :
    ∃ P0 : ℝ, 0 < P0 ∧
      2 + 2 * khat * rearDriftConst Qmax kh ≤ 1 / P0 ∧
      (d + 2) + khat ^ 2 + 2 * rearDriftConst Qmax kh * kx
        ≤ 1 / P0 ^ 2 + khat ^ 2 := by
  set R : ℝ := rearDriftConst Qmax kh with hR
  have hR0 : 0 ≤ R := rearDriftConst_nonneg hQ hkh0 hkh1
  set A : ℝ := 2 + 2 * khat * R with hA
  set Bq : ℝ := (d + 2) + 2 * R * kx with hB
  have hA2 : (2:ℝ) ≤ A := by rw [hA]; nlinarith
  have hApos : (0:ℝ) < A := by linarith
  have hB0 : (0:ℝ) ≤ Bq := by rw [hB]; nlinarith
  set M : ℝ := max A (Real.sqrt Bq) with hM
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le hApos (le_max_left _ _)
  have hM0 : M ≠ 0 := ne_of_gt hMpos
  refine ⟨1 / M, by positivity, ?_, ?_⟩
  · rw [one_div_one_div]
    exact le_max_left _ _
  · have hinv : 1 / (1 / M) ^ 2 = M ^ 2 := by field_simp
    rw [hinv]
    have hsq : Real.sqrt Bq ≤ M := le_max_right _ _
    have hsq0 : 0 ≤ Real.sqrt Bq := Real.sqrt_nonneg _
    have hBle : Bq ≤ M ^ 2 := by
      have := Real.sq_sqrt hB0
      nlinarith [hsq, hsq0]
    rw [hB] at hBle
    linarith

end GaugeRearFamilyFromFront
