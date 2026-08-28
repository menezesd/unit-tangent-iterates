import UnitTangentIterates.DataInterior
import UnitTangentIterates.HairpinPulseBarrier
import UnitTangentIterates.CanonicalConsecutiveInterior
import UnitTangentIterates.HairpinMassInterior

/-!
# The hairpin pulse-data package, from interior data

`FrontPeriodizationHairpin.exists_hairpin_pulse_data` is the package that the
curvature-measure matching theorem of Section 5
(`MatchingHairpinComplete.hairpin_matching_complete`, the paper's
`thm:L1match`) consumes.  It is proved from a profile smooth and positive on all
of `ℝ`, and it *constructs* the hairpin coordinates by compactness on `[0, π]`.

This file produces the same package from the regularity the paper actually
states — `f ∈ C^∞(0,π)` with barriers, and the coordinates given — so that
Section 5 becomes available on the endpoint-free route.

Every component has an interior source already in the development:

| component | source |
|---|---|
| curvature nonneg, tail | `curvField_pos_interior`, the hypothesis `hdecay` |
| curvature integrable | `HairpinMassInterior.integrableOn_curv_{Ioi,Iic}_of_comp` |
| pulse continuous, `y'` | `HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates` |
| pulse tails at `j = 0, 1` | the `decay` field of `data_of_interior` |
| `sup y ≤ b < 1` | `pulseField_le_of_barrier` |
| `|y'| ≤ D y` | the hypothesis `hrel` at `j = 1` |
-/

noncomputable section

open Set Real MeasureTheory HairpinRelative

open scoped ContDiff

namespace FrontPeriodizationHairpin

/-- **The hairpin pulse-data package, from interior data.**  This is
`exists_hairpin_pulse_data` with the global profile hypotheses replaced by
`f ∈ C^∞(0,π)` together with the paper's barrier, and with the coordinates
supplied rather than constructed. -/
theorem exists_hairpin_pulse_data_of_interior {f : ℝ → ℝ} {m A M : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t)
    {theta x : ℝ → ℝ}
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    (hsm : StrictMono theta)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hA : 0 ≤ A) (hM : 0 < M)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (relativeConst : ℕ → ℝ) (hrc0 : ∀ j, 0 ≤ relativeConst j)
    (hrel : ∀ j ≤ 4, ∀ s,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        ≤ relativeConst j * pulseField f (theta (x s))) :
    ∃ (yp : ℝ → ℝ) (alpha C D b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, 0 ≤ curvField f (theta u)) ∧
      Integrable (fun u => curvField f (theta u)) ∧
      (∀ u, |curvField f (theta u)| ≤ C * Real.exp (-alpha * |u|)) ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      Continuous (fun s => pulseField f (theta (x s))) ∧
      (∀ s, 0 ≤ pulseField f (theta (x s))) ∧
      (∀ s, pulseField f (theta (x s)) ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, pulseField f (theta (x s)) ≤ b) ∧
      (∀ s, HasDerivAt (fun s => pulseField f (theta (x s))) (yp s) s) ∧
      Continuous yp ∧
      (∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, |yp s| ≤ D * pulseField f (theta (x s))) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hyC := (HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf hfpos
    hmem hderiv hw).2.2
  have hcont : Continuous fun u => curvField f (theta u) :=
    continuous_curv_along_theta hf hfpos hmem hderiv
  have hnn : ∀ u, 0 ≤ curvField f (theta u) := fun u =>
    (curvField_pos_interior hfpos (hmem u)).le
  -- the tail constants of `data_of_interior`
  have hdecayJ : ∀ j ≤ 4, ∀ s : ℝ,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s| ≤
        relativeConst j * (A * Real.exp (A ^ 2 / 2)) * Real.exp (-|s| / M) :=
    fun j hj s => (PaperHairpinQuantitativeData.data_of_interior hf hm hlow hmem
      hval hderiv hxinv hw hsm hsurj hA hM hdecay relativeConst hrc0 hrel).decay
        j hj s
  set K0 : ℝ := relativeConst 0 * (A * Real.exp (A ^ 2 / 2)) with hK0def
  set K1 : ℝ := relativeConst 1 * (A * Real.exp (A ^ 2 / 2)) with hK1def
  set C : ℝ := max (max K0 K1) A with hCdef
  have hK0nn : 0 ≤ K0 := mul_nonneg (hrc0 0) (by positivity)
  have hC0 : 0 ≤ C := le_trans hK0nn (le_trans (le_max_left _ _) (le_max_left _ _))
  have hK0C : K0 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hK1C : K1 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hAC : A ≤ C := le_max_right _ _
  -- the exponential is the same, written two ways
  have hrw : ∀ s : ℝ, Real.exp (-|s| / M) = Real.exp (-(1 / M) * |s|) := by
    intro s; congr 1; ring
  refine ⟨iteratedDeriv 1 (fun r => pulseField f (theta (x r))), 1 / M, C,
    relativeConst 1, 1 / Real.sqrt (1 + m ^ 2), by positivity, hC0, hrc0 1,
    by positivity, one_div_sqrt_one_add_sq_lt_one hm, hnn, ?_, ?_, hmem, hval,
    hderiv, hxinv, hw, (hyC 0).continuous, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- integrability
    have hI : IntegrableOn (fun u => curvField f (theta u)) (Iic 0 ∪ Ioi 0) volume :=
      (HairpinMassInterior.integrableOn_curv_Iic_of_comp hcont hnn hdecay hM).union
        (HairpinMassInterior.integrableOn_curv_Ioi_of_comp hcont hnn hdecay hM)
    rwa [Set.Iic_union_Ioi, integrableOn_univ] at hI
  · -- curvature tail
    intro u
    rw [abs_of_nonneg (hnn u), ← hrw u]
    exact le_trans (hdecay u)
      (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)
  · -- pulse nonneg
    exact fun s => pulseField_nonneg_interior hfpos (hmem (x s))
  · -- pulse tail
    intro s
    have h := hdecayJ 0 (by norm_num) s
    rw [iteratedDeriv_zero, abs_of_nonneg
      (pulseField_nonneg_interior hfpos (hmem (x s))), hrw s] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hK0C (Real.exp_pos _).le)
  · -- pulse sup
    exact fun s => pulseField_le_of_barrier hm (hlow _ (hmem (x s))) (hmem (x s))
  · -- the derivative witness
    intro s
    have hd := (hyC 1).differentiable (by norm_num)
    simpa [iteratedDeriv_one] using (hd s).hasDerivAt
  · -- continuity of the derivative
    have := (hyC 2).continuous_deriv (by norm_num)
    simpa [iteratedDeriv_one] using this
  · -- derivative tail
    intro s
    have h := hdecayJ 1 (by norm_num) s
    rw [hrw s] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hK1C (Real.exp_pos _).le)
  · -- relative bound
    exact fun s => hrel 1 (by norm_num) s

end FrontPeriodizationHairpin
