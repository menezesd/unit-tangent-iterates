import UnitTangentIterates.ConfiguredUniformSubunitCurvature
import UnitTangentIterates.ConstructedProfileData

/-!
# Retaining the first relative pulse constant

The all-order interior discharge previously hid the first relative constant
behind an existential choice.  The subunit curvature estimate needs its
actual value.  This module retains the explicit constant produced by the
translator/Harnack calculation and records the elementary final smallness
step separately.
-/

noncomputable section

open Real Set HairpinRelative PaperHairpinQuantitativeData
open scoped ContDiff

namespace WideHairpinFirstRelativeBound

/-- The explicit order-one relative pulse constant from
`InteriorRelativeDischarge.rel_pulse_one_of_interior`. -/
def firstRelativeConst (f g : ℝ → ℝ) (m Am A M : ℝ) : ℝ :=
  (Am / m) * Real.exp
      ((|Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))| +
        A ^ 2 * M / 2) / m) /
      Real.sqrt (1 - (1 / Real.sqrt (1 + m ^ 2)) ^ 2) + 1

/-- The translator equations give the relative derivative estimate with the
displayed constant, rather than merely with an unspecified witness. -/
theorem firstRelativeConst_spec
    {f theta x g gp yp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hlow : ∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M)
    (hypd : ∀ s, HasDerivAt
      (fun r => pulseField f (theta (x r))) (yp s) s) :
    0 ≤ firstRelativeConst f g m Am A M ∧
      ∀ s, |yp s| ≤ firstRelativeConst f g m Am A M *
        pulseField f (theta (x s)) := by
  constructor
  · unfold firstRelativeConst
    have hratio : 0 ≤ Am / m := div_nonneg (hm.le.trans hmA) hm.le
    have hb : (1 : ℝ) / Real.sqrt (1 + m ^ 2) < 1 :=
      HairpinRelative.one_div_sqrt_one_add_sq_lt_one hm
    have hb0 : (0 : ℝ) ≤ 1 / Real.sqrt (1 + m ^ 2) := by positivity
    have hb_sq : (1 / Real.sqrt (1 + m ^ 2)) ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hb0 zero_le_one).2 hb
    have hs : 0 < Real.sqrt (1 - (1 / Real.sqrt (1 + m ^ 2)) ^ 2) :=
      Real.sqrt_pos.2 (by nlinarith)
    positivity
  · simpa [firstRelativeConst] using
      (rel_pulse_one_of_interior d hm hmA hf hlow hupp hdecay hM hypd)

/-- All relative pulse bounds can be chosen while retaining the exact
order-one constant. -/
theorem hrelj_of_interior_with_first
    {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hlow : ∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M)
    (hsurj : ∀ z ∈ Ioo (0 : ℝ) Real.pi, ∃ u, theta u = z) :
    ∃ relativeConst : ℕ → ℝ,
      (∀ j, 0 ≤ relativeConst j) ∧
      (relativeConst 1 = firstRelativeConst f g m Am A M) ∧
      ∀ j ≤ 4, ∀ s,
        |iteratedDeriv j (fun r => pulseField f (theta (x r))) s| ≤
          relativeConst j * pulseField f (theta (x s)) := by
  have hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  obtain ⟨-, -, hyC⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have hYd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r)))
      (iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s) s := fun s => by
    have h := hasDerivAt_iteratedDeriv (hyC 2) (show 0 < 2 by norm_num) s
    rwa [iteratedDeriv_zero] at h
  obtain ⟨hD1, h1⟩ := firstRelativeConst_spec d hm hmA hf hlow hupp hdecay hM hYd
  obtain ⟨D2, hD2, h2⟩ := rel_pulse_two_of_interior d hm hmA hf hlow hupp
    hdecay hM hsurj hYd
  obtain ⟨D3, hD3, h3⟩ := rel_pulse_three_of_interior d hm hmA hf hlow hupp
    hdecay hM hsurj
  obtain ⟨D4, hD4, h4⟩ := rel_pulse_four_of_interior d hm hmA hf hlow hupp
    hdecay hM hsurj
  let D1 := firstRelativeConst f g m Am A M
  let relativeConst : ℕ → ℝ := fun j =>
    if j = 0 then 1 else if j = 1 then D1 else
      if j = 2 then D2 else if j = 3 then D3 else D4
  refine ⟨relativeConst, ?_, ?_, ?_⟩
  · intro j
    dsimp [relativeConst]
    split_ifs
    · norm_num
    · exact hD1
    · exact hD2
    · exact hD3
    · exact hD4
  · simp [relativeConst, D1]
  · refine rel_pulse_le_four_of_orders
      (fun s => pulseField_nonneg_interior hfpos (d.angle_mem (x s)))
      (by simp [relativeConst]) (by simpa [D1] using h1) (by simpa using h2)
      (by simpa using h3) (by simpa using h4)

/-- On the wide strip `2 eps ≤ 1/5`, the nonlinear factor `G` is at most two. -/
theorem G_two_mul_le_two {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) : FrontPeriodization.G (2 * eps) ≤ 2 := by
  have ha0 : 0 ≤ 2 * eps := by positivity
  have hale : 2 * eps ≤ (1 / 5 : ℝ) := by linarith
  have hsq : (2 * eps) ^ 2 ≤ (1 / 5 : ℝ) ^ 2 :=
    (sq_le_sq₀ ha0 (by norm_num)).2 hale
  have hrad : (1 / 2 : ℝ) ^ 2 ≤ 1 - (2 * eps) ^ 2 := by nlinarith
  have hrad0 : 0 ≤ 1 - (2 * eps) ^ 2 := by linarith
  have hsqrt_sq := Real.sq_sqrt hrad0
  have hsqrt_nonneg := Real.sqrt_nonneg (1 - (2 * eps) ^ 2)
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - (2 * eps) ^ 2) := by
    nlinarith
  have hsqrt0 : 0 < Real.sqrt (1 - (2 * eps) ^ 2) :=
    lt_of_lt_of_le (by norm_num) hsqrt
  rw [FrontPeriodization.G]
  have hinv := (inv_le_inv₀ hsqrt0 (by norm_num : (0 : ℝ) < 1 / 2)).2 hsqrt
  simpa using hinv

/-- An explicit first-relative bound gives the profile-level subunit estimate.
This is the scalar endpoint of the wide-hairpin asymptotic argument. -/
theorem prior_model_lt_one_of_firstRelative_bound
    {eps D1 Dbar : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (hD1 : 0 ≤ D1) (hD : D1 ≤ Dbar)
    (hsmall : 2 * eps * (1 + 2 * Dbar) < 1) :
    (1 + FrontPeriodization.G (2 * eps) * D1) * (2 * eps) < 1 := by
  have hG := G_two_mul_le_two heps heps10
  have hG0 : 0 ≤ FrontPeriodization.G (2 * eps) := by
    unfold FrontPeriodization.G
    positivity
  have hDbar0 : 0 ≤ Dbar := hD1.trans hD
  have hfactor : 1 + FrontPeriodization.G (2 * eps) * D1 ≤ 1 + 2 * Dbar := by
    simpa [add_comm] using
      (add_le_add_left (mul_le_mul hG hD hD1 (by norm_num)) 1)
  have he2 : 0 ≤ 2 * eps := by positivity
  calc
    (1 + FrontPeriodization.G (2 * eps) * D1) * (2 * eps)
        ≤ (1 + 2 * Dbar) * (2 * eps) := mul_le_mul_of_nonneg_right hfactor he2
    _ = 2 * eps * (1 + 2 * Dbar) := by ring
    _ < 1 := hsmall

/-- Backwards-compatible enriched data: the legacy weighted sequence is kept
unchanged and accompanied by the subunit certificate required by the selected
inverse construction. -/
structure WeightedDataWithSubunitCeiling where
  data : ConstructedConfiguredSequenceWeighted.Data
  ceiling : ConstructedConfiguredSequenceWeighted.SubunitCurvatureCeiling data

end WideHairpinFirstRelativeBound
