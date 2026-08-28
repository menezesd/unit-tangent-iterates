import UnitTangentIterates.CanonicalTranslatorLocalPhase
import UnitTangentIterates.TranslatorTranslation
import UnitTangentIterates.HairpinInteriorRegularity
import UnitTangentIterates.CanonicalConsecutiveInterior
import UnitTangentIterates.TranslatorConsecutiveBridge

/-!
# The constructed profile satisfies the interior hypotheses

Everything the endpoint-free route asks of a profile is now checked against the
profile the paper actually constructs, rather than assumed.

`exists_interiorPhaseData_of_eps` produces, from the translator construction of
`TranslatorTranslation.exists_translating_hairpin_translation`:

* explicit two-sided barriers `m = ε⁻¹ − ε` and `Am = ε⁻¹ + 4/3 + 3ε`;
* `ContDiffOn ℝ ∞ f (Ioo 0 π)` — assembled from the finite orders the
  fixed-point bootstrap gives, via `contDiffOn_infty_of_forall_nat`;
* the hairpin coordinates `θ` and `x`, with `θ` strictly monotone and onto
  `(0,π)`;
* the order-zero curvature tail `K_* ≤ (2/m)e^{−|u|/Am}`;
* the full `InteriorPhaseData` record.

Those are exactly the coordinate-side and profile-side inputs of
`PaperHairpinQuantitativeData.data_of_interior`.  What that constructor still
needs beyond them is `hrelj`, the relative bounds at `j ≤ 4`, which
`PulseRelativeAssembly` supplies from the order lemmas.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Real HairpinRelative

open scoped ContDiff


theorem exists_interiorPhaseData_of_eps {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) :
    ∃ (f g gp theta x : ℝ → ℝ) (m Am : ℝ),
      eps⁻¹ - eps ≤ m ∧
      0 < m ∧ m ≤ Am ∧
      (∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) ∧ (∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am) ∧
      ContDiffOn ℝ ∞ f (Ioo 0 π) ∧
      StrictMono theta ∧
      (∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z) ∧
      (∀ u, curvField f (theta u) ≤ (2 / m) * Real.exp (-|u| / Am)) ∧
      CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp := by
  obtain ⟨f, V, hVpos, hfl, hfu, hfc, hmaps', hU, hsmooth, hshiftEq, hgderiv,
    htrans⟩ := TranslatorTranslation.exists_translating_hairpin_translation heps heps10
  have hm1 : 1 < eps⁻¹ - eps := BarrierEstimates.m_gt_one heps heps10
  have hm0 : (0:ℝ) < eps⁻¹ - eps := lt_trans zero_lt_one hm1
  have hlow : ∀ t, eps⁻¹ - eps ≤ f t := fun t =>
    le_trans ((Barriers.fMinus_min heps).1 t) (hfl t)
  have hup : ∀ t, f t ≤ eps⁻¹ + 4 / 3 + 3 * eps := fun t =>
    le_trans (hfu t) ((BarrierEstimates.profile_fPlus heps).upper t)
  have hfpos : ∀ t, 0 < f t := fun t => lt_of_lt_of_le hm0 (hlow t)
  have hfinf : ContDiffOn ℝ ∞ f (Ioo 0 π) :=
    TranslatorConsecutiveBridge.contDiffOn_infty_of_forall_nat hsmooth
  -- the angle map
  obtain ⟨theta, hmem, hval, hleft, hsm, hthetac, hderiv⟩ :=
    HairpinArclength.exists_angle hfc hm0 (fun t _ => hlow t)
  have hderiv' : ∀ u, HasDerivAt theta (curvField f (theta u)) u := hderiv
  have hGc : Continuous fun u => curvField f (theta u) :=
    continuous_curv_along_theta hfinf (fun t _ => hfpos t) hmem hderiv'
  -- the front coordinate
  obtain ⟨x, hxinv, -, hxderiv⟩ :=
    HairpinInteriorRegularity.exists_pulseState_of_continuous_comp hGc
      (fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩) hderiv'
  refine ⟨f, Translator.next f, fun t => (f t + Real.cos t) / f (Translator.next f t),
    theta, x, eps⁻¹ - eps, eps⁻¹ + 4 / 3 + 3 * eps, le_rfl, hm0, ?_,
    fun t _ => hlow t, fun t _ => hup t, hfinf, hsm, ?_, ?_, ?_⟩
  · exact le_trans (hlow 0) (hup 0)
  · intro z hz
    exact ⟨Hairpin.hairpinArclength f (π / 2) z, hleft z hz⟩
  · intro u
    exact HairpinArclength.curvature_decay_arclength hfc hm0 (fun t _ => hlow t)
      (fun t _ => hup t) hmem hval u
  · exact
      { profile_continuous := hfc
        profile_smooth := hsmooth
        profile_pos := fun t _ => hfpos t
        angle_mem := hmem
        image_mem := fun t ht => ⟨lt_trans ht.1 (hmaps' t ht).1, (hmaps' t ht).2⟩
        angle_value := hval
        arclength_strictMono :=
          CanonicalTranslatorLocalPhase.arclength_strictMonoOn_of_positive hfc
            (fun t _ => hfpos t)
        angle_deriv := hderiv'
        inverse_value := hxinv
        state_deriv := hxderiv
        shift := hshiftEq
        translator_deriv := hgderiv
        translator_identity := fun t ht => by
          have hne : f (Translator.next f t) ≠ 0 := (hfpos _).ne'
          field_simp }
