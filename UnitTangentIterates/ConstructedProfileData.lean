import UnitTangentIterates.InteriorRelativeDischarge
import UnitTangentIterates.DataInterior

/-!
# The quantitative packages, for the profile the paper constructs

This closes the loop opened in §21 of the session log: the interior route is not
merely consistent, it applies to the paper's own object, and the packages the
model-orbit development consumes are *constructed*, not assumed.

* `exists_data_of_eps` — `PaperHairpinQuantitativeData.Data` for the profile of
  `TranslatorTranslation.exists_translating_hairpin_translation`;
* `exists_consecutiveData_of_eps` — the same for `ConsecutiveData`, the input of
  the model-orbit defect chain.

Every hypothesis is discharged:

| input | source |
|---|---|
| interior smoothness, barriers, coordinates, tail | `ConstructedProfileInterior` |
| `hrelj` at `j ≤ 4` | `hrelj_of_interior` |
| `TranslatorData` | the `InteriorPhaseData` fields |

No endpoint value of the profile is used anywhere in the chain.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real HairpinRelative PaperHairpinQuantitativeData

open scoped ContDiff

/-- **The quantitative package `Data`, for the profile the paper constructs.** -/
theorem exists_data_of_eps {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ (f theta x : ℝ → ℝ) (M : ℝ),
      Nonempty (Data f theta x M 0 0 0 0 (fun _ => 0) (fun _ => 0)) := by
  obtain ⟨f, g, gp, theta, x, m, Am, hbar, hm, hmA, hlow, hupp, hfinf, hsm, hsurj,
    hdecay, d⟩ := exists_interiorPhaseData_of_eps heps heps10
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hA : (0:ℝ) ≤ 2 / m := by positivity
  have hMpos : (0:ℝ) < Am := lt_of_lt_of_le hm hmA
  obtain ⟨relativeConst, hrc0, hrel⟩ := hrelj_of_interior d hm hmA hfinf hlow
    hupp hdecay hMpos hsurj
  exact ⟨f, theta, x, Am, ⟨data_of_interior hfinf hm hlow d.angle_mem
    d.angle_value d.angle_deriv d.inverse_value d.state_deriv hsm hsurj hA
    hMpos hdecay relativeConst hrc0 hrel⟩⟩

/-- **The consecutive package, for the profile the paper constructs.** -/
theorem exists_consecutiveData_of_eps {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) :
    ∃ (f g gp theta x yp : ℝ → ℝ) (M : ℝ),
      Nonempty (ConsecutiveData f theta x g gp yp M 0 0 0 0
        (fun _ => 0) (fun _ => 0)) := by
  obtain ⟨f, g, gp, theta, x, m, Am, hbar, hm, hmA, hlow, hupp, hfinf, hsm, hsurj,
    hdecay, d⟩ := exists_interiorPhaseData_of_eps heps heps10
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hA : (0:ℝ) ≤ 2 / m := by positivity
  have hMpos : (0:ℝ) < Am := lt_of_lt_of_le hm hmA
  obtain ⟨relativeConst, hrc0, hrel⟩ := hrelj_of_interior d hm hmA hfinf hlow
    hupp hdecay hMpos hsurj
  have htrans : TranslatorData f g gp :=
    { angle_shift := d.shift
      maps_angle := d.image_mem
      profile_deriv_identity := d.translator_identity
      angle_deriv := d.translator_deriv }
  exact ⟨f, g, gp, theta, x, _, Am,
    ⟨consecutiveData_of_interior hfinf hm hlow d.angle_mem d.angle_value
      d.angle_deriv d.inverse_value d.state_deriv hsm hsurj hA hMpos hdecay
      relativeConst hrc0 hrel htrans⟩⟩
