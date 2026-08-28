import UnitTangentIterates.InteriorConfiguredModelSequence
import UnitTangentIterates.ConstructedProfileData
import UnitTangentIterates.ProfileConstantsInstance

/-!
# A configured model sequence, for the profile the paper constructs

This runs the composition end to end: from the translator construction of
`TranslatorTranslation.exists_translating_hairpin_translation`, through the
interior quantitative package, to a configured model sequence **with summable
step defects**.

Every hypothesis of
`CanonicalConfiguredModelCapstone.exists_configuredModelSequence_of_interior_barrier`
is discharged rather than assumed:

| input | source |
|---|---|
| interior smoothness, barriers, coordinates, tail | `ConstructedProfileInterior` |
| `hrelj` at `j ≤ 4` | `hrelj_of_interior` |
| `hdb` (pulse derivative) | `abs_coeff_pulse_le_of_flow` on the order-one bound |
| `TranslatorData`, `InteriorPhaseData` | `ConstructedProfileInterior` |
| `ProfileConstants` | `exists_profileConstants` |
| the constant placements | `b = 1/√(1+m²)`, `a = au = (b+1)/2`, `α = 1/Am`, `β = α/4`, `C = max` of the two tail constants, `CU = C·e^{α|s₀|}`, `B = (1+b)π/2`, `ε₀ = 1` |

The placements are the only freedom exercised, and each is forced up to a choice
of margin: `a` and `au` must lie strictly between `sup y = 1/√(1+m²)` and one,
and `α` must not exceed `1/M`.

No endpoint value of the profile is used anywhere in the chain, and no
derivative of the profile appears.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real HairpinRelative PaperHairpinQuantitativeData PaperHairpinConfig

open scoped ContDiff

/-- **A configured model sequence, for the profile the paper constructs.** -/
theorem exists_configuredModelSequence_of_eps {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) :
    ∃ (kappas : ℕ → ℝ → ℝ) (Hs : ℕ → ℝ) (deltaStep kd kstar cst beta : ℝ),
      0 < deltaStep ∧ (∀ n, Hs n + deltaStep ≤ Hs (n + 1)) ∧
      Nonempty (UnconditionalAssembly.ConfiguredModelSequence
        kappas Hs (fun _ => (1:ℝ))) ∧
      Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (cst * Real.exp (-(beta * Hs (n + 1)))) (Hs n)
          * (1:ℝ) ^ 2 * (1 + kstar * (1:ℝ))) := by
  obtain ⟨f, g, gp, theta, x, m, Am, hbar, hm, hmA, hlow, hupp, hfinf, hsm, hsurj,
    hdecay, d⟩ := exists_interiorPhaseData_of_eps heps heps10
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hMpos : (0:ℝ) < Am := lt_of_lt_of_le hm hmA
  have hA : (0:ℝ) ≤ 2 / m := by positivity
  obtain ⟨relativeConst, hrc0, hrel⟩ := hrelj_of_interior d hm hmA hfinf hlow
    hupp hdecay hMpos hsurj
  have htrans : TranslatorData f g gp :=
    { angle_shift := d.shift
      maps_angle := d.image_mem
      profile_deriv_identity := d.translator_identity
      angle_deriv := d.translator_deriv }
  -- the pulse-derivative bound
  obtain ⟨-, -, hyC⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hfinf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have hYd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r)))
      (iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s) s := fun s => by
    have h := hasDerivAt_iteratedDeriv (hyC 2) (show 0 < 2 by norm_num) s
    rwa [iteratedDeriv_zero] at h
  obtain ⟨Dp, hDp, h1⟩ := rel_pulse_one_of_interior' d hm hmA hfinf hlow hupp
    hdecay hMpos hYd
  have hdb : ∀ t ∈ Ioo (0:ℝ) π, |deriv (pulseField f) t| ≤ Dp := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hfinf hfpos d.angle_mem d.angle_deriv
      d.inverse_value hsurj d.state_deriv h1 t ht
    rwa [coeff_one] at h
  -- constants
  set b := 1 / Real.sqrt (1 + m ^ 2) with hbdef
  have hb0 : (0:ℝ) ≤ b := by positivity
  have hb1 : b < 1 := one_div_sqrt_one_add_sq_lt_one hm
  set aa := (b + 1) / 2 with haadef
  have hba : b < aa := by simp [haadef]; linarith
  have ha0 : (0:ℝ) ≤ aa := by simp [haadef]; linarith
  have ha1 : aa < 1 := by simp [haadef]; linarith
  set alpha := 1 / Am with halphadef
  have halpha : 0 < alpha := by positivity
  set A := 2 / m with hAdef
  set C := max (relativeConst 0 * (A * Real.exp (A ^ 2 / 2)))
    (relativeConst 1 * (A * Real.exp (A ^ 2 / 2))) with hCdef
  set CU := C * Real.exp (alpha * |ConsecutiveData.phase f theta g|) with hCUdef
  obtain ⟨CK, Km, Kd, kstar, kd, profile⟩ :=
    exists_profileConstants (alpha := alpha) (beta := alpha / 4) (a := aa)
      (au := aa) (CU := CU) (DU := relativeConst 1) (DU2 := relativeConst 2)
      (D := relativeConst 1) (by positivity) (by linarith) (hrc0 1) (hrc0 1)
      (hrc0 2) ha0 ha1 ha0 ha1
  obtain ⟨Hs, kappas, deltaStep, hdelta, -, hstep, -, -, model, -, -, -, -, hsum⟩ :=
    UnitTangentIterates.CanonicalConfiguredModelCapstone.exists_configuredModelSequence_of_interior_barrier
      (theta0 := 0) (b := b) (B := (1 + b) / 2 * Real.pi) (eps0 := 1)
      hfinf hm hlow hupp hmA hdb d.angle_mem d.angle_value d.angle_deriv
      d.inverse_value d.state_deriv hsm hsurj hA hMpos hdecay relativeConst
      hrc0 hrel htrans d profile one_pos halpha (by rw [halphadef])
      (le_max_left _ _) (le_max_right _ _) (le_refl _) (le_refl _) (le_refl _)
      (le_refl _) hb0 (by simp [hba]) (le_refl _) (le_refl _) profile.rear_derivative_pos.le
  exact ⟨kappas, Hs, deltaStep, kd, kstar, _, _, hdelta, hstep, ⟨model⟩, hsum⟩
