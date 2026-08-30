import UnitTangentIterates.StrictConstructedModelGeometry
import UnitTangentIterates.WidthUniformProduced
import UnitTangentIterates.AdmissibleFrontFamily
import UnitTangentIterates.ModelWidth
import UnitTangentIterates.ConstructedConfiguredSequenceWeighted
import UnitTangentIterates.ActualFrontCurvatureLargePeriod
import UnitTangentIterates.HairpinPulseDataInterior

/-!
# Uniform width from the retained constructed pulse

This file isolates the normalization datum needed to apply the uniform-width
argument to an asymmetric periodized pulse.  Pointwise positive curvature and
total turning do not by themselves put the centered tangent angle in `(0,π)`:
with the origin fixed at `π/2`, that assertion requires the exact half-cell
mass identity.  Once that identity is supplied, centered-angle positivity is
proved here rather than assumed.
-/

noncomputable section

open Real Set Function MeasureTheory intervalIntegral
open ModelOrbitDefect TwoCapPairsAssembly ConstructedModelGeometry
open FrontPeriodization
open PaperHairpinQuantitativeData

namespace ConstructedPulseWidth

set_option maxHeartbeats 4000000

/-- Strictly positive periodic curvature with total turning `π` and exactly
half of that turning on the left half-cell has its `π/2`-normalized tangent
angle strictly between `0` and `π` throughout the open centered cell. -/
theorem centered_frontAngle_mem_Ioo
    {kappa : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0 : ℝ)..H, kappa r) = π)
    (hpos : ∀ s, 0 < kappa s)
    (hhalf : (∫ r in (-(H / 2))..(0 : ℝ), kappa r) = π / 2) :
    ∀ t ∈ Ioo (-(H / 2)) (H / 2),
      frontAngle kappa (π / 2) t ∈ Ioo 0 π := by
  obtain ⟨kmin, hkmin0, hkmin⟩ :=
    StrictConstructedModelGeometry.exists_positive_floor_of_periodic
      hH hk hper hpos
  have hmono : StrictMono (frontAngle kappa (π / 2)) :=
    TwoCapMarked.strictMono_frontAngle hk hkmin0 hkmin
  have hleft : frontAngle kappa (π / 2) (-(H / 2)) = 0 := by
    change π / 2 + (∫ r in (0 : ℝ)..(-(H / 2)), kappa r) = 0
    rw [intervalIntegral.integral_symm]
    linarith
  have hwindow : (∫ r in (-(H / 2))..(H / 2), kappa r) = π := by
    have h := hper.intervalIntegral_add_eq (-(H / 2)) 0
    rw [show (-(H / 2) + H : ℝ) = H / 2 by ring,
      show (0 : ℝ) + H = H by ring] at h
    rw [h, htotal]
  have hrightIntegral : (∫ r in (0 : ℝ)..(H / 2), kappa r) = π / 2 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hk.intervalIntegrable (μ := volume) (-(H / 2)) 0)
      (hk.intervalIntegrable (μ := volume) 0 (H / 2))
    linarith
  have hright : frontAngle kappa (π / 2) (H / 2) = π := by
    change π / 2 + (∫ r in (0 : ℝ)..(H / 2), kappa r) = π
    linarith
  intro t ht
  constructor
  · have h := hmono ht.1
    rw [hleft] at h
    exact h
  · have h := hmono ht.2
    rw [hright] at h
    exact h

/-- The half-cell identity is necessary, not just sufficient: centered-angle
positivity with the fixed origin `π/2` and total turning `π` forces exactly
half the curvature mass onto each half-cell. -/
theorem half_cell_mass_of_centered_frontAngle
    {kappa : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0 : ℝ)..H, kappa r) = π)
    (hangle : ∀ t ∈ Ioo (-(H / 2)) (H / 2),
      frontAngle kappa (π / 2) t ∈ Ioo 0 π) :
    (∫ r in (-(H / 2))..(0 : ℝ), kappa r) = π / 2 := by
  have hΘc : Continuous (frontAngle kappa (π / 2)) :=
    CurvatureInterpolation.continuous_tangentAngle hk
  have hsub : Ioo (-(H / 2)) (H / 2) ⊆
      {t | frontAngle kappa (π / 2) t ∈ Icc 0 π} := by
    intro t ht
    exact ⟨(hangle t ht).1.le, (hangle t ht).2.le⟩
  have hclosed : IsClosed {t | frontAngle kappa (π / 2) t ∈ Icc 0 π} :=
    isClosed_Icc.preimage hΘc
  have hne : -(H / 2) ≠ H / 2 := by intro h; linarith
  have hcell : Icc (-(H / 2)) (H / 2) ⊆
      {t | frontAngle kappa (π / 2) t ∈ Icc 0 π} := by
    rw [← closure_Ioo hne]
    exact hclosed.closure_subset_iff.2 hsub
  have hleft := (hcell ⟨le_rfl, (by linarith : -(H / 2) ≤ H / 2)⟩).1
  have hright := (hcell ⟨(by linarith : -(H / 2) ≤ H / 2), le_rfl⟩).2
  have hwindow : (∫ r in (-(H / 2))..(H / 2), kappa r) = π := by
    have h := hper.intervalIntegral_add_eq (-(H / 2)) 0
    rw [show (-(H / 2) + H : ℝ) = H / 2 by ring,
      show (0 : ℝ) + H = H by ring] at h
    rw [h, htotal]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hk.intervalIntegrable (μ := volume) (-(H / 2)) 0)
    (hk.intervalIntegrable (μ := volume) 0 (H / 2))
  change 0 ≤ π / 2 + (∫ r in (0 : ℝ)..(-(H / 2)), kappa r) at hleft
  change π / 2 + (∫ r in (0 : ℝ)..(H / 2), kappa r) ≤ π at hright
  rw [intervalIntegral.integral_symm] at hleft
  linarith

/-- Every positive-period continuous periodic curvature of total mass `π` has
a phase center which splits a period into two half-cells of mass `π/2`. -/
theorem exists_half_mass_center
    {kappa : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0 : ℝ)..H, kappa r) = π) :
    ∃ a ∈ Icc (0 : ℝ) (H / 2),
      (∫ r in (a - H / 2)..a, kappa r) = π / 2 := by
  let primitive : ℝ → ℝ := fun a => ∫ r in (0 : ℝ)..a, kappa r
  let halfMass : ℝ → ℝ := fun a => primitive a - primitive (a - H / 2)
  have hprim : Continuous primitive :=
    intervalIntegral.continuous_primitive
      (fun a b => hk.intervalIntegrable (μ := volume) a b) 0
  have hhalfCont : Continuous halfMass := by
    exact hprim.sub (hprim.comp (continuous_id.sub continuous_const))
  have hhalfEq : ∀ a, halfMass a = ∫ r in (a - H / 2)..a, kappa r := by
    intro a
    dsimp [halfMass, primitive]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hk.intervalIntegrable (μ := volume) (a - H / 2) 0)
      (hk.intervalIntegrable (μ := volume) 0 a)
    rw [sub_eq_add_neg, ← intervalIntegral.integral_symm]
    simpa [add_comm] using hadd
  have hsum : halfMass 0 + halfMass (H / 2) = π := by
    rw [hhalfEq, hhalfEq]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hk.intervalIntegrable (μ := volume) (-(H / 2)) 0)
      (hk.intervalIntegrable (μ := volume) 0 (H / 2))
    have hwindow : (∫ r in (-(H / 2))..(H / 2), kappa r) = π := by
      have hp := hper.intervalIntegral_add_eq (-(H / 2)) 0
      rw [show (-(H / 2) + H : ℝ) = H / 2 by ring,
        show (0 : ℝ) + H = H by ring] at hp
      rw [hp, htotal]
    have hz : H / 2 - H / 2 = 0 := by ring
    rw [zero_sub, hz]
    exact hadd.trans hwindow
  have htarget : π / 2 ∈ uIcc (halfMass 0) (halfMass (H / 2)) := by
    rw [mem_uIcc]
    rcases le_total (halfMass 0) (π / 2) with hle | hge
    · left
      constructor
      · exact hle
      · linarith
    · right
      constructor
      · linarith
      · exact hge
  have hiv := intermediate_value_uIcc
    (a := (0 : ℝ)) (b := H / 2) hhalfCont.continuousOn htarget
  obtain ⟨a, ha, hval⟩ := hiv
  rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ H / 2)] at ha
  exact ⟨a, ha, by rw [← hhalfEq a, hval]⟩

/-- A noncomputably selected half-mass center. -/
noncomputable def halfMassCenter (kappa : ℝ → ℝ) (H : ℝ) : ℝ :=
  by
    classical
    exact if h : 0 < H ∧ Continuous kappa ∧ Periodic kappa H ∧
        (∫ r in (0 : ℝ)..H, kappa r) = π then
      Classical.choose (exists_half_mass_center h.1 h.2.1 h.2.2.1 h.2.2.2)
    else 0

theorem halfMassCenter_mem
    {kappa : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0 : ℝ)..H, kappa r) = π) :
    halfMassCenter kappa H ∈ Icc (0 : ℝ) (H / 2) := by
  rw [halfMassCenter, dif_pos ⟨hH, hk, hper, htotal⟩]
  exact (Classical.choose_spec (exists_half_mass_center hH hk hper htotal)).1

theorem halfMassCenter_half
    {kappa : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0 : ℝ)..H, kappa r) = π) :
    (∫ r in (halfMassCenter kappa H - H / 2)..halfMassCenter kappa H,
      kappa r) = π / 2 := by
  rw [halfMassCenter, dif_pos ⟨hH, hk, hper, htotal⟩]
  exact (Classical.choose_spec (exists_half_mass_center hH hk hper htotal)).2

/-- Translate the parameter so the selected half-mass center becomes the
origin of the centered cell. -/
noncomputable def phaseCenteredCurvature (kappa : ℝ → ℝ) (H : ℝ) : ℝ → ℝ :=
  fun t => kappa (t + halfMassCenter kappa H)

theorem phaseCenteredCurvature_half
    {kappa : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0 : ℝ)..H, kappa r) = π) :
    (∫ r in (-(H / 2))..(0 : ℝ), phaseCenteredCurvature kappa H r) = π / 2 := by
  change (∫ r in (-(H / 2))..(0 : ℝ),
    kappa (r + halfMassCenter kappa H)) = π / 2
  rw [intervalIntegral.integral_comp_add_right]
  convert halfMassCenter_half hH hk hper htotal using 1 <;> ring

theorem phaseCenteredCurvature_mem_Ioo
    {kappa : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0 : ℝ)..H, kappa r) = π)
    (hpos : ∀ s, 0 < kappa s) :
    ∀ t ∈ Ioo (-(H / 2)) (H / 2),
      frontAngle (phaseCenteredCurvature kappa H) (π / 2) t ∈ Ioo 0 π := by
  apply centered_frontAngle_mem_Ioo hH
  · exact hk.comp (continuous_id.add continuous_const)
  · intro t
    dsimp [phaseCenteredCurvature]
    convert hper (t + halfMassCenter kappa H) using 1 <;> ring
  · have hp := hper.intervalIntegral_add_eq (halfMassCenter kappa H) 0
    change (∫ r in (0 : ℝ)..H,
      kappa (r + halfMassCenter kappa H)) = π
    rw [intervalIntegral.integral_comp_add_right]
    have hp' : (∫ r in halfMassCenter kappa H..
        halfMassCenter kappa H + H, kappa r) = π := by
      calc
        (∫ r in halfMassCenter kappa H..halfMassCenter kappa H + H, kappa r) =
            ∫ r in (0 : ℝ)..H, kappa r := by simpa using hp
        _ = π := htotal
    simpa [add_comm] using hp'
  · exact fun s => hpos _
  · exact phaseCenteredCurvature_half hH hk hper htotal

/-! ### The direction selected by phase normalization -/

/-- The unit rotation which sends the tangent angle at the selected phase
center to the normalized angle `π / 2`. -/
noncomputable def phaseRotation (kappa : ℝ → ℝ) (theta0 H : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi / 2 -
    frontAngle kappa theta0 (halfMassCenter kappa H) : ℝ) : ℂ))

/-- The direction on the original front which becomes `I` after applying
`phaseRotation`. -/
noncomputable def phaseDirection (kappa : ℝ → ℝ) (theta0 H : ℝ) : ℂ :=
  starRingEnd ℂ (phaseRotation kappa theta0 H) * Complex.I

theorem phaseRotation_norm (kappa : ℝ → ℝ) (theta0 H : ℝ) :
    ‖phaseRotation kappa theta0 H‖ = 1 := by
  simp [phaseRotation, Complex.norm_exp]

theorem phaseRotation_mul_phaseDirection (kappa : ℝ → ℝ) (theta0 H : ℝ) :
    phaseRotation kappa theta0 H * phaseDirection kappa theta0 H = Complex.I := by
  have hn : Complex.normSq (phaseRotation kappa theta0 H) = 1 := by
    rw [← Complex.sq_norm, phaseRotation_norm]
    norm_num
  simp only [phaseDirection, ← mul_assoc, Complex.mul_conj, hn,
    Complex.ofReal_one, one_mul]

theorem phaseDirection_norm (kappa : ℝ → ℝ) (theta0 H : ℝ) :
    ‖phaseDirection kappa theta0 H‖ = 1 := by
  change ‖star (phaseRotation kappa theta0 H) * Complex.I‖ = 1
  rw [norm_mul, norm_star, phaseRotation_norm, Complex.norm_I, one_mul]

/-- Rotation and transverse direction normalized at an explicitly retained
half-mass center. -/
noncomputable def centeredRotation (kappa : ℝ → ℝ) (theta0 q : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((π / 2 - frontAngle kappa theta0 q : ℝ) : ℂ))

noncomputable def centeredDirection (kappa : ℝ → ℝ) (theta0 q : ℝ) : ℂ :=
  starRingEnd ℂ (centeredRotation kappa theta0 q) * Complex.I

theorem centeredRotation_norm (kappa : ℝ → ℝ) (theta0 q : ℝ) :
    ‖centeredRotation kappa theta0 q‖ = 1 := by
  simp [centeredRotation, Complex.norm_exp]

theorem centeredRotation_mul_centeredDirection (kappa : ℝ → ℝ) (theta0 q : ℝ) :
    centeredRotation kappa theta0 q * centeredDirection kappa theta0 q = Complex.I := by
  have hn : Complex.normSq (centeredRotation kappa theta0 q) = 1 := by
    rw [← Complex.sq_norm, centeredRotation_norm]
    norm_num
  simp only [centeredDirection, ← mul_assoc, Complex.mul_conj, hn,
    Complex.ofReal_one, one_mul]

theorem centeredDirection_norm (kappa : ℝ → ℝ) (theta0 q : ℝ) :
    ‖centeredDirection kappa theta0 q‖ = 1 := by
  change ‖star (centeredRotation kappa theta0 q) * Complex.I‖ = 1
  rw [norm_mul, norm_star, centeredRotation_norm, Complex.norm_I, one_mul]

/-- Geometric width in the direction normalized at an explicitly retained
half-mass center. -/
theorem width_front_eq_centered_integral
    {kappa : ℝ → ℝ} {theta0 H q : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0 : ℝ)..H, kappa r) = π)
    (hpos : ∀ s, 0 < kappa s)
    (hq : (∫ r in (q - H / 2)..q, kappa r) = π / 2) :
    Width.width (range (front kappa theta0 H))
        (centeredDirection kappa theta0 q) =
      ∫ s in (-(H / 2))..(H / 2),
        sin (frontAngle (fun r => kappa (r + q)) (π / 2) s) := by
  let a := centeredRotation kappa theta0 q
  let e := centeredDirection kappa theta0 q
  let F : ℝ → ℂ := fun s => front kappa theta0 H (s + q)
  let kc : ℝ → ℝ := fun s => kappa (s + q)
  let Θ : ℝ → ℝ := fun s => frontAngle kc (π / 2) s
  have hkcc : Continuous kc := hk.comp (continuous_id.add continuous_const)
  have hkcper : Periodic kc H := by
    intro s
    dsimp [kc]
    convert hper (s + q) using 1 <;> ring
  have hkctotal : (∫ r in (0 : ℝ)..H, kc r) = π := by
    change (∫ r in (0 : ℝ)..H, kappa (r + q)) = π
    rw [intervalIntegral.integral_comp_add_right]
    have hp := hper.intervalIntegral_add_eq q 0
    have htotal' : (∫ r in (0 : ℝ)..((0 : ℝ) + H), kappa r) = π := by
      simpa using htotal
    convert hp.trans htotal' using 1 <;> ring
  have hkchalf : (∫ r in (-(H / 2))..(0 : ℝ), kc r) = π / 2 := by
    change (∫ r in (-(H / 2))..(0 : ℝ), kappa (r + q)) = π / 2
    rw [intervalIntegral.integral_comp_add_right]
    convert hq using 1 <;> ring
  have hangle : ∀ s, Θ s =
      frontAngle kappa theta0 (s + q) - frontAngle kappa theta0 q + π / 2 := by
    intro s
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hk.intervalIntegrable (μ := volume) 0 q)
      (hk.intervalIntegrable (μ := volume) q (s + q))
    dsimp [Θ, kc]
    change π / 2 + (∫ r in (0 : ℝ)..s, kappa (r + q)) =
      (theta0 + ∫ r in (0 : ℝ)..(s + q), kappa r) -
        (theta0 + ∫ r in (0 : ℝ)..q, kappa r) + π / 2
    rw [intervalIntegral.integral_comp_add_right]
    have hdiff : (∫ r in q..(s + q), kappa r) =
        (∫ r in (0 : ℝ)..(s + q), kappa r) - (∫ r in (0 : ℝ)..q, kappa r) := by
      linarith
    rw [show (0 : ℝ) + q = q by ring, hdiff]
    ring
  have hFrot : ∀ s, HasDerivAt (fun r => a * F r)
      (Complex.exp (Complex.I * (Θ s : ℂ))) s := by
    intro s
    have hd0 := front_hasDerivAt (theta0 := theta0) (H := H) hk (s + q)
    have hd : HasDerivAt F
        (Complex.exp (Complex.I * (frontAngle kappa theta0 (s + q) : ℂ))) s := by
      simpa only [F] using hd0.comp_add_const s q
    have hd' := hd.const_mul a
    convert hd' using 1
    dsimp [a, centeredRotation]
    rw [hangle, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hFper : Periodic F (2 * H) := by
    intro s
    dsimp [F]
    have hp := front_periodic (theta0 := theta0) hk hper htotal (s + q)
    convert hp using 1 <;> ring
  have hΘc : Continuous Θ := CurvatureInterpolation.continuous_tangentAngle hkcc
  have hhalf : ∀ s, Θ (s + H) = Θ s + π :=
    fun s => frontAngle_add_halfPeriod hkcc hkcper hkctotal s
  have hcell : ∀ s ∈ Icc (-(H / 2)) (H / 2), 0 ≤ sin (Θ s) := by
    have hmem : ∀ t ∈ Ioo (-(H / 2)) (H / 2), Θ t ∈ Ioo 0 π := by
      apply centered_frontAngle_mem_Ioo hH hkcc hkcper hkctotal
        (fun s => hpos _) hkchalf
    have hsub : Ioo (-(H / 2)) (H / 2) ⊆ {s | 0 ≤ sin (Θ s)} := by
      intro s hs
      exact Real.sin_nonneg_of_nonneg_of_le_pi (hmem s hs).1.le (hmem s hs).2.le
    have hclosed : IsClosed {s | 0 ≤ sin (Θ s)} :=
      isClosed_Ici.preimage (Real.continuous_sin.comp hΘc)
    have hne : -(H / 2) ≠ H / 2 := by intro heq; linarith
    rw [← closure_Ioo hne]
    exact hclosed.closure_subset_iff.2 hsub
  have hwidth := ModelWidth.width_range_eq_integral_unit_rotation
    (F := F) (Θ := Θ) (H := H) a e
    (by simpa [a] using centeredRotation_norm kappa theta0 q)
    (by simpa [a, e] using centeredRotation_mul_centeredDirection kappa theta0 q)
    hH hFrot hΘc hFper hhalf hcell
  have hrange : range F = range (front kappa theta0 H) := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s + q, rfl⟩
    · rintro ⟨s, rfl⟩
      refine ⟨s - q, ?_⟩
      dsimp [F]
      congr 1
      ring
  simpa [e, Θ, kc, hrange] using hwidth

/-- The phase-centered sine integral is the geometric width of the original,
unrephased front in the unit direction selected by the normalization. -/
theorem width_front_eq_phaseCentered_integral
    {kappa : ℝ → ℝ} {theta0 H : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0 : ℝ)..H, kappa r) = π)
    (hpos : ∀ s, 0 < kappa s) :
    Width.width (range (front kappa theta0 H))
        (phaseDirection kappa theta0 H) =
      ∫ s in (-(H / 2))..(H / 2),
        sin (frontAngle (phaseCenteredCurvature kappa H) (π / 2) s) := by
  let q := halfMassCenter kappa H
  let a := phaseRotation kappa theta0 H
  let e := phaseDirection kappa theta0 H
  let F : ℝ → ℂ := fun s => front kappa theta0 H (s + q)
  let Θ : ℝ → ℝ := fun s =>
    frontAngle (phaseCenteredCurvature kappa H) (π / 2) s
  have hshiftc : Continuous (phaseCenteredCurvature kappa H) :=
    hk.comp (continuous_id.add continuous_const)
  have hshiftper : Periodic (phaseCenteredCurvature kappa H) H := by
    intro s
    dsimp [phaseCenteredCurvature]
    convert hper (s + halfMassCenter kappa H) using 1 <;> ring
  have hshifttotal : (∫ r in (0 : ℝ)..H,
      phaseCenteredCurvature kappa H r) = π := by
    change (∫ r in (0 : ℝ)..H,
      kappa (r + halfMassCenter kappa H)) = π
    rw [intervalIntegral.integral_comp_add_right]
    have hp := hper.intervalIntegral_add_eq (halfMassCenter kappa H) 0
    have htotal' : (∫ r in (0 : ℝ)..((0 : ℝ) + H), kappa r) = π := by
      simpa using htotal
    convert hp.trans htotal' using 1 <;> ring
  have hangle : ∀ s, Θ s =
      frontAngle kappa theta0 (s + q) - frontAngle kappa theta0 q + π / 2 := by
    intro s
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hk.intervalIntegrable (μ := volume) 0 q)
      (hk.intervalIntegrable (μ := volume) q (s + q))
    dsimp [Θ, phaseCenteredCurvature, q]
    change π / 2 + (∫ r in (0 : ℝ)..s,
      kappa (r + halfMassCenter kappa H)) =
      (theta0 + ∫ r in (0 : ℝ)..(s + halfMassCenter kappa H), kappa r) -
      (theta0 + ∫ r in (0 : ℝ)..halfMassCenter kappa H, kappa r) + π / 2
    rw [intervalIntegral.integral_comp_add_right]
    have hdiff : (∫ r in q..(s + q), kappa r) =
        (∫ r in (0 : ℝ)..(s + q), kappa r) - (∫ r in (0 : ℝ)..q, kappa r) := by
      linarith
    rw [show (0 : ℝ) + q = q by ring, hdiff]
    ring
  have hFrot : ∀ s, HasDerivAt (fun r => a * F r)
      (Complex.exp (Complex.I * (Θ s : ℂ))) s := by
    intro s
    have hd0 := front_hasDerivAt (theta0 := theta0) (H := H) hk (s + q)
    have hd : HasDerivAt F
        (Complex.exp (Complex.I * (frontAngle kappa theta0 (s + q) : ℂ))) s := by
      simpa only [F] using hd0.comp_add_const s q
    have hd' := hd.const_mul a
    convert hd' using 1
    dsimp [a, phaseRotation]
    rw [hangle]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hFper : Periodic F (2 * H) := by
    intro s
    dsimp [F]
    have hp := front_periodic (theta0 := theta0) hk hper htotal (s + q)
    convert hp using 1 <;> ring
  have hΘc : Continuous Θ :=
    CurvatureInterpolation.continuous_tangentAngle hshiftc
  have hhalf : ∀ s, Θ (s + H) = Θ s + π :=
    fun s => frontAngle_add_halfPeriod hshiftc hshiftper hshifttotal s
  have hcell : ∀ s ∈ Icc (-(H / 2)) (H / 2), 0 ≤ sin (Θ s) := by
    have hsub : Ioo (-(H / 2)) (H / 2) ⊆ {s | 0 ≤ sin (Θ s)} := by
      intro s hs
      exact Real.sin_nonneg_of_nonneg_of_le_pi
        (phaseCenteredCurvature_mem_Ioo hH hk hper htotal hpos s hs).1.le
        (phaseCenteredCurvature_mem_Ioo hH hk hper htotal hpos s hs).2.le
    have hclosed : IsClosed {s | 0 ≤ sin (Θ s)} :=
      isClosed_Ici.preimage (Real.continuous_sin.comp hΘc)
    have hne : -(H / 2) ≠ H / 2 := by intro h; linarith
    rw [← closure_Ioo hne]
    exact hclosed.closure_subset_iff.2 hsub
  have hwidth := ModelWidth.width_range_eq_integral_unit_rotation
    (F := F) (Θ := Θ) (H := H) a e
    (by simpa [a] using phaseRotation_norm kappa theta0 H)
    (by simpa [a, e] using phaseRotation_mul_phaseDirection kappa theta0 H)
    hH hFrot hΘc hFper hhalf hcell
  have hrange : range F = range (front kappa theta0 H) := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s + q, rfl⟩
    · rintro ⟨s, rfl⟩
      refine ⟨s - q, ?_⟩
      dsimp [F]
      congr 1
      ring
  simpa [e, Θ, hrange] using hwidth

/-- A nonnegative continuous function with an exponential two-sided tail has
a uniform bound on all centered interval integrals. -/
theorem centered_integral_le_of_exp_bound
    {w : ℝ → ℝ} {C alpha : ℝ} (halpha : 0 < alpha)
    (hw : Continuous w) (hw0 : ∀ s, 0 ≤ w s)
    (hwb : ∀ s, w s ≤ C * exp (-alpha * |s|)) :
    ∀ H, 0 < H → (∫ s in (-(H / 2))..(H / 2), w s) ≤ 2 * C / alpha := by
  have hC0 : 0 ≤ C := by
    have h := (hw0 0).trans (hwb 0)
    simpa using h
  let majorant : ℝ → ℝ := fun s => C * exp (-alpha * |s|)
  have hMint : Integrable majorant :=
    (L1Matching.integrable_expabs halpha).const_mul C
  have hM0 : ∀ s, 0 ≤ majorant s := fun s => mul_nonneg hC0 (exp_pos _).le
  intro H hH
  have hab : -(H / 2) ≤ H / 2 := by linarith
  have hmono := intervalIntegral.integral_mono_on hab
    (hw.intervalIntegrable _ _) (hMint.intervalIntegrable)
    (fun s _ => hwb s)
  have hset : (∫ s in (-(H / 2))..(H / 2), majorant s) ≤
      ∫ s : ℝ, majorant s := by
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_le_integral hMint
      (Filter.Eventually.of_forall hM0)
  have hval : (∫ s : ℝ, majorant s) = 2 * C / alpha := by
    dsimp [majorant]
    rw [MeasureTheory.integral_const_mul, L1Matching.integral_expabs halpha]
    ring
  linarith

/-- The isolated translating hairpin has uniformly bounded transverse width.
The explicit bound `4 Am` follows only from the interior barriers and the
intrinsic arclength coordinate. -/
theorem isolated_hairpin_width_le
    {f theta : ℝ → ℝ} {m Am : ℝ}
    (hf : ContinuousOn f (Ioo 0 π)) (hm : 0 < m) (hmA : m ≤ Am)
    (hlow : ∀ t ∈ Ioo (0 : ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) π, f t ≤ Am)
    (hmem : ∀ u, theta u ∈ Ioo (0 : ℝ) π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (htheta : ∀ u, HasDerivAt theta
      (HairpinRelative.curvField f (theta u)) u) :
    ∀ H, 0 < H →
      (∫ s in (-(H / 2))..(H / 2), sin (theta s)) ≤ 4 * Am := by
  have hAm : 0 < Am := lt_of_lt_of_le hm hmA
  have hthetac : Continuous theta :=
    continuous_iff_continuousAt.mpr fun s => (htheta s).continuousAt
  have hw : Continuous (fun s => sin (theta s)) :=
    Real.continuous_sin.comp hthetac
  have hw0 : ∀ s, 0 ≤ sin (theta s) := fun s =>
    (Real.sin_pos_of_pos_of_lt_pi (hmem s).1 (hmem s).2).le
  have htail : ∀ s, sin (theta s) ≤
      2 * exp (-(1 / Am) * |s|) := by
    intro s
    have hs := HairpinTails.sin_le_two_exp (hmem s)
    have harc := HairpinTails.abs_arclength_le hf hm hlow hupp (hmem s)
    rw [hval s] at harc
    have hlog : |s| / Am ≤ |HairpinTails.logHalf (theta s)| := by
      rw [div_le_iff₀ hAm]
      simpa [mul_comm] using harc
    have hlog' : (1 / Am) * |s| ≤ |HairpinTails.logHalf (theta s)| := by
      calc
        (1 / Am) * |s| = |s| / Am := by ring
        _ ≤ |HairpinTails.logHalf (theta s)| := hlog
    have he : exp (-|HairpinTails.logHalf (theta s)|) ≤
        exp (-(1 / Am) * |s|) := by
      apply exp_le_exp.mpr
      linarith
    exact hs.trans (mul_le_mul_of_nonneg_left he (by norm_num))
  have h := centered_integral_le_of_exp_bound (C := (2 : ℝ))
    (alpha := 1 / Am) (by positivity) hw hw0 htail
  intro H hH
  have hh := h H hH
  convert hh using 1 <;> field_simp <;> ring

/-- Uniform width with an `H`-dependent comparison angle.  The original proof
is pointwise in `H`, so a common isolated comparator is unnecessary. -/
theorem exists_uniform_width_bound_of_large_family
    {Theta ThetaS : ℝ → ℝ → ℝ} {C0 C beta H1 : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hH1 : 0 < H1)
    (hTheta : ∀ H, H1 ≤ H → Continuous (Theta H))
    (hThetaS : ∀ H, H1 ≤ H → Continuous (ThetaS H))
    (hmodel : ∀ H, H1 ≤ H →
      (∫ t in (-(H / 2))..(H / 2), sin (ThetaS H t)) ≤ C0)
    (hclose : ∀ H, H1 ≤ H → ∀ t ∈ uIoc (-(H / 2)) (H / 2),
      |Theta H t - ThetaS H t| ≤ C * exp (-beta * H))
    (hpos : ∀ H, H1 ≤ H → ∀ t ∈ Ioo (-(H / 2)) (H / 2),
      Theta H t ∈ Ioo 0 π) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H →
      0 < (∫ t in (-(H / 2))..(H / 2), sin (Theta H t)) ∧
      (∫ t in (-(H / 2))..(H / 2), sin (Theta H t)) ≤ C0 + 1 := by
  have hsmall : ∀ᶠ H in Filter.atTop, C * exp (-beta * H) * H ≤ 1 := by
    have h0 : Filter.Tendsto
        (fun x : ℝ => C * ((1 + x) ^ 2 * exp (-beta * x)))
        Filter.atTop (nhds 0) := by
      have ht := (MainThresholds.tendsto_tail_zero (beta := beta) hbeta).const_mul C
      simpa using ht
    have hev := h0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hev, Filter.eventually_ge_atTop (0 : ℝ)] with H hH hH0
    have hexp : 0 < exp (-beta * H) := exp_pos _
    have hle : C * exp (-beta * H) * H ≤
        C * ((1 + H) ^ 2 * exp (-beta * H)) := by
      have hHle : H ≤ (1 + H) ^ 2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hHle (mul_nonneg hC hexp.le)
      calc
        C * exp (-beta * H) * H ≤ C * exp (-beta * H) * (1 + H) ^ 2 := hmul
        _ = C * ((1 + H) ^ 2 * exp (-beta * H)) := by ring
    linarith [hH.le]
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨max (max B 1) H1, lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_right _ _) (le_max_left _ _)), ?_⟩
  intro H hH
  have hH1' : H1 ≤ H := le_trans (le_max_right _ _) hH
  have hHone : (1 : ℝ) ≤ H :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hH
  have hHB : B ≤ H :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hH
  have hab : -(H / 2) ≤ H / 2 := by linarith
  refine ⟨PhaseWidth.width_pos (Θ := Theta H) (hTheta H hH1')
    (by linarith) (hpos H hH1'), ?_⟩
  have hle := PhaseWidth.width_le (Θ := Theta H) (Θs := ThetaS H)
    (ε := C * exp (-beta * H)) (hTheta H hH1') (hThetaS H hH1')
    hab (hclose H hH1')
  have herr : C * exp (-beta * H) * (H / 2 - -(H / 2)) ≤ 1 := by
    have hrw : H / 2 - -(H / 2) = H := by ring
    rw [hrw]
    exact hB H hHB
  linarith [hmodel H hH1']

/-- Phase-centered adapter for the `H`-dependent-comparator width theorem.
All centered-angle positivity hypotheses are discharged by the selected
half-mass centers. -/
theorem exists_uniform_width_bound_of_phase_centered_family
    {K : ℝ → ℝ → ℝ} {ThetaS : ℝ → ℝ → ℝ}
    {C0 C beta H1 : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hH1 : 0 < H1)
    (hKcont : ∀ H, H1 ≤ H → Continuous (K H))
    (hKper : ∀ H, H1 ≤ H → Periodic (K H) H)
    (hKtotal : ∀ H, H1 ≤ H → (∫ r in (0 : ℝ)..H, K H r) = π)
    (hKpos : ∀ H, H1 ≤ H → ∀ s, 0 < K H s)
    (hThetaS : ∀ H, H1 ≤ H → Continuous (ThetaS H))
    (hmodel : ∀ H, H1 ≤ H →
      (∫ t in (-(H / 2))..(H / 2), sin (ThetaS H t)) ≤ C0)
    (hclose : ∀ H, H1 ≤ H → ∀ t ∈ uIoc (-(H / 2)) (H / 2),
      |frontAngle (phaseCenteredCurvature (K H) H) (π / 2) t - ThetaS H t| ≤
        C * exp (-beta * H)) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H →
      0 < (∫ t in (-(H / 2))..(H / 2),
        sin (frontAngle (phaseCenteredCurvature (K H) H) (π / 2) t)) ∧
      (∫ t in (-(H / 2))..(H / 2),
        sin (frontAngle (phaseCenteredCurvature (K H) H) (π / 2) t)) ≤ C0 + 1 := by
  apply exists_uniform_width_bound_of_large_family hbeta hC hH1
  · intro H hH
    exact CurvatureInterpolation.continuous_tangentAngle
      ((hKcont H hH).comp (continuous_id.add continuous_const))
  · exact hThetaS
  · exact hmodel
  · exact hclose
  · intro H hH
    exact phaseCenteredCurvature_mem_Ioo (lt_of_lt_of_le hH1 hH)
      (hKcont H hH) (hKper H hH) (hKtotal H hH) (hKpos H hH)

/-- Simultaneously translating and renormalizing two angles costs at most
twice their pointwise comparison error on the translated cell. -/
theorem shifted_normalized_angle_close
    {Theta ThetaS : ℝ → ℝ} {a H E : ℝ}
    (hclose : ∀ u ∈ Icc (a - H / 2) (a + H / 2),
      |Theta u - ThetaS u| ≤ E) :
    ∀ t ∈ Icc (-(H / 2)) (H / 2),
      |(Theta (t + a) - Theta (a - H / 2)) -
        (ThetaS (t + a) - ThetaS (a - H / 2))| ≤ 2 * E := by
  intro t ht
  have hta : t + a ∈ Icc (a - H / 2) (a + H / 2) := by
    constructor <;> linarith [ht.1, ht.2]
  have hleft : a - H / 2 ∈ Icc (a - H / 2) (a + H / 2) := by
    exact ⟨le_rfl, by linarith [ht.1, ht.2]⟩
  have htri := abs_sub_le
    (Theta (t + a) - ThetaS (t + a))
    0 (Theta (a - H / 2) - ThetaS (a - H / 2))
  simp only [sub_zero, zero_sub, abs_neg] at htri
  have hrewrite :
      (Theta (t + a) - Theta (a - H / 2)) -
          (ThetaS (t + a) - ThetaS (a - H / 2)) =
        (Theta (t + a) - ThetaS (t + a)) -
          (Theta (a - H / 2) - ThetaS (a - H / 2)) := by ring
  rw [hrewrite]
  exact htri.trans (by linarith [hclose _ hta, hclose _ hleft])

/-- A fixed bracket with opposite half-mass inequalities contains a phase
center.  Unlike `exists_half_mass_center`, the bracket here is independent of
the period; this is the form needed to prevent the chosen phase from drifting
by order `H`. -/
theorem exists_half_mass_center_in_fixed_bracket
    {kappa : ℝ → ℝ} {H L R : ℝ} (hLR : L ≤ R)
    (hk : Continuous kappa)
    (hleft : (∫ r in (L - H / 2)..L, kappa r) ≤ π / 2)
    (hright : π / 2 ≤ (∫ r in (R - H / 2)..R, kappa r)) :
    ∃ a ∈ Icc L R, (∫ r in (a - H / 2)..a, kappa r) = π / 2 := by
  let primitive : ℝ → ℝ := fun a => ∫ r in (0 : ℝ)..a, kappa r
  let halfMass : ℝ → ℝ := fun a => primitive a - primitive (a - H / 2)
  have hprim : Continuous primitive :=
    intervalIntegral.continuous_primitive
      (fun a b => hk.intervalIntegrable (μ := volume) a b) 0
  have hhalfCont : Continuous halfMass := by
    exact hprim.sub (hprim.comp (continuous_id.sub continuous_const))
  have hhalfEq : ∀ a, halfMass a = ∫ r in (a - H / 2)..a, kappa r := by
    intro a
    dsimp [halfMass, primitive]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hk.intervalIntegrable (μ := volume) (a - H / 2) 0)
      (hk.intervalIntegrable (μ := volume) 0 a)
    rw [sub_eq_add_neg, ← intervalIntegral.integral_symm]
    simpa [add_comm] using hadd
  have htarget : π / 2 ∈ uIcc (halfMass L) (halfMass R) := by
    rw [mem_uIcc]
    left
    constructor
    · simpa [hhalfEq] using hleft
    · simpa [hhalfEq] using hright
  have hiv := intermediate_value_uIcc
    (a := L) (b := R) hhalfCont.continuousOn htarget
  obtain ⟨a, ha, hval⟩ := hiv
  rw [uIcc_of_le hLR] at ha
  exact ⟨a, ha, by rw [← hhalfEq a, hval]⟩

/-- Eventual fixed-bracket crossing produces one family of half-mass centers
whose absolute values are uniformly bounded. -/
theorem exists_uniformly_bounded_half_mass_centers
    {K : ℝ → ℝ → ℝ} {H0 L R : ℝ} (hLR : L ≤ R)
    (hKcont : ∀ H, H0 ≤ H → Continuous (K H))
    (hleft : ∀ H, H0 ≤ H →
      (∫ r in (L - H / 2)..L, K H r) ≤ π / 2)
    (hright : ∀ H, H0 ≤ H →
      π / 2 ≤ (∫ r in (R - H / 2)..R, K H r)) :
    ∃ center : ℝ → ℝ, ∀ H, H0 ≤ H →
      center H ∈ Icc L R ∧
      |center H| ≤ max |L| |R| ∧
      (∫ r in (center H - H / 2)..center H, K H r) = π / 2 := by
  classical
  have hexists : ∀ H, H0 ≤ H →
      ∃ a ∈ Icc L R, (∫ r in (a - H / 2)..a, K H r) = π / 2 := by
    intro H hH
    exact exists_half_mass_center_in_fixed_bracket hLR (hKcont H hH)
      (hleft H hH) (hright H hH)
  let center : ℝ → ℝ := fun H =>
    if hH : H0 ≤ H then Classical.choose (hexists H hH) else 0
  refine ⟨center, ?_⟩
  intro H hH
  have hspec := Classical.choose_spec (hexists H hH)
  have hc : center H = Classical.choose (hexists H hH) := by
    simp [center, hH]
  rw [hc]
  refine ⟨hspec.1, ?_, hspec.2⟩
  exact (abs_le_max_abs_abs hspec.1.1 hspec.1.2)

/-- The angle-closeness theorem is stable under a uniformly bounded
translation.  The exponential localization constants are enlarged by the
explicit factor `exp (alpha * R)`. -/
theorem angle_sup_close_of_bounded_shift
    {y yp Kstar KH ThH Ths : ℝ → ℝ}
    {C CK D a alpha beta H q R : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H) (hbeta : 0 < beta)
    (hba : beta < alpha / 2)
    (hhalf : Real.exp (-(beta * H)) ≤ 1 / 2)
    (hR : 0 ≤ R) (hq : |q| ≤ R)
    (hy : Continuous y) (hyp : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u, (∑' m : ℤ, y (u - m * H)) ≤ a)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hKH : ∀ t, KH t = (∑' m : ℤ, y (t - m * H)) +
      G (∑' m : ℤ, y (t - m * H)) * (∑' m : ℤ, yp (t - m * H)))
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hThH : ∀ t, HasDerivAt ThH (KH t) t)
    (hThs : ∀ t, HasDerivAt Ths (Kstar t) t)
    {s : ℝ} (hs : s ∈ Icc (-(H / 2)) (H / 2)) :
    |(ThH (s + q) - ThH q) - (Ths (s + q) - Ths q)| ≤
      (lipConst a * D *
          (8 * (C * Real.exp (alpha * R)) ^ 2 / (alpha - beta)) +
        2 * (CK * Real.exp (alpha * R)) / alpha) *
        Real.exp (-(beta * H)) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hCK : 0 ≤ CK := by
    have h := hKbd 0
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact (abs_nonneg (Kstar 0)).trans h
  have habs_shift : ∀ t : ℝ, -|t + q| ≤ -|t| + R := by
    intro t
    have htri : |t| ≤ |t + q| + |q| := by
      have := abs_add_le (t + q) (-q)
      simpa using this
    linarith
  have hyb_shift : ∀ t, y (t + q) ≤
      (C * Real.exp (alpha * R)) * Real.exp (-alpha * |t|) := by
    intro t
    refine (hyb (t + q)).trans ?_
    have hexp : Real.exp (-alpha * |t + q|) ≤
        Real.exp (alpha * R) * Real.exp (-alpha * |t|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by
        have := habs_shift t
        nlinarith)
    calc C * Real.exp (-alpha * |t + q|)
        ≤ C * (Real.exp (alpha * R) * Real.exp (-alpha * |t|)) :=
          mul_le_mul_of_nonneg_left hexp hC
      _ = (C * Real.exp (alpha * R)) * Real.exp (-alpha * |t|) := by ring
  have hKbd_shift : ∀ t, |Kstar (t + q)| ≤
      (CK * Real.exp (alpha * R)) * Real.exp (-alpha * |t|) := by
    intro t
    refine (hKbd (t + q)).trans ?_
    have hexp : Real.exp (-alpha * |t + q|) ≤
        Real.exp (alpha * R) * Real.exp (-alpha * |t|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by
        have := habs_shift t
        nlinarith)
    calc CK * Real.exp (-alpha * |t + q|)
        ≤ CK * (Real.exp (alpha * R) * Real.exp (-alpha * |t|)) :=
          mul_le_mul_of_nonneg_left hexp hCK
      _ = (CK * Real.exp (alpha * R)) * Real.exp (-alpha * |t|) := by ring
  apply AngleClose.angle_sup_close
    (y := fun t => y (t + q)) (yp := fun t => yp (t + q))
    (Kstar := fun t => Kstar (t + q)) (KH := fun t => KH (t + q))
    (ThH := fun t => ThH (t + q) - ThH q)
    (Ths := fun t => Ths (t + q) - Ths q)
    (C := C * Real.exp (alpha * R)) (CK := CK * Real.exp (alpha * R))
    halpha hH hbeta hba hhalf
  · exact hy.comp (continuous_id.add continuous_const)
  · exact hyp.comp (continuous_id.add continuous_const)
  · exact fun t => hy0 (t + q)
  · exact hyb_shift
  · exact hD
  · exact fun t => hypb (t + q)
  · exact ha0
  · exact ha1
  · intro u
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hYa (u + q)
  · exact fun t => hKstar (t + q)
  · intro t
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hKH (t + q)
  · exact hKint.comp_add_right q
  · exact fun t => hK0 (t + q)
  · exact hKbd_shift
  · intro t
    simpa using (((hThH (t + q)).comp t
      ((hasDerivAt_id t).add_const q)).sub_const (ThH q))
  · intro t
    simpa using (((hThs (t + q)).comp t
      ((hasDerivAt_id t).add_const q)).sub_const (Ths q))
  · simp
  · exact hs

/-- An `L¹` comparison on the centered cell controls every ordered
subinterval of that cell. -/
theorem abs_intervalIntegral_sub_le_cell_L1
    {f g : ℝ → ℝ} {H p q E : ℝ}
    (hH : 0 < H) (hpq : p ≤ q)
    (hp : -(H / 2) ≤ p) (hq : q ≤ H / 2)
    (hf : Continuous f) (hg : Continuous g)
    (hL1 : (∫ t in (-(H / 2))..(H / 2), |f t - g t|) ≤ E) :
    |(∫ t in p..q, f t) - ∫ t in p..q, g t| ≤ E := by
  have hfi := hf.intervalIntegrable (μ := volume) p q
  have hgi := hg.intervalIntegrable (μ := volume) p q
  have hdiff : (∫ t in p..q, f t) - ∫ t in p..q, g t =
      ∫ t in p..q, (f t - g t) := by
    rw [intervalIntegral.integral_sub hfi hgi]
  rw [hdiff]
  refine (intervalIntegral.abs_integral_le_integral_abs hpq).trans ?_
  refine (intervalIntegral.integral_mono_interval hp hpq hq
    (Filter.Eventually.of_forall (fun t => abs_nonneg (f t - g t)))
    ((hf.sub hg).abs.intervalIntegrable _ _)).trans hL1

/-- Quantitative fixed-bracket signs.  If the periodized curvature is `L¹`
close to an isolated curvature of total mass `π`, and the isolated
exponential tails plus that error are below `π/2`, then the two sliding
half-window masses at `-R` and `R` lie on opposite sides of `π/2`. -/
theorem fixed_bracket_half_mass_inequalities
    {KH Kstar : ℝ → ℝ} {H R E CK alpha : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H) (hR : 0 ≤ R)
    (h2R : 2 * R ≤ H)
    (hKHcont : Continuous KH) (hKcont : Continuous Kstar)
    (hKHper : Periodic KH H)
    (hKHtotal : (∫ t in (0 : ℝ)..H, KH t) = π)
    (hKint : Integrable Kstar) (hKtotal : (∫ t : ℝ, Kstar t) = π)
    (hKbd : ∀ t, |Kstar t| ≤ CK * Real.exp (-alpha * |t|))
    (hL1 : (∫ t in (-(H / 2))..(H / 2), |KH t - Kstar t|) ≤ E)
    (htail : CK * Real.exp (-alpha * R) / alpha +
        CK * Real.exp (-alpha * (H / 2 - R)) / alpha + E ≤ π / 2) :
    (∫ t in (-R - H / 2)..(-R), KH t) ≤ π / 2 ∧
      π / 2 ≤ (∫ t in (R - H / 2)..R, KH t) := by
  have hpRight : R - H / 2 ≤ 0 := by linarith
  have hqRight : 0 ≤ R := hR
  have htailRight := MatchingEstimates.abs_integral_compl_le
    (g := Kstar) (C := CK) (alpha := alpha)
    halpha hpRight hqRight hKint hKbd
  rw [hKtotal] at htailRight
  have hrightApprox := abs_intervalIntegral_sub_le_cell_L1
    (f := KH) (g := Kstar) (H := H) (p := R - H / 2) (q := R) (E := E)
    hH (by linarith) (by linarith) (by linarith) hKHcont hKcont hL1
  have hrightMass : π / 2 ≤ ∫ t in (R - H / 2)..R, KH t := by
    have hexp : Real.exp (alpha * (R - H / 2)) =
        Real.exp (-alpha * (H / 2 - R)) := by
      congr 1
      ring
    have htailRight' :
        |π - ∫ s in (R - H / 2)..R, Kstar s| ≤
          CK * Real.exp (-alpha * R) / alpha +
            CK * Real.exp (-alpha * (H / 2 - R)) / alpha := by
      calc
        |π - ∫ s in (R - H / 2)..R, Kstar s| ≤
            CK * Real.exp (alpha * (R - H / 2)) / alpha +
              CK * Real.exp (-alpha * R) / alpha := htailRight
        _ = CK * Real.exp (-alpha * R) / alpha +
              CK * Real.exp (-alpha * (H / 2 - R)) / alpha := by rw [hexp]; ring
    have h1 := le_of_abs_le htailRight'
    have h2 := neg_le_of_abs_le hrightApprox
    linarith
  have hpLeft : -R ≤ 0 := by linarith
  have hqLeft : 0 ≤ H / 2 - R := by linarith
  have htailLeft := MatchingEstimates.abs_integral_compl_le
    (g := Kstar) (C := CK) (alpha := alpha)
    halpha hpLeft hqLeft hKint hKbd
  rw [hKtotal] at htailLeft
  have hleftApprox := abs_intervalIntegral_sub_le_cell_L1
    (f := KH) (g := Kstar) (H := H) (p := -R) (q := H / 2 - R) (E := E)
    hH (by linarith) (by linarith) (by linarith) hKHcont hKcont hL1
  have hcentralMass : π / 2 ≤ ∫ t in (-R)..(H / 2 - R), KH t := by
    have hexp : Real.exp (alpha * (-R)) = Real.exp (-alpha * R) := by
      congr 1
      ring
    have htailLeft' :
        |π - ∫ s in (-R)..(H / 2 - R), Kstar s| ≤
          CK * Real.exp (-alpha * R) / alpha +
            CK * Real.exp (-alpha * (H / 2 - R)) / alpha := by
      simpa [hexp] using htailLeft
    have h1 := le_of_abs_le htailLeft'
    have h2 := neg_le_of_abs_le hleftApprox
    linarith
  have hperiod : (∫ t in (-R - H / 2)..(H / 2 - R), KH t) = π := by
    have hp := hKHper.intervalIntegral_add_eq (-R - H / 2) 0
    rw [show -R - H / 2 + H = H / 2 - R by ring,
      show (0 : ℝ) + H = H by ring] at hp
    exact hp.trans hKHtotal
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hKHcont.intervalIntegrable (μ := volume) (-R - H / 2) (-R))
    (hKHcont.intervalIntegrable (μ := volume) (-R) (H / 2 - R))
  constructor
  · linarith [hadd, hperiod]
  · exact hrightMass

/-- Once the fixed isolated tail beyond `R` is below half the total mass, the
opposite moving tail and an exponential periodization error are simultaneously
small for all sufficiently large periods. -/
theorem eventually_fixed_bracket_tail_error
    {alpha beta CK E0 R : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hfixed : CK * Real.exp (-alpha * R) / alpha < π / 2) :
    ∀ᶠ H in Filter.atTop,
      2 * R ≤ H ∧
      CK * Real.exp (-alpha * R) / alpha +
          CK * Real.exp (-alpha * (H / 2 - R)) / alpha +
            E0 * Real.exp (-beta * H) ≤ π / 2 := by
  let gap : ℝ := π / 2 - CK * Real.exp (-alpha * R) / alpha
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hmove := FrontPeriodizationPositivity.eventually_const_mul_exp_neg_le
    (A := CK / alpha * Real.exp (alpha * R))
    (c := alpha / 2) (b := gap / 2) (by positivity) (by positivity)
  have herr := FrontPeriodizationPositivity.eventually_const_mul_exp_neg_le
    (A := E0) (c := beta) (b := gap / 2) hbeta (by positivity)
  filter_upwards [hmove, herr, Filter.eventually_ge_atTop (2 * R)] with H hm he hHR
  refine ⟨hHR, ?_⟩
  have hmoveEq :
      CK / alpha * Real.exp (alpha * R) * Real.exp (-(alpha / 2) * H) =
        CK * Real.exp (-alpha * (H / 2 - R)) / alpha := by
    calc
      CK / alpha * Real.exp (alpha * R) * Real.exp (-(alpha / 2) * H) =
          CK / alpha * (Real.exp (alpha * R) * Real.exp (-(alpha / 2) * H)) := by ring
      _ = CK / alpha * Real.exp (alpha * R + -(alpha / 2) * H) := by
        rw [Real.exp_add]
      _ = CK * Real.exp (-alpha * (H / 2 - R)) / alpha := by
        have hexp : Real.exp (alpha * R + -(alpha / 2) * H) =
            Real.exp (-alpha * (H / 2 - R)) := by
          congr 1
          ring
        rw [hexp]
        ring
  rw [hmoveEq] at hm
  dsimp [gap] at hm he ⊢
  linarith

/-- Every exponential isolated-curvature bound admits a positive symmetric
bracket radius whose fixed tail contribution is below `π/2`. -/
theorem exists_fixed_tail_radius {alpha CK : ℝ} (halpha : 0 < alpha) :
    ∃ R : ℝ, 0 < R ∧ CK * Real.exp (-alpha * R) / alpha < π / 2 := by
  have hev := FrontPeriodizationPositivity.eventually_const_mul_exp_neg_le
    (A := CK / alpha) (c := alpha) (b := π / 4)
    halpha (by positivity)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hev
  let R := max B 1
  refine ⟨R, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  have hsmall := hB R (le_max_left _ _)
  have heq : CK / alpha * Real.exp (-alpha * R) =
      CK * Real.exp (-alpha * R) / alpha := by ring
  rw [heq] at hsmall
  linarith [Real.pi_pos]

/-- Subtracting the isolated angle at the left endpoint changes its sine
integral by at most the cell length times the size of that endpoint angle. -/
theorem normalized_shifted_sine_integral_le
    {theta : ℝ → ℝ} {H q C0 E : ℝ}
    (hH : 0 < H) (htheta : Continuous theta)
    (hsin0 : ∀ t, 0 ≤ Real.sin (theta t))
    (hmodel : (∫ t in (-(H / 2))..(H / 2),
      Real.sin (theta (t + q))) ≤ C0)
    (hleft : |theta (q - H / 2)| ≤ E) :
    (∫ t in (-(H / 2))..(H / 2),
        Real.sin (theta (t + q) - theta (q - H / 2))) ≤ C0 + H * E := by
  have hab : -(H / 2) ≤ H / 2 := by linarith
  have hpoint : ∀ t,
      Real.sin (theta (t + q) - theta (q - H / 2)) ≤
        Real.sin (theta (t + q)) + |theta (q - H / 2)| := by
    intro t
    rw [Real.sin_sub]
    have hfirst : Real.sin (theta (t + q)) * Real.cos (theta (q - H / 2)) ≤
        Real.sin (theta (t + q)) := by
      have hc := Real.cos_le_one (theta (q - H / 2))
      nlinarith [hsin0 (t + q)]
    have hsecond : -(Real.cos (theta (t + q)) * Real.sin (theta (q - H / 2))) ≤
        |theta (q - H / 2)| := by
      calc
        -(Real.cos (theta (t + q)) * Real.sin (theta (q - H / 2))) ≤
            |Real.cos (theta (t + q)) * Real.sin (theta (q - H / 2))| :=
              neg_le_abs _
        _ = |Real.cos (theta (t + q))| * |Real.sin (theta (q - H / 2))| :=
              abs_mul _ _
        _ ≤ 1 * |Real.sin (theta (q - H / 2))| :=
              mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
        _ ≤ |theta (q - H / 2)| := by
              simpa using (Real.abs_sin_le_abs :
                |Real.sin (theta (q - H / 2))| ≤ |theta (q - H / 2)|)
    linarith
  have hleft0 : 0 ≤ |theta (q - H / 2)| := abs_nonneg _
  have hcomp : Continuous (fun t => theta (t + q)) :=
    htheta.comp (continuous_id.add continuous_const)
  have hnorm : Continuous (fun t => theta (t + q) - theta (q - H / 2)) :=
    hcomp.sub continuous_const
  have hmono := intervalIntegral.integral_mono_on hab
    ((Real.continuous_sin.comp hnorm).intervalIntegrable (μ := volume) _ _)
    (((Real.continuous_sin.comp hcomp).add continuous_const).intervalIntegrable
      (μ := volume) _ _)
    (fun t _ => hpoint t)
  change (∫ t in (-(H / 2))..(H / 2),
      Real.sin (theta (t + q) - theta (q - H / 2))) ≤
    ∫ t in (-(H / 2))..(H / 2),
      (Real.sin (theta (t + q)) + |theta (q - H / 2)|) at hmono
  have hsplit :
      (∫ t in (-(H / 2))..(H / 2),
        (Real.sin (theta (t + q)) + |theta (q - H / 2)|)) =
      (∫ t in (-(H / 2))..(H / 2), Real.sin (theta (t + q))) +
        H * |theta (q - H / 2)| := by
    calc
      (∫ t in (-(H / 2))..(H / 2),
          (Real.sin (theta (t + q)) + |theta (q - H / 2)|)) =
          (∫ t in (-(H / 2))..(H / 2), Real.sin (theta (t + q))) +
            ∫ _t in (-(H / 2))..(H / 2), |theta (q - H / 2)| := by
              exact intervalIntegral.integral_add
                ((Real.continuous_sin.comp hcomp).intervalIntegrable _ _)
                ((continuous_const : Continuous
                  (fun _ : ℝ => |theta (q - H / 2)|)).intervalIntegrable
                    (μ := volume) _ _)
      _ = (∫ t in (-(H / 2))..(H / 2), Real.sin (theta (t + q))) +
          H * |theta (q - H / 2)| := by simp
  rw [hsplit] at hmono
  have hmul : H * |theta (q - H / 2)| ≤ H * E :=
    mul_le_mul_of_nonneg_left hleft hH.le
  linarith

/-- A uniformly bounded phase and an exponential left-angle tail make the
normalization cost `H * |theta(center H - H/2)|` eventually at most one. -/
theorem eventually_normalized_shifted_sine_integral_le
    {theta : ℝ → ℝ} {center : ℝ → ℝ}
    {C0 A gamma R : ℝ}
    (hgamma : 0 < gamma) (hA : 0 ≤ A)
    (htheta : Continuous theta) (hsin0 : ∀ t, 0 ≤ Real.sin (theta t))
    (hcenter : ∀ H, |center H| ≤ R)
    (hbase : ∀ H, 0 < H →
      (∫ t in (-(H / 2))..(H / 2), Real.sin (theta (t + center H))) ≤ C0)
    (hleftTail : ∀ x, x ≤ 0 → |theta x| ≤ A * Real.exp (gamma * x)) :
    ∀ᶠ H in Filter.atTop,
      (∫ t in (-(H / 2))..(H / 2),
        Real.sin (theta (t + center H) - theta (center H - H / 2))) ≤ C0 + 1 := by
  have hsmall : ∀ᶠ H in Filter.atTop,
      A * Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H) * H ≤ 1 := by
    have ht := (MainThresholds.tendsto_tail_zero (beta := gamma / 2) (by positivity)).const_mul
      (A * Real.exp (gamma * R))
    simp only [mul_zero] at ht
    have hev := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hev, Filter.eventually_ge_atTop (0 : ℝ)] with H he hH0
    have hHle : H ≤ (1 + H) ^ 2 := by nlinarith
    have hcoef : 0 ≤ A * Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H) := by positivity
    have hdom := mul_le_mul_of_nonneg_left hHle hcoef
    have he' : A * Real.exp (gamma * R) *
        ((1 + H) ^ 2 * Real.exp (-(gamma / 2) * H)) < 1 := by
      simpa using he
    calc
      A * Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H) * H ≤
          A * Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H) * (1 + H) ^ 2 := hdom
      _ = A * Real.exp (gamma * R) *
          ((1 + H) ^ 2 * Real.exp (-(gamma / 2) * H)) := by ring
      _ ≤ 1 := he'.le
  filter_upwards [hsmall, Filter.eventually_ge_atTop (max 1 (2 * R))] with H hs hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hH)
  have h2R : 2 * R ≤ H := le_trans (le_max_right _ _) hH
  have hqle : center H ≤ R := (le_abs_self (center H)).trans (hcenter H)
  have hx : center H - H / 2 ≤ 0 := by linarith
  have htail0 := hleftTail (center H - H / 2) hx
  have hexp : Real.exp (gamma * (center H - H / 2)) ≤
      Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have htail : |theta (center H - H / 2)| ≤
      A * Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H) := by
    refine htail0.trans ?_
    calc
      A * Real.exp (gamma * (center H - H / 2)) ≤
          A * (Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H)) :=
            mul_le_mul_of_nonneg_left hexp hA
      _ = A * Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H) := by ring
  have hnorm := normalized_shifted_sine_integral_le hHpos htheta hsin0
    (hbase H hHpos) htail
  have hcost : H * (A * Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H)) ≤ 1 := by
    calc
      H * (A * Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H)) =
          A * Real.exp (gamma * R) * Real.exp (-(gamma / 2) * H) * H := by ring
      _ ≤ 1 := hs
  linarith

/-- The exponential-majorant integral bound holds on every ordered finite
interval, not only centered ones. -/
theorem interval_integral_le_of_exp_bound
    {w : ℝ → ℝ} {C alpha p q : ℝ} (halpha : 0 < alpha) (hpq : p ≤ q)
    (hw : Continuous w) (hw0 : ∀ s, 0 ≤ w s)
    (hwb : ∀ s, w s ≤ C * Real.exp (-alpha * |s|)) :
    (∫ s in p..q, w s) ≤ 2 * C / alpha := by
  have hC0 : 0 ≤ C := by
    have h := (hw0 0).trans (hwb 0)
    simpa using h
  let majorant : ℝ → ℝ := fun s => C * Real.exp (-alpha * |s|)
  have hMint : Integrable majorant :=
    (L1Matching.integrable_expabs halpha).const_mul C
  have hM0 : ∀ s, 0 ≤ majorant s := fun s => mul_nonneg hC0 (Real.exp_pos _).le
  have hmono := intervalIntegral.integral_mono_on hpq
    (hw.intervalIntegrable _ _) (hMint.intervalIntegrable)
    (fun s _ => hwb s)
  have hset : (∫ s in p..q, majorant s) ≤ ∫ s : ℝ, majorant s := by
    rw [intervalIntegral.integral_of_le hpq]
    exact MeasureTheory.setIntegral_le_integral hMint
      (Filter.Eventually.of_forall hM0)
  have hval : (∫ s : ℝ, majorant s) = 2 * C / alpha := by
    dsimp [majorant]
    rw [MeasureTheory.integral_const_mul, L1Matching.integral_expabs halpha]
    ring
  linarith

/-- The isolated translating hairpin has the same `4 Am` transverse bound on
every shifted interval. -/
theorem isolated_hairpin_interval_width_le
    {f theta : ℝ → ℝ} {m Am : ℝ}
    (hf : ContinuousOn f (Ioo 0 π)) (hm : 0 < m) (hmA : m ≤ Am)
    (hlow : ∀ t ∈ Ioo (0 : ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) π, f t ≤ Am)
    (hmem : ∀ u, theta u ∈ Ioo (0 : ℝ) π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (htheta : ∀ u, HasDerivAt theta
      (HairpinRelative.curvField f (theta u)) u) :
    ∀ p q, p ≤ q → (∫ s in p..q, Real.sin (theta s)) ≤ 4 * Am := by
  have hAm : 0 < Am := lt_of_lt_of_le hm hmA
  have hthetac : Continuous theta :=
    continuous_iff_continuousAt.mpr fun s => (htheta s).continuousAt
  have hw : Continuous (fun s => Real.sin (theta s)) :=
    Real.continuous_sin.comp hthetac
  have hw0 : ∀ s, 0 ≤ Real.sin (theta s) := fun s =>
    (Real.sin_pos_of_pos_of_lt_pi (hmem s).1 (hmem s).2).le
  have htail : ∀ s, Real.sin (theta s) ≤
      2 * Real.exp (-(1 / Am) * |s|) := by
    intro s
    have hs := HairpinTails.sin_le_two_exp (hmem s)
    have harc := HairpinTails.abs_arclength_le hf hm hlow hupp (hmem s)
    rw [hval s] at harc
    have hlog : |s| / Am ≤ |HairpinTails.logHalf (theta s)| := by
      rw [div_le_iff₀ hAm]
      simpa [mul_comm] using harc
    have hlog' : (1 / Am) * |s| ≤ |HairpinTails.logHalf (theta s)| := by
      calc
        (1 / Am) * |s| = |s| / Am := by ring
        _ ≤ |HairpinTails.logHalf (theta s)| := hlog
    have he : Real.exp (-|HairpinTails.logHalf (theta s)|) ≤
        Real.exp (-(1 / Am) * |s|) := by
      apply Real.exp_le_exp.mpr
      linarith
    exact hs.trans (mul_le_mul_of_nonneg_left he (by norm_num))
  intro p q hpq
  have hh := interval_integral_le_of_exp_bound (C := (2 : ℝ))
    (alpha := 1 / Am) (by positivity) hpq hw hw0 htail
  convert hh using 1 <;> field_simp <;> ring

/-- On the negative intrinsic-arclength ray, the isolated translator angle
itself has an exponential tail. -/
theorem isolated_hairpin_left_angle_le
    {f theta : ℝ → ℝ} {m Am : ℝ}
    (hf : ContinuousOn f (Ioo 0 π)) (hm : 0 < m) (hmA : m ≤ Am)
    (hlow : ∀ t ∈ Ioo (0 : ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) π, f t ≤ Am)
    (hmem : ∀ u, theta u ∈ Ioo (0 : ℝ) π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) :
    ∀ s, s ≤ 0 → |theta s| ≤ π * Real.exp ((1 / Am) * s) := by
  have hAm : 0 < Am := lt_of_lt_of_le hm hmA
  have hmono := HairpinArclength.strictMonoOn_arclength hf hm hlow
  intro s hs0
  have hthetaHalf : theta s ≤ π / 2 := by
    by_contra hnot
    have hlt : π / 2 < theta s := lt_of_not_ge hnot
    have hpiHalf : π / 2 ∈ Ioo (0 : ℝ) π :=
      ⟨Real.pi_div_two_pos, half_lt_self Real.pi_pos⟩
    have hstrict := hmono hpiHalf (hmem s) hlt
    have hzero : Hairpin.hairpinArclength f (π / 2) (π / 2) = 0 := by
      simp [Hairpin.hairpinArclength]
    rw [hzero, hval s] at hstrict
    linarith
  have hsinTail : Real.sin (theta s) ≤ 2 * Real.exp ((1 / Am) * s) := by
    have htail := HairpinTails.sin_le_two_exp (hmem s)
    have harc := HairpinTails.abs_arclength_le hf hm hlow hupp (hmem s)
    rw [hval s] at harc
    have hlog : |s| / Am ≤ |HairpinTails.logHalf (theta s)| := by
      rw [div_le_iff₀ hAm]
      simpa [mul_comm] using harc
    have hlog' : (1 / Am) * |s| ≤ |HairpinTails.logHalf (theta s)| := by
      calc
        (1 / Am) * |s| = |s| / Am := by ring
        _ ≤ |HairpinTails.logHalf (theta s)| := hlog
    have he : Real.exp (-|HairpinTails.logHalf (theta s)|) ≤
        Real.exp (-(1 / Am) * |s|) := by
      apply Real.exp_le_exp.mpr
      linarith
    have htail' := htail.trans (mul_le_mul_of_nonneg_left he (by norm_num))
    rw [abs_of_nonpos hs0] at htail'
    convert htail' using 1 <;> congr 2 <;> ring
  have hmul := Real.mul_le_sin (hmem s).1.le hthetaHalf
  have hthetaSin : theta s ≤ π / 2 * Real.sin (theta s) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at hmul
    nlinarith
  rw [abs_of_pos (hmem s).1]
  calc
    theta s ≤ π / 2 * Real.sin (theta s) := hthetaSin
    _ ≤ π / 2 * (2 * Real.exp ((1 / Am) * s)) :=
      mul_le_mul_of_nonneg_left hsinTail (by positivity)
    _ = π * Real.exp ((1 / Am) * s) := by ring

/-- For every uniformly bounded phase family, the left-normalized isolated
hairpin comparator has eventual width at most `4 Am + 1`. -/
theorem eventually_isolated_hairpin_normalized_width_le
    {f theta : ℝ → ℝ} {center : ℝ → ℝ} {m Am R : ℝ}
    (hf : ContinuousOn f (Ioo 0 π)) (hm : 0 < m) (hmA : m ≤ Am)
    (hlow : ∀ t ∈ Ioo (0 : ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) π, f t ≤ Am)
    (hmem : ∀ u, theta u ∈ Ioo (0 : ℝ) π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (htheta : ∀ u, HasDerivAt theta
      (HairpinRelative.curvField f (theta u)) u)
    (hcenter : ∀ H, |center H| ≤ R) :
    ∀ᶠ H in Filter.atTop,
      (∫ t in (-(H / 2))..(H / 2),
        Real.sin (theta (t + center H) - theta (center H - H / 2))) ≤
          4 * Am + 1 := by
  have hAm : 0 < Am := lt_of_lt_of_le hm hmA
  have hthetac : Continuous theta :=
    continuous_iff_continuousAt.mpr fun s => (htheta s).continuousAt
  have hsin0 : ∀ s, 0 ≤ Real.sin (theta s) := fun s =>
    (Real.sin_pos_of_pos_of_lt_pi (hmem s).1 (hmem s).2).le
  apply eventually_normalized_shifted_sine_integral_le
    (theta := theta) (center := center) (C0 := 4 * Am)
    (A := π) (gamma := 1 / Am) (R := R)
    (by positivity) Real.pi_pos.le hthetac hsin0 hcenter
  · intro H hH
    change (∫ t in (-(H / 2))..(H / 2),
      (fun s : ℝ => Real.sin (theta s)) (t + center H)) ≤ 4 * Am
    rw [intervalIntegral.integral_comp_add_right
      (f := fun s : ℝ => Real.sin (theta s)) (center H)]
    have hw := isolated_hairpin_interval_width_le hf hm hmA hlow hupp hmem hval htheta
      (center H - H / 2) (center H + H / 2) (by linarith)
    convert hw using 1 <;> ring
  · exact isolated_hairpin_left_angle_le hf hm hmA hlow hupp hmem hval

/-- Width theorem for an explicitly selected family of exact half-mass
centers.  This is the final geometric adapter used after the fixed-bracket
selection: all positivity hypotheses for the shifted periodized angle are
derived here. -/
theorem exists_uniform_width_bound_of_selected_centers
    {K : ℝ → ℝ → ℝ} {center : ℝ → ℝ}
    {ThetaS : ℝ → ℝ → ℝ} {C0 C beta H1 : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hH1 : 0 < H1)
    (hKcont : ∀ H, H1 ≤ H → Continuous (K H))
    (hKper : ∀ H, H1 ≤ H → Periodic (K H) H)
    (hKtotal : ∀ H, H1 ≤ H → (∫ r in (0 : ℝ)..H, K H r) = π)
    (hKpos : ∀ H, H1 ≤ H → ∀ s, 0 < K H s)
    (hhalf : ∀ H, H1 ≤ H →
      (∫ r in (center H - H / 2)..center H, K H r) = π / 2)
    (hThetaS : ∀ H, H1 ≤ H → Continuous (ThetaS H))
    (hmodel : ∀ H, H1 ≤ H →
      (∫ t in (-(H / 2))..(H / 2), Real.sin (ThetaS H t)) ≤ C0)
    (hclose : ∀ H, H1 ≤ H → ∀ t ∈ uIoc (-(H / 2)) (H / 2),
      |frontAngle (fun s => K H (s + center H)) (π / 2) t - ThetaS H t| ≤
        C * Real.exp (-beta * H)) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H →
      0 < (∫ t in (-(H / 2))..(H / 2),
        Real.sin (frontAngle (fun s => K H (s + center H)) (π / 2) t)) ∧
      (∫ t in (-(H / 2))..(H / 2),
        Real.sin (frontAngle (fun s => K H (s + center H)) (π / 2) t)) ≤ C0 + 1 := by
  apply exists_uniform_width_bound_of_large_family hbeta hC hH1
  · intro H hH
    exact CurvatureInterpolation.continuous_tangentAngle
      ((hKcont H hH).comp (continuous_id.add continuous_const))
  · exact hThetaS
  · exact hmodel
  · exact hclose
  · intro H hH t ht
    have hkshift : Continuous (fun s => K H (s + center H)) :=
      (hKcont H hH).comp (continuous_id.add continuous_const)
    have hpershift : Periodic (fun s => K H (s + center H)) H := by
      intro s
      change K H (s + H + center H) = K H (s + center H)
      convert (hKper H hH) (s + center H) using 1 <;> ring
    have htotalshift :
        (∫ r in (0 : ℝ)..H, K H (r + center H)) = π := by
      rw [intervalIntegral.integral_comp_add_right]
      have hp := (hKper H hH).intervalIntegral_add_eq 0 (center H)
      calc
        (∫ r in (0 : ℝ) + center H..H + center H, K H r) =
            ∫ r in center H..center H + H, K H r := by congr 1 <;> ring
        _ = ∫ r in (0 : ℝ)..H, K H r := by simpa using hp.symm
        _ = π := hKtotal H hH
    have hhalfshift :
        (∫ r in (-(H / 2))..(0 : ℝ), K H (r + center H)) = π / 2 := by
      rw [intervalIntegral.integral_comp_add_right]
      convert hhalf H hH using 1 <;> ring
    exact centered_frontAngle_mem_Ioo (lt_of_lt_of_le hH1 hH) hkshift hpershift
      htotalshift (fun s => hKpos H hH (s + center H)) hhalfshift t ht

/-- `WidthUniformProduced` with its centered-angle hypothesis discharged by
strict curvature, total turning, and the exact half-cell normalization.

The family `KH H` is required to be the periodization formula of one fixed
pulse `y`; the resulting tangent-angle family is constructed here as
`frontAngle (KH H) (π/2)`. -/
theorem exists_uniform_width_bound_of_strict_pulse
    {y yp Kstar Ths : ℝ → ℝ} {KH : ℝ → ℝ → ℝ}
    {C CK D a alpha beta C0 H1 : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hba : beta < alpha / 2)
    (hy : Continuous y) (hyp : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * exp (-alpha * |s|))
    (hThs : ∀ t, HasDerivAt Ths (Kstar t) t)
    (hThs0 : Ths 0 = π / 2)
    (hH1 : 0 < H1)
    (hYa : ∀ H, H1 ≤ H → ∀ u,
      (∑' m : ℤ, y (u - m * H)) ≤ a)
    (hKH : ∀ H, H1 ≤ H → ∀ t,
      KH H t = (∑' m : ℤ, y (t - m * H)) +
        G (∑' m : ℤ, y (t - m * H)) * (∑' m : ℤ, yp (t - m * H)))
    (hKHcont : ∀ H, H1 ≤ H → Continuous (KH H))
    (hKHper : ∀ H, H1 ≤ H → Periodic (KH H) H)
    (hKHtotal : ∀ H, H1 ≤ H → (∫ r in (0 : ℝ)..H, KH H r) = π)
    (hKHpos : ∀ H, H1 ≤ H → ∀ s, 0 < KH H s)
    (hhalf : ∀ H, H1 ≤ H →
      (∫ r in (-(H / 2))..(0 : ℝ), KH H r) = π / 2)
    (hmodel : ∀ H, H1 ≤ H →
      (∫ t in (-(H / 2))..(H / 2), sin (Ths t)) ≤ C0) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H →
      0 < (∫ t in (-(H / 2))..(H / 2),
        sin (frontAngle (KH H) (π / 2) t)) ∧
      (∫ t in (-(H / 2))..(H / 2),
        sin (frontAngle (KH H) (π / 2) t)) ≤ C0 + 1 := by
  apply WidthUniformProduced.exists_uniform_width_bound_of_pulse
    (Θ := fun H => frontAngle (KH H) (π / 2))
    (KH := KH) halpha hbeta hba hy hyp hy0 hyb hD hypb ha0 ha1
    hKstar hKint hK0 hKbd hThs hH1 hYa hKH
  · intro H hH t
    exact CurvatureInterpolation.hasDerivAt_tangentAngle
      (θ₀ := π / 2) (hKHcont H hH) t
  · intro H hH
    change π / 2 + (∫ r in (0 : ℝ)..(0 : ℝ), KH H r) = Ths 0
    simp [hThs0]
  · exact hmodel
  · intro H hH
    exact centered_frontAngle_mem_Ioo (lt_of_lt_of_le hH1 hH)
      (hKHcont H hH) (hKHper H hH) (hKHtotal H hH)
      (hKHpos H hH) (hhalf H hH)

/-- The all-real-period family attached directly to one fixed pulse.  All
periodization hypotheses of `exists_uniform_width_bound_of_strict_pulse` are
produced here.  The two remaining geometric inputs are displayed explicitly:
the isolated-width bound and exact half-cell normalization. -/
theorem exists_uniform_width_bound_of_periodized_pulse
    {y yp Kstar Ths : ℝ → ℝ}
    {C CK D a b b0 alpha beta C0 Hhalf : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hba : beta < alpha / 2)
    (hy : Continuous y) (hyp : Continuous yp)
    (hyderiv : ∀ s, HasDerivAt y (yp s) s)
    (hypos : ∀ s, 0 < y s)
    (hyb : ∀ s, y s ≤ C * exp (-alpha * |s|))
    (hyint : Integrable y) (hymass : (∫ s : ℝ, y s) = π)
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hbmin : b < a) (hsup : ∀ s, y s ≤ b)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * exp (-alpha * |s|))
    (hb00 : 0 < b0) (hlower : ∀ s, b0 * y s ≤ Kstar s)
    (hThs : ∀ t, HasDerivAt Ths (Kstar t) t)
    (hThs0 : Ths 0 = π / 2)
    (hHhalf : 0 < Hhalf)
    (hhalf : ∀ H, Hhalf ≤ H →
      (∫ r in (-(H / 2))..(0 : ℝ), modelCurvature y yp H r) = π / 2)
    (hmodel : ∀ H, 0 < H →
      (∫ t in (-(H / 2))..(H / 2), sin (Ths t)) ≤ C0) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H →
      0 < (∫ t in (-(H / 2))..(H / 2),
        sin (frontAngle (modelCurvature y yp H) (π / 2) t)) ∧
      (∫ t in (-(H / 2))..(H / 2),
        sin (frontAngle (modelCurvature y yp H) (π / 2) t)) ≤ C0 + 1 := by
  have hy0 : ∀ s, 0 ≤ y s := fun s => (hypos s).le
  have hC0 : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  obtain ⟨Hstrip, hHstrip0, hstrip⟩ :=
    PaperHairpinConfig.PeriodizedStripData.exists_threshold
      halpha (lt_trans hbmin ha1) hy0 hyb hsup
  obtain ⟨Hbudget, hHbudget0, hbudget⟩ :=
    PaperHairpinConfig.exists_simultaneous_strip_budget_threshold
      (a := a) (au := a) halpha (by simpa using hbmin)
  obtain ⟨Hpositive, hHpositive0, hpositive⟩ :=
    StrictConstructedModelGeometry.exists_largePeriod_strict_positivity_threshold
      halpha hb00 ha0 ha1 hD hC0
  let H1 := max Hhalf (max Hstrip (max Hbudget Hpositive))
  have hH1 : 0 < H1 := lt_of_lt_of_le hHhalf (le_max_left _ _)
  have hhalf_le : Hhalf ≤ H1 := le_max_left _ _
  have hstrip_le : Hstrip ≤ H1 :=
    le_max_of_le_right (le_max_left _ _)
  have hbudget_le : Hbudget ≤ H1 :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hpositive_le : Hpositive ≤ H1 :=
    le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  let KH : ℝ → ℝ → ℝ := fun H => modelCurvature y yp H
  have hYa : ∀ H, H1 ≤ H → ∀ u,
      (∑' m : ℤ, y (u - m * H)) ≤ a := by
    intro H hH u
    have hs := hstrip H (hstrip_le.trans hH)
    have habs := hs.periodized_abs_le
      (hbudget H (hbudget_le.trans hH)).1 u
    exact (le_abs_self _).trans (by
      simpa [periodizedPulse] using habs)
  have hyabs : ∀ s, |y s| ≤ max C (D * C) * exp (-alpha * |s|) := by
    intro s
    rw [abs_of_pos (hypos s)]
    exact (hyb s).trans (mul_le_mul_of_nonneg_right
      (le_max_left C (D * C)) (exp_pos _).le)
  have hypabs : ∀ s, |yp s| ≤ max C (D * C) * exp (-alpha * |s|) := by
    intro s
    calc
      |yp s| ≤ D * y s := hypb s
      _ ≤ D * (C * exp (-alpha * |s|)) :=
        mul_le_mul_of_nonneg_left (hyb s) hD
      _ = (D * C) * exp (-alpha * |s|) := by ring
      _ ≤ max C (D * C) * exp (-alpha * |s|) :=
        mul_le_mul_of_nonneg_right (le_max_right C (D * C)) (exp_pos _).le
  have hKHcont : ∀ H, H1 ≤ H → Continuous (KH H) := by
    intro H hH
    exact continuous_modelCurvature halpha (lt_of_lt_of_le hH1 hH)
      hy hyp hyabs hypabs hy0 ha0 ha1 (hYa H hH)
  have hKHper : ∀ H, H1 ≤ H → Periodic (KH H) H := by
    intro H hH
    exact periodic_modelCurvature y yp H
  have hKHtotal : ∀ H, H1 ≤ H →
      (∫ r in (0 : ℝ)..H, KH H r) = π := by
    intro H hH
    have hYaAbs : ∀ u, |∑' m : ℤ, y (u - m * H)| ≤ a := by
      intro u
      rw [abs_of_nonneg (tsum_nonneg fun m => hy0 _)]
      exact hYa H hH u
    exact integral_modelCurvature_eq_pi halpha (lt_of_lt_of_le hH1 hH)
      hy hyp hyderiv hyabs hypabs hy0 hyint ha0 ha1 hYaAbs hymass
  have hKHpos : ∀ H, H1 ≤ H → ∀ s, 0 < KH H s := by
    intro H hH s
    have hp := hpositive H (hpositive_le.trans hH)
    have hsumK : ∀ u, Summable fun m : ℤ =>
        hairpinCurvature y yp (u - m * H) := by
      intro u
      have hs := FrontPeriodizationIntegral.summable_translates
        halpha hp.1 hKbd u
      simpa only [hairpinCurvature, ← hKstar] using hs
    have hlower' : ∀ r, b0 * y r ≤ hairpinCurvature y yp r := by
      intro r
      simpa only [hairpinCurvature, ← hKstar] using hlower r
    exact StrictConstructedModelGeometry.modelCurvature_pos_of_large_period
      halpha hp.1 hp.2.1 hy0 hypos hyb hD hypb ha0 ha1
      (hYa H hH) hlower' hsumK hp.2.2 s
  apply exists_uniform_width_bound_of_strict_pulse
    (KH := KH) halpha hbeta hba hy hyp hy0 hyb hD hypb ha0 ha1
    hKstar hKint hK0 hKbd hThs hThs0 hH1 hYa
  · intro H hH t
    rfl
  · exact hKHcont
  · exact hKHper
  · exact hKHtotal
  · exact hKHpos
  · intro H hH
    exact hhalf H (hhalf_le.trans hH)
  · intro H hH
    exact hmodel H (lt_of_lt_of_le hH1 hH)

/-- A bounded exact half-mass center, together with the retained isolated
hairpin angle, supplies all hypotheses of the `H`-dependent-comparator width
theorem.  The isolated comparator is translated by the selected center and
normalized at the left endpoint of the cell.  Its width is eventually at most
`4 * Am + 1`; the final comparison contributes one further unit. -/
theorem exists_uniform_width_bound_of_bounded_center_pulse
    {f theta y yp Kstar : ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    {center : ℝ → ℝ}
    {m Am s0 R C CK D a alpha beta H1 : ℝ}
    (hf : ContinuousOn f (Ioo 0 π)) (hm : 0 < m) (hmA : m ≤ Am)
    (hlow : ∀ t ∈ Ioo (0 : ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) π, f t ≤ Am)
    (hmem : ∀ u, theta u ∈ Ioo (0 : ℝ) π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (htheta : ∀ u, HasDerivAt theta
      (HairpinRelative.curvField f (theta u)) u)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hba : beta < alpha / 2)
    (hy : Continuous y) (hyp : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hKangle : ∀ s, Kstar s = HairpinRelative.curvField f (theta (s + s0)))
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * exp (-alpha * |s|))
    (hR : 0 ≤ R) (hcenter : ∀ H, |center H| ≤ R)
    (hH1 : 0 < H1)
    (hhalfexp : ∀ H, H1 ≤ H → exp (-(beta * H)) ≤ 1 / 2)
    (hYa : ∀ H, H1 ≤ H → ∀ u,
      (∑' j : ℤ, y (u - j * H)) ≤ a)
    (hKH : ∀ H, H1 ≤ H → ∀ t,
      K H t = (∑' j : ℤ, y (t - j * H)) +
        G (∑' j : ℤ, y (t - j * H)) * (∑' j : ℤ, yp (t - j * H)))
    (hKcont : ∀ H, H1 ≤ H → Continuous (K H))
    (hKper : ∀ H, H1 ≤ H → Periodic (K H) H)
    (hKtotal : ∀ H, H1 ≤ H → (∫ r in (0 : ℝ)..H, K H r) = π)
    (hKpos : ∀ H, H1 ≤ H → ∀ s, 0 < K H s)
    (hhalf : ∀ H, H1 ≤ H →
      (∫ r in (center H - H / 2)..center H, K H r) = π / 2) :
    ∃ Hstar Cw : ℝ, 0 < Hstar ∧ Cw = 4 * Am + 2 ∧
      ∀ H, Hstar ≤ H →
        0 < (∫ t in (-(H / 2))..(H / 2),
          sin (frontAngle (fun s => K H (s + center H)) (π / 2) t)) ∧
        (∫ t in (-(H / 2))..(H / 2),
          sin (frontAngle (fun s => K H (s + center H)) (π / 2) t)) ≤ Cw := by
  let centerIso : ℝ → ℝ := fun H => center H + s0
  have hcenterIso : ∀ H, |centerIso H| ≤ R + |s0| := by
    intro H
    exact (abs_add_le _ _).trans (add_le_add (hcenter H) le_rfl)
  have hmodelEv := eventually_isolated_hairpin_normalized_width_le
    (f := f) (theta := theta) (center := centerIso)
    (m := m) (Am := Am) (R := R + |s0|)
    hf hm hmA hlow hupp hmem hval htheta hcenterIso
  obtain ⟨Bmodel, hBmodel⟩ := Filter.eventually_atTop.mp hmodelEv
  let H2 := max H1 Bmodel
  have hH2 : 0 < H2 := lt_of_lt_of_le hH1 (le_max_left _ _)
  have hH12 : H1 ≤ H2 := le_max_left _ _
  have hB2 : Bmodel ≤ H2 := le_max_right _ _
  let Ths : ℝ → ℝ := fun u => theta (u + s0)
  let ThetaS : ℝ → ℝ → ℝ := fun H t =>
    theta (t + centerIso H) - theta (centerIso H - H / 2)
  let E0 : ℝ :=
    lipConst a * D * (8 * (C * exp (alpha * R)) ^ 2 / (alpha - beta)) +
      2 * (CK * exp (alpha * R)) / alpha
  have hC0 : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hCK0 : 0 ≤ CK := by
    have h := hKbd 0
    simpa using (le_trans (abs_nonneg (Kstar 0)) h)
  have hab : 0 < alpha - beta := by linarith
  have hE0 : 0 ≤ E0 := by
    dsimp [E0]
    have hlip : 0 ≤ lipConst a := lipConst_nonneg ha0 ha1
    positivity
  have hthetac : Continuous theta :=
    continuous_iff_continuousAt.mpr fun u => (htheta u).continuousAt
  have hThsDeriv : ∀ u, HasDerivAt Ths (Kstar u) u := by
    intro u
    have hd := (htheta (u + s0)).comp u ((hasDerivAt_id u).add_const s0)
    rw [hKangle u]
    simpa [Ths] using hd
  have hThetaS : ∀ H, H2 ≤ H → Continuous (ThetaS H) := by
    intro H _
    exact (hthetac.comp (continuous_id.add continuous_const)).sub continuous_const
  have hmodel : ∀ H, H2 ≤ H →
      (∫ t in (-(H / 2))..(H / 2), sin (ThetaS H t)) ≤ 4 * Am + 1 := by
    intro H hH
    have hmH := hBmodel H (hB2.trans hH)
    simpa [ThetaS, centerIso, add_assoc] using hmH
  have hclose : ∀ H, H2 ≤ H → ∀ t ∈ uIoc (-(H / 2)) (H / 2),
      |frontAngle (fun s => K H (s + center H)) (π / 2) t - ThetaS H t| ≤
        (2 * E0) * exp (-beta * H) := by
    intro H hH t ht
    have hH1' : H1 ≤ H := hH12.trans hH
    have hHp : 0 < H := lt_of_lt_of_le hH2 hH
    have htIcc : t ∈ Icc (-(H / 2)) (H / 2) := by
      rw [uIoc_of_le (by linarith : -(H / 2) ≤ H / 2)] at ht
      exact ⟨ht.1.le, ht.2⟩
    let ThH : ℝ → ℝ := fun u =>
      frontAngle (fun s => K H (s + center H)) (π / 2) (u - center H)
    have hThHDeriv : ∀ u, HasDerivAt ThH (K H u) u := by
      intro u
      have hkshift : Continuous (fun s : ℝ => K H (s + center H)) :=
        (hKcont H hH1').comp (continuous_id.add continuous_const)
      have hd := CurvatureInterpolation.hasDerivAt_tangentAngle
        (θ₀ := π / 2) hkshift (u - center H)
      have hc := hd.comp u ((hasDerivAt_id u).sub_const (center H))
      convert hc using 1 <;> simp [ThH] <;> ring
    have hraw : ∀ s ∈ Icc (-(H / 2)) (H / 2),
        |(ThH (s + center H) - ThH (center H)) -
          (Ths (s + center H) - Ths (center H))| ≤
            E0 * exp (-beta * H) := by
      intro s hs
      simpa [E0] using angle_sup_close_of_bounded_shift
        (y := y) (yp := yp) (Kstar := Kstar) (KH := K H)
        (ThH := ThH) (Ths := Ths) (C := C) (CK := CK) (D := D)
        (a := a) (alpha := alpha) (beta := beta) (H := H)
        (q := center H) (R := R)
        halpha hHp hbeta hba (hhalfexp H hH1') hR (hcenter H)
        hy hyp hy0 hyb hD hypb ha0 ha1 (hYa H hH1') hKstar
        (hKH H hH1') hKint hK0 hKbd hThHDeriv hThsDeriv hs
    have hhalfshift :
        (∫ r in (-(H / 2))..(0 : ℝ), K H (r + center H)) = π / 2 := by
      rw [intervalIntegral.integral_comp_add_right]
      convert hhalf H hH1' using 1 <;> ring
    have hleft :
        frontAngle (fun s => K H (s + center H)) (π / 2) (-(H / 2)) = 0 := by
      change π / 2 +
        (∫ r in (0 : ℝ)..(-(H / 2)), K H (r + center H)) = 0
      rw [intervalIntegral.integral_symm]
      linarith
    have hrawT :
        |(frontAngle (fun s => K H (s + center H)) (π / 2) t - π / 2) -
          (theta (t + center H + s0) - theta (center H + s0))| ≤
            E0 * exp (-beta * H) := by
      convert hraw t htIcc using 1 <;> simp [ThH, Ths, frontAngle] <;> ring
    have hrawL :
        |(-π / 2) -
          (theta (center H - H / 2 + s0) - theta (center H + s0))| ≤
            E0 * exp (-beta * H) := by
      have hh := hraw (-(H / 2)) ⟨le_rfl, by linarith⟩
      have hThHleft : ThH (-(H / 2) + center H) = 0 := by
        dsimp [ThH]
        convert hleft using 1 <;> ring
      have hThHcenter : ThH (center H) = π / 2 := by
        simp [ThH, frontAngle]
      rw [hThHleft, hThHcenter] at hh
      convert hh using 1 <;> simp [Ths] <;> ring
    have htri := abs_sub_le
      ((frontAngle (fun s => K H (s + center H)) (π / 2) t - π / 2) -
        (theta (t + center H + s0) - theta (center H + s0)))
      0
      ((-π / 2) -
        (theta (center H - H / 2 + s0) - theta (center H + s0)))
    simp only [sub_zero, zero_sub, abs_neg] at htri
    have hrewrite :
        frontAngle (fun s => K H (s + center H)) (π / 2) t - ThetaS H t =
          ((frontAngle (fun s => K H (s + center H)) (π / 2) t - π / 2) -
            (theta (t + center H + s0) - theta (center H + s0))) -
          ((-π / 2) -
            (theta (center H - H / 2 + s0) - theta (center H + s0))) := by
      dsimp [ThetaS, centerIso]
      rw [show t + (center H + s0) = t + center H + s0 by ring,
        show center H + s0 - H / 2 = center H - H / 2 + s0 by ring]
      ring
    rw [hrewrite]
    exact htri.trans (by linarith [hrawT, hrawL])
  obtain ⟨Hstar, hHstar, hwidth⟩ :=
    exists_uniform_width_bound_of_selected_centers
      (K := K) (center := center) (ThetaS := ThetaS)
      (C0 := 4 * Am + 1) (C := 2 * E0) (beta := beta) (H1 := H2)
      hbeta (mul_nonneg (by norm_num) hE0) hH2
      (fun H hH => hKcont H (hH12.trans hH))
      (fun H hH => hKper H (hH12.trans hH))
      (fun H hH => hKtotal H (hH12.trans hH))
      (fun H hH => hKpos H (hH12.trans hH))
      (fun H hH => hhalf H (hH12.trans hH))
      hThetaS hmodel hclose
  refine ⟨Hstar, 4 * Am + 2, hHstar, rfl, ?_⟩
  intro H hH
  obtain ⟨hpos, hle⟩ := hwidth H hH
  exact ⟨hpos, by linarith⟩

/-- The fixed-bracket construction closes the last phase-selection input of
`exists_uniform_width_bound_of_bounded_center_pulse`.  The bracket radius and
the large-period threshold are obtained from the isolated exponential tail
and the `L¹` periodization estimate. -/
theorem exists_uniform_width_bound_of_fixed_bracket_pulse
    {f theta y yp Kstar : ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    {m Am s0 C CK D a alpha beta H1 : ℝ}
    (hf : ContinuousOn f (Ioo 0 π)) (hm : 0 < m) (hmA : m ≤ Am)
    (hlow : ∀ t ∈ Ioo (0 : ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) π, f t ≤ Am)
    (hmem : ∀ u, theta u ∈ Ioo (0 : ℝ) π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (htheta : ∀ u, HasDerivAt theta
      (HairpinRelative.curvField f (theta u)) u)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hba : beta < alpha / 2)
    (hy : Continuous y) (hyp : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hKangle : ∀ s, Kstar s = HairpinRelative.curvField f (theta (s + s0)))
    (hKstarCont : Continuous Kstar)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKtotalStar : (∫ u : ℝ, Kstar u) = π)
    (hKbd : ∀ s, |Kstar s| ≤ CK * exp (-alpha * |s|))
    (hH1 : 0 < H1)
    (hhalfexp : ∀ H, H1 ≤ H → exp (-(beta * H)) ≤ 1 / 2)
    (hYa : ∀ H, H1 ≤ H → ∀ u,
      (∑' j : ℤ, y (u - j * H)) ≤ a)
    (hKH : ∀ H, H1 ≤ H → ∀ t,
      K H t = (∑' j : ℤ, y (t - j * H)) +
        G (∑' j : ℤ, y (t - j * H)) * (∑' j : ℤ, yp (t - j * H)))
    (hKcont : ∀ H, H1 ≤ H → Continuous (K H))
    (hKper : ∀ H, H1 ≤ H → Periodic (K H) H)
    (hKtotal : ∀ H, H1 ≤ H → (∫ r in (0 : ℝ)..H, K H r) = π)
    (hKpos : ∀ H, H1 ≤ H → ∀ s, 0 < K H s) :
    ∃ center : ℝ → ℝ, ∃ Hstar Cw : ℝ,
      0 < Hstar ∧ Cw = 4 * Am + 2 ∧
      (∀ H, Hstar ≤ H →
        (∫ r in (center H - H / 2)..center H, K H r) = π / 2) ∧
      ∀ H, Hstar ≤ H →
        0 < (∫ t in (-(H / 2))..(H / 2),
          sin (frontAngle (fun s => K H (s + center H)) (π / 2) t)) ∧
        (∫ t in (-(H / 2))..(H / 2),
          sin (frontAngle (fun s => K H (s + center H)) (π / 2) t)) ≤ Cw := by
  let EL1 : ℝ :=
    lipConst a * D * (8 * C ^ 2 / (alpha - beta)) + 2 * CK / alpha
  obtain ⟨R, hR, hRtail⟩ := exists_fixed_tail_radius (CK := CK) halpha
  have htailEv := eventually_fixed_bracket_tail_error
    (E0 := EL1) halpha hbeta hRtail
  obtain ⟨Btail, hBtail⟩ := Filter.eventually_atTop.mp htailEv
  let H2 := max H1 Btail
  have hH2 : 0 < H2 := lt_of_lt_of_le hH1 (le_max_left _ _)
  have hH12 : H1 ≤ H2 := le_max_left _ _
  have hBt2 : Btail ≤ H2 := le_max_right _ _
  have hsigns : ∀ H, H2 ≤ H →
      (∫ r in (-R - H / 2)..(-R), K H r) ≤ π / 2 ∧
      π / 2 ≤ (∫ r in (R - H / 2)..R, K H r) := by
    intro H hH
    have hH1' : H1 ≤ H := hH12.trans hH
    have hHp : 0 < H := lt_of_lt_of_le hH2 hH
    have htail := hBtail H (hBt2.trans hH)
    have hL1 := AngleClose.curvature_L1_close
      (y := y) (yp := yp) (Kstar := Kstar) (KH := K H)
      (C := C) (CK := CK) (D := D) (a := a)
      halpha hHp hbeta hba (hhalfexp H hH1')
      hy hyp hy0 hyb hD hypb ha0 ha1 (hYa H hH1')
      hKstar (hKH H hH1') hKint hK0 hKbd
    apply fixed_bracket_half_mass_inequalities
      (KH := K H) (Kstar := Kstar) (H := H) (R := R)
      (E := EL1 * exp (-beta * H)) (CK := CK) (alpha := alpha)
      halpha hHp hR.le htail.1 (hKcont H hH1') hKstarCont
      (hKper H hH1') (hKtotal H hH1') hKint hKtotalStar hKbd
    · simpa [EL1] using hL1
    · exact htail.2
  obtain ⟨c, hc⟩ := exists_uniformly_bounded_half_mass_centers
    (K := K) (H0 := H2) (L := -R) (R := R) (by linarith)
    (fun H hH => hKcont H (hH12.trans hH))
    (fun H hH => (hsigns H hH).1)
    (fun H hH => (hsigns H hH).2)
  let center : ℝ → ℝ := fun H => if H2 ≤ H then c H else 0
  have hcenter : ∀ H, |center H| ≤ R := by
    intro H
    by_cases hH : H2 ≤ H
    · have hb := (hc H hH).2.1
      simp only [abs_neg] at hb
      rw [abs_of_pos hR] at hb
      simpa [center, hH, max_self] using hb
    · simp [center, hH, hR.le]
  have hhalf : ∀ H, H2 ≤ H →
      (∫ r in (center H - H / 2)..center H, K H r) = π / 2 := by
    intro H hH
    simpa [center, hH] using (hc H hH).2.2
  obtain ⟨Hstar, Cw, hHs, hCw, hwidth⟩ :=
    exists_uniform_width_bound_of_bounded_center_pulse
      (f := f) (theta := theta) (y := y) (yp := yp) (Kstar := Kstar)
      (K := K) (center := center) (m := m) (Am := Am) (s0 := s0)
      (R := R) (C := C) (CK := CK) (D := D) (a := a)
      (alpha := alpha) (beta := beta) (H1 := H2)
      hf hm hmA hlow hupp hmem hval htheta halpha hbeta hba hy hyp hy0 hyb
      hD hypb ha0 ha1 hKstar hKangle hKint hK0 hKbd hR.le hcenter hH2
      (fun H hH => hhalfexp H (hH12.trans hH))
      (fun H hH => hYa H (hH12.trans hH))
      (fun H hH => hKH H (hH12.trans hH))
      (fun H hH => hKcont H (hH12.trans hH))
      (fun H hH => hKper H (hH12.trans hH))
      (fun H hH => hKtotal H (hH12.trans hH))
      (fun H hH => hKpos H (hH12.trans hH)) hhalf
  let Hfinal := max Hstar H2
  have hHfinal : 0 < Hfinal := lt_of_lt_of_le hHs (le_max_left _ _)
  refine ⟨center, Hfinal, Cw, hHfinal, hCw, ?_, ?_⟩
  · intro H hH
    exact hhalf H ((le_max_right _ _).trans hH)
  · intro H hH
    exact hwidth H ((le_max_left _ _).trans hH)

/-- Epsilon-level paper façade: the same interior profile produces a strict
configured sequence and, from its canonically shifted prior pulse, an all-real
period family with an exact bounded phase center and a uniform width bound. -/
theorem exists_strict_sequence_and_uniform_width_of_eps
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ (y yp : ℝ → ℝ) (center : ℝ → ℝ)
      (Dseq : ConstructedConfiguredSequenceWeighted.Data)
      (direction : ℕ → ℂ) (Am Hstar Cw : ℝ),
      0 < Am ∧ 0 < Hstar ∧ Cw = 4 * Am + 2 ∧
      (∀ n, Dseq.kappas n = modelCurvature y yp (Dseq.Hs n)) ∧
      (∀ n, direction n = centeredDirection (Dseq.kappas n)
        Dseq.model.thetaBase (center (Dseq.Hs n))) ∧
      (∀ n, ‖direction n‖ = 1) ∧
      (∀ n, Width.width
        (range (front (Dseq.kappas n) Dseq.model.thetaBase (Dseq.Hs n)))
        (direction n) ≤ Cw) ∧
      (∀ H, Hstar ≤ H →
        (∫ r in (center H - H / 2)..center H,
          modelCurvature y yp H r) = π / 2) ∧
      (∀ H, Hstar ≤ H →
        0 < (∫ t in (-(H / 2))..(H / 2),
          sin (frontAngle
            (fun s => modelCurvature y yp H (s + center H)) (π / 2) t)) ∧
        (∫ t in (-(H / 2))..(H / 2),
          sin (frontAngle
            (fun s => modelCurvature y yp H (s + center H)) (π / 2) t)) ≤ Cw) ∧
      Dseq.model.a ≤ 1 / 2 ∧
      (∀ n s, Dseq.kappas n s ≤ 1 / 2) ∧
      (∀ n s, (Dseq.model.configs n).kH s ≤ 1 / 2) ∧
      (∀ n, ContDiff ℝ 3
        (modelCurvature (Dseq.model.configs n).yu
          (Dseq.model.configs n).yu' (Dseq.Hs n))) ∧
      ∀ n, ContDiff ℝ 3 (Dseq.model.configs n).kH := by
  obtain ⟨f, g, gp, theta, x, m, Am, hbar, hm, hmA, hlow, hupp, hfinf, hsm,
    hsurj, hdecay, d⟩ := exists_interiorPhaseData_of_eps heps heps10
  have hfpos : ∀ t ∈ Ioo (0 : ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hAm : 0 < Am := lt_of_lt_of_le hm hmA
  have hA : 0 ≤ 2 / m := by positivity
  obtain ⟨relativeConst, hrc0, hrel⟩ :=
    hrelj_of_interior d hm hmA hfinf hlow hupp hdecay hAm hsurj
  obtain ⟨yp0, alpha, C, D, b, halpha, hC, hD, hb0, hb1,
    hcurv0, hcurvint, hcurvbd, -, -, -, -, -, hyc0, hy0c, hybc, hsupc,
    hyderiv0, hypc0, hypbc, hyprelc⟩ :=
    FrontPeriodizationHairpin.exists_hairpin_pulse_data_of_interior
      hfinf hm hlow d.angle_mem d.angle_value d.angle_deriv d.inverse_value
      d.state_deriv hsm hsurj hA hAm hdecay relativeConst hrc0 hrel
  have htrans : PaperHairpinQuantitativeData.TranslatorData f g gp :=
    { angle_shift := d.shift
      maps_angle := d.image_mem
      profile_deriv_identity := d.translator_identity
      angle_deriv := d.translator_deriv }
  let c : PaperHairpinQuantitativeData.ConsecutiveData f theta x g gp yp0 Am 0 0 0 0
      (fun _ => 0) (fun _ => 0) :=
    { quantitative := data_of_interior hfinf hm hlow d.angle_mem d.angle_value
        d.angle_deriv d.inverse_value d.state_deriv hsm hsurj hA hAm hdecay
        relativeConst hrc0 hrel
      translator := htrans
      pulse_deriv := hyderiv0 }
  obtain ⟨-, -, hyC⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hfinf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have hYd : ∀ s, HasDerivAt
      (fun r => HairpinRelative.pulseField f (theta (x r)))
      (iteratedDeriv 1
        (fun r => HairpinRelative.pulseField f (theta (x r))) s) s := fun s => by
    have h := hasDerivAt_iteratedDeriv (hyC 2) (show 0 < 2 by norm_num) s
    rwa [iteratedDeriv_zero] at h
  obtain ⟨Dp, hDp, h1⟩ :=
    rel_pulse_one_of_interior' d hm hmA hfinf hlow hupp hdecay hAm hYd
  have hdb : ∀ t ∈ Ioo (0 : ℝ) π,
      |deriv (HairpinRelative.pulseField f) t| ≤ Dp := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hfinf hfpos d.angle_mem d.angle_deriv
      d.inverse_value hsurj d.state_deriv h1 t ht
    rwa [HairpinRelative.coeff_one] at h
  let bbar : ℝ := 1 / sqrt (1 + m ^ 2)
  have hbbar0 : 0 ≤ bbar := by dsimp [bbar]; positivity
  have hbbar1 : bbar < 1 := by
    dsimp [bbar]
    exact HairpinRelative.one_div_sqrt_one_add_sq_lt_one hm
  have hpulseBarrier : ∀ t ∈ Ioo (0 : ℝ) π,
      |HairpinRelative.pulseField f t| ≤ bbar := by
    intro t ht
    rw [abs_of_nonneg (HairpinRelative.pulseField_nonneg_interior hfpos ht)]
    exact HairpinRelative.pulseField_le_of_barrier hm (hlow t ht) ht
  have hrelK := HairpinRelative.relK_of_pulse_deriv_bound
    hfinf hfpos hbbar0 hbbar1 hpulseBarrier hdb d.angle_mem d.angle_deriv
  let D1 : ℝ := Dp / sqrt (1 - bbar ^ 2) ^ 3
  have hD1 : 0 ≤ D1 := by dsimp [D1]; positivity
  obtain ⟨bpos, hbpos, hlower⟩ :=
    c.exists_previous_lower_comparison_interior d hfinf hfpos hAm hD1 hdecay
      hrelK hm hmA (fun t => hlow _ (d.angle_mem t))
      (fun t => hupp _ (d.angle_mem t))
  let q := ConsecutiveData.phase f theta g
  let y : ℝ → ℝ := ConsecutiveData.previousPulse f theta x g
  let yp : ℝ → ℝ := ConsecutiveData.previousPulseDeriv f theta g yp0
  let Kstar : ℝ → ℝ := fun s => HairpinRelative.curvField f (theta s)
  let CU : ℝ := C * exp (alpha * |q|)
  let a : ℝ := (b + 1) / 2
  let beta : ℝ := alpha / 4
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hba : beta < alpha / 2 := by dsimp [beta]; linarith
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hbaStrip : b < a := by dsimp [a]; linarith
  let aa : ℝ := 2 * eps
  have haa0 : (0 : ℝ) ≤ aa := by dsimp [aa]; positivity
  have haa1 : aa < 1 := by dsimp [aa]; linarith
  have hbbarAA : bbar < aa := by
    have hsqrt : m < Real.sqrt (1 + m ^ 2) := by
      rw [lt_sqrt (by positivity)]
      nlinarith
    have hprod : 1 < 2 * eps * m := by
      have hmprod := mul_le_mul_of_nonneg_left hbar
        (by positivity : 0 ≤ 2 * eps)
      have hinv : eps * eps⁻¹ = 1 := by field_simp
      nlinarith [sq_nonneg eps]
    have hprod' : 1 < 2 * eps * Real.sqrt (1 + m ^ 2) := by
      have := mul_lt_mul_of_pos_left hsqrt (by positivity : 0 < 2 * eps)
      linarith
    dsimp [bbar, aa]
    rw [div_lt_iff₀ (HairpinRelative.sqrt_one_add_sq_pos m)]
    simpa [mul_comm] using hprod'
  have hyc : Continuous y := by
    simpa [y, ConsecutiveData.previousPulse, q] using
      hyc0.comp (continuous_id.sub continuous_const)
  have hypc : Continuous yp := by
    simpa [yp, ConsecutiveData.previousPulseDeriv, q] using
      hypc0.comp (continuous_id.sub continuous_const)
  have hy0 : ∀ s, 0 ≤ y s := by
    intro s
    simpa [y, ConsecutiveData.previousPulse, q] using hy0c (s - q)
  have hypos : ∀ s, 0 < y s := by
    intro s
    exact StrictConstructedModelGeometry.pulseField_pos_interior hfpos
      (d.angle_mem (x (s - q)))
  have hyb : ∀ s, y s ≤ CU * exp (-alpha * |s|) := by
    intro s
    have h := hybc (s - q)
    have habs : -|s - q| ≤ -|s| + |q| := by
      have ht := abs_add_le (s - q) q
      rw [sub_add_cancel] at ht
      linarith
    have he := exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs halpha.le)
    calc
      y s ≤ C * exp (-alpha * |s - q|) := by
        simpa [y, ConsecutiveData.previousPulse, q] using h
      _ ≤ C * exp (alpha * |q| - alpha * |s|) := by
        gcongr
        nlinarith
      _ = CU * exp (-alpha * |s|) := by
        dsimp [CU]
        rw [show alpha * |q| - alpha * |s| =
          alpha * |q| + (-alpha * |s|) by ring, exp_add]
        ring
  have hypb : ∀ s, |yp s| ≤ D * y s := by
    intro s
    simpa [y, yp, ConsecutiveData.previousPulse,
      ConsecutiveData.previousPulseDeriv, q] using hyprelc (s - q)
  have hsup : ∀ s, y s ≤ b := by
    intro s
    simpa [y, ConsecutiveData.previousPulse, q] using hsupc (s - q)
  have hyderiv : ∀ s, HasDerivAt y (yp s) s := by
    intro s
    simpa [y, yp, ConsecutiveData.previousPulse,
      ConsecutiveData.previousPulseDeriv, q] using
      (hyderiv0 (s - q)).comp s ((hasDerivAt_id s).sub_const q)
  have hKstar : ∀ s, Kstar s = y s + G (y s) * yp s := by
    intro s
    simpa [Kstar, y, yp, ConsecutiveData.previousPulse,
      ConsecutiveData.previousPulseDeriv, q, hairpinCurvature] using
      (CanonicalTranslatorLocalPhase.front_curvature_identity_shifted
        d d.x_zero c.pulse_deriv s)
  have hKangle : ∀ s, Kstar s =
      HairpinRelative.curvField f (theta (s + 0)) := by simp [Kstar]
  have hcurvc : Continuous Kstar := by
    exact (HairpinRelative.continuous_curv_along_theta
      hfinf hfpos d.angle_mem d.angle_deriv).congr
      (fun s => rfl)
  have hK0 : ∀ s, 0 ≤ Kstar s := by intro s; exact hcurv0 s
  have hKint : Integrable Kstar := by simpa [Kstar] using hcurvint
  have hKtotal : (∫ s : ℝ, Kstar s) = π := by
    simpa [Kstar] using HairpinMassInterior.integral_curv_eq_pi_of_comp
      (HairpinRelative.continuous_curv_along_theta
        hfinf hfpos d.angle_mem d.angle_deriv)
      hcurv0 d.angle_mem hsm hsurj d.angle_deriv hdecay hAm
  have hKbd : ∀ s, |Kstar s| ≤ C * exp (-alpha * |s|) := by
    intro s
    simpa [Kstar] using hcurvbd s
  have hKiso : ∀ s, Kstar s ≤ 2 * eps := by
    intro s
    have hgap0 : 0 < eps⁻¹ - eps :=
      lt_trans zero_lt_one (BarrierEstimates.m_gt_one heps heps10)
    have hft : eps⁻¹ - eps ≤ f (theta s) :=
      hbar.trans (hlow _ (d.angle_mem s))
    have hfp : 0 < f (theta s) := lt_of_lt_of_le hgap0 hft
    calc
      Kstar s = Real.sin (theta s) / f (theta s) := rfl
      _ ≤ 1 / f (theta s) :=
        div_le_div_of_nonneg_right (Real.sin_le_one _) hfp.le
      _ ≤ 1 / (eps⁻¹ - eps) := one_div_le_one_div_of_le hgap0 hft
      _ ≤ 2 * eps := WideHairpinSmallness.inv_gap_le_two_mul heps heps10
  obtain ⟨Hstrip, hHstrip, hstrip⟩ :=
    PaperHairpinConfig.PeriodizedStripData.exists_threshold
      halpha hb1 hy0 hyb hsup
  obtain ⟨Hpos, hHpos, hposThreshold⟩ :=
    StrictConstructedModelGeometry.exists_largePeriod_strict_positivity_threshold
      halpha hbpos ha0 ha1 hD (by positivity : 0 ≤ CU)
  obtain ⟨Hbudget, hHbudget, hbudget⟩ :=
    PaperHairpinConfig.exists_simultaneous_strip_budget_threshold
      (a := a) (au := a) halpha (by simpa using hbaStrip)
  have hsupActual : ∀ s, y s ≤ bbar := by
    intro s
    exact HairpinRelative.pulseField_le_of_barrier hm
      (hlow _ (d.angle_mem (x (s - q)))) (d.angle_mem (x (s - q)))
  obtain ⟨HstripActual, -, hstripActual⟩ :=
    PaperHairpinConfig.PeriodizedStripData.exists_threshold
      halpha hbbar1 hy0 hyb hsupActual
  obtain ⟨HbudgetActual, -, hbudgetActual⟩ :=
    PaperHairpinConfig.exists_simultaneous_strip_budget_threshold
      (a := aa) (au := aa) halpha (by simpa using hbbarAA)
  let HactualStrip := max HstripActual HbudgetActual
  have hYaActual : ∀ H, HactualStrip ≤ H → ∀ u,
      (∑' j : ℤ, y (u - j * H)) ≤ aa := by
    intro H hH u
    have hs := hstripActual H ((le_max_left _ _).trans hH)
    exact (le_abs_self _).trans (by
      simpa [periodizedPulse] using hs.periodized_abs_le
        (hbudgetActual H ((le_max_right _ _).trans hH)).1 u)
  obtain ⟨Hfront, -, hfront⟩ :=
    ActualFrontCurvatureLargePeriod.exists_threshold_modelCurvature_le
      (y := y) (yp := yp) (Kstar := Kstar) (C := CU) (CK := C)
      (alpha := alpha) (a := aa) (D := D)
      (kiso := 2 * eps) (kh := 1 / 2) (Hstrip := HactualStrip)
      halpha hy0 hyb hD hypb haa0 haa1 hYaActual hKstar hK0
      (fun s => (le_abs_self _).trans (hKbd s)) hKiso (by linarith)
  have hhalfEv := FrontPeriodizationPositivity.eventually_const_mul_exp_neg_le
    (A := (1 : ℝ)) (c := beta) (b := 1 / 2) hbeta (by norm_num)
  obtain ⟨Hhalf, hHhalf⟩ := Filter.eventually_atTop.mp hhalfEv
  let H1 := max 1 (max Hstrip (max Hbudget (max Hpos Hhalf)))
  have hH1 : 0 < H1 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsle : Hstrip ≤ H1 := le_max_of_le_right (le_max_left _ _)
  have hble : Hbudget ≤ H1 :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hple : Hpos ≤ H1 :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))
  have hhle : Hhalf ≤ H1 :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _)))
  let K : ℝ → ℝ → ℝ := fun H => modelCurvature y yp H
  have hYa : ∀ H, H1 ≤ H → ∀ u,
      (∑' j : ℤ, y (u - j * H)) ≤ a := by
    intro H hH u
    have hs := hstrip H (hsle.trans hH)
    exact (le_abs_self _).trans (by
      simpa [periodizedPulse] using hs.periodized_abs_le
        (hbudget H (hble.trans hH)).1 u)
  have hyabs : ∀ s, |y s| ≤ max CU (D * CU) * exp (-alpha * |s|) := by
    intro s
    rw [abs_of_pos (hypos s)]
    exact (hyb s).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (exp_pos _).le)
  have hypabs : ∀ s, |yp s| ≤ max CU (D * CU) * exp (-alpha * |s|) := by
    intro s
    calc
      |yp s| ≤ D * y s := hypb s
      _ ≤ D * (CU * exp (-alpha * |s|)) :=
        mul_le_mul_of_nonneg_left (hyb s) hD
      _ ≤ max CU (D * CU) * exp (-alpha * |s|) := by
        have := mul_le_mul_of_nonneg_right (le_max_right CU (D * CU))
          (exp_pos (-alpha * |s|)).le
        nlinarith
  have hKcont : ∀ H, H1 ≤ H → Continuous (K H) := by
    intro H hH
    exact continuous_modelCurvature halpha (lt_of_lt_of_le hH1 hH)
      hyc hypc hyabs hypabs hy0 ha0 ha1 (hYa H hH)
  have hKper : ∀ H, H1 ≤ H → Periodic (K H) H := fun H _ =>
    periodic_modelCurvature y yp H
  have hmass := c.previousPulse_massData
  have hKperiod : ∀ H, H1 ≤ H →
      (∫ r in (0 : ℝ)..H, K H r) = π := by
    intro H hH
    have hYaAbs : ∀ u, |∑' j : ℤ, y (u - j * H)| ≤ a := by
      intro u
      rw [abs_of_nonneg (tsum_nonneg fun _ => hy0 _)]
      exact hYa H hH u
    exact integral_modelCurvature_eq_pi halpha (lt_of_lt_of_le hH1 hH)
      hyc hypc hyderiv hyabs hypabs hy0 hmass.integrable ha0 ha1 hYaAbs
      hmass.mass_eq_pi
  have hKpos : ∀ H, H1 ≤ H → ∀ s, 0 < K H s := by
    intro H hH s
    have hp := hposThreshold H (hple.trans hH)
    have hsumK : ∀ u, Summable fun j : ℤ => hairpinCurvature y yp (u - j * H) := by
      intro u
      have hs := FrontPeriodizationIntegral.summable_translates
        halpha hp.1 hKbd u
      simpa only [hairpinCurvature, hKstar] using hs
    exact StrictConstructedModelGeometry.modelCurvature_pos_of_large_period
      halpha hp.1 hp.2.1 hy0 hypos hyb hD hypb ha0 ha1 (hYa H hH)
      hlower hsumK hp.2.2 s
  have hhalfexp : ∀ H, H1 ≤ H → exp (-(beta * H)) ≤ 1 / 2 := by
    intro H hH
    have hh := hHhalf H (hhle.trans hH)
    simpa using hh
  obtain ⟨center, Hw, Cw, hHw, hCw, hhalf, hwidth⟩ :=
    exists_uniform_width_bound_of_fixed_bracket_pulse
      (f := f) (theta := theta) (y := y) (yp := yp) (Kstar := Kstar)
      (K := K) (m := m) (Am := Am) (s0 := 0) (C := CU) (CK := C)
      (D := D) (a := a) (alpha := alpha) (beta := beta) (H1 := H1)
      hfinf.continuousOn hm hmA hlow hupp d.angle_mem d.angle_value
      d.angle_deriv halpha hbeta hba hyc hypc hy0 hyb hD hypb ha0 ha1
      hKstar hKangle hcurvc hKint hK0 hKtotal hKbd hH1 hhalfexp hYa
      (fun _ _ _ => rfl) hKcont hKper hKperiod hKpos
  obtain ⟨CK, Km, Kd, kstar, kd, profile⟩ :=
    PaperHairpinConfig.exists_profileConstants
      (alpha := alpha) (beta := alpha / 4) (a := aa) (au := aa)
      (CU := CU) (DU := relativeConst 1) (DU2 := relativeConst 2)
      (D := relativeConst 1) (by positivity) (by linarith)
      (hrc0 1) (hrc0 1) (hrc0 2) haa0 haa1 haa0 haa1
  have hdec0current : ∀ s,
      |ConsecutiveData.currentPulse f theta x s| ≤ C * exp (-alpha * |s|) := by
    intro s
    rw [abs_of_nonneg]
    · simpa [ConsecutiveData.currentPulse] using hybc s
    · simpa [ConsecutiveData.currentPulse] using hy0c s
  have hdec1current : ∀ s, |yp0 s| ≤ C * exp (-alpha * |s|) := hypbc
  let cst : ℝ := matchConst aa C CK CU (relativeConst 1)
    Km Kd aa alpha (alpha / 4) ((1 + bbar) / 2 * π)
  have hcst : 0 ≤ cst := by
    dsimp [cst]
    exact PaperHairpinConfig.matchConst_nonneg profile halpha hC (by positivity)
  let Hcombined := max Hw Hfront
  obtain ⟨Hs, kappas, deltaStep, hdelta, hHcombined0, hlinear, hstep, -, -,
    ⟨model, hmodelkd, hmodelkstar, hmodelKP, hmodelkH, hmodelCurrent,
      hmodela, -⟩,
    hkpos, hkappa, -⟩ :=
    StrictConstructedModelGeometry.exists_strict_configuredModelSequence_above
      (theta0 := 0) Hcombined c d hfinf hfpos hAm hD1 hdecay hrelK hm hmA
      (fun t => hlow _ (d.angle_mem t)) (fun t => hupp _ (d.angle_mem t))
      profile one_pos halpha hdec0current hdec1current (by simp [CU, q])
      (le_refl _) (le_refl _) (le_refl _) hbbar0
      (by simpa using hbbarAA)
      (by
        intro s
        simpa [ConsecutiveData.currentPulse, bbar, one_div] using
          (HairpinRelative.pulseField_le_of_barrier hm
            (hlow _ (d.angle_mem (x s))) (d.angle_mem (x s))))
      (le_refl _) profile.rear_derivative_pos.le hcst
  have hkappa' : ∀ n, kappas n = modelCurvature y yp (Hs n) := by
    intro n
    simpa [y, yp] using hkappa n
  let betaWeight : ℝ := alpha / 8
  have hbetaWeight : 0 < betaWeight := by dsimp [betaWeight]; positivity
  let Dseq : ConstructedConfiguredSequenceWeighted.Data :=
    { kappas := kappas
      Hs := Hs
      deltaStep := deltaStep
      kd := kd
      kstar := kstar
      matchCoefficient := cst
      beta := betaWeight
      deltaStep_pos := hdelta
      beta_pos := hbetaWeight
      matchCoefficient_nonneg := hcst
      kd_nonneg := profile.rear_derivative_pos.le
      kstar_nonneg := le_trans
        (div_nonneg haa0 (Real.sqrt_nonneg _)) profile.current_rear_sup
      separation_zero_pos := model.separation_pos 0
      separation_lower := model.separation_mono
      separation_linear := hlinear
      separation_step := hstep
      model := model
      model_kd := hmodelkd
      model_kstar := hmodelkstar
      model_KP_C2 := fun n => (hmodelKP n).of_le (by norm_num)
      model_kH_C2 := fun n => (hmodelkH n).of_le (by norm_num)
      phase := ConsecutiveData.phase f theta g
      model_current_curvature_eq_next_shift := by
        intro n s
        simpa [y, yp] using hmodelCurrent n s
      model_curvature_pos := hkpos }
  let direction : ℕ → ℂ := fun n =>
    centeredDirection (Dseq.kappas n) Dseq.model.thetaBase (center (Dseq.Hs n))
  have hdir : ∀ n, ‖direction n‖ = 1 := by
    intro n
    exact centeredDirection_norm _ _ _
  have hgeomWidth : ∀ n, Width.width
      (range (front (Dseq.kappas n) Dseq.model.thetaBase (Dseq.Hs n)))
      (direction n) ≤ Cw := by
    intro n
    have hHn : Hw ≤ Dseq.Hs n := by
      exact (le_max_left Hw Hfront).trans
        (hHcombined0.trans (model.separation_mono n))
    rw [show direction n = centeredDirection (Dseq.kappas n)
      Dseq.model.thetaBase (center (Dseq.Hs n)) by rfl]
    rw [width_front_eq_centered_integral (model.separation_pos n)
      (model.curvature_continuous n) (model.curvature_periodic n)
      (model.total_turning n) (by simpa [Dseq] using hkpos n)
      (by simpa [Dseq, hkappa' n] using hhalf (Dseq.Hs n) hHn)]
    have hw := (hwidth (Dseq.Hs n) hHn).2
    simpa [Dseq, hkappa' n] using hw
  have hfrontHalf : ∀ n s, Dseq.kappas n s ≤ 1 / 2 := by
    intro n s
    have hHn : Hfront ≤ Dseq.Hs n :=
      (le_max_right Hw Hfront).trans
        (hHcombined0.trans (model.separation_mono n))
    rw [show Dseq.kappas n = modelCurvature y yp (Dseq.Hs n) by
      simpa [Dseq] using hkappa' n]
    exact hfront (Dseq.Hs n) hHn s
  have hrearHalf : ∀ n s, (Dseq.model.configs n).kH s ≤ 1 / 2 := by
    intro n s
    let cfg := Dseq.model.configs n
    have hY0 := cfg.Y_nonneg (cfg.sf s)
    have hYle : cfg.Y (cfg.sf s) ≤ aa :=
      (le_abs_self _).trans (by simpa [Dseq, hmodela] using cfg.hYa (cfg.sf s))
    have haa : aa ≤ 1 / 5 := by dsimp [aa]; linarith
    have hrad : 0 < 1 - cfg.Y (cfg.sf s) ^ 2 := by
      nlinarith [cfg.ha1, cfg.ha0]
    have hsqrt : 2 * cfg.Y (cfg.sf s) ≤
        Real.sqrt (1 - cfg.Y (cfg.sf s) ^ 2) := by
      refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
      nlinarith
    rw [show (Dseq.model.configs n).kH s = cfg.kH s by rfl,
      cfg.kH_eq, cfg.tan_dl, div_le_iff₀ (Real.sqrt_pos.2 hrad)]
    nlinarith
  have hsteeringHalf : Dseq.model.a ≤ 1 / 2 := by
    simpa [Dseq, hmodela, aa] using (show 2 * eps ≤ (1 : ℝ) / 2 by linarith)
  exact ⟨y, yp, center, Dseq, direction, Am, Hw, Cw, hAm, hHw, hCw,
    (by simpa [Dseq] using hkappa'), (fun n => rfl), hdir, hgeomWidth,
    hhalf, hwidth, hsteeringHalf, hfrontHalf, hrearHalf,
    (by simpa [Dseq] using hmodelKP), (by simpa [Dseq] using hmodelkH)⟩

/-- Uniform width and the actual half-curvature ceiling are retained for the
same configured sequence. -/
theorem exists_actualHalf_widthData_of_eps
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ (E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf)
      (direction : ℕ → ℂ) (Cw : ℝ),
      0 ≤ Cw ∧
      (∀ n, ‖direction n‖ = 1) ∧
      ∀ n, Width.width
        (range (front (E.data.kappas n) E.data.model.thetaBase
          (E.data.Hs n))) (direction n) ≤ Cw := by
  obtain ⟨y, yp, center, D, direction, Am, Hstar, Cw, hAm, hHstar, hCw,
    hkappa, hdirection, hdir, hwidth, hhalf, hcenter, hsteering, hfront, hrear,
    -, -⟩ :=
    exists_strict_sequence_and_uniform_width_of_eps heps heps10
  have hCw0 : 0 ≤ Cw := by rw [hCw]; positivity
  exact ⟨⟨D, hsteering, hfront, hrear⟩, direction, Cw, hCw0, hdir, hwidth⟩

/-- The endpoint regularity retained by the canonical smooth pulse, beyond
the legacy `C²` fields stored in `Data`. -/
structure C3Certificate (D : ConstructedConfiguredSequenceWeighted.Data) : Prop where
  model_KP_C3 : ∀ n, ContDiff ℝ 3
    (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
  model_kH_C3 : ∀ n, ContDiff ℝ 3 (D.model.configs n).kH

/-- Uniform width, the actual half-curvature ceiling, and the `C³` endpoint
certificate are retained for one and the same configured sequence. -/
theorem exists_actualHalf_widthDataC3_of_eps
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ (E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf)
      (direction : ℕ → ℂ) (Cw : ℝ),
      0 ≤ Cw ∧
      (∀ n, ‖direction n‖ = 1) ∧
      (∀ n, Width.width
        (range (front (E.data.kappas n) E.data.model.thetaBase
          (E.data.Hs n))) (direction n) ≤ Cw) ∧
      C3Certificate E.data := by
  obtain ⟨y, yp, center, D, direction, Am, Hstar, Cw, hAm, hHstar, hCw,
    hkappa, hdirection, hdir, hwidth, hhalf, hcenter, hsteering, hfront, hrear,
    hKP3, hkH3⟩ :=
    exists_strict_sequence_and_uniform_width_of_eps heps heps10
  have hCw0 : 0 ≤ Cw := by rw [hCw]; positivity
  exact ⟨⟨D, hsteering, hfront, hrear⟩, direction, Cw, hCw0, hdir, hwidth,
    ⟨hKP3, hkH3⟩⟩

end ConstructedPulseWidth
