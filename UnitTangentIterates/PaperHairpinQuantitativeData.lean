import Mathlib
import UnitTangentIterates.HairpinAsymptoticsComplete
import UnitTangentIterates.HairpinPulseSmooth
import UnitTangentIterates.WideHairpinSmallness
import UnitTangentIterates.PeriodizedTurningHairpin
import UnitTangentIterates.ExpDecay
import UnitTangentIterates.L1Matching
import UnitTangentIterates.PaperHairpinConfig
import UnitTangentIterates.HairpinFrontCurvature
import UnitTangentIterates.HairpinPulseIdentity
import UnitTangentIterates.HairpinODERegularity
import UnitTangentIterates.TranslatorTranslation

/-!
# Quantitative profile data for the paper hairpin

This file collects, on one canonical pair of hairpin coordinates, the
profile-side constants later consumed by `ModelOrbitDefect.Config`: finite
smoothness, exponential derivative bounds, relative derivative bounds, mass
and first-moment finiteness, defect positivity, and the two perimeter
asymptotics.  Periodization and model-orbit synchronization are deliberately
not part of this package.
-/

noncomputable section

open Real Set MeasureTheory
open scoped ContDiff

namespace PaperHairpinQuantitativeData

/-- An exponentially localized continuous function has a finite first
absolute moment. -/
theorem integrable_abs_mul_of_exp_bound {y : ℝ → ℝ} {C alpha : ℝ}
    (halpha : 0 < alpha) (hC : 0 ≤ C) (hy : Continuous y)
    (hyb : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|)) :
    Integrable (fun s => |s| * y s) := by
  have hc : 0 < alpha / 2 := by linarith
  have hmaj : Integrable (fun s : ℝ =>
      (C / ((alpha / 2) * Real.exp 1)) * Real.exp (-(alpha / 2) * |s|)) :=
    (L1Matching.integrable_expabs hc).const_mul _
  refine Integrable.mono' hmaj ((continuous_abs.mul hy).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs]
  have hsplit : Real.exp (-alpha * |s|) =
      Real.exp (-(alpha / 2 * |s|)) * Real.exp (-(alpha / 2) * |s|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpoly := ExpDecay.mul_exp_neg_le (c := alpha / 2) (x := |s|) hc
  have hright0 : 0 ≤ Real.exp (-(alpha / 2) * |s|) := Real.exp_nonneg _
  calc
    |s| * |y s| ≤ |s| * (C * Real.exp (-alpha * |s|)) :=
      mul_le_mul_of_nonneg_left (hyb s) (abs_nonneg s)
    _ = C * (|s| * Real.exp (-(alpha / 2 * |s|))) *
        Real.exp (-(alpha / 2) * |s|) := by rw [hsplit]; ring
    _ ≤ C * (1 / ((alpha / 2) * Real.exp 1)) *
        Real.exp (-(alpha / 2) * |s|) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly hC) hright0
    _ = C / ((alpha / 2) * Real.exp 1) *
        Real.exp (-(alpha / 2) * |s|) := by ring

/-- All profile-side data, with decay and relative constants indexed by the
derivative order so later consumers may select exactly the finite orders they
need.

The perimeter-asymptotics block of the paper's Proposition *Perimeter defect
value and derivative asymptotics* (`Delta > 0`, `Delta = ∫ Φ(y)`, and the two
`P`, `P'` estimates past a threshold) used to be carried here as well.  It is
not carried any more: nothing in the development ever projected it out of
`Data`, and constructing it is what forced the profile package to go through the
perimeter-asymptotics chain, which in turn is what required smoothness of the
profile beyond `(0, π)` — regularity the paper explicitly does not provide.  The
proposition itself is unaffected and remains proved in `HairpinDefect` and
`TwoCapAsymptoticsComplete`.  The parameters `Delta, beta, C, Ht, P, Pp` are
retained in the signature so that existing instantiations are unchanged. -/
structure Data (f theta x : ℝ → ℝ) (M Delta beta C Ht : ℝ)
    (P Pp : ℝ → ℝ) where
  M_pos : 0 < M
  angle_mem : ∀ u, theta u ∈ Ioo 0 Real.pi
  angle_value : ∀ u, Hairpin.hairpinArclength f (Real.pi / 2) (theta u) = u
  angle_deriv : ∀ u, HasDerivAt theta (HairpinRelative.curvField f (theta u)) u
  inverse_value : ∀ s, HairpinRelative.frontArclength f theta (x s) = s
  state_deriv : ∀ s, HasDerivAt (fun r => theta (x r))
    (HairpinRelative.pulseField f (theta (x s))) s
  smooth_pulse : ∀ n : ℕ, ContDiff ℝ (n : ℕ)
    (fun s => HairpinRelative.pulseField f (theta (x s)))
  decayConst : ℕ → ℝ
  decayConst_nonneg : ∀ j, 0 ≤ decayConst j
  /-- Exponential tails, at the orders the development consumes.  The paper
  proves these for every order; the bound `j ≤ 4` records what the endpoint-free
  route of `PulseIteratedDeriv` / `HairpinTailsInterior` supplies, which is
  every order actually used (`CanonicalConsecutivePulseJet` needs `j ≤ 4`). -/
  decay : ∀ j ≤ 4, ∀ s,
    |iteratedDeriv j (fun r => HairpinRelative.pulseField f (theta (x r))) s|
      ≤ decayConst j * Real.exp (-|s| / M)
  relativeConst : ℕ → ℝ
  relativeConst_nonneg : ∀ j, 0 ≤ relativeConst j
  /-- Relative derivative bounds, at the orders the development consumes.  See
  the note on `decay`. -/
  relative : ∀ j ≤ 4, ∀ s,
    |iteratedDeriv j (fun r => HairpinRelative.pulseField f (theta (x r))) s|
      ≤ relativeConst j * HairpinRelative.pulseField f (theta (x s))
  pulse_integrable : Integrable (fun s => HairpinRelative.pulseField f (theta (x s)))
  firstMoment_integrable :
    Integrable (fun s => |s| * HairpinRelative.pulseField f (theta (x s)))
  mass : (∫ s : ℝ, HairpinRelative.pulseField f (theta (x s))) = Real.pi

/-- The translator information which relates two consecutive appearances of
the one fixed hairpin profile.  The paper does not choose independent
profiles: `g` advances the tangent angle on the same translator. -/
structure TranslatorData (f g gp : ℝ → ℝ) : Prop where
  angle_shift : ∀ t ∈ Ioo (0 : ℝ) Real.pi,
    g t - t = Real.arctan (HairpinRelative.curvField f t)
  maps_angle : ∀ t ∈ Ioo (0 : ℝ) Real.pi, g t ∈ Ioo (0 : ℝ) Real.pi
  profile_deriv_identity : ∀ t ∈ Ioo (0 : ℝ) Real.pi,
    f (g t) * gp t = f t + Real.cos t
  angle_deriv : ∀ t ∈ Ioo (0 : ℝ) Real.pi, HasDerivAt g (gp t) t

/-- The constructed translator supplies `TranslatorData`.  Its profile is at
this stage only known to be continuous on the open angle interval; this
statement deliberately records that exact regularity rather than silently
identifying it with the smooth profile consumed by `Data`. -/
theorem exists_translatorData {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) :
    ∃ f g gp : ℝ → ℝ, (∀ t, 0 < f t) ∧ ContinuousOn f (Ioo 0 Real.pi) ∧
      TranslatorData f g gp := by
  obtain ⟨f, g, gp, hfpos, hfc, hshift, hmaps, hident, hg⟩ :=
    HairpinFrontCurvature.exists_translator_relations heps heps10
  exact ⟨f, g, gp, hfpos, hfc, ⟨hshift, hmaps, hident, hg⟩⟩

/-- The canonical translator package without discarding its interior
finite-order regularity.  All fields refer to the same fixed profile and the
same angle map `Translator.next f`. -/
theorem exists_smoothOn_translatorData {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) :
    ∃ f g gp : ℝ → ℝ, (∀ t, 0 < f t) ∧
      (∀ n : ℕ, ContDiffOn ℝ n f (Ioo 0 Real.pi)) ∧
      TranslatorData f g gp := by
  obtain ⟨f, V, hV, hfl, hfu, hfc, hmaps, hU, hsmooth, hshift, hg, htrans⟩ :=
    TranslatorTranslation.exists_translating_hairpin_translation heps heps10
  let g : ℝ → ℝ := Translator.next f
  let gp : ℝ → ℝ := fun t => (f t + Real.cos t) / f (g t)
  have hm1 : 1 < eps⁻¹ - eps := BarrierEstimates.m_gt_one heps heps10
  have hfpos : ∀ t, 0 < f t := fun t =>
    lt_of_lt_of_le (lt_trans zero_lt_one hm1)
      (le_trans ((Barriers.fMinus_min heps).1 t) (hfl t))
  refine ⟨f, g, gp, hfpos, hsmooth, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    simpa [g, HairpinRelative.curvField] using hshift t ht
  · intro t ht
    exact ⟨lt_trans ht.1 (hmaps t ht).1, (hmaps t ht).2⟩
  · intro t ht
    have hne : f (g t) ≠ 0 := (hfpos _).ne'
    dsimp [gp]
    field_simp
  · intro t ht
    simpa [g, gp] using hg t ht

namespace TranslatorData

/-- Translator relations only evaluate the profile at angles in `[0,π]`, so
they pass unchanged to any extension agreeing there. -/
theorem transfer_extension {f F g gp : ℝ → ℝ}
    (d : TranslatorData f g gp)
    (hagree : ∀ t ∈ Icc (0 : ℝ) Real.pi, F t = f t) :
    TranslatorData F g gp := by
  refine ⟨?_, d.maps_angle, ?_, d.angle_deriv⟩
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Real.pi := ⟨ht.1.le, ht.2.le⟩
    rw [HairpinRelative.curvField, hagree t ht']
    exact d.angle_shift t ht
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Real.pi := ⟨ht.1.le, ht.2.le⟩
    have hgt := d.maps_angle t ht
    have hgt' : g t ∈ Icc (0 : ℝ) Real.pi := ⟨hgt.1.le, hgt.2.le⟩
    rw [hagree t ht', hagree (g t) hgt']
    exact d.profile_deriv_identity t ht

end TranslatorData

/-- A quantitative pulse package together with the translator and an explicit
first derivative of its pulse.  This is the correct consecutive-profile
object: the previous pulse is a phase translate of the current pulse, not a
second independently chosen hairpin. -/
structure ConsecutiveData (f theta x g gp yp : ℝ → ℝ)
    (M Delta beta C Ht : ℝ) (P Pp : ℝ → ℝ) where
  quantitative : Data f theta x M Delta beta C Ht P Pp
  translator : TranslatorData f g gp
  pulse_deriv : ∀ s, HasDerivAt
    (fun r => HairpinRelative.pulseField f (theta (x r))) (yp s) s

namespace ConsecutiveData

/-- The translator phase between intrinsic hairpin arclength and the front
origin. -/
def phase (f theta g : ℝ → ℝ) : ℝ :=
  Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))

/-- The pulse used by the current two-cap model. -/
def currentPulse (f theta x : ℝ → ℝ) : ℝ → ℝ := fun s =>
  HairpinRelative.pulseField f (theta (x s))

/-- The pulse used for the preceding isolated curvature.  It is the same
fixed pulse translated by the canonical front phase. -/
def previousPulse (f theta x g : ℝ → ℝ) : ℝ → ℝ := fun s =>
  HairpinRelative.pulseField f (theta (x (s - phase f theta g)))

/-- The correspondingly translated derivative. -/
def previousPulseDeriv (f theta g yp : ℝ → ℝ) : ℝ → ℝ := fun s =>
  yp (s - phase f theta g)

/-- **Consecutive-profile coherence.**  The normalized steering identity for
the current pulse and the translator's shifted front-curvature identity
combine to give exactly `PaperHairpinData.local_phase`, with the prior pulse a
translate of the same fixed profile. -/
theorem local_phase
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (d : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp) :
    ∀ s, currentPulse f theta x s =
      Real.sqrt (1 - currentPulse f theta x s ^ 2) *
        ModelOrbitDefect.hairpinCurvature
          (previousPulse f theta x g) (previousPulseDeriv f theta g yp) (x s) := by
  intro s
  have hcurv := HairpinFrontCurvature.front_curvature_identity_shifted
    hf hfpos d.translator.angle_shift d.translator.maps_angle
    d.translator.profile_deriv_identity d.translator.angle_deriv
    d.quantitative.angle_mem d.quantitative.angle_value d.quantitative.angle_deriv
    d.quantitative.inverse_value d.quantitative.state_deriv d.pulse_deriv (x s)
  have hsteer := HairpinPulseIdentity.pulseField_eq_speed_mul_curvField
    f (theta (x s))
  rw [hcurv] at hsteer
  simpa [currentPulse, previousPulse, previousPulseDeriv, phase,
    ModelOrbitDefect.hairpinCurvature] using hsteer

end ConsecutiveData

namespace Data

/-- Exact mass supplies the constant required by
`PaperHairpinConfig.RearCellData.of_tail_bounds`. -/
theorem rearCell_mass_budget
    {f theta x : ℝ → ℝ} {M Delta beta C Ht b : ℝ} {P Pp : ℝ → ℝ}
    (d : Data f theta x M Delta beta C Ht P Pp) :
    (1 + b) / 2 *
        (∫ s : ℝ, HairpinRelative.pulseField f (theta (x s)))
      ≤ (1 + b) / 2 * Real.pi := by
  rw [d.mass]

/-- The barrier width converts the package's relative constants into the
absolute `O(eps)` derivative bounds used for the small-curvature choice. -/
theorem wide_pulse_and_derivative_bounds
    {f theta x : ℝ → ℝ} {M Delta beta C Ht eps : ℝ} {P Pp : ℝ → ℝ}
    (d : Data f theta x M Delta beta C Ht P Pp)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 10)
    (hfl : ∀ t, Barriers.fMinus eps t ≤ f t) :
    (∀ s, HairpinRelative.pulseField f (theta (x s)) ≤ 2 * eps) ∧
      ∀ j ≤ 4, ∀ s,
        |iteratedDeriv j (fun r => HairpinRelative.pulseField f (theta (x r))) s|
          ≤ (2 * d.relativeConst j) * eps := by
  have hmem : ∀ s, theta (x s) ∈ Icc (0 : ℝ) Real.pi := fun s =>
    ⟨(d.angle_mem (x s)).1.le, (d.angle_mem (x s)).2.le⟩
  constructor
  · intro s
    exact WideHairpinSmallness.pulseField_le_two_mul heps heps' hfl (hmem s)
  · intro j hj s
    exact WideHairpinSmallness.abs_iteratedDeriv_pulse_le_two_mul
      heps heps' hfl hmem (d.relativeConst_nonneg j) (d.relative j hj) s

/-- **The fixed profile inequalities admit a simultaneous choice of
constants.**  We use the natural decay rate `alpha=1/M`, take
`beta=alpha/4`, use the wide-hairpin strip `a=au=2 eps`, and choose every
remaining upper-bound constant to be its displayed expression or a maximum
of the expressions it must dominate.

This theorem does not assert a prescribed universal upper bound on `kstar` or
`kd`; such a statement would require quantitative control of how the relative
constants vary with the barrier parameter. -/
theorem exists_profileConstants_of_wide
    {f theta x : ℝ → ℝ} {M Delta beta0 C0 Ht eps : ℝ}
    {P Pp : ℝ → ℝ}
    (d : Data f theta x M Delta beta0 C0 Ht P Pp)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 10) :
    ∃ alpha beta a au CU CK DU DU2 D Km Kd kstar kd : ℝ,
      PaperHairpinConfig.ProfileConstants
        (alpha := alpha) (beta := beta) (a := a) (au := au)
        (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
        (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd) := by
  let alpha : ℝ := 1 / M
  let beta : ℝ := alpha / 4
  let a : ℝ := 2 * eps
  let au : ℝ := 2 * eps
  let CU : ℝ := d.decayConst 0
  let DU : ℝ := d.relativeConst 1
  let DU2 : ℝ := d.relativeConst 2
  let D : ℝ := d.relativeConst 1
  let supExpr : ℝ := (1 + FrontPeriodization.G au * DU) * au
  let decayExpr : ℝ := (1 + FrontPeriodization.G au * DU) * CU
  let currentRear : ℝ := a / Real.sqrt (1 - a ^ 2)
  let currentDeriv : ℝ := ((1 + FrontPeriodization.G a * D) * a + a) /
    Real.sqrt (1 - a ^ 2) ^ 3
  let priorDeriv : ℝ := DU * au +
    FrontPeriodization.lipConst au * (DU ^ 2 * au ^ 2) +
    FrontPeriodization.G au * (DU2 * au)
  let Km : ℝ := supExpr
  let CK : ℝ := decayExpr
  let kstar : ℝ := max supExpr currentRear
  let kd : ℝ := max 1 (max currentDeriv priorDeriv)
  let Kd : ℝ := priorDeriv
  have hM : 0 < M := d.M_pos
  have halpha : 0 < alpha := by
    dsimp [alpha]
    exact div_pos one_pos hM
  have hbeta : 0 < beta := by
    dsimp [beta, alpha]
    linarith [div_pos (zero_lt_one (α := ℝ)) hM]
  have hbetalt : beta < alpha / 2 := by
    dsimp [beta]
    linarith
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hau0 : 0 ≤ au := by dsimp [au]; positivity
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hau1 : au < 1 := by dsimp [au]; linarith
  refine ⟨alpha, beta, a, au, CU, CK, DU, DU2, D, Km, Kd, kstar, kd, ?_⟩
  refine
    { derivative_nonneg := d.relativeConst_nonneg 1
      beta_pos := hbeta
      beta_lt := hbetalt
      prior_derivative_nonneg := d.relativeConst_nonneg 1
      prior_second_nonneg := d.relativeConst_nonneg 2
      prior_strip_nonneg := hau0
      current_strip_nonneg := ha0
      current_strip_lt := ha1
      prior_strip_lt := hau1
      isolated_sup := ?_
      isolated_decay := ?_
      prior_model_sup := ?_
      rear_derivative_pos := ?_
      current_rear_sup := ?_
      current_rear_deriv := ?_
      prior_deriv_sup := ?_
      isolated_deriv_sup := ?_ }
  · exact le_rfl
  · exact le_rfl
  · exact le_max_left _ _
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · exact le_max_right _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)
  · exact le_rfl

/-- The profile-constant certificate and the actual `O(eps)` pulse bounds are
available simultaneously for a barrier-wide profile. -/
theorem exists_profileConstants_and_wide_bounds
    {f theta x : ℝ → ℝ} {M Delta beta0 C0 Ht eps : ℝ}
    {P Pp : ℝ → ℝ}
    (d : Data f theta x M Delta beta0 C0 Ht P Pp)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 10)
    (hfl : ∀ t, Barriers.fMinus eps t ≤ f t) :
    (∃ alpha beta a au CU CK DU DU2 D Km Kd kstar kd : ℝ,
      PaperHairpinConfig.ProfileConstants
        (alpha := alpha) (beta := beta) (a := a) (au := au)
        (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
        (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd)) ∧
    (∀ s, HairpinRelative.pulseField f (theta (x s)) ≤ 2 * eps) ∧
    ∀ j ≤ 4, ∀ s,
      |iteratedDeriv j (fun r => HairpinRelative.pulseField f (theta (x r))) s|
        ≤ (2 * d.relativeConst j) * eps := by
  refine ⟨exists_profileConstants_of_wide d heps heps', ?_⟩
  exact wide_pulse_and_derivative_bounds d heps heps' hfl

end Data

/-- **The constructed translator supplies the complete profile-side
quantitative package.** -/
theorem exists_data {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x : ℝ → ℝ) (M Delta beta C Ht : ℝ) (P Pp : ℝ → ℝ),
      Nonempty (Data f theta x M Delta beta C Ht P Pp) := by
  obtain ⟨theta, x, M, Delta, beta, C, Ht, P, Pp, hM, hmem, hval, htheta,
    hx, hw, hexp, hDelta, hDeltaEq, hbeta, hC, hHt, hPval, hPderiv, hPp⟩ :=
    HairpinAsymptoticsComplete.hairpin_perimeter_tail_asymptotics hf hfpos
  choose decayConst hdecay0 hdecay using hexp
  have hmem' : ∀ s, theta (x s) ∈ Icc (0 : ℝ) Real.pi := fun s =>
    ⟨(hmem (x s)).1.le, (hmem (x s)).2.le⟩
  choose relativeConst hrelative0 hrelative using fun j =>
    HairpinRelative.abs_iteratedDeriv_pulse_le hf hfpos hmem' hw j
  have hsmooth : ∀ n : ℕ, ContDiff ℝ (n : ℕ)
      (fun s => HairpinRelative.pulseField f (theta (x s))) :=
    HairpinPulseSmooth.contDiff_nat_comp
      (HairpinRelative.contDiff_pulseField hf hfpos)
      (HairpinPulseSmooth.contDiff_nat_of_autonomous
        (HairpinRelative.contDiff_pulseField hf hfpos) hw)
  have hycont : Continuous (fun s => HairpinRelative.pulseField f (theta (x s))) :=
    (hsmooth 0).continuous
  have hy0 : ∀ s, 0 ≤ HairpinRelative.pulseField f (theta (x s)) := fun s =>
    HairpinRelative.pulseField_nonneg hfpos (hmem' s)
  have hyb : ∀ s, |HairpinRelative.pulseField f (theta (x s))|
      ≤ decayConst 0 * Real.exp (-(1 / M) * |s|) := by
    intro s
    have := hdecay 0 s
    simpa [show -|s| / M = -(1 / M) * |s| by ring] using this
  have halpha : 0 < 1 / M := by positivity
  have hyint := FrontPeriodizationIntegral.integrable_of_exp_bound' halpha hycont hyb
  have hmoment := integrable_abs_mul_of_exp_bound halpha (hdecay0 0) hycont hyb
  have hthetac : Continuous theta :=
    Differentiable.continuous fun u => (htheta u).differentiableAt
  have hmass := PeriodizedTurningHairpin.hairpin_pulse_mass_of_data
    hf hfpos hmem hval hthetac hx
  exact ⟨theta, x, M, Delta, beta, C, Ht, P, Pp,
    ⟨hM, hmem, hval, htheta, hx, hw, hsmooth, decayConst, hdecay0,
    (fun j _ => hdecay j),
    relativeConst, hrelative0, (fun j _ => hrelative j), hyint, hmoment,
    hmass⟩⟩

namespace ConsecutiveData

/-- A smooth positive extension of the translator profile produces the full
quantitative consecutive package on one common profile.  This theorem closes
the extension/coherence API: its only profile hypothesis beyond existing
translator data is precisely the neighbourhood regularity required by
`HairpinODERegularity.exists_smooth_positive_hairpin_extension`. -/
theorem exists_of_smooth_extension {r : ℝ} (hr : 0 < r)
    {f g gp : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo (-r) (Real.pi + r)))
    (hfpos : ∀ t ∈ Ioo (-r) (Real.pi + r), 0 < f t)
    (translator : TranslatorData f g gp) :
    ∃ (F theta x yp : ℝ → ℝ) (M Delta beta C Ht : ℝ) (P Pp : ℝ → ℝ),
      ContDiff ℝ ∞ F ∧ (∀ t, 0 < F t) ∧
      Nonempty (Data F theta x M Delta beta C Ht P Pp) ∧
      Nonempty (ConsecutiveData F theta x g gp yp M Delta beta C Ht P Pp) := by
  obtain ⟨F, hF, hFpos, hagree⟩ :=
    HairpinODERegularity.exists_smooth_positive_hairpin_extension hr hf hfpos
  have translated : TranslatorData F g gp :=
    translator.transfer_extension hagree
  obtain ⟨theta, x, M, Delta, beta, C, Ht, P, Pp, ⟨quantitative⟩⟩ :=
    exists_data hF hFpos
  let y : ℝ → ℝ := fun s => HairpinRelative.pulseField F (theta (x s))
  let yp : ℝ → ℝ := iteratedDeriv 1 y
  have hyp : ∀ s, HasDerivAt y (yp s) s := by
    intro s
    have hd := (quantitative.smooth_pulse 1).differentiable
      (by norm_num)
    simpa [yp, y, iteratedDeriv_one] using (hd s).hasDerivAt
  refine ⟨F, theta, x, yp, M, Delta, beta, C, Ht, P, Pp,
    hF, hFpos, ⟨quantitative⟩, ?_⟩
  exact ⟨⟨quantitative, translated, hyp⟩⟩

end ConsecutiveData

/-- **The quantifier order used in the paper.**  First `eps` and the barrier
profile `f` are fixed, with `eps <= 1/40` making the intrinsic curvature at
most `1/20`.  Only then are the profile-dependent decay and relative
derivative constants produced.  No uniform estimate on `eps * D_j(eps)` is
asserted or needed here. -/
theorem fixed_wide_profile_quantifier_order
    {eps : ℝ} {f : ℝ → ℝ}
    (heps : 0 < eps) (heps40 : eps ≤ 1 / 40)
    (hfl : ∀ t, Barriers.fMinus eps t ≤ f t)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x : ℝ → ℝ) (M Delta beta C Ht : ℝ) (P Pp : ℝ → ℝ),
      Nonempty (Data f theta x M Delta beta C Ht P Pp) ∧
      (∀ t ∈ Icc (0 : ℝ) Real.pi,
        HairpinRelative.curvField f t ≤ 1 / 20) ∧
      (∀ s, HairpinRelative.pulseField f (theta (x s)) ≤ 1 / 20) := by
  obtain ⟨theta, x, M, Delta, beta, C, Ht, P, Pp, ⟨d⟩⟩ := exists_data hf hfpos
  have heps10 : eps ≤ 1 / 10 := by linarith
  refine ⟨theta, x, M, Delta, beta, C, Ht, P, Pp, ⟨d⟩, ?_, ?_⟩
  · intro t ht
    exact (WideHairpinSmallness.curvField_le_two_mul heps heps10 hfl ht).trans (by linarith)
  · intro s
    have ht : theta (x s) ∈ Icc (0 : ℝ) Real.pi :=
      ⟨(d.angle_mem (x s)).1.le, (d.angle_mem (x s)).2.le⟩
    exact (WideHairpinSmallness.pulseField_le_two_mul heps heps10 hfl ht).trans (by linarith)

end PaperHairpinQuantitativeData
