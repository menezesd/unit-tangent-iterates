import Mathlib
import UnitTangentIterates.Barriers
import UnitTangentIterates.PhiBounds
import UnitTangentIterates.TranslatorOperator

/-!
# The explicit barriers are a subsolution and a supersolution

This file completes the lemma *Explicit barriers* of Section 3 of *A Noncircular
Oval with Convex Unit-Tangent Iterates*, in the form in which the monotone
iteration of `TranslatorOperator.lean` consumes it:

for `0 < ε ≤ 1/10`, the profiles

```
  f_ε^-(θ) = ε⁻¹ + (2/3)(1 - cos θ) - ε cos θ ,
  f_ε^+(θ) = ε⁻¹ + (2/3)(1 - cos θ) + ε(cos θ + 2)
```

of `Barriers.lean` satisfy `f_ε^- ≤ 𝒫 f_ε^-` and `𝒫 f_ε^+ ≤ f_ε^+` on `(0, π)`.

The argument is the one of the paper: for a profile `f = A + B cos` the residual
`ℛ(θ) = ∫_θ^{θ + d} f - sin θ` taken at the steering shift
`d = arctan(sin θ / f(θ))` has the exact factorization of `Barriers.lean`
through `Φ₀, Φ₁, Φ₂`, and the quantitative bounds of `PhiBounds.lean` make its
sign visible: it is positive for the lower barrier and negative for the upper
one.  The sign of the residual compares the true mass time `D_f(θ)` with `d`,
and `sin θ cot` reverses that comparison, which is exactly the comparison of
`𝒫f` with `f`.

Combined with `TranslatorOperator.exists_translator_profile` this gives the
**profile of the translating hairpin**, unconditionally
(`exists_hairpin_profile`): a continuous profile between the two barriers
solving the translator equation `D_f(θ) = arctan (sin θ / f(θ))` on `(0, π)`.
-/

noncomputable section

open Real Set MeasureTheory

namespace BarrierEstimates

open TranslatorOperator

/-- A profile of the form `A + B cos`. -/
def prof (A B : ℝ) : ℝ → ℝ := fun t => A + B * Real.cos t

/-- The steering shift `d = arctan(sin θ / f(θ))` of such a profile. -/
def steer (A B θ : ℝ) : ℝ := Real.arctan (Real.sin θ / prof A B θ)

theorem continuous_prof (A B : ℝ) : Continuous (prof A B) := by
  unfold prof
  fun_prop

/-! ### The sign dictionary in the two directions -/

/-- The companion of `Barriers.residual_nonneg_iff`: a nonpositive residual at
`d` means that the true mass time is at least `d`. -/
theorem residual_nonpos_iff {f : ℝ → ℝ} {θ Df d : ℝ}
    (hf0 : ∀ t, 0 < f t)
    (hIf : ∫ t in θ..(θ + Df), f t = Real.sin θ)
    (hfint : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    Barriers.residual f θ d ≤ 0 ↔ d ≤ Df := by
  have hsplit : (∫ t in θ..(θ + d), f t)
      = (∫ t in θ..(θ + Df), f t) + ∫ t in (θ + Df)..(θ + d), f t :=
    (intervalIntegral.integral_add_adjacent_intervals (hfint _ _) (hfint _ _)).symm
  have hres : Barriers.residual f θ d = ∫ t in (θ + Df)..(θ + d), f t := by
    rw [Barriers.residual, hsplit, hIf]; ring
  rw [hres]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < ∫ t in (θ + Df)..(θ + d), f t :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hfint _ _)
        (fun x _ => hf0 x) (by linarith)
    linarith
  · intro h
    have hpos : 0 ≤ ∫ t in (θ + d)..(θ + Df), f t :=
      intervalIntegral.integral_nonneg (by linarith) (fun x _ => (hf0 x).le)
    rw [intervalIntegral.integral_symm]
    linarith

/-! ### The residual criterion -/

variable {A B m M : ℝ}

/-- The steering shift lies in `(0, π/2)` and realizes the profile value:
`f(θ) = sin θ cot d`. -/
theorem steer_spec (hm : 1 < m) (hprof : Profile m M (prof A B)) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < steer A B θ ∧ steer A B θ < π / 2 ∧
      prof A B θ = Real.sin θ * (Real.cos (steer A B θ) / Real.sin (steer A B θ)) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hF : 0 < prof A B θ := lt_of_lt_of_le (lt_trans zero_lt_one hm) (hprof.lower θ)
  have hd0 : 0 < steer A B θ := Real.arctan_pos.mpr (div_pos hs hF)
  have hd2 : steer A B θ < π / 2 := Real.arctan_lt_pi_div_two _
  refine ⟨hd0, hd2, ?_⟩
  exact (TranslatorFixedPoint.fixed_point_iff_arctan (θ := θ) hd0 hd2 hF).2 rfl

/-- The normalized residual of `A + B cos` at its steering shift, in terms of
the three functions `Φ₀, Φ₁, Φ₂`. -/
def normResidual (A B θ : ℝ) : ℝ :=
  Barriers.Phi0 (steer A B θ ^ 2) + B * Barriers.Phi1 (steer A B θ ^ 2)
    + (B * Real.cos θ / prof A B θ) * Barriers.Phi2 (steer A B θ ^ 2)

/-- **A nonnegative normalized residual makes the profile a subsolution.** -/
theorem le_Pop_of_normResidual_nonneg (hm : 1 < m) (hprof : Profile m M (prof A B))
    {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (hN : 0 ≤ normResidual A B θ) :
    prof A B θ ≤ Pop (prof A B) θ := by
  obtain ⟨hd0, hd2, hFd⟩ := steer_spec hm hprof hθ
  set d := steer A B θ with hd
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hF : 0 < prof A B θ := lt_of_lt_of_le (lt_trans zero_lt_one hm) (hprof.lower θ)
  have hfact := Barriers.residual_factorization (A := A) (B := B) (d := d) (s := Real.sin θ)
    (c := Real.cos θ) (F := prof A B θ) hd0 hd2 hs hFd rfl
  have hden : 0 < d ^ 2 * Real.sin θ := by positivity
  have hres : Barriers.residual (prof A B) θ d
      = A * d + B * (Real.sin θ * (Real.cos d - 1) + Real.cos θ * Real.sin d) - Real.sin θ :=
    Barriers.residual_affine_cos A B θ d
  have hnonneg : 0 ≤ Barriers.residual (prof A B) θ d := by
    rw [hres]
    have h := hfact
    rw [← normResidual] at h
    have h2 := (div_eq_iff (ne_of_gt hden)).mp h
    have h3 : 0 ≤ normResidual A B θ * (d ^ 2 * Real.sin θ) := mul_nonneg hN hden.le
    linarith
  have hDle : shift (prof A B) θ ≤ d := by
    refine (Barriers.residual_nonneg_iff (f := prof A B) (θ := θ) (Df := shift (prof A B) θ)
      (d := d) (fun t => lt_of_lt_of_le (lt_trans zero_lt_one hm) (hprof.lower t))
      (shift_integral hprof hm hθ) (hprof.int)).1 hnonneg
  have hDpos : 0 < shift (prof A B) θ := (shift_bounds hprof hm hθ).1
  have hmono := Translator.translator_operator_mono (θ := θ) (Dh := shift (prof A B) θ)
    (Df := d) hθ hDpos hd2 hDle
  rw [hFd]
  exact hmono

/-- **A nonpositive normalized residual makes the profile a supersolution.** -/
theorem Pop_le_of_normResidual_nonpos (hm : 1 < m) (hprof : Profile m M (prof A B))
    {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (hN : normResidual A B θ ≤ 0) :
    Pop (prof A B) θ ≤ prof A B θ := by
  obtain ⟨hd0, hd2, hFd⟩ := steer_spec hm hprof hθ
  set d := steer A B θ with hd
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hF : 0 < prof A B θ := lt_of_lt_of_le (lt_trans zero_lt_one hm) (hprof.lower θ)
  have hfact := Barriers.residual_factorization (A := A) (B := B) (d := d) (s := Real.sin θ)
    (c := Real.cos θ) (F := prof A B θ) hd0 hd2 hs hFd rfl
  have hden : 0 < d ^ 2 * Real.sin θ := by positivity
  have hres : Barriers.residual (prof A B) θ d
      = A * d + B * (Real.sin θ * (Real.cos d - 1) + Real.cos θ * Real.sin d) - Real.sin θ :=
    Barriers.residual_affine_cos A B θ d
  have hnonpos : Barriers.residual (prof A B) θ d ≤ 0 := by
    rw [hres]
    have h := hfact
    rw [← normResidual] at h
    have h2 := (div_eq_iff (ne_of_gt hden)).mp h
    have h3 : 0 ≤ (-normResidual A B θ) * (d ^ 2 * Real.sin θ) :=
      mul_nonneg (neg_nonneg.mpr hN) hden.le
    nlinarith [h2, h3]
  have hDge : d ≤ shift (prof A B) θ :=
    (residual_nonpos_iff (f := prof A B) (θ := θ) (Df := shift (prof A B) θ) (d := d)
      (fun t => lt_of_lt_of_le (lt_trans zero_lt_one hm) (hprof.lower t))
      (shift_integral hprof hm hθ) (hprof.int)).1 hnonpos
  have hDlt : shift (prof A B) θ < π / 2 := (shift_bounds hprof hm hθ).2
  have hmono := Translator.translator_operator_mono (θ := θ) (Dh := d)
    (Df := shift (prof A B) θ) hθ hd0 hDlt hDge
  rw [hFd, Pop]
  exact hmono

/-! ### The numerical estimates -/

theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  rcases eq_or_lt_of_le hx with rfl | h
  · simp
  · have hd0 : 0 < Real.arctan x := Real.arctan_pos.mpr h
    have hd2 : Real.arctan x < π / 2 := Real.arctan_lt_pi_div_two x
    have hlt := Real.lt_tan hd0 hd2
    rw [Real.tan_arctan] at hlt
    exact hlt.le

/-- An elementary product bound used twice below. -/
theorem abs_triple_le {c w X : ℝ} (hc : |c| ≤ 1) (hw0 : 0 ≤ w) (hX : |X| ≤ 1 / 3) :
    |c| * |w| * |X| ≤ 1 * w * (1 / 3) := by
  have hw : |w| ≤ w := le_of_eq (abs_of_nonneg hw0)
  have h1 : |c| * |w| ≤ 1 * w := mul_le_mul hc hw (abs_nonneg w) zero_le_one
  exact mul_le_mul h1 hX (abs_nonneg X) (by positivity)

/-- The elementary inequality behind the lower barrier. -/
theorem normalized_nonneg_of_bounds {X0 X1 X2 B c w dd eps : ℝ}
    (hX0 : |X0 + 2 / 3| ≤ dd / 6) (hX1u : X1 ≤ -1 + dd / 12)
    (hX2 : |X2| ≤ 1 / 3) (hc : |c| ≤ 1) (hw0 : 0 ≤ w) (hweps : w ≤ 2 * eps)
    (hdd : dd ≤ 4 * eps ^ 2) (heps0 : 0 < eps) (heps : eps ≤ 1 / 10)
    (hB : B = -(2 / 3 + eps)) : 0 ≤ X0 + B * X1 + B * c * w * X2 := by
  subst hB
  rw [abs_le] at hX0 hX2 hc
  have h1 : -(2 / 3) - dd / 6 ≤ X0 := by linarith [hX0.1]
  have h2 : (2 / 3 + eps) * (1 - dd / 12) ≤ -(2 / 3 + eps) * X1 := by nlinarith
  have h3 : |(-(2 / 3 + eps)) * c * w * X2| ≤ (2 / 3 + eps) * w / 3 := by
    have hbc : |c| * |w| * |X2| ≤ 1 * w * (1 / 3) :=
      abs_triple_le (abs_le.mpr ⟨hc.1, hc.2⟩) hw0 (abs_le.mpr ⟨hX2.1, hX2.2⟩)
    calc |(-(2 / 3 + eps)) * c * w * X2| = (2 / 3 + eps) * (|c| * |w| * |X2|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2/3 + eps)]
          ring
      _ ≤ (2 / 3 + eps) * (1 * w * (1 / 3)) := by nlinarith
      _ = (2 / 3 + eps) * w / 3 := by ring
  have h4 : -((2 / 3 + eps) * w / 3) ≤ (-(2 / 3 + eps)) * c * w * X2 := by
    have := (abs_le.mp h3).1
    linarith
  nlinarith

/-- The elementary inequality behind the upper barrier. -/
theorem normalized_nonpos_of_bounds {X0 X1 X2 B c w dd eps : ℝ}
    (hX0 : |X0 + 2 / 3| ≤ dd / 6) (hX1l : -1 ≤ X1)
    (hX2 : |X2| ≤ 1 / 3) (hc : |c| ≤ 1) (hw0 : 0 ≤ w) (hweps : w ≤ 2 * eps)
    (hdd : dd ≤ 4 * eps ^ 2) (heps0 : 0 < eps) (heps : eps ≤ 1 / 10)
    (hB : B = eps - 2 / 3) : X0 + B * X1 + B * c * w * X2 ≤ 0 := by
  subst hB
  rw [abs_le] at hX0 hX2 hc
  have h1 : X0 ≤ -(2 / 3) + dd / 6 := by linarith [hX0.2]
  have h2 : (eps - 2 / 3) * X1 ≤ 2 / 3 - eps := by nlinarith
  have h3 : |(eps - 2 / 3) * c * w * X2| ≤ (2 / 3 - eps) * w / 3 := by
    calc |(eps - 2 / 3) * c * w * X2| = (2 / 3 - eps) * (|c| * |w| * |X2|) := by
          rw [abs_mul, abs_mul, abs_mul,
            abs_of_nonpos (by linarith : eps - 2/3 ≤ 0)]
          ring
      _ ≤ (2 / 3 - eps) * (1 * w * (1 / 3)) := by
          have hbc : |c| * |w| * |X2| ≤ 1 * w * (1 / 3) :=
            abs_triple_le (abs_le.mpr ⟨hc.1, hc.2⟩) hw0 (abs_le.mpr ⟨hX2.1, hX2.2⟩)
          nlinarith
      _ = (2 / 3 - eps) * w / 3 := by ring
  have h4 : (eps - 2 / 3) * c * w * X2 ≤ (2 / 3 - eps) * w / 3 := (abs_le.mp h3).2
  nlinarith

/-! ### The two barriers -/

/-- The lower barrier as a profile of the form `A + B cos`. -/
theorem fMinus_eq (ε : ℝ) : Barriers.fMinus ε = prof (ε⁻¹ + 2 / 3) (-(2 / 3 + ε)) := by
  funext θ
  simp only [Barriers.fMinus, Barriers.u0, prof]
  ring

/-- The upper barrier as a profile of the form `A + B cos`. -/
theorem fPlus_eq (ε : ℝ) : Barriers.fPlus ε = prof (ε⁻¹ + 2 / 3 + 2 * ε) (ε - 2 / 3) := by
  funext θ
  simp only [Barriers.fPlus, Barriers.u0, prof]
  ring

section Numeric

variable {ε : ℝ}

theorem inv_gt (hε : 0 < ε) (hε' : ε ≤ 1 / 10) : 10 ≤ ε⁻¹ := by
  rw [le_inv_comm₀ (by norm_num) hε]
  simpa using hε'

theorem m_gt_one (hε : 0 < ε) (hε' : ε ≤ 1 / 10) : 1 < ε⁻¹ - ε := by
  have := inv_gt hε hε'
  linarith

/-- Both barriers are profiles with `ε⁻¹ - ε ≤ f ≤ ε⁻¹ + 4/3 + 3ε`. -/
theorem profile_fMinus (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    Profile (ε⁻¹ - ε) (ε⁻¹ + 4 / 3 + 3 * ε) (Barriers.fMinus ε) := by
  refine ⟨?_, (Barriers.fMinus_min hε).1, fun θ => ?_⟩
  · rw [fMinus_eq]
    exact (continuous_prof _ _).measurable
  · have hc := Real.neg_one_le_cos θ
    have hc' := Real.cos_le_one θ
    simp only [Barriers.fMinus, Barriers.u0]
    nlinarith

theorem profile_fPlus (hε : 0 < ε) :
    Profile (ε⁻¹ - ε) (ε⁻¹ + 4 / 3 + 3 * ε) (Barriers.fPlus ε) := by
  refine ⟨?_, fun θ => le_trans ((Barriers.fMinus_min hε).1 θ) (Barriers.fMinus_le_fPlus hε θ),
    fun θ => ?_⟩
  · rw [fPlus_eq]
    exact (continuous_prof _ _).measurable
  · have hc := Real.neg_one_le_cos θ
    have hc' := Real.cos_le_one θ
    simp only [Barriers.fPlus, Barriers.u0]
    nlinarith

/-- For a barrier profile the steering shift and the reciprocal value are at
most `2ε`. -/
theorem steer_bounds {A B : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hlow : ∀ t, ε⁻¹ - ε ≤ prof A B t) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < steer A B θ ∧ steer A B θ ≤ 2 * ε ∧ 1 / prof A B θ ≤ 2 * ε := by
  have hinv := inv_gt hε hε'
  have hF := hlow θ
  have hFpos : 0 < prof A B θ := by linarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hw : 1 / prof A B θ ≤ 2 * ε := by
    rw [div_le_iff₀ hFpos]
    have hεinv : ε * ε⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hε)
    nlinarith
  have hd0 : 0 < steer A B θ := Real.arctan_pos.mpr (div_pos hs hFpos)
  refine ⟨hd0, ?_, hw⟩
  have hle : Real.sin θ / prof A B θ ≤ 1 / prof A B θ := by
    gcongr
    exact Real.sin_le_one θ
  exact le_trans (arctan_le_self (le_of_lt (div_pos hs hFpos))) (le_trans hle hw)

/-- **The lower barrier is a subsolution**: `f_ε^- ≤ 𝒫 f_ε^-` on `(0, π)` for
`0 < ε ≤ 1/10`. -/
theorem fMinus_le_Pop (hε : 0 < ε) (hε' : ε ≤ 1 / 10) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    Barriers.fMinus ε θ ≤ Pop (Barriers.fMinus ε) θ := by
  have hprof := profile_fMinus hε hε'
  rw [fMinus_eq] at hprof ⊢
  set A : ℝ := ε⁻¹ + 2 / 3
  set B : ℝ := -(2 / 3 + ε)
  have hlow : ∀ t, ε⁻¹ - ε ≤ prof A B t := hprof.lower
  obtain ⟨hd0, hdle, hw⟩ := steer_bounds hε hε' hlow hθ
  have hd1 : steer A B θ ≤ 1 := by linarith
  have hFpos : 0 < prof A B θ := by
    have := hlow θ
    have := inv_gt hε hε'
    linarith
  refine le_Pop_of_normResidual_nonneg (m := ε⁻¹ - ε) (m_gt_one hε hε') hprof hθ ?_
  have hterm : B * Real.cos θ / prof A B θ = B * Real.cos θ * (1 / prof A B θ) := by
    field_simp
  rw [normResidual, hterm]
  refine normalized_nonneg_of_bounds (eps := ε) (dd := steer A B θ ^ 2)
    (PhiBounds.abs_Phi0_add_le hd0 hd1) (PhiBounds.Phi1_le hd0)
    (PhiBounds.abs_Phi2_le hd0 hd1) (abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
    (by positivity) hw ?_ hε hε' rfl
  nlinarith [hd0.le, hdle]

/-- **The upper barrier is a supersolution**: `𝒫 f_ε^+ ≤ f_ε^+` on `(0, π)` for
`0 < ε ≤ 1/10`. -/
theorem Pop_le_fPlus (hε : 0 < ε) (hε' : ε ≤ 1 / 10) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    Pop (Barriers.fPlus ε) θ ≤ Barriers.fPlus ε θ := by
  have hprof := profile_fPlus hε
  rw [fPlus_eq] at hprof ⊢
  set A : ℝ := ε⁻¹ + 2 / 3 + 2 * ε
  set B : ℝ := ε - 2 / 3
  have hlow : ∀ t, ε⁻¹ - ε ≤ prof A B t := hprof.lower
  obtain ⟨hd0, hdle, hw⟩ := steer_bounds hε hε' hlow hθ
  have hd1 : steer A B θ ≤ 1 := by linarith
  have hFpos : 0 < prof A B θ := by
    have := hlow θ
    have := inv_gt hε hε'
    linarith
  refine Pop_le_of_normResidual_nonpos (m := ε⁻¹ - ε) (m_gt_one hε hε') hprof hθ ?_
  have hterm : B * Real.cos θ / prof A B θ = B * Real.cos θ * (1 / prof A B θ) := by
    field_simp
  rw [normResidual, hterm]
  refine normalized_nonpos_of_bounds (eps := ε) (dd := steer A B θ ^ 2)
    (PhiBounds.abs_Phi0_add_le hd0 hd1) (PhiBounds.Phi1_ge hd0)
    (PhiBounds.abs_Phi2_le hd0 hd1) (abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
    (by positivity) hw ?_ hε hε' rfl
  nlinarith [hd0.le, hdle]

/-! ### The profile of the translating hairpin -/

/-- **The profile of the translating hairpin exists.**  For every
`0 < ε ≤ 1/10` there is a profile `f`, continuous on `(0, π)` and trapped
between the two explicit barriers, which satisfies the translator equation
`D_f(θ) = arctan (sin θ / f(θ))`, where `D_f(θ)` is the shift determined by
`∫_θ^{θ + D_f(θ)} f = sin θ`.  This is the analytic content of the theorem
*Translating hairpin*. -/
theorem exists_hairpin_profile (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    ∃ f : ℝ → ℝ, Measurable f ∧
      (∀ t, Barriers.fMinus ε t ≤ f t) ∧ (∀ t, f t ≤ Barriers.fPlus ε t) ∧
      ContinuousOn f (Ioo 0 π) ∧
      (∀ θ ∈ Ioo 0 π, θ + shift f θ ∈ Ioo θ π) ∧
      (∀ θ ∈ Ioo 0 π, (∫ t in θ..(θ + shift f θ), f t) = Real.sin θ) ∧
      (∀ θ ∈ Ioo 0 π, shift f θ = Real.arctan (Real.sin θ / f θ)) ∧
      (∀ θ ∈ Ioo 0 π, f θ = Real.sin θ *
        (Real.cos (shift f θ) / Real.sin (shift f θ))) := by
  obtain ⟨f, hprof, hfl, hfu, hcont, hfix, hint, harctan⟩ :=
    exists_translator_profile (m := ε⁻¹ - ε) (M := ε⁻¹ + 4 / 3 + 3 * ε)
      (low := Barriers.fMinus ε) (up := Barriers.fPlus ε) (m_gt_one hε hε')
      (by rw [fMinus_eq]; exact continuous_prof _ _)
      (profile_fMinus hε hε') (profile_fPlus hε)
      (fun t => Barriers.fMinus_le_fPlus hε t)
      (fun θ hθ => fMinus_le_Pop hε hε' hθ)
      (fun θ hθ => Pop_le_fPlus hε hε' hθ)
  refine ⟨f, hprof.meas, hfl, hfu, hcont, ?_, hint, harctan, fun θ hθ => hfix θ hθ⟩
  intro θ hθ
  have hmem := massTime_mem hprof (m_gt_one hε hε') hθ
  simpa [TranslatorOperator.shift] using hmem

end Numeric

end BarrierEstimates
