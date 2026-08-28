import UnitTangentIterates.CanonicalConfiguredModelCapstone
import UnitTangentIterates.DataInterior
import UnitTangentIterates.HairpinPulseBarrier
import UnitTangentIterates.MatchConstNonneg
import UnitTangentIterates.CurvFieldDerivBound
import UnitTangentIterates.PulseRelativeFromIdentity

/-!
# The configured model sequence from interior data

This composes the two endpoint-free constructions:

* `PaperHairpinQuantitativeData.consecutiveData_of_interior`, which builds the
  consecutive quantitative package from the regularity the paper actually
  proves — `f ∈ C^∞(0,π)`, with **no endpoint values assigned** — and

* `CanonicalConfiguredModelCapstone.exists_configuredModelSequence_with_step`,
  now localized to the same hypotheses,

into a single statement running from the paper's hypotheses to a configured
model sequence together with the **summable** step defects.

The significance is that no step of this chain asks for the profile to extend
smoothly across `0` or `π`.  That extension is not available: the paper does
not assign endpoint values, and a profile smooth on the open interval need not
extend (`f(t) = 2 + sin(1/t)`).  Every appeal to the closed interval `[0, π]`
— the compactness extraction of `min f` and `max f` in the lower comparison,
and the smoothness of the curvature along the angle — has been replaced by the
paper's own barrier bounds on `(0, π)`.
-/

noncomputable section

open Set Real

open scoped ContDiff

namespace UnitTangentIterates.CanonicalConfiguredModelCapstone

open ShiftedCurvatureJetMajorant PaperHairpinQuantitativeData
open PaperHairpinConfig ModelPeriodContinuity ModelOrbitDefect
open PaperHairpinQuantitativeData.ConsecutiveData
open HairpinRelative

/-- **From the paper's interior hypotheses to a configured model sequence with
summable defects.**  The profile is smooth and positive only on `(0, π)`; the
two barriers `m ≤ f ≤ Am` there are the paper's own. -/
theorem exists_configuredModelSequence_of_interior
    {f g gp : ℝ → ℝ} {theta x : ℝ → ℝ} {m Am A M D1 : ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 b : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am) (hmA : m ≤ Am)
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
        ≤ relativeConst j * pulseField f (theta (x s)))
    (translator : TranslatorData f g gp)
    (hD1 : 0 ≤ D1)
    (hrelK : ∀ u, |deriv (fun r => curvField f (theta r)) u| ≤
      D1 * curvField f (theta u))
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha)
    (hdec0 : ∀ s, |pulseField f (theta (x s))| ≤ C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s,
      |iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s| ≤
        C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |ConsecutiveData.phase f theta g|) ≤ CU)
    (hD : relativeConst 1 ≤ D)
    (hDU : relativeConst 1 ≤ DU)
    (hDU2 : relativeConst 2 ≤ DU2)
    (hb0 : 0 ≤ b) (hbmin : b < min a au)
    (hsup : ∀ s, pulseField f (theta (x s)) ≤ b)
    (hB : (1 + b) / 2 * Real.pi ≤ B)
    (hkd0 : 0 ≤ kd)
    (hmatch0 : 0 ≤ matchConst a C CK CU DU Km Kd au alpha beta B) :
    ∃ (Hs : ℕ → ℝ) (kappas : ℕ → ℝ → ℝ) (deltaStep : ℝ),
      0 < deltaStep ∧
      (∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n) ∧
      (∀ n, Hs n + deltaStep ≤ Hs (n + 1)) ∧
      (∀ n, Hs n < Hs (n + 1)) ∧
      (∀ n, rearPeriod (fun s => pulseField f (theta (x s))) (Hs (n + 1)) = Hs n) ∧
      ∃ model : UnconditionalAssembly.ConfiguredModelSequence
          kappas Hs (fun _ => eps0),
        model.kstar = kstar ∧ model.kd = kd ∧
        (∀ n, ContDiff ℝ 3
          (modelCurvature (model.configs n).yu (model.configs n).yu' (Hs n))) ∧
        (∀ n, ContDiff ℝ 3 (model.configs n).kH) ∧
        Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B *
            Real.exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hl : ∀ t, m ≤ f (theta t) := fun t => hlow _ (hmem t)
  have hu : ∀ t, f (theta t) ≤ Am := fun t => hupp _ (hmem t)
  exact exists_configuredModelSequence_with_step (theta0 := theta0)
    (consecutiveData_of_interior hf hm hlow hmem hval hderiv hxinv hw hsm hsurj
      hA hM hdecay relativeConst hrc0 hrel translator)
    d hf hfpos hM hD1 hdecay hrelK hm hmA hl hu profile heps halpha
    hdec0 hdec1 hCU hD hDU hDU2 hb0 hbmin hsup hB hkd0 hmatch0

/-- **The same conclusion with the pulse hypotheses discharged.**

Three of the analytic hypotheses of `exists_configuredModelSequence_of_interior`
are not independent assumptions: they follow from the data the interior route
already carries.

* the order-zero and order-one exponential tails `hdec0`, `hdec1` are the cases
  `j = 0, 1` of the tail field of `data_of_interior`, which the interior route
  derives from the order-zero curvature tail and the relative bounds;
* the uniform bound `sup y ≤ b` follows from the paper's own lower barrier
  `f ≥ m`, which forces `y ≤ 1/√(1+m²) < 1`.

What is left for the caller is only to place the constants: `C` above the two
tail constants, `alpha` no larger than `1/M`, and `b` between the barrier bound
and `min a au`. -/
theorem exists_configuredModelSequence_of_interior_barrier
    {f g gp : ℝ → ℝ} {theta x : ℝ → ℝ} {m Am A M Dp : ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 b : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am) (hmA : m ≤ Am)
    (hdb : ∀ t ∈ Ioo (0:ℝ) π, |deriv (pulseField f) t| ≤ Dp)
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
        ≤ relativeConst j * pulseField f (theta (x s)))
    (translator : TranslatorData f g gp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha) (halphaM : alpha ≤ 1 / M)
    (hC0 : relativeConst 0 * (A * Real.exp (A ^ 2 / 2)) ≤ C)
    (hC1 : relativeConst 1 * (A * Real.exp (A ^ 2 / 2)) ≤ C)
    (hCU : C * Real.exp (alpha * |ConsecutiveData.phase f theta g|) ≤ CU)
    (hD : relativeConst 1 ≤ D)
    (hDU : relativeConst 1 ≤ DU)
    (hDU2 : relativeConst 2 ≤ DU2)
    (hb0 : 0 ≤ b) (hbmin : b < min a au)
    (hbarrier : 1 / Real.sqrt (1 + m ^ 2) ≤ b)
    (hB : (1 + b) / 2 * Real.pi ≤ B)
    (hkd0 : 0 ≤ kd) :
    ∃ (Hs : ℕ → ℝ) (kappas : ℕ → ℝ → ℝ) (deltaStep : ℝ),
      0 < deltaStep ∧
      (∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n) ∧
      (∀ n, Hs n + deltaStep ≤ Hs (n + 1)) ∧
      (∀ n, Hs n < Hs (n + 1)) ∧
      (∀ n, rearPeriod (fun s => pulseField f (theta (x s))) (Hs (n + 1)) = Hs n) ∧
      ∃ model : UnconditionalAssembly.ConfiguredModelSequence
          kappas Hs (fun _ => eps0),
        model.kstar = kstar ∧ model.kd = kd ∧
        (∀ n, ContDiff ℝ 3
          (modelCurvature (model.configs n).yu (model.configs n).yu' (Hs n))) ∧
        (∀ n, ContDiff ℝ 3 (model.configs n).kH) ∧
        Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B *
            Real.exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  have hfpos' : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hbb : (1:ℝ) / Real.sqrt (1 + m ^ 2) < 1 :=
    one_div_sqrt_one_add_sq_lt_one hm
  have hbb0 : (0:ℝ) ≤ 1 / Real.sqrt (1 + m ^ 2) := by positivity
  have hyb : ∀ t ∈ Ioo (0:ℝ) π,
      |pulseField f t| ≤ 1 / Real.sqrt (1 + m ^ 2) := by
    intro t ht
    rw [abs_of_nonneg (pulseField_nonneg_interior hfpos' ht)]
    exact pulseField_le_of_barrier hm (hlow t ht) ht
  have hDp0 : 0 ≤ Dp := le_trans (abs_nonneg _) (hdb _ (hmem 0))
  have hD1 : (0:ℝ) ≤ Dp / Real.sqrt (1 - (1 / Real.sqrt (1 + m ^ 2)) ^ 2) ^ 3 := by
    positivity
  have hrelK := relK_of_pulse_deriv_bound hf hfpos' hbb0 hbb hyb hdb hmem hderiv
  have hC : 0 ≤ C :=
    le_trans (mul_nonneg (hrc0 0) (by positivity)) hC0
  have hCU0 : 0 ≤ CU :=
    le_trans (mul_nonneg hC (Real.exp_pos _).le) hCU
  have hmatch0 : 0 ≤ matchConst a C CK CU DU Km Kd au alpha beta B :=
    PaperHairpinConfig.matchConst_nonneg profile halpha hC hCU0
  have hdecayJ : ∀ j ≤ 4, ∀ s : ℝ,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s| ≤
        relativeConst j * (A * Real.exp (A ^ 2 / 2)) * Real.exp (-|s| / M) :=
    fun j hj s => (data_of_interior hf hm hlow hmem hval hderiv hxinv hw hsm
      hsurj hA hM hdecay relativeConst hrc0 hrel).decay j hj s
  have hexp : ∀ s : ℝ, Real.exp (-|s| / M) ≤ Real.exp (-alpha * |s|) := by
    intro s
    apply Real.exp_le_exp.mpr
    have h1 : alpha * |s| ≤ 1 / M * |s| :=
      mul_le_mul_of_nonneg_right halphaM (abs_nonneg s)
    have h2 : -|s| / M = -(1 / M * |s|) := by ring
    rw [h2]
    linarith [h1]
  have hstep : ∀ j : ℕ, j ≤ 4 → relativeConst j * (A * Real.exp (A ^ 2 / 2)) ≤ C →
      ∀ s : ℝ, |iteratedDeriv j (fun r => pulseField f (theta (x r))) s| ≤
        C * Real.exp (-alpha * |s|) := by
    intro j hj hle s
    have hD0 : 0 ≤ relativeConst j * (A * Real.exp (A ^ 2 / 2)) :=
      mul_nonneg (hrc0 j) (by positivity)
    exact le_trans (hdecayJ j hj s)
      (mul_le_mul hle (hexp s) (Real.exp_pos _).le (le_trans hD0 hle))
  have hdec0 : ∀ s, |pulseField f (theta (x s))| ≤ C * Real.exp (-alpha * |s|) := by
    intro s
    have h := hstep 0 (by norm_num) hC0 s
    rwa [iteratedDeriv_zero] at h
  have hdec1 : ∀ s,
      |iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s| ≤
        C * Real.exp (-alpha * |s|) := hstep 1 (by norm_num) hC1
  have hsup : ∀ s, pulseField f (theta (x s)) ≤ b := fun s =>
    le_trans (pulseField_le_of_barrier hm (hlow _ (hmem (x s))) (hmem (x s)))
      hbarrier
  exact exists_configuredModelSequence_of_interior (theta0 := theta0)
    hf hm hlow hupp hmA hmem hval hderiv hxinv hw hsm hsurj hA hM hdecay
    relativeConst hrc0 hrel translator hD1 hrelK d profile heps halpha
    hdec0 hdec1 hCU hD hDU hDU2 hb0 hbmin hsup hB hkd0 hmatch0
