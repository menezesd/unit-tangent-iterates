import Mathlib
import UnitTangentIterates.CurvatureStabilityL1
import UnitTangentIterates.ShadowingTails

/-!
# Summability of the model defect sequence

The closing argument of `MainTheoremModelL1.lean` asks for the defect sequence

`n ↦ l1Modulus M εₙ Pₙ · (2Hₙ)² (1 + kb·2Hₙ)`

to be summable, `εₙ` being the `L¹` defect of the matching theorem at the `n`-th
step.  For the model pseudo-orbit that hypothesis is not an extra assumption:
the matching theorem gives `εₙ ≤ C e^{−βHₙ}` and the separations grow at least
linearly along the recursion (`ModelPeriodGrowth.lean`), so the whole sequence
decays geometrically, the polynomial factor `(2Hₙ)²(1 + 2kb Hₙ)` being absorbed
by a quarter of the exponential.

Main results:

* `pow_mul_exp_neg_le` — the elementary bound `xᵏ e^{−γx} ≤ (k/γ)ᵏ` for `x ≥ 0`;
* `l1Modulus_le_of_exp` — both branches of `l1Modulus` are dominated by
  `e^{−(β/2)H}` when the `L¹` defect is and the period is bounded below;
* `summable_exp_neg_of_growth` — geometric summability of `e^{−γHₙ}` for
  separations growing at least linearly;
* `model_defect_le` — the pointwise bound `modelDefectConst · e^{−(β/4)Hₙ}` for one
  term of the defect sequence;
* `summable_model_defect` — the summability the closing argument asks for;
* `tail_model_defect_le` — an explicit bound for the *total* defect,
  `modelDefectConst · e^{−(β/4)H₀}/(1 − e^{−(β/4)Δ})`, which is the quantity the
  width gap of the closing argument has to beat.
-/

noncomputable section

open Set Function CurvatureStabilityL1

namespace ModelDefectSummable

/-! ### Polynomials against exponentials -/

/-- **`xᵏ e^{−γx} ≤ (k/γ)ᵏ` for `x ≥ 0` and `γ > 0`.**  A polynomial factor is
absorbed by any exponential decay. -/
theorem pow_mul_exp_neg_le {gamma x : ℝ} {k : ℕ} (hk : 0 < k) (hgamma : 0 < gamma)
    (hx : 0 ≤ x) : x ^ k * Real.exp (-(gamma * x)) ≤ ((k : ℝ) / gamma) ^ k := by
  have hkR : (0:ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hb : gamma * x / k ≤ Real.exp (gamma * x / k) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  have hnn : (0:ℝ) ≤ gamma * x / k := by positivity
  have h1 : (gamma * x / k) ^ k ≤ Real.exp (gamma * x) := by
    calc (gamma * x / k) ^ k ≤ (Real.exp (gamma * x / k)) ^ k := by
          exact pow_le_pow_left₀ hnn hb k
      _ = Real.exp (gamma * x) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hkey : ((k : ℝ) / gamma) ^ k * (gamma * x / k) ^ k = x ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  have h2 : x ^ k ≤ ((k : ℝ) / gamma) ^ k * Real.exp (gamma * x) := by
    rw [← hkey]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  calc x ^ k * Real.exp (-(gamma * x))
      ≤ (((k : ℝ) / gamma) ^ k * Real.exp (gamma * x)) * Real.exp (-(gamma * x)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = ((k : ℝ) / gamma) ^ k := by
        rw [mul_assoc, ← Real.exp_add]
        simp

/-! ### The two branches of the `L¹` modulus -/

/-- **The `L¹` modulus of an exponentially small defect.**  If the `L¹` defect
over a window of length at least `P₀` is at most `C e^{−βH}`, then
`l1Modulus M ε P ≤ (√(2MC) + 4C/P₀)·e^{−(β/2)H}`. -/
theorem l1Modulus_le_of_exp {M eps Cm P0 Pp beta H : ℝ} (hbeta : 0 ≤ beta) (hM : 0 ≤ M)
    (hCm : 0 ≤ Cm) (heps0 : 0 ≤ eps) (hepsb : eps ≤ Cm * Real.exp (-(beta * H)))
    (hP0 : 0 < P0) (hPp : P0 ≤ Pp) (hH : 0 ≤ H) :
    l1Modulus M eps Pp
      ≤ (Real.sqrt (2 * M * Cm) + 4 * Cm / P0) * Real.exp (-(beta / 2) * H) := by
  have hE2 : (0:ℝ) < Real.exp (-(beta / 2) * H) := Real.exp_pos _
  have hsqc : (0:ℝ) ≤ Real.sqrt (2 * M * Cm) := Real.sqrt_nonneg _
  have hdiv : (0:ℝ) ≤ 4 * Cm / P0 := by positivity
  have hhalf : Real.exp (-(beta * H)) ≤ Real.exp (-(beta / 2) * H) :=
    Real.exp_le_exp.mpr (by nlinarith)
  refine max_le ?_ ?_
  · have hstep : 2 * M * eps ≤ (2 * M * Cm) * Real.exp (-(beta * H)) := by
      have : 2 * M * eps ≤ 2 * M * (Cm * Real.exp (-(beta * H))) := by
        exact mul_le_mul_of_nonneg_left hepsb (by positivity)
      nlinarith [Real.exp_pos (-(beta * H))]
    have hsq : Real.sqrt (2 * M * eps)
        ≤ Real.sqrt (2 * M * Cm) * Real.exp (-(beta / 2) * H) := by
      have h1 : Real.sqrt (2 * M * eps)
          ≤ Real.sqrt ((2 * M * Cm) * Real.exp (-(beta * H))) := Real.sqrt_le_sqrt hstep
      have h2 : Real.sqrt ((2 * M * Cm) * Real.exp (-(beta * H)))
          = Real.sqrt (2 * M * Cm) * Real.exp (-(beta / 2) * H) := by
        rw [Real.sqrt_mul (by positivity)]
        congr 1
        have hsq2 : (Real.exp (-(beta / 2) * H)) ^ 2 = Real.exp (-(beta * H)) := by
          rw [sq, ← Real.exp_add]; ring_nf
        rw [← hsq2, Real.sqrt_sq (Real.exp_pos _).le]
      exact le_trans h1 (le_of_eq h2)
    nlinarith [hE2.le]
  · have h1 : 4 * eps / Pp ≤ 4 * (Cm * Real.exp (-(beta / 2) * H)) / P0 := by
      have hnum : 4 * eps ≤ 4 * (Cm * Real.exp (-(beta / 2) * H)) := by
        nlinarith [Real.exp_pos (-(beta * H))]
      have hPppos : 0 < Pp := lt_of_lt_of_le hP0 hPp
      rw [div_le_div_iff₀ hPppos hP0]
      nlinarith [Real.exp_pos (-(beta / 2) * H), heps0, hP0.le, hPp]
    have h2 : 4 * (Cm * Real.exp (-(beta / 2) * H)) / P0
        = (4 * Cm / P0) * Real.exp (-(beta / 2) * H) := by ring
    rw [h2] at h1
    nlinarith [hE2.le]

/-! ### Geometric summability of the separations -/

/-- **Exponentials of linearly growing separations are summable.** -/
theorem summable_exp_neg_of_growth {gamma H0 Delta : ℝ} {Hs : ℕ → ℝ}
    (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hgrow : ∀ n : ℕ, H0 + n * Delta ≤ Hs n) :
    Summable (fun n : ℕ => Real.exp (-(gamma * Hs n))) := by
  set q : ℝ := Real.exp (-(gamma * Delta)) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hqdef]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hgeo : Summable (fun n : ℕ => Real.exp (-(gamma * H0)) * q ^ n) :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  refine hgeo.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
  have hstep : Real.exp (-(gamma * Hs n)) ≤ Real.exp (-(gamma * (H0 + n * Delta))) :=
    Real.exp_le_exp.mpr (by nlinarith [hgrow n])
  have hval : Real.exp (-(gamma * (H0 + n * Delta)))
      = Real.exp (-(gamma * H0)) * q ^ n := by
    rw [hqdef, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [← hval]
  exact hstep

/-! ### The defect sequence of the model orbit -/

/-- The constant of the pointwise defect bound: the two branches of the `L¹`
modulus against the two powers of the separation. -/
def modelDefectConst (M kb Cm P0 beta : ℝ) : ℝ :=
  4 * (Real.sqrt (2 * M * Cm) + 4 * Cm / P0) * ((2 : ℝ) / (beta / 4)) ^ 2
    + 8 * (Real.sqrt (2 * M * Cm) + 4 * Cm / P0) * kb * ((3 : ℝ) / (beta / 4)) ^ 3

theorem modelDefectConst_nonneg {M kb Cm P0 beta : ℝ} (hCm : 0 ≤ Cm)
    (hkb : 0 ≤ kb) (hP0 : 0 < P0) (hbeta : 0 < beta) :
    0 ≤ modelDefectConst M kb Cm P0 beta := by
  have hA0 : (0:ℝ) ≤ Real.sqrt (2 * M * Cm) + 4 * Cm / P0 :=
    add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have h1 : (0:ℝ) ≤ 4 * (Real.sqrt (2 * M * Cm) + 4 * Cm / P0) * ((2 : ℝ) / (beta / 4)) ^ 2 := by
    positivity
  have h2 : (0:ℝ)
      ≤ 8 * (Real.sqrt (2 * M * Cm) + 4 * Cm / P0) * kb * ((3 : ℝ) / (beta / 4)) ^ 3 := by
    positivity
  rw [modelDefectConst]
  linarith

/-- **The pointwise defect bound.**  With the `L¹` defect exponentially small in
the separation and the window bounded below, the term of the defect sequence is
at most `modelDefectConst · e^{−(β/4)Hₙ}`: a quarter of the exponential absorbs
the polynomial factor coming from the growing perimeters. -/
theorem model_defect_le {M kb Cm P0 beta : ℝ} {Hs eps P : ℕ → ℝ}
    (hbeta : 0 < beta) (hM : 0 ≤ M) (hCm : 0 ≤ Cm) (hkb : 0 ≤ kb)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ P n) (hHnn : ∀ n, 0 ≤ Hs n)
    (heps0 : ∀ n, 0 ≤ eps n) (hepsb : ∀ n, eps n ≤ Cm * Real.exp (-(beta * Hs n))) (n : ℕ) :
    l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))
      ≤ modelDefectConst M kb Cm P0 beta * Real.exp (-(beta / 4 * Hs n)) := by
  set A : ℝ := Real.sqrt (2 * M * Cm) + 4 * Cm / P0 with hAdef
  have hA0 : 0 ≤ A := add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hmod : l1Modulus M (eps n) (P n) ≤ A * Real.exp (-(beta / 2) * Hs n) :=
    l1Modulus_le_of_exp hbeta.le hM hCm (heps0 n) (hepsb n) hP0 (hPle n) (hHnn n)
  have hpoly0 : (0:ℝ) ≤ (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)) := by
    have h3 : (0:ℝ) ≤ 1 + kb * (2 * Hs n) := by
      have : (0:ℝ) ≤ kb * (2 * Hs n) := by have := hHnn n; positivity
      linarith
    positivity
  have hstep1 : l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))
      ≤ (A * Real.exp (-(beta / 2) * Hs n)) * ((2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) := by
    calc l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))
        = l1Modulus M (eps n) (P n) * ((2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) := by ring
      _ ≤ (A * Real.exp (-(beta / 2) * Hs n)) * ((2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) :=
          mul_le_mul_of_nonneg_right hmod hpoly0
  have hsplit : Real.exp (-(beta / 2) * Hs n)
      = Real.exp (-(beta / 4 * Hs n)) * Real.exp (-(beta / 4 * Hs n)) := by
    rw [← Real.exp_add]; ring_nf
  have hp2 : (Hs n) ^ 2 * Real.exp (-(beta / 4 * Hs n)) ≤ ((2 : ℝ) / (beta / 4)) ^ 2 := by
    have := pow_mul_exp_neg_le (gamma := beta / 4) (x := Hs n) (k := 2)
      (by norm_num) (by linarith) (hHnn n)
    simpa using this
  have hp3 : (Hs n) ^ 3 * Real.exp (-(beta / 4 * Hs n)) ≤ ((3 : ℝ) / (beta / 4)) ^ 3 := by
    have := pow_mul_exp_neg_le (gamma := beta / 4) (x := Hs n) (k := 3)
      (by norm_num) (by linarith) (hHnn n)
    simpa using this
  have hEpos : (0:ℝ) < Real.exp (-(beta / 4 * Hs n)) := Real.exp_pos _
  have hexpand : (A * Real.exp (-(beta / 2) * Hs n))
        * ((2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)))
      = (4 * A * ((Hs n) ^ 2 * Real.exp (-(beta / 4 * Hs n)))
          + 8 * A * kb * ((Hs n) ^ 3 * Real.exp (-(beta / 4 * Hs n))))
        * Real.exp (-(beta / 4 * Hs n)) := by
    rw [hsplit]; ring
  rw [hexpand] at hstep1
  refine le_trans hstep1 ?_
  have hcoef : 4 * A * ((Hs n) ^ 2 * Real.exp (-(beta / 4 * Hs n)))
      + 8 * A * kb * ((Hs n) ^ 3 * Real.exp (-(beta / 4 * Hs n)))
      ≤ modelDefectConst M kb Cm P0 beta := by
    rw [modelDefectConst, ← hAdef]
    have h1 : 4 * A * ((Hs n) ^ 2 * Real.exp (-(beta / 4 * Hs n)))
        ≤ 4 * A * ((2 : ℝ) / (beta / 4)) ^ 2 :=
      mul_le_mul_of_nonneg_left hp2 (by positivity)
    have h2 : 8 * A * kb * ((Hs n) ^ 3 * Real.exp (-(beta / 4 * Hs n)))
        ≤ 8 * A * kb * ((3 : ℝ) / (beta / 4)) ^ 3 :=
      mul_le_mul_of_nonneg_left hp3 (by positivity)
    linarith
  exact mul_le_mul_of_nonneg_right hcoef hEpos.le

/-- **The defect sequence of the model pseudo-orbit is summable.**  With the
`L¹` defect exponentially small in the separation, the period bounded below and
the separations growing at least linearly, the sequence

`n ↦ l1Modulus M εₙ Pₙ · (2Hₙ)² (1 + kb·2Hₙ)`

is summable. -/
theorem summable_model_defect {M kb Cm P0 H0 Delta beta : ℝ} {Hs eps P : ℕ → ℝ}
    (hbeta : 0 < beta) (hDelta : 0 < Delta) (hM : 0 ≤ M) (hCm : 0 ≤ Cm) (hkb : 0 ≤ kb)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ P n)
    (hHnn : ∀ n, 0 ≤ Hs n) (hgrow : ∀ n : ℕ, H0 + n * Delta ≤ Hs n)
    (heps0 : ∀ n, 0 ≤ eps n) (hepsb : ∀ n, eps n ≤ Cm * Real.exp (-(beta * Hs n))) :
    Summable (fun n : ℕ =>
      l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) := by
  have hcomp : Summable (fun n : ℕ =>
      modelDefectConst M kb Cm P0 beta * Real.exp (-(beta / 4 * Hs n))) :=
    (summable_exp_neg_of_growth (gamma := beta / 4) (by linarith) hDelta hgrow).mul_left _
  refine hcomp.of_nonneg_of_le (fun n => ?_) (fun n =>
    model_defect_le hbeta hM hCm hkb hP0 hPle hHnn heps0 hepsb n)
  have h1 : (0:ℝ) ≤ l1Modulus M (eps n) (P n) := l1Modulus_nonneg _ _ _
  have h3 : (0:ℝ) ≤ 1 + kb * (2 * Hs n) := by
    have : (0:ℝ) ≤ kb * (2 * Hs n) := by have := hHnn n; positivity
    linarith
  positivity

/-- **An explicit bound for the total defect.**  The whole tail of the defect
sequence is at most `modelDefectConst · e^{−(β/4)H₀}/(1 − e^{−(β/4)Δ})`, a
quantity that tends to `0` as the initial separation grows. -/
theorem tail_model_defect_le {M kb Cm P0 H0 Delta beta : ℝ} {Hs eps P : ℕ → ℝ}
    (hbeta : 0 < beta) (hDelta : 0 < Delta) (hM : 0 ≤ M) (hCm : 0 ≤ Cm) (hkb : 0 ≤ kb)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ P n)
    (hHnn : ∀ n, 0 ≤ Hs n) (hgrow : ∀ n : ℕ, H0 + n * Delta ≤ Hs n)
    (heps0 : ∀ n, 0 ≤ eps n) (hepsb : ∀ n, eps n ≤ Cm * Real.exp (-(beta * Hs n))) :
    ShadowingTails.tail
        (fun n : ℕ => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) 0
      ≤ modelDefectConst M kb Cm P0 beta * Real.exp (-(beta / 4 * H0))
        / (1 - Real.exp (-(beta / 4 * Delta))) := by
  set C : ℝ := modelDefectConst M kb Cm P0 beta with hCdef
  have hC0 : 0 ≤ C := modelDefectConst_nonneg hCm hkb hP0 hbeta
  set q : ℝ := Real.exp (-(beta / 4 * Delta)) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hqdef]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  -- the termwise geometric bound
  have hterm : ∀ n : ℕ,
      l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))
        ≤ (C * Real.exp (-(beta / 4 * H0))) * q ^ n := by
    intro n
    refine le_trans (model_defect_le hbeta hM hCm hkb hP0 hPle hHnn heps0 hepsb n) ?_
    have hstep : Real.exp (-(beta / 4 * Hs n)) ≤ Real.exp (-(beta / 4 * (H0 + n * Delta))) :=
      Real.exp_le_exp.mpr (by nlinarith [hgrow n])
    have hval : Real.exp (-(beta / 4 * (H0 + n * Delta)))
        = Real.exp (-(beta / 4 * H0)) * q ^ n := by
      rw [hqdef, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    calc C * Real.exp (-(beta / 4 * Hs n))
        ≤ C * (Real.exp (-(beta / 4 * H0)) * q ^ n) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          rw [← hval]; exact hstep
      _ = (C * Real.exp (-(beta / 4 * H0))) * q ^ n := by ring
  have hgeo : Summable (fun n : ℕ => (C * Real.exp (-(beta / 4 * H0))) * q ^ n) :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  have hnn : ∀ n : ℕ,
      0 ≤ l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)) := by
    intro n
    have h1 : (0:ℝ) ≤ l1Modulus M (eps n) (P n) := l1Modulus_nonneg _ _ _
    have h3 : (0:ℝ) ≤ 1 + kb * (2 * Hs n) := by
      have : (0:ℝ) ≤ kb * (2 * Hs n) := by have := hHnn n; positivity
      linarith
    positivity
  have hsum : Summable (fun n : ℕ =>
      l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) :=
    hgeo.of_nonneg_of_le hnn hterm
  have hle : (∑' n : ℕ, l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)))
      ≤ ∑' n : ℕ, (C * Real.exp (-(beta / 4 * H0))) * q ^ n :=
    hsum.tsum_le_tsum hterm hgeo
  have hgeoval : (∑' n : ℕ, (C * Real.exp (-(beta / 4 * H0))) * q ^ n)
      = C * Real.exp (-(beta / 4 * H0)) / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
    ring
  have htail : ShadowingTails.tail
      (fun n : ℕ => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) 0
      = ∑' n : ℕ, l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)) := by
    simp [ShadowingTails.tail]
  rw [htail]
  exact le_trans hle (le_of_eq hgeoval)

end ModelDefectSummable
