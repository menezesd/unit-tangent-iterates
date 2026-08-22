import Mathlib
import UnitTangentIterates.MainTheoremModelL1
import UnitTangentIterates.ModelDefectSummable

/-!
# The closing argument with the summability of the defects produced

`MainTheoremModelL1.main_theorem_of_model_of_L1_curvature` runs the closing step
of *A Noncircular Oval with Convex Unit-Tangent Iterates* with the defect
estimate given as an `L¹` comparison of the curvatures, and asks the caller for
the summability of the resulting defect sequence

`n ↦ l1Modulus M εₙ Pₙ · (2Hₙ)² (1 + kb·2Hₙ)`.

For the model pseudo-orbit that hypothesis is not independent of the rest: the
matching theorem gives `εₙ ≤ C e^{−βHₙ}` and the separations of the recursion
grow at least linearly, so `ModelDefectSummable.summable_model_defect` supplies
the summability.  This file substitutes it, so that what is asked about the
defects is only their exponential decay and the linear growth of the
separations.

What is still **not** supplied is the comparison itself — that each model is
close to the selected inverse of the next — nor the non-expansiveness of the
selected inverse; the paper's main theorem is therefore **not** formalized.
-/

noncomputable section

open Set Function CurvatureStabilityL1

namespace MarkedSpace

open ModelDefectSummable

/-- **The closing argument with the summability of the defect sequence
produced.**  Same as `MainTheoremModelL1.main_theorem_of_model_of_L1_curvature`,
with the hypothesis `Summable (fun n => l1Modulus M εₙ Pₙ · (2Hₙ)²(1 + kb·2Hₙ))`
replaced by the exponential decay `εₙ ≤ C e^{−βHₙ}` of the `L¹` defects, a lower
bound `P₀ > 0` for the windows and the linear growth `H₀ + nΔ ≤ Hₙ` of the
separations. -/
theorem main_theorem_of_model_of_L1_exp {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap dlt Cw Csh kb M : ℝ} {eps cw P : ℕ → ℝ} {dir : ℂ}
    {Cm P0 H0 Delta beta : ℝ}
    (hkminpos : 0 < kmin) (hdltpos : 0 < dlt)
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) x
            - TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) y‖)
    {B T : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0)) → tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0)),
      range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data)))))
    (hMpos : 0 < M)
    -- the exponential decay of the defects and the growth of the separations
    (hbeta : 0 < beta) (hDelta : 0 < Delta) (hCm : 0 ≤ Cm) (hkb0 : 0 ≤ kb)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ P n)
    (hgrow : ∀ n : ℕ, H0 + n * Delta ≤ Hs n)
    (heps0 : ∀ n, 0 ≤ eps n) (hepsb : ∀ n, eps n ≤ Cm * Real.exp (-(beta * Hs n)))
    (hdefL1 : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))),
      ev ((p : Data)) = TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) →
      ev ((q : Data)) = TwoCapPairsAssembly.front (kappas (n + 1)) (theta0 (n + 1)) (Hs (n + 1)) →
      perim ((p : Data)) = 2 * Hs n ∧ perim ((B q : Data)) = 2 * Hs n ∧
      ∃ Θp Θq kp kq kp' kq' : ℝ → ℝ,
        (∀ s, HasDerivAt (ev ((p : Data))) (Complex.exp (Complex.I * (Θp s : ℂ))) s) ∧
        (∀ s, HasDerivAt (ev ((B q : Data))) (Complex.exp (Complex.I * (Θq s : ℂ))) s) ∧
        (∀ s, HasDerivAt Θp (kp s) s) ∧ (∀ s, HasDerivAt Θq (kq s) s) ∧
        ev ((p : Data)) 0 = ev ((B q : Data)) 0 ∧ Θp 0 = Θq 0 ∧
        Periodic kp (P n) ∧ Periodic kq (P n) ∧
        (∀ x, HasDerivAt kp (kp' x) x) ∧ (∀ x, HasDerivAt kq (kq' x) x) ∧
        (∀ x, |kp' x| ≤ M / 2) ∧ (∀ x, |kq' x| ≤ M / 2) ∧
        (∫ x in (cw n)..(cw n + P n), |kp x - kq x|) ≤ eps n ∧
        (∀ s, |kq s| ≤ kb))
    (hCsh : 1 ≤ Csh) (hdir : ‖dir‖ = 1)
    (hQw : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail
        (fun n => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) 0)
      < (2 * Hs 0 - Csh * ShadowingTails.tail
        (fun n => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) 0)
          / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  have hsum : Summable (fun n : ℕ =>
      l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) :=
    summable_model_defect hbeta hDelta hMpos.le hCm hkb0 hP0 hPle
      (fun n => (hH n).le) hgrow heps0 hepsb
  exact main_theorem_of_model_of_L1_curvature hkminpos hdltpos hH hmono hk hper hkmin hkap
    htotal hchord hB hBcont hT hTev hMpos (fun n => lt_of_lt_of_le hP0 (hPle n)) hsum
    hdefL1 hCsh hdir hQw hgap

/-- **The closing argument with the width gap tested against the explicit total
defect.**  The gap condition of `main_theorem_of_model_of_L1_exp` involves the
tail of the defect sequence, which is not given in closed form; here it is
replaced by the explicit bound
`modelDefectConst · e^{−(β/4)H₀}/(1 − e^{−(β/4)Δ})` of
`ModelDefectSummable.tail_model_defect_le`, so the gap can be checked from the
constants of the configuration alone. -/
theorem main_theorem_of_model_of_L1_exp_gap {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap dlt Cw Csh kb M : ℝ} {eps cw P : ℕ → ℝ} {dir : ℂ}
    {Cm P0 H0 Delta beta : ℝ}
    (hkminpos : 0 < kmin) (hdltpos : 0 < dlt)
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) x
            - TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) y‖)
    {B T : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0)) → tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0)),
      range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data)))))
    (hMpos : 0 < M)
    (hbeta : 0 < beta) (hDelta : 0 < Delta) (hCm : 0 ≤ Cm) (hkb0 : 0 ≤ kb)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ P n)
    (hgrow : ∀ n : ℕ, H0 + n * Delta ≤ Hs n)
    (heps0 : ∀ n, 0 ≤ eps n) (hepsb : ∀ n, eps n ≤ Cm * Real.exp (-(beta * Hs n)))
    (hdefL1 : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))),
      ev ((p : Data)) = TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) →
      ev ((q : Data)) = TwoCapPairsAssembly.front (kappas (n + 1)) (theta0 (n + 1)) (Hs (n + 1)) →
      perim ((p : Data)) = 2 * Hs n ∧ perim ((B q : Data)) = 2 * Hs n ∧
      ∃ Θp Θq kp kq kp' kq' : ℝ → ℝ,
        (∀ s, HasDerivAt (ev ((p : Data))) (Complex.exp (Complex.I * (Θp s : ℂ))) s) ∧
        (∀ s, HasDerivAt (ev ((B q : Data))) (Complex.exp (Complex.I * (Θq s : ℂ))) s) ∧
        (∀ s, HasDerivAt Θp (kp s) s) ∧ (∀ s, HasDerivAt Θq (kq s) s) ∧
        ev ((p : Data)) 0 = ev ((B q : Data)) 0 ∧ Θp 0 = Θq 0 ∧
        Periodic kp (P n) ∧ Periodic kq (P n) ∧
        (∀ x, HasDerivAt kp (kp' x) x) ∧ (∀ x, HasDerivAt kq (kq' x) x) ∧
        (∀ x, |kp' x| ≤ M / 2) ∧ (∀ x, |kq' x| ≤ M / 2) ∧
        (∫ x in (cw n)..(cw n + P n), |kp x - kq x|) ≤ eps n ∧
        (∀ s, |kq s| ≤ kb))
    (hCsh : 1 ≤ Csh) (hdir : ‖dir‖ = 1)
    (hQw : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * (ModelDefectSummable.modelDefectConst M kb Cm P0 beta
          * Real.exp (-(beta / 4 * H0)) / (1 - Real.exp (-(beta / 4 * Delta)))))
      < (2 * Hs 0 - Csh * (ModelDefectSummable.modelDefectConst M kb Cm P0 beta
          * Real.exp (-(beta / 4 * H0)) / (1 - Real.exp (-(beta / 4 * Delta))))) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  set S : ℝ := ModelDefectSummable.modelDefectConst M kb Cm P0 beta
    * Real.exp (-(beta / 4 * H0)) / (1 - Real.exp (-(beta / 4 * Delta))) with hSdef
  have htail : ShadowingTails.tail
      (fun n : ℕ => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) 0 ≤ S :=
    ModelDefectSummable.tail_model_defect_le hbeta hDelta hMpos.le hCm hkb0 hP0 hPle
      (fun n => (hH n).le) hgrow heps0 hepsb
  have hCsh0 : (0:ℝ) ≤ Csh := le_trans zero_le_one hCsh
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  refine main_theorem_of_model_of_L1_exp hkminpos hdltpos hH hmono hk hper hkmin hkap htotal
    hchord hB hBcont hT hTev hMpos hbeta hDelta hCm hkb0 hP0 hPle hgrow heps0 hepsb hdefL1
    hCsh hdir hQw ?_
  set t : ℝ := ShadowingTails.tail
    (fun n : ℕ => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) 0 with htdef
  have h1 : Cw + 2 * (Csh * t) ≤ Cw + 2 * (Csh * S) := by nlinarith
  have h2 : (2 * Hs 0 - Csh * S) / Real.pi ≤ (2 * Hs 0 - Csh * t) / Real.pi := by
    gcongr
  linarith

end MarkedSpace
