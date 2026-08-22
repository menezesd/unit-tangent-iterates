import Mathlib
import UnitTangentIterates.MainTheoremModelPerimeter
import UnitTangentIterates.CurvatureStabilityL1

/-!
# The closing argument with the defect estimate given in `L¹`

`MainTheoremModelCurvature.main_theorem_of_model_of_curvature` and
`MainTheoremModelPerimeter.main_theorem_of_model_of_curvature_perim` run the
closing step of *A Noncircular Oval with Convex Unit-Tangent Iterates* with the
defect estimate of the model pseudo-orbit stated on the **curvatures**, but in
the **uniform** norm; the paper's theorem *Curvature-measure matching* produces
instead an `L¹` comparison over one period of the configuration.

This file removes that discrepancy.  `CurvatureStabilityL1.lean` turns an `L¹`
bound `εₙ` over a window of length `Pₙ` into the uniform bound

`l1Modulus M εₙ Pₙ = max (√(2Mεₙ), 4εₙ/Pₙ)`

for two `Pₙ`-periodic curvatures whose derivatives are bounded by `M/2`, and the
two theorems below feed it into the closing argument:

* `main_theorem_of_model_of_L1_curvature` — the selected inverse of the
  `(n+1)`-st model has the same perimeter as the `n`-th model, and the defect
  sequence is `l1Modulus M εₙ Pₙ · (2Hₙ)²(1 + kb·2Hₙ)`;
* `main_theorem_of_model_of_L1_curvature_perim` — the two perimeters differ by
  at most `Dₙ`, and the defect sequence is
  `defectBound (l1Modulus M εₙ Pₙ) Dₙ (2Hₙ + Dₙ) kb kL`.

What is still **not** supplied is the comparison itself — that each model is
close to the selected inverse of the next — nor the non-expansiveness of the
selected inverse; the paper's main theorem is therefore **not** formalized.
-/

noncomputable section

open Set Function CurvatureStabilityL1

namespace MarkedSpace

/-- **The closing argument with the model curves, the defect estimate being
given as an `L¹` comparison of the curvatures.**  Same as
`MainTheoremModelCurvature.main_theorem_of_model_of_curvature`, with the uniform
curvature comparison replaced by the `L¹` comparison
`∫_{cₙ}^{cₙ+Pₙ} |k_p − k_{Bq}| ≤ εₙ` over one period of the two curvatures,
whose derivatives are bounded by `M/2`. -/
theorem main_theorem_of_model_of_L1_curvature {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap dlt Cw Csh kb M : ℝ} {eps cw P : ℕ → ℝ} {dir : ℂ}
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
    (hMpos : 0 < M) (hPpos : ∀ n, 0 < P n)
    (hsum : Summable fun n =>
      l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)))
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
  have hcpos : (0:ℝ) < 2 * Hs 0 := by linarith [hH 0]
  refine main_theorem_of_model hkminpos hdltpos hH hmono hk hper hkmin hkap htotal hchord
    hB hBcont hT hTev hsum ?_ hCsh hdir hQw hgap
  intro n p q hp hq
  obtain ⟨hLp, hLBq, Θp, Θq, kp, kq, kp', kq', hevp, hevq, hΘp, hΘq, hF0, hΘ0, hpp, hpq,
    hdp, hdq, hbp, hbq, hint, hkqb⟩ := hdefL1 n p q hp hq
  have hdist := CurvatureStabilityL1.dist_le_of_L1_curvature_close (cc := 2 * Hs 0)
    hcpos p.2 (B q).2 hLp hLBq hevp hevq hΘp hΘq hF0 hΘ0 (hPpos n) hMpos hpp hpq
    hdp hdq hbp hbq hint hkqb
  simpa [Subtype.dist_eq, l1Modulus] using hdist

/-- **The closing argument with an `L¹` defect estimate and a moving
perimeter.**  Same as
`MainTheoremModelPerimeter.main_theorem_of_model_of_curvature_perim`, with the
uniform curvature comparison replaced by the `L¹` comparison over one period. -/
theorem main_theorem_of_model_of_L1_curvature_perim {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap dlt Cw Csh kb kL M : ℝ} {eps cw P D : ℕ → ℝ} {dir : ℂ}
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
    (hMpos : 0 < M) (hPpos : ∀ n, 0 < P n)
    (hsum : Summable fun n =>
      defectBound (l1Modulus M (eps n) (P n)) (D n) (2 * Hs n + D n) kb kL)
    (hdefL1 : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))),
      ev ((p : Data)) = TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) →
      ev ((q : Data)) = TwoCapPairsAssembly.front (kappas (n + 1)) (theta0 (n + 1)) (Hs (n + 1)) →
      perim ((p : Data)) = 2 * Hs n ∧
      |perim ((p : Data)) - perim ((B q : Data))| ≤ D n ∧
      ∃ Θp Θq kp kq kp' kq' : ℝ → ℝ,
        (∀ s, HasDerivAt (ev ((p : Data))) (Complex.exp (Complex.I * (Θp s : ℂ))) s) ∧
        (∀ s, HasDerivAt (ev ((B q : Data))) (Complex.exp (Complex.I * (Θq s : ℂ))) s) ∧
        (∀ s, HasDerivAt Θp (kp s) s) ∧ (∀ s, HasDerivAt Θq (kq s) s) ∧
        ev ((p : Data)) 0 = ev ((B q : Data)) 0 ∧ Θp 0 = Θq 0 ∧
        Periodic kp (P n) ∧ Periodic kq (P n) ∧
        (∀ x, HasDerivAt kp (kp' x) x) ∧ (∀ x, HasDerivAt kq (kq' x) x) ∧
        (∀ x, |kp' x| ≤ M / 2) ∧ (∀ x, |kq' x| ≤ M / 2) ∧
        (∫ x in (cw n)..(cw n + P n), |kp x - kq x|) ≤ eps n ∧
        (∀ s, |kp s| ≤ kb) ∧ (∀ s, |kq s| ≤ kb) ∧
        (∀ a b, |kq a - kq b| ≤ kL * |a - b|))
    (hCsh : 1 ≤ Csh) (hdir : ‖dir‖ = 1)
    (hQw : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail
        (fun n => defectBound (l1Modulus M (eps n) (P n)) (D n) (2 * Hs n + D n) kb kL) 0)
      < (2 * Hs 0 - Csh * ShadowingTails.tail
        (fun n => defectBound (l1Modulus M (eps n) (P n)) (D n) (2 * Hs n + D n) kb kL) 0)
          / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  have hcpos : (0:ℝ) < 2 * Hs 0 := by linarith [hH 0]
  refine main_theorem_of_model hkminpos hdltpos hH hmono hk hper hkmin hkap htotal hchord
    hB hBcont hT hTev hsum ?_ hCsh hdir hQw hgap
  intro n p q hp hq
  obtain ⟨hLp, hDn, Θp, Θq, kp, kq, kp', kq', hevp, hevq, hΘp, hΘq, hF0, hΘ0, hpp, hpq,
    hdp, hdq, hbp, hbq, hint, hkpb, hkqb, hkqL⟩ := hdefL1 n p q hp hq
  have hD0 : 0 ≤ D n := le_trans (abs_nonneg _) hDn
  have hLple : perim ((p : Data)) ≤ 2 * Hs n + D n := by rw [hLp]; linarith
  have hLqle : perim ((B q : Data)) ≤ 2 * Hs n + D n := by
    have h := abs_le.1 hDn
    rw [hLp] at h
    linarith [h.1]
  have hunif : ∀ s, |kp s - kq s| ≤ l1Modulus M (eps n) (P n) := fun s =>
    CurvatureStabilityL1.abs_sub_le_of_periodic (hPpos n) hMpos hpp hpq hdp hdq hbp hbq hint s
  have hdist := dist_le_of_curvature_close_perim (c := 2 * Hs 0) hcpos p.2 (B q).2
    hLple hLqle hDn hevp hevq hΘp hΘq hF0 hΘ0 (l1Modulus_nonneg M (eps n) (P n))
    hunif hkpb hkqb hkqL
  simpa [Subtype.dist_eq] using hdist

end MarkedSpace
