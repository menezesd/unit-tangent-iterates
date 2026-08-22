import Mathlib
import UnitTangentIterates.MainTheoremModel
import UnitTangentIterates.MarkedDistanceCurvature

/-!
# The closing argument with the defect estimate given on the curvatures

`MainTheoremModel.main_theorem_of_model` runs the closing step of
*A Noncircular Oval with Convex Unit-Tangent Iterates* with the model curves of
the paper, but asks the **defect estimate** in the metric of the space of
marked curves: `dist p (B q) ≤ eₙ`.  The theorem *Curvature-measure matching*,
on the other hand, compares the model with the selected inverse of the next
model through their **curvatures**.

`MarkedDistanceCurvature.dist_le_of_curvature_close` converts the one into the
other, and this file applies the conversion: in
`main_theorem_of_model_of_curvature` the defect hypothesis is

> whenever `p` carries the `n`-th model front and `q` the `(n+1)`-st, the
> selected inverse `B q` has the same perimeter as `p`, is aligned with it in
> position and direction at the marked point, and its curvature differs from
> that of `p` by at most `εₙ`,

with `∑ εₙ (2Hₙ)² (1 + kb·2Hₙ)` summable.  The conclusion is unchanged.

Two restrictions should be kept in mind.  The curvature comparison is asked
here in the **uniform** norm, whereas the paper's matching theorem produces an
`L¹` comparison; and the selected inverse of the `(n+1)`-st model is asked to
have **exactly** the perimeter of the `n`-th model, while in the paper the two
perimeters agree only up to the defect.  Those gaps, and the non-expansiveness
of the selected inverse, remain, so the paper's main theorem is still **not**
formalized.
-/

noncomputable section

open Set Function

namespace MarkedSpace

/-- **The closing argument with the model curves, the defect estimate being
given on the curvatures.**  Same as
`MainTheoremModel.main_theorem_of_model` with the metric defect hypothesis
replaced by a uniform comparison of the curvature of the `n`-th model with that
of the selected inverse of the `(n+1)`-st. -/
theorem main_theorem_of_model_of_curvature {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap dlt Cw Csh kb : ℝ} {eps : ℕ → ℝ} {dir : ℂ}
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
    (hsum : Summable fun n => eps n * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)))
    (hdefC : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))),
      ev ((p : Data)) = TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) →
      ev ((q : Data)) = TwoCapPairsAssembly.front (kappas (n + 1)) (theta0 (n + 1)) (Hs (n + 1)) →
      perim ((p : Data)) = 2 * Hs n ∧ perim ((B q : Data)) = 2 * Hs n ∧
      0 ≤ eps n ∧
      ∃ Θp Θq kp kq : ℝ → ℝ,
        (∀ s, HasDerivAt (ev ((p : Data))) (Complex.exp (Complex.I * (Θp s : ℂ))) s) ∧
        (∀ s, HasDerivAt (ev ((B q : Data))) (Complex.exp (Complex.I * (Θq s : ℂ))) s) ∧
        (∀ s, HasDerivAt Θp (kp s) s) ∧ (∀ s, HasDerivAt Θq (kq s) s) ∧
        ev ((p : Data)) 0 = ev ((B q : Data)) 0 ∧ Θp 0 = Θq 0 ∧
        (∀ s, |kp s - kq s| ≤ eps n) ∧ (∀ s, |kq s| ≤ kb))
    (hCsh : 1 ≤ Csh) (hdir : ‖dir‖ = 1)
    (hQw : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail
        (fun n => eps n * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) 0)
      < (2 * Hs 0 - Csh * ShadowingTails.tail
        (fun n => eps n * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))) 0) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  have hcpos : (0:ℝ) < 2 * Hs 0 := by linarith [hH 0]
  refine main_theorem_of_model hkminpos hdltpos hH hmono hk hper hkmin hkap htotal hchord
    hB hBcont hT hTev hsum ?_ hCsh hdir hQw hgap
  intro n p q hp hq
  obtain ⟨hLp, hLBq, heps, Θp, Θq, kp, kq, hevp, hevq, hΘp, hΘq, hF0, hΘ0, hkpq, hkqb⟩ :=
    hdefC n p q hp hq
  have hdist := dist_le_of_curvature_close (c := 2 * Hs 0) hcpos p.2 (B q).2
    hLp hLBq hevp hevq hΘp hΘq hF0 hΘ0 heps hkpq hkqb
  simpa [Subtype.dist_eq] using hdist

end MarkedSpace
