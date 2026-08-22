import Mathlib
import UnitTangentIterates.MainTheoremModelCurvature
import UnitTangentIterates.MarkedDistancePerimeter

/-!
# The closing argument with a curvature defect estimate and a moving perimeter

`MainTheoremModelCurvature.main_theorem_of_model_of_curvature` states the
closing argument of *A Noncircular Oval with Convex Unit-Tangent Iterates* with
the defect estimate given on the curvatures, but asks the selected inverse of
the `(n+1)`-st model to have **exactly** the perimeter of the `n`-th model.  In
the paper the two agree only up to the defect, and this file removes the
restriction, on `MarkedDistancePerimeter.dist_le_of_curvature_close_perim`.

The defect hypothesis is now: whenever `p` carries the `n`-th model front and
`q` the `(n+1)`-st, the selected inverse `B q` is aligned with `p` at the marked
point, its perimeter differs from that of `p` by at most `Dₙ`, its curvature is
`kL`-Lipschitz, both curvatures are bounded by `kb`, and the two curvatures
differ by at most `εₙ`.  The resulting summable defect sequence is
`defectBound εₙ Dₙ (2Hₙ + Dₙ) kb kL`.

The comparison of the curvatures is still asked in the **uniform** norm, where
the paper's matching theorem gives an `L¹` comparison, and the non-expansiveness
of the selected inverse is still a hypothesis; the paper's main theorem is
**not** formalized.
-/

noncomputable section

open Set Function

namespace MarkedSpace

/-- **The closing argument with the model curves, the defect estimate being
given on the curvatures and the perimeters allowed to differ.** -/
theorem main_theorem_of_model_of_curvature_perim {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap dlt Cw Csh kb kL : ℝ} {eps D : ℕ → ℝ} {dir : ℂ}
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
    (hsum : Summable fun n => defectBound (eps n) (D n) (2 * Hs n + D n) kb kL)
    (hdefC : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))),
      ev ((p : Data)) = TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) →
      ev ((q : Data)) = TwoCapPairsAssembly.front (kappas (n + 1)) (theta0 (n + 1)) (Hs (n + 1)) →
      perim ((p : Data)) = 2 * Hs n ∧
      |perim ((p : Data)) - perim ((B q : Data))| ≤ D n ∧
      0 ≤ eps n ∧
      ∃ Θp Θq kp kq : ℝ → ℝ,
        (∀ s, HasDerivAt (ev ((p : Data))) (Complex.exp (Complex.I * (Θp s : ℂ))) s) ∧
        (∀ s, HasDerivAt (ev ((B q : Data))) (Complex.exp (Complex.I * (Θq s : ℂ))) s) ∧
        (∀ s, HasDerivAt Θp (kp s) s) ∧ (∀ s, HasDerivAt Θq (kq s) s) ∧
        ev ((p : Data)) 0 = ev ((B q : Data)) 0 ∧ Θp 0 = Θq 0 ∧
        (∀ s, |kp s - kq s| ≤ eps n) ∧ (∀ s, |kp s| ≤ kb) ∧ (∀ s, |kq s| ≤ kb) ∧
        (∀ a b, |kq a - kq b| ≤ kL * |a - b|))
    (hCsh : 1 ≤ Csh) (hdir : ‖dir‖ = 1)
    (hQw : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail
        (fun n => defectBound (eps n) (D n) (2 * Hs n + D n) kb kL) 0)
      < (2 * Hs 0 - Csh * ShadowingTails.tail
        (fun n => defectBound (eps n) (D n) (2 * Hs n + D n) kb kL) 0) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  have hcpos : (0:ℝ) < 2 * Hs 0 := by linarith [hH 0]
  refine main_theorem_of_model hkminpos hdltpos hH hmono hk hper hkmin hkap htotal hchord
    hB hBcont hT hTev hsum ?_ hCsh hdir hQw hgap
  intro n p q hp hq
  obtain ⟨hLp, hDn, heps, Θp, Θq, kp, kq, hevp, hevq, hΘp, hΘq, hF0, hΘ0, hkpq, hkpb, hkqb,
    hkqL⟩ := hdefC n p q hp hq
  have hD0 : 0 ≤ D n := le_trans (abs_nonneg _) hDn
  have hLple : perim ((p : Data)) ≤ 2 * Hs n + D n := by rw [hLp]; linarith
  have hLqle : perim ((B q : Data)) ≤ 2 * Hs n + D n := by
    have h := abs_le.1 hDn
    rw [hLp] at h
    linarith [h.1]
  have hdist := dist_le_of_curvature_close_perim (c := 2 * Hs 0) hcpos p.2 (B q).2
    hLple hLqle hDn hevp hevq hΘp hΘq hF0 hΘ0 heps hkpq hkpb hkqb hkqL
  simpa [Subtype.dist_eq] using hdist

end MarkedSpace
