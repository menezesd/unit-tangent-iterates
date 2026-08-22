import Mathlib
import UnitTangentIterates.MainTheoremModelL1
import UnitTangentIterates.ModelChordArc

/-!
# The closing argument with the chord-arc bound of the models produced

`MainTheoremModel.main_theorem_of_model` and its variants run the closing step
of *A Noncircular Oval with Convex Unit-Tangent Iterates* with the model curves
of the paper, but ask for a **hypothesis** on the geometry of those curves: a
quantitative chord-arc bound, uniform along the family, which is what puts them
all into one tube of marked curves.

`ModelChordArc.model_chord_arc` produces that bound from the curvature pinching
alone, and this file substitutes it: in the two theorems below the chord-arc
hypothesis has disappeared, and the chord-arc constant of the tube is the
explicit `dlt = min(H₀, 2h₀)/(2H₀)` of `ModelChordArc.modelChordConst`.  What is
asked of the model curvatures is only what the paper asks: continuity,
`Hₙ`-periodicity, the pinching `0 < kmin ≤ Kₙ ≤ κ̂` and the total turning `π`
over one period.

* `main_theorem_of_model_pinched` — the defect estimate in the marked metric;
* `main_theorem_of_model_L1_pinched` — the defect estimate as the `L¹`
  comparison of the curvatures produced by the theorem *Curvature-measure
  matching*.

As before the non-expansive selected inverse and the defect estimate itself are
hypotheses, so the paper's main theorem is **not** formalized.
-/

noncomputable section

open Set Function CurvatureStabilityL1

namespace MarkedSpace

/-- **The closing argument with the model curves, the chord-arc bound
produced.**  Same as `MainTheoremModel.main_theorem_of_model`, with the
chord-arc hypothesis discharged from the curvature pinching and the chord-arc
constant of the tube fixed to `ModelChordArc.modelChordConst kmin κ̂ H₀`. -/
theorem main_theorem_of_model_pinched {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap Cw Csh : ℝ} {e : ℕ → ℝ} {dir : ℂ}
    (hkminpos : 0 < kmin)
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    {B T : tube (2 * Hs 0) kmin (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0)) →
      tube (2 * Hs 0) kmin (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0))}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube (2 * Hs 0) kmin
        (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0)),
      range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data)))))
    (hsum : Summable e)
    (hdef : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin
        (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0))),
      ev ((p : Data)) = TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) →
      ev ((q : Data)) = TwoCapPairsAssembly.front (kappas (n + 1)) (theta0 (n + 1)) (Hs (n + 1)) →
      dist p (B q) ≤ e n)
    (hCsh : 1 ≤ Csh) (hdir : ‖dir‖ = 1)
    (hQw : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail e 0)
      < (2 * Hs 0 - Csh * ShadowingTails.tail e 0) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX :=
  main_theorem_of_model hkminpos
    (ModelChordArc.modelChordConst_pos hkminpos (le_trans (hkmin 0 0) (hkap 0 0)) (hH 0))
    hH hmono hk hper hkmin hkap htotal
    (ModelChordArc.model_chord_arc (theta0 := theta0) hH hmono hkminpos hk hper hkmin hkap htotal)
    hB hBcont hT hTev hsum hdef hCsh hdir hQw hgap

/-- **The closing argument with the model curves, the chord-arc bound produced
and the defect estimate given in `L¹`.**  Same as
`MainTheoremModelL1.main_theorem_of_model_of_L1_curvature`, with the chord-arc
hypothesis discharged from the curvature pinching. -/
theorem main_theorem_of_model_L1_pinched {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap Cw Csh kb M : ℝ} {eps cw P : ℕ → ℝ} {dir : ℂ}
    (hkminpos : 0 < kmin)
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    {B T : tube (2 * Hs 0) kmin (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0)) →
      tube (2 * Hs 0) kmin (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0))}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube (2 * Hs 0) kmin
        (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0)),
      range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data)))))
    (hMpos : 0 < M) (hPpos : ∀ n, 0 < P n)
    (hsum : Summable fun n =>
      l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)))
    (hdefL1 : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin
        (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0))),
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
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX :=
  main_theorem_of_model_of_L1_curvature hkminpos
    (ModelChordArc.modelChordConst_pos hkminpos (le_trans (hkmin 0 0) (hkap 0 0)) (hH 0))
    hH hmono hk hper hkmin hkap htotal
    (ModelChordArc.model_chord_arc (theta0 := theta0) hH hmono hkminpos hk hper hkmin hkap htotal)
    hB hBcont hT hTev hMpos hPpos hsum hdefL1 hCsh hdir hQw hgap

end MarkedSpace
