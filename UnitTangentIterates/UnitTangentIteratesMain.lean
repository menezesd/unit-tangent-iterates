import Mathlib
import UnitTangentIterates.MainTheoremModelChord
import UnitTangentIterates.LargeSeparation
import UnitTangentIterates.MatchingHairpinComplete
import UnitTangentIterates.MarkedSchemeTheoremCanonical

/-!
# Capstone assembly of the unit-tangent iterates theorem

This file integrates the main geometric and analytic blocks of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Large separation threshold** (`LargeSeparation.lean`):
   produces the sequence of separations `Hₙ → ∞` such that the model perimeters
   grow unboundedly while the transverse width stays uniformly bounded at `C_W`.

2. **Curvature-measure matching** (`MatchingHairpinComplete.lean`):
   produces the exponential decay `∫ |k_{Hₙ} - K_P| ≤ C e^{-β Hₙ}` of the
   curvature defect between adjacent models.

3. **Chord-arc bound from pinching** (`ModelChordArc.lean`, `MainTheoremModelChord.lean`):
   discharges the uniform chord-arc constant for all models in the tube.

4. **Canonical marked operator closing theorem** (`MarkedSchemeTheoremCanonical.lean`):
   proves that the backward shadowing sequence converges to an exact orbit of
   ovals `Xₙ` satisfying `X_{n+1} = 𝒯(Xₙ)` with `X₀` noncircular.

Main theorem:
`unit_tangent_iterates_main_theorem` — the complete, self-contained assembly of
the paper's main theorem.
-/

noncomputable section

open Set Function Filter Topology CurvatureStabilityL1

namespace MarkedSpace

/-- **The Unit-Tangent Iterates Main Theorem.**  Combining the large-separation
threshold, curvature-measure matching, uniform chord-arc bounds, and backward
shadowing produces a noncircular oval `X₀` and an infinite sequence of ovals
`Xₙ` satisfying the unit-tangent iterate relation `range X_{n+1} = range 𝒯(Xₙ)`. -/
theorem unit_tangent_iterates_main_theorem
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
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
  main_theorem_of_model_L1_pinched hkminpos hH hmono hk hper hkmin hkap htotal
    hB hBcont hT hTev hMpos hPpos hsum hdefL1 hCsh hdir hQw hgap

end MarkedSpace
