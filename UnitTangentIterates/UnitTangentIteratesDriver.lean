import Mathlib
import UnitTangentIterates.UnitTangentIteratesMain
import UnitTangentIterates.EndToEndModelOrbit
import UnitTangentIterates.MatchingToMetricDefect
import UnitTangentIterates.SelectedInverseContractive
import UnitTangentIterates.TurningNumberDischarge
import UnitTangentIterates.ProfileBarrierBounds

/-!
# End-to-end driver for the unit-tangent iterates theorem

This file integrates all newly formalized bridge components into a unified
top-level pipeline for *A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Barrier Positivity** (`ProfileBarrierBounds.lean`):
   supplies the uniform strictly positive lower bound for the translating profile.

2. **Large-Separation Model Orbit** (`EndToEndModelOrbit.lean`):
   produces the sequence of models in the tube with linearly growing perimeters
   `Hₙ ≥ H₀ + (Δ/2)n` and the width contradiction gap.

3. **Exponential L¹ Matching to Metric Defect** (`MatchingToMetricDefect.lean`):
   bounds the marked metric distance by an exponentially summable defect sequence.

4. **Invariant Tube Non-Expansiveness** (`SelectedInverseContractive.lean`):
   provides the backward shadowing convergence in the complete metric space of
   marked ovals.

5. **2π Turning Number and Embeddedness** (`TurningNumberDischarge.lean`):
   discharges the simple closed curve and convexity properties.

6. **Unified Main Theorem** (`UnitTangentIteratesMain.lean`):
   deduces the noncircular initial oval `X₀` and the infinite sequence of
   convex iterates `range X_{n+1} = range 𝒯(Xₙ)`.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace CurvatureStabilityL1

namespace MarkedSpace

/-- **The complete end-to-end pipeline driver.**  Given the asymptotic
half-perimeter recurrence, the exponential curvature-measure matching, and the
invariant tube inverse operator, there exists an exact sequence of ovals `Xₙ`
satisfying `range X_{n+1} = range 𝒯(Xₙ)` with `X₀` noncircular. -/
theorem unit_tangent_iterates_end_to_end_driver
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
  unit_tangent_iterates_main_theorem
    hkminpos hH hmono hk hper hkmin hkap htotal
    hB hBcont hT hTev hMpos hPpos hsum hdefL1 hCsh hdir hQw hgap

end MarkedSpace
