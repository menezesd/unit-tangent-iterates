import UnitTangentIterates.MainTheoremFloorFree
import UnitTangentIterates.ModelChordScaled

/-!
# The floor-free closing theorem with its chord field supplied

`main_theorem_of_model_of_L1_curvature_floor_free` (§50) takes the tube's chord
bound as a hypothesis.  §57 constructed that bound for the two-cap model, with

```
  dlt = min(1/2, π/(12·kap·H₀)) .
```

`main_theorem_of_model_L1_floor_free` puts the two together: the chord field is
no longer a hypothesis but is derived from the curvature ceiling `kap`, which
the construction supplies.

What the theorem still takes, and what each is:

* `hstrict` — `LimitStrictnessData` for tube members, reduced in §53 to the
  order-one relative bound and the turning identity;
* `B`, `T`, `hTev` — the tube's shift and unit-tangent transfer;
* `hdefL1` — the summable `L¹` curvature defects, which
  `exists_configuredModelSequence_of_eps` (§46) produces;
* the width gap.

No curvature floor appears anywhere in the statement.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Filter Topology Function CurvatureStabilityL1

namespace MarkedSpace

theorem main_theorem_of_model_L1_floor_free
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kap Cw Csh kb M : ℝ} {eps cw P : ℕ → ℝ} {dir : ℂ}
    (hkap0 : 0 < kap)
    (hstrict : ∀ p : tube (2 * Hs 0) 0 (min (1/2 : ℝ) (Real.pi / (12 * kap * Hs 0)) * (2 * Hs 0)),
      Nonempty (UnconditionalAssembly.LimitStrictnessData ((p : Data))))
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, (0:ℝ) ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    {B T : tube (2 * Hs 0) 0 (min (1/2 : ℝ) (Real.pi / (12 * kap * Hs 0)) * (2 * Hs 0)) → tube (2 * Hs 0) 0 (min (1/2 : ℝ) (Real.pi / (12 * kap * Hs 0)) * (2 * Hs 0))}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube (2 * Hs 0) 0 (min (1/2 : ℝ) (Real.pi / (12 * kap * Hs 0)) * (2 * Hs 0)),
      range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data)))))
    (hMpos : 0 < M) (hPpos : ∀ n, 0 < P n)
    (hsum : Summable fun n =>
      l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)))
    (hdefL1 : ∀ (n : ℕ) (p q : tube (2 * Hs 0) 0 (min (1/2 : ℝ) (Real.pi / (12 * kap * Hs 0)) * (2 * Hs 0))),
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
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX     := by
  have hdltpos : (0:ℝ) < min (1/2 : ℝ) (Real.pi / (12 * kap * Hs 0)) := by
    apply lt_min (by norm_num)
    have := hH 0
    positivity
  exact main_theorem_of_model_of_L1_curvature_floor_free hdltpos hstrict hH hmono
    hk hper hkmin hkap htotal
    (TwoCapPairsAssembly.chord_arc_front_scaled hH hmono hk hper htotal hkmin
      hkap hkap0)
    hB hBcont hT hTev hMpos hPpos hsum hdefL1 hCsh hdir hQw hgap

end MarkedSpace
