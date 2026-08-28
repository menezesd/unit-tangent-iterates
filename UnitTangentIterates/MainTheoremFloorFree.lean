import UnitTangentIterates.MainTheoremModel
import UnitTangentIterates.MainTheoremModelL1
import UnitTangentIterates.MarkedSchemeFloorFree

/-!
# The model closing theorems, without a curvature floor

Continuing §49 outward.  `main_theorem_of_model` and
`main_theorem_of_model_of_L1_curvature` each threaded `hkminpos : 0 < kmin`,
and each used it for exactly one thing: passing it down.  Both are restated here
on the floor-free tube.

* `main_theorem_of_model_floor_free`
* `main_theorem_of_model_of_L1_curvature_floor_free`

The curvature hypothesis is now `0 ≤ κₙ(s)` — the closed condition, which the
construction satisfies — and the oval conclusion comes from the strictness data
rather than from a floor.

The `..._L1_pinched` layer has no floor-free analogue **and needs none**: its
only content was deriving `delta` and the chord bound from `kmin` via
`ModelChordArc`.  On this route those are supplied directly, which is what the
paper does — its `lem:curv-interp` carries the constant `C(1+L)²` in the
half-perimeter and never mentions a chord-arc constant at all.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Filter Topology Function CurvatureStabilityL1

namespace MarkedSpace

theorem main_theorem_of_model_floor_free {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kap dlt Cw Csh : ℝ} {e : ℕ → ℝ} {dir : ℂ}
    (hdltpos : 0 < dlt)
    (hstrict : ∀ p : tube (2 * Hs 0) 0 (dlt * (2 * Hs 0)),
      Nonempty (UnconditionalAssembly.LimitStrictnessData ((p : Data))))
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, (0:ℝ) ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) x
            - TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) y‖)
    {B T : tube (2 * Hs 0) 0 (dlt * (2 * Hs 0)) → tube (2 * Hs 0) 0 (dlt * (2 * Hs 0))}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube (2 * Hs 0) 0 (dlt * (2 * Hs 0)),
      range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data)))))
    (hsum : Summable e)
    (hdef : ∀ (n : ℕ) (p q : tube (2 * Hs 0) 0 (dlt * (2 * Hs 0))),
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
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  -- the model curves, as a sequence of points of one tube
  obtain ⟨Q, hQ⟩ := TwoCapModelOrbit.exists_model_orbit_tube hH hmono hk hper
    hkmin hkap htotal hchord
  have hcpos : (0:ℝ) < 2 * Hs 0 := by linarith [hH 0]
  exact main_theorem_on_marked_space_range_floor_free hcpos (by positivity)
    hstrict
    hB hBcont hT hTev hsum
    (fun n => hdef n (Q n) (Q (n + 1)) (hQ n).2 (hQ (n + 1)).2)
    hCsh (hQ 0).1 hdir (by rw [(hQ 0).2]; exact hQw) hgap

theorem main_theorem_of_model_of_L1_curvature_floor_free
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kap dlt Cw Csh kb M : ℝ} {eps cw P : ℕ → ℝ} {dir : ℂ}
    (hdltpos : 0 < dlt)
    (hstrict : ∀ p : tube (2 * Hs 0) 0 (dlt * (2 * Hs 0)),
      Nonempty (UnconditionalAssembly.LimitStrictnessData ((p : Data))))
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, (0:ℝ) ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) x
            - TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) y‖)
    {B T : tube (2 * Hs 0) 0 (dlt * (2 * Hs 0)) → tube (2 * Hs 0) 0 (dlt * (2 * Hs 0))}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube (2 * Hs 0) 0 (dlt * (2 * Hs 0)),
      range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data)))))
    (hMpos : 0 < M) (hPpos : ∀ n, 0 < P n)
    (hsum : Summable fun n =>
      l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)))
    (hdefL1 : ∀ (n : ℕ) (p q : tube (2 * Hs 0) 0 (dlt * (2 * Hs 0))),
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
  refine main_theorem_of_model_floor_free hdltpos hstrict hH hmono hk hper hkmin hkap htotal hchord
    hB hBcont hT hTev hsum ?_ hCsh hdir hQw hgap
  intro n p q hp hq
  obtain ⟨hLp, hLBq, Θp, Θq, kp, kq, kp', kq', hevp, hevq, hΘp, hΘq, hF0, hΘ0, hpp, hpq,
    hdp, hdq, hbp, hbq, hint, hkqb⟩ := hdefL1 n p q hp hq
  have hdist := CurvatureStabilityL1.dist_le_of_L1_curvature_close (cc := 2 * Hs 0)
    hcpos p.2 (B q).2 hLp hLBq hevp hevq hΘp hΘq hF0 hΘ0 (hPpos n) hMpos hpp hpq
    hdp hdq hbp hbq hint hkqb
  simpa [Subtype.dist_eq, l1Modulus] using hdist
end MarkedSpace
