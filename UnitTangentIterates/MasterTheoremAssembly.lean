import Mathlib
import UnitTangentIterates.UnitTangentIteratesDriver
import UnitTangentIterates.MainTheoremFloorFree

/-!
# Master Theorem Assembly

> **Fix (floor-free):** The original `master_theorem_assembly` assumes
> `0 < kmin` and `H_n ≤ π/kmin` (`CurvatureFloorObstruction`), contradicting
> `H_n ≥ H_0 + (Δ/2)n`.  The corrected assembly is
> `master_theorem_assembly_floor_free` below, with `0 ≤ κ_n` and explicit
> chord-arc `dlt` (via `CurvatureFloorFreeFamily`), and
> `C_j,D_j` depending on fixed `ε` — matching the paper's
> `Thm:hairpin` quantifier order.


This file provides the master assembly of *A Noncircular Oval with Convex
Unit-Tangent Iterates* (Theorem 1.1).

It unifies the full formal library across all 7 sections of the paper:
1. **Geometric Preliminaries & Speed-Curvature Laws** (Section 2)
2. **Translating Hairpin Soliton & Regularity** (Section 3)
3. **Exact Two-Cap Pairs & Half-Perimeter Asymptotics** (Section 4)
4. **Exponential L¹ Curvature Matching to Marked Metric Defect** (Section 5)
5. **Complete Marked Metric Space, Invariant Tube, & Inverse Jacobi Estimates** (Section 6)
6. **Backward Shadowing Scheme & Transverse Width Contradiction Gap** (Section 7)

Main results:
* `master_theorem_assembly` : the integrated master theorem pipeline.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace CurvatureStabilityL1

set_option maxHeartbeats 800000

namespace MasterTheoremAssembly

/-- **Master Theorem 1.1 Assembly.**
Under the verified geometric and analytic pipeline established in Sections 2–7,
there exists an arclength-parametrized, smooth, strictly convex, embedded
closed planar curve `X₀` (an oval) which is not a circle, such that every
unit-tangent iterate `X_{n+1} = 𝒯(Xₙ)` is an oval. -/
theorem master_theorem_assembly
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
  unit_tangent_iterates_end_to_end_driver
    hkminpos hH hmono hk hper hkmin hkap htotal
    hB hBcont hT hTev hMpos hPpos hsum hdefL1 hCsh hdir hQw hgap

/-- **Corrected master theorem — floor-free, explicit chord-arc, linear growth.**
`0 ≤ κ_n` (closed tube) and explicit `dlt` from `TwoCapModelOrbit`
replace `0 < kmin` and `ModelChordArc`.  `H_n ≥ H_0 + (Δ/2)n` is compatible
with `∫_0^{H_n} κ_n = π` only when the floor is dropped. -/
theorem master_theorem_assembly_floor_free
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kap dlt Cw Csh kb M : ℝ} {eps cw P : ℕ → ℝ} {dir : ℂ}
    (hdlt : 0 < dlt)
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
  -- reduce to floor-free closing argument
  have hcpos : (0:ℝ) < 2 * Hs 0 := by linarith [hH 0]
  exact MarkedSpace.main_theorem_of_model_floor_free hdlt hstrict hH hmono hk hper hkmin hkap htotal hchord
    hB hBcont hT hTev hsum
    (by
      intro n p q hp hq
      obtain ⟨hLp, hLBq, Θp, Θq, kp, kq, kp', kq', hevp, hevq, hΘp, hΘq, hF0, hΘ0, hpp, hpq, hdp, hdq, hbp, hbq, hint, hkqb⟩ :=
        hdefL1 n p q hp hq
      have hdist := CurvatureStabilityL1.dist_le_of_L1_curvature_close (cc := 2 * Hs 0)
        hcpos p.2 (B q).2 hLp hLBq hevp hevq hΘp hΘq hF0 hΘ0 (hPpos n) hMpos hpp hpq hdp hdq hbp hbq hint hkqb
      simpa [Subtype.dist_eq, l1Modulus] using hdist)
    hCsh hdir hQw hgap

end MasterTheoremAssembly
