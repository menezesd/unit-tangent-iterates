import Mathlib
import UnitTangentIterates.MarkedSchemeTheoremRange
import UnitTangentIterates.TwoCapModelOrbit
import UnitTangentIterates.ModelWidth

/-!
# The closing argument with the model curves of the paper

`MarkedSchemeTheoremRange.main_theorem_on_marked_space_range` runs the closing
step of *A Noncircular Oval with Convex Unit-Tangent Iterates* on the space of
marked curves, with an **abstract** model pseudo-orbit `Q` given as a sequence
of points of the tube.  `TwoCapModelOrbit.lean` now produces such a sequence
from the geometry: the fronts of the exact two-cap pairs at the separations
`Hₙ`.

This file feeds the one into the other.  In `main_theorem_of_model` the model
sequence has disappeared from the hypotheses: what is asked of the geometry is

* a family of admissible front curvatures (continuous, `Hₙ`-periodic, pinched
  by `0 < kmin ≤ Kₙ ≤ κ̂`, of total turning `π` over one period) whose fronts
  satisfy a common quantitative chord-arc bound, with separations at least
  `H₀`; the bound is the one membership in a single tube needs, namely a common
  constant in the **normalized** parameter, so that in the arclength of the
  `n`-th model its constant `dlt·2H₀/2Hₙ` is allowed to decay with the
  separation — as it must for long thin curves of bounded width;
* the **defect estimate of the pseudo-orbit** — each model front is within
  `eₙ` of the selected inverse of the next, in the marked distance — with `eₙ`
  summable;
* the width bound of the first model and the numerical gap of the closing
  argument;

and the dynamical input is, as before, a non-expansive selected inverse `B` of
the tube with a left inverse realizing the unit-tangent transform up to
reparametrization.  The conclusion is the one of the paper's closing step: an
orbit of ovals `Xₙ` with `range X_{n+1} = range 𝒯(Xₙ)` whose first member is not
a circle.

What is *not* supplied — here or anywhere in this project — is the defect
estimate itself (the theorem *Curvature-measure matching*) or the
non-expansiveness of the selected inverse; the paper's main theorem is
therefore **not** formalized.
-/

noncomputable section

open Set Function

namespace MarkedSpace

/-- **The closing argument on the space of marked curves, with the model curves
of the paper.**  The abstract model pseudo-orbit of
`main_theorem_on_marked_space_range` is replaced by the fronts of the exact
two-cap pairs: only the admissibility of the front curvatures, the uniform
chord-arc bound, the defect estimate of the models and the width gap are
asked. -/
theorem main_theorem_of_model {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap dlt Cw Csh : ℝ} {e : ℕ → ℝ} {dir : ℂ}
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
    (hsum : Summable e)
    (hdef : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))),
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
  exact main_theorem_on_marked_space_range hcpos hkminpos (by positivity)
    hB hBcont hT hTev hsum
    (fun n => hdef n (Q n) (Q (n + 1)) (hQ n).2 (hQ (n + 1)).2)
    hCsh (hQ 0).1 hdir (by rw [(hQ 0).2]; exact hQw) hgap

/-- **The closing argument with the width given as the transverse displacement.**
The same statement as `main_theorem_of_model`, with the geometric width of the
first model replaced by the quantity the lemma *Uniform transverse width*
bounds: the transverse displacement `∫_{−H₀/2}^{H₀/2} sin Θ` of the first model
over its centred cell, its tangent angle being nonnegative there.  The direction
of the width is the transverse one. -/
theorem main_theorem_of_model_transverse {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap dlt Cw Csh : ℝ} {e : ℕ → ℝ}
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
    (hsum : Summable e)
    (hdef : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))),
      ev ((p : Data)) = TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) →
      ev ((q : Data)) = TwoCapPairsAssembly.front (kappas (n + 1)) (theta0 (n + 1)) (Hs (n + 1)) →
      dist p (B q) ≤ e n)
    (hCsh : 1 ≤ Csh)
    (hcell : ∀ s ∈ Icc (-(Hs 0 / 2)) (Hs 0 / 2),
      0 ≤ Real.sin (TwoCapPairsAssembly.frontAngle (kappas 0) (theta0 0) s))
    (hW : (∫ t in (-(Hs 0 / 2))..(Hs 0 / 2),
      Real.sin (TwoCapPairsAssembly.frontAngle (kappas 0) (theta0 0) t)) ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail e 0)
      < (2 * Hs 0 - Csh * ShadowingTails.tail e 0) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  have hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) Complex.I ≤ Cw := by
    rw [ModelWidth.width_front_eq_integral (hH 0) (hk 0) (hper 0) (htotal 0) hcell]
    exact hW
  exact main_theorem_of_model hkminpos hdltpos hH hmono hk hper hkmin hkap htotal hchord
    hB hBcont hT hTev hsum hdef hCsh (by simp) hwidth hgap

end MarkedSpace
