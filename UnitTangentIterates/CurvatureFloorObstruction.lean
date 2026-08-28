import Mathlib
import UnitTangentIterates.MasterTheoremAssembly

/-!
# A uniform positive curvature floor bounds the separations

This file records an obstruction inside the present formalization, not a result
of the paper.

`MasterTheoremAssembly.master_theorem_assembly` carries the hypotheses

* `hkminpos : 0 < kmin`,
* `hkmin : ∀ n s, kmin ≤ kappas n s`,
* `htotal : ∀ n, ∫₀^{Hₙ} κₙ = π`   (total turning `π` over a half period),
* `hH : ∀ n, 0 < Hs n`.

Together these force

```
  kmin · Hₙ ≤ ∫₀^{Hₙ} κₙ = π,     hence   Hₙ ≤ π / kmin
```

for every `n`: **the separations are bounded**.  The paper's pseudo-orbit,
however, has `Hₙ ≥ H₀ + (Δ/2)·n → ∞` (lemma *Large-separation threshold*, and
`eq:Hrec`), and the paper asserts only a common curvature **ceiling** `κ₀ < 1`,
never a positive floor — the curvature minima of the periodized hairpin decay
like `e^{-βHₙ}`.

So the uniform floor `kmin > 0` is a hypothesis the paper does not make, and it
is not merely stronger than needed: it is *incompatible* with the family the
theorem is meant to be applied to.  A faithful statement must let the lower
curvature bound depend on `n`, or drop it (the closed `kmin = 0` tube used by
`UnconditionalAssembly.PaperFaithfulAssemblyRemainder` is the route the project
already identifies for this).

This does **not** make `master_theorem_assembly` vacuous: its hypotheses are
satisfiable by a *constant*-separation family (`AdmissibleFrontFamily` uses
`H = 64`, `kmin = 1/1024`, and `kmin · H = 1/16 ≤ π`).  What the two theorems
below show is that they are satisfiable *only* by families of bounded
separation, so the paper's pseudo-orbit — whose whole point is `Hₙ → ∞`, since
that is what makes the transverse width gap open up — is not among them.

Main results: `separation_le_of_curvature_floor`,
`not_forall_of_curvature_floor_of_linear_growth`.
-/

noncomputable section

open MeasureTheory

namespace CurvatureFloorObstruction

/-- **A positive curvature floor with total turning `π` bounds the half-period.**
If `kmin ≤ κₙ` everywhere and `∫₀^{Hₙ} κₙ = π` with `Hₙ > 0`, then
`Hₙ ≤ π / kmin`. -/
theorem separation_le_of_curvature_floor {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ}
    {kmin : ℝ} (hkminpos : 0 < kmin) (hH : ∀ n, 0 < Hs n)
    (hk : ∀ n, Continuous (kappas n))
    (hkmin : ∀ n s, kmin ≤ kappas n s)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi) (n : ℕ) :
    Hs n ≤ Real.pi / kmin := by
  have hmono := intervalIntegral.integral_mono_on (hH n).le
    (intervalIntegrable_const (μ := volume) (c := kmin) (a := (0:ℝ)) (b := Hs n))
    ((hk n).intervalIntegrable _ _)
    (fun s _ => hkmin n s)
  rw [htotal n] at hmono
  rw [intervalIntegral.integral_const] at hmono
  rw [le_div_iff₀ hkminpos]
  simp only [smul_eq_mul, sub_zero] at hmono
  linarith

/-- **The floor is incompatible with the paper's growing separations.**  The
paper's pseudo-orbit satisfies `Hₙ ≥ H₀ + (Δ/2)·n` with `Δ > 0`, so the
separations are unbounded; a uniform positive curvature floor with total turning
`π` makes that impossible. -/
theorem not_forall_of_curvature_floor_of_linear_growth
    {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ} {kmin Delta : ℝ}
    (hkminpos : 0 < kmin) (hH : ∀ n, 0 < Hs n)
    (hk : ∀ n, Continuous (kappas n))
    (hkmin : ∀ n s, kmin ≤ kappas n s)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hDelta : 0 < Delta)
    (hgrow : ∀ n : ℕ, Hs 0 + Delta / 2 * n ≤ Hs n) : False := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((Real.pi / kmin - Hs 0) / (Delta / 2))
  have hbdd := separation_le_of_curvature_floor hkminpos hH hk hkmin htotal n
  have hgn := hgrow n
  have hd2 : 0 < Delta / 2 := by linarith
  have hmul := (div_lt_iff₀ hd2).mp hn
  linarith

end CurvatureFloorObstruction
