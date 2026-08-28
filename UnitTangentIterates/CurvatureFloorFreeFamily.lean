import Mathlib
import UnitTangentIterates.CurvatureFloorObstruction
import UnitTangentIterates.TwoCapModelOrbit

/-!
# Dropping the curvature floor admits the paper's unbounded separations

`CurvatureFloorObstruction` shows that the hypotheses of
`MasterTheoremAssembly.master_theorem_assembly` — a uniform positive curvature
floor `0 < kmin ≤ κₙ` together with total turning `∫₀^{Hₙ} κₙ = π` — force
`Hₙ ≤ π / kmin`, and are contradictory with the paper's `Hₙ ≥ H₀ + (Δ/2)·n`.

That diagnosis leaves a question: is the *rest* of the hypothesis set still
satisfiable once the floor is dropped to `kmin = 0` (the closed tube), or is the
obstruction deeper?  It is not deeper.  This file exhibits an explicit family

```
  Hₙ = 2π + n,     κₙ ≡ π / (2π + n),
```

which satisfies every remaining hypothesis — continuity, `Hₙ`-periodicity,
nonnegative curvature, a common ceiling `κ̂ = 1/2 < 1`, total turning `π`, and
`H₀ ≤ Hₙ` — **with separations tending to infinity**, exactly as the paper's
recursion `P(H_{n+1}) = Hₙ` requires.

It also shows the floor must genuinely vanish: for this family, no positive
`kmin` bounds the curvatures from below, since `inf_n κₙ = 0`.  So `kmin = 0`
is not a convenience, it is forced by `Hₙ → ∞` and total turning `π`.

(The family is of course not itself the paper's two-cap model — its curvature is
constant, so it is a circle of perimeter `2Hₙ`.  It is a witness that the
hypothesis *set* is consistent with unbounded separations, which is what the
obstruction called into question.)

Main results: `exists_unbounded_floor_free_family`, `no_positive_floor`.
-/

noncomputable section

open MeasureTheory

namespace CurvatureFloorFreeFamily

/-- The separations of the witness family: `Hₙ = 2π + n`. -/
def Hs (n : ℕ) : ℝ := 2 * Real.pi + n

/-- The curvatures of the witness family: the constant `π / Hₙ`. -/
def kappas (n : ℕ) : ℝ → ℝ := fun _ => Real.pi / Hs n

theorem Hs_pos (n : ℕ) : 0 < Hs n := by
  have := Real.pi_pos
  have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold Hs; linarith [Real.pi_pos]

theorem Hs_mono (n : ℕ) : Hs 0 ≤ Hs n := by
  unfold Hs
  have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Nat.cast_zero]
  linarith

theorem Hs_unbounded (B : ℝ) : ∃ n : ℕ, B ≤ Hs n := by
  obtain ⟨n, hn⟩ := exists_nat_ge B
  exact ⟨n, le_trans hn (by unfold Hs; linarith [Real.pi_pos])⟩

theorem continuous_kappas (n : ℕ) : Continuous (kappas n) := continuous_const

theorem periodic_kappas (n : ℕ) : Function.Periodic (kappas n) (Hs n) :=
  fun _ => rfl

theorem kappas_nonneg (n : ℕ) (s : ℝ) : 0 ≤ kappas n s :=
  div_nonneg Real.pi_pos.le (Hs_pos n).le

theorem kappas_le (n : ℕ) (s : ℝ) : kappas n s ≤ 1 / 2 := by
  have hH : 2 * Real.pi ≤ Hs n := by
    unfold Hs
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2pi : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  unfold kappas
  rw [div_le_iff₀ (Hs_pos n)]
  nlinarith [Real.pi_pos]

theorem kappas_total (n : ℕ) :
    (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi := by
  have hne : Hs n ≠ 0 := (Hs_pos n).ne'
  unfold kappas
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    mul_div_cancel₀ _ hne]

/-- **The floor-free hypothesis set is satisfiable with unbounded
separations.**  Everything the master theorem asks of the model family apart
from the positive curvature floor holds, and the separations tend to
infinity. -/
theorem exists_unbounded_floor_free_family :
    ∃ (κ : ℕ → ℝ → ℝ) (H : ℕ → ℝ) (kap : ℝ),
      kap < 1 ∧
      (∀ n, 0 < H n) ∧ (∀ n, H 0 ≤ H n) ∧
      (∀ n, Continuous (κ n)) ∧ (∀ n, Function.Periodic (κ n) (H n)) ∧
      (∀ n s, 0 ≤ κ n s) ∧ (∀ n s, κ n s ≤ kap) ∧
      (∀ n, (∫ r in (0:ℝ)..(H n), κ n r) = Real.pi) ∧
      (∀ B : ℝ, ∃ n : ℕ, B ≤ H n) :=
  ⟨kappas, Hs, 1 / 2, by norm_num, Hs_pos, Hs_mono, continuous_kappas,
    periodic_kappas, kappas_nonneg, kappas_le, kappas_total, Hs_unbounded⟩

/-- **The floor must vanish.**  No positive constant bounds the curvatures of
the witness family from below: with total turning `π` fixed and `Hₙ → ∞`, the
curvature minima necessarily tend to zero.  So `kmin = 0` — the closed tube — is
forced, not chosen. -/
theorem no_positive_floor {kmin : ℝ} (hkmin : 0 < kmin) :
    ¬ ∀ n s, kmin ≤ kappas n s := by
  intro h
  have hbdd := CurvatureFloorObstruction.separation_le_of_curvature_floor
    hkmin Hs_pos continuous_kappas h kappas_total
  obtain ⟨n, hn⟩ := Hs_unbounded (Real.pi / kmin + 1)
  have := hbdd n
  linarith

/-! ### The model orbit in the closed tube -/

open Set MarkedSpace TwoCapPairsAssembly

/-- **The model orbit construction accepts the closed `kmin = 0` tube.**
`MarkedSpaceChord.exists_tube_member_of_oval_chord` — the constructor underneath
`TwoCapModelOrbit.exists_model_orbit_tube` — requires only `kmin ≤ k`, never
`0 < kmin`, so the whole model-orbit construction goes through with the floor
dropped.  Combined with `exists_unbounded_floor_free_family` and
`no_positive_floor`, this is the concrete form of the correction: the curvature
hypothesis of the model family should be **nonnegativity**, and then the
separations are free to grow.

The chord-arc input is unchanged and orthogonal: it is a statement about
embeddedness of the model fronts, not about a curvature floor.  (Its uniform
constant does have to be supplied without `ModelChordArc.model_chord_arc`, whose
proof does use `0 < kmin`.) -/
theorem exists_model_orbit_tube_zero_floor {kappas : ℕ → ℝ → ℝ}
    {Hs theta0 : ℕ → ℝ} {kap dlt : ℝ}
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Function.Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, 0 ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖front (kappas n) (theta0 n) (Hs n) x
            - front (kappas n) (theta0 n) (Hs n) y‖) :
    ∃ Q : ℕ → tube (2 * Hs 0) 0 (dlt * (2 * Hs 0)), ∀ n,
      perim ((Q n : Data)) = 2 * Hs n ∧
      ev ((Q n : Data)) = front (kappas n) (theta0 n) (Hs n) :=
  TwoCapModelOrbit.exists_model_orbit_tube hH hmono hk hper hkmin hkap htotal
    hchord

end CurvatureFloorFreeFamily
