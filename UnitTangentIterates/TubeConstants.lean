import Mathlib

/-!
# The tube constants of the shadowing theorem

This file formalizes the explicit constant bookkeeping in the proof of the
theorem *Regularizing backward shadowing* of the paper *A Noncircular Oval with
Convex Unit-Tangent Iterates*.

Given a curvature ceiling `κ₀ < 1`, the proof interpolates two further
ceilings `κ̄ = (2κ₀+1)/3` and `κ̂ = (κ₀+2)/3`, sets

`M₀ = max{1, C₀}`,  `M₁ = max{1, C₁(1+M₀)}`,

and shows that the tube conditions `W ≤ aₙ`, `S₀ ≤ M₀aₙ`, `S₁ ≤ M₁aₙ` are
reproduced after one inverse step followed by concatenation with the defect
path, because `aₙ = dₙ + a_{n+1}`.  Finally the explicit threshold

`η_* = (1/(2C_int)) min{(κ̄-κ₀)/C_tube, (κ̂-κ̄)/C_inc}`

makes the two smallness conditions of the proof valid from level zero.

Main results:

* `kappa_chain` : `κ₀ < κ̄ < κ̂ < 1`;
* `tube_invariance_bounds` : reproduction of the tube conditions;
* `endpoint_margin` : the endpoint curvature margin `κ₀ + C_tube a_{n+1} ≤ κ̄`;
* `etaStar_bounds` : the explicit uniform smallness threshold works.
-/

noncomputable section

namespace TubeConstants

/-- The intermediate curvature ceiling `κ̄ = (2κ₀+1)/3`. -/
def kbar (k0 : ℝ) : ℝ := (2 * k0 + 1) / 3

/-- The outer curvature ceiling `κ̂ = (κ₀+2)/3`. -/
def khat (k0 : ℝ) : ℝ := (k0 + 2) / 3

/-- **The ceiling chain** `κ₀ < κ̄ < κ̂ < 1`. -/
theorem kappa_chain {k0 : ℝ} (hk : k0 < 1) :
    k0 < kbar k0 ∧ kbar k0 < khat k0 ∧ khat k0 < 1 := by
  simp only [kbar, khat]
  refine ⟨by linarith, by linarith, by linarith⟩

theorem kbar_sub {k0 : ℝ} : kbar k0 - k0 = (1 - k0) / 3 := by unfold kbar; ring

theorem khat_sub_kbar {k0 : ℝ} : khat k0 - kbar k0 = (1 - k0) / 3 := by
  unfold kbar khat; ring

/-! ### Reproduction of the tube conditions -/

/-- **Tube invariance.**  After one inverse step (which contributes the bounds
`a_{n+1}`, `C₀a_{n+1}`, `C₁(1+M₀)a_{n+1}`) and concatenation with the defect
path (which contributes `dₙ`), the tube conditions hold again at level `n`
with `aₙ = dₙ + a_{n+1}`. -/
theorem tube_invariance_bounds {C0 C1 M0 M1 dn an1 W S0 S1 : ℝ}
    (hM0 : M0 = max 1 C0) (hM1 : M1 = max 1 (C1 * (1 + M0)))
    (hd : 0 ≤ dn) (ha : 0 ≤ an1)
    (hW : W ≤ dn + an1) (hS0 : S0 ≤ dn + C0 * an1)
    (hS1 : S1 ≤ dn + C1 * (1 + M0) * an1) :
    W ≤ dn + an1 ∧ S0 ≤ M0 * (dn + an1) ∧ S1 ≤ M1 * (dn + an1) := by
  have hM0one : 1 ≤ M0 := by rw [hM0]; exact le_max_left _ _
  have hM0C0 : C0 ≤ M0 := by rw [hM0]; exact le_max_right _ _
  have hM1one : 1 ≤ M1 := by rw [hM1]; exact le_max_left _ _
  have hM1C1 : C1 * (1 + M0) ≤ M1 := by rw [hM1]; exact le_max_right _ _
  refine ⟨hW, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- **The endpoint margin.**  If the second-derivative tube estimate is small
enough, the output curvature stays below the intermediate ceiling `κ̄`. -/
theorem endpoint_margin {k0 Ctube an1 maxk : ℝ}
    (hmax : maxk ≤ k0 + Ctube * an1) (hsmall : Ctube * an1 < kbar k0 - k0) :
    maxk < kbar k0 := by linarith

/-! ### The explicit uniform smallness threshold -/

/-- The explicit threshold `η_*` of the shadowing theorem. -/
def etaStar (Cint Ctube Cinc k0 : ℝ) : ℝ :=
  1 / (2 * Cint) * min ((kbar k0 - k0) / Ctube) ((khat k0 - kbar k0) / Cinc)

/-- **The threshold works.**  If `r₀ ≤ η_*` then, with `a₀ = C_int r₀`, both
smallness conditions of the shadowing proof hold from level zero. -/
theorem etaStar_bounds {Cint Ctube Cinc k0 r0 : ℝ}
    (hCint : 0 < Cint) (hCtube : 0 < Ctube) (hCinc : 0 < Cinc)
    (hk : k0 < 1) (hle : r0 ≤ etaStar Cint Ctube Cinc k0) :
    Ctube * (Cint * r0) < kbar k0 - k0 ∧ Cinc * (Cint * r0) < khat k0 - kbar k0 := by
  have hpos : 0 < (1 - k0) / 3 := by linarith
  have h1 : 0 < (kbar k0 - k0) / Ctube := by rw [kbar_sub]; positivity
  have h2 : 0 < (khat k0 - kbar k0) / Cinc := by rw [khat_sub_kbar]; positivity
  have hmin : 0 < min ((kbar k0 - k0) / Ctube) ((khat k0 - kbar k0) / Cinc) := lt_min h1 h2
  have hbound : Cint * r0 ≤ 1 / 2 * min ((kbar k0 - k0) / Ctube) ((khat k0 - kbar k0) / Cinc) := by
    have := mul_le_mul_of_nonneg_left hle hCint.le
    calc Cint * r0 ≤ Cint * (1 / (2 * Cint)
        * min ((kbar k0 - k0) / Ctube) ((khat k0 - kbar k0) / Cinc)) := this
      _ = 1 / 2 * min ((kbar k0 - k0) / Ctube) ((khat k0 - kbar k0) / Cinc) := by
          field_simp
  constructor
  · have hle1 : Cint * r0 ≤ 1 / 2 * ((kbar k0 - k0) / Ctube) := by
      have := min_le_left ((kbar k0 - k0) / Ctube) ((khat k0 - kbar k0) / Cinc)
      linarith
    have hstep : Ctube * (Cint * r0) ≤ Ctube * (1 / 2 * ((kbar k0 - k0) / Ctube)) :=
      mul_le_mul_of_nonneg_left hle1 hCtube.le
    have hval : Ctube * (1 / 2 * ((kbar k0 - k0) / Ctube)) = 1 / 2 * (kbar k0 - k0) := by
      field_simp
    rw [hval] at hstep
    rw [kbar_sub] at hstep ⊢
    linarith
  · have hle2 : Cint * r0 ≤ 1 / 2 * ((khat k0 - kbar k0) / Cinc) := by
      have := min_le_right ((kbar k0 - k0) / Ctube) ((khat k0 - kbar k0) / Cinc)
      linarith
    have hstep : Cinc * (Cint * r0) ≤ Cinc * (1 / 2 * ((khat k0 - kbar k0) / Cinc)) :=
      mul_le_mul_of_nonneg_left hle2 hCinc.le
    have hval : Cinc * (1 / 2 * ((khat k0 - kbar k0) / Cinc)) = 1 / 2 * (khat k0 - kbar k0) := by
      field_simp
    rw [hval] at hstep
    rw [khat_sub_kbar] at hstep ⊢
    linarith

end TubeConstants
