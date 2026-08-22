import Mathlib

/-!
# Smooth positive extension of the profile

Many statements of this project about the hairpin of *A Noncircular Oval with
Convex Unit-Tangent Iterates* are phrased for a profile `f : ℝ → ℝ` which is
`C^∞` and positive on the **whole line**, even though only the values of the
profile on `[0, π]` enter their conclusions.  The profile produced in Section 3
is smooth and positive on the open interval `(0, π)`, and the passage from the
one to the other was recorded in the README as a convention rather than a
proof.

This file removes the gap between an *open neighbourhood* of the closed
interval and the whole line: if a function is `C^∞` and positive on
`(a - r, b + r)`, then there is a function which is `C^∞` and positive on all
of `ℝ` and which agrees with it on `[a, b]`
(`ProfileExtension.exists_contDiff_pos_extension`).  The extension is the
convex interpolation `χ·f + (1 - χ)·1` against a smooth bump `χ` which is `1`
on `[a, b]` and supported well inside the neighbourhood; positivity is then
automatic because both `f` and the constant `1` are positive, and smoothness
because the interpolation is constantly `1` outside the support of the bump.

`ProfileExtension.exists_contDiff_pos_extension_pi` is the instance used by the
hairpin: a profile smooth and positive on a neighbourhood of `[0, π]` has a
smooth positive extension to the line.  What is still not proved here is that
the Section 3 profile is smooth up to (and across) the endpoints; the reduction
is from "smooth and positive on the line" to "smooth and positive near
`[0, π]`".
-/

open Set Metric

open scoped ContDiff

namespace ProfileExtension

/-- **Smooth positive extension.**  A function which is `C^∞` and positive on
the open neighbourhood `(a - r, b + r)` of `[a, b]` agrees on `[a, b]` with a
function which is `C^∞` and positive on the whole line. -/
theorem exists_contDiff_pos_extension {a b r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo (a - r) (b + r)))
    (hpos : ∀ x ∈ Ioo (a - r) (b + r), 0 < f x) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ (∀ x, 0 < F x) ∧ ∀ x ∈ Icc a b, F x = f x := by
  set U : Set ℝ := Ioo (a - r) (b + r) with hU
  have hUopen : IsOpen U := isOpen_Ioo
  set c : ℝ := (a + b) / 2 with hc
  -- the bump: `1` on `[a, b]`, supported in `(a - 2r/3, b + 2r/3)`
  have hrIn : 0 < (b - a) / 2 + r / 3 := by linarith
  have hrLt : (b - a) / 2 + r / 3 < (b - a) / 2 + 2 * r / 3 := by linarith
  set chi : ContDiffBump c :=
    { rIn := (b - a) / 2 + r / 3
      rOut := (b - a) / 2 + 2 * r / 3
      rIn_pos := hrIn
      rIn_lt_rOut := hrLt } with hchi
  have hrOut : chi.rOut = (b - a) / 2 + 2 * r / 3 := rfl
  -- the closed ball on which the bump lives sits inside the neighbourhood
  have hball : closedBall c chi.rOut ⊆ U := by
    intro x hx
    rw [mem_closedBall, Real.dist_eq, abs_le] at hx
    rw [hrOut] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hIcc : Icc a b ⊆ closedBall c chi.rIn := by
    intro x hx
    rw [mem_closedBall, Real.dist_eq, abs_le]
    have h1 : chi.rIn = (b - a) / 2 + r / 3 := rfl
    rw [h1]
    exact ⟨by simp only [hc]; linarith [hx.1], by simp only [hc]; linarith [hx.2]⟩
  have hIccU : Icc a b ⊆ U := hIcc.trans (closedBall_subset_closedBall hrLt.le) |>.trans hball
  classical
  refine ⟨fun x => if x ∈ U then chi x * f x + (1 - chi x) else 1, ?_, ?_, ?_⟩
  · -- smoothness, checked pointwise
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · have hnhds : U ∈ nhds x := hUopen.mem_nhds hx
      have heq : (fun y => if y ∈ U then chi y * f y + (1 - chi y) else 1)
          =ᶠ[nhds x] fun y => chi y * f y + (1 - chi y) := by
        filter_upwards [hnhds] with y hy using if_pos hy
      refine ContDiffAt.congr_of_eventuallyEq ?_ heq
      have hchiAt : ContDiffAt ℝ ∞ (fun y : ℝ => (chi : ℝ → ℝ) y) x :=
        (chi.contDiff (n := ⊤)).contDiffAt
      exact (hchiAt.mul (hf.contDiffAt hnhds)).add (contDiffAt_const.sub hchiAt)
    · have hxb : x ∉ closedBall c chi.rOut := fun h => hx (hball h)
      have hV : (closedBall c chi.rOut)ᶜ ∈ nhds x :=
        (isClosed_closedBall.isOpen_compl).mem_nhds hxb
      have heq : (fun y => if y ∈ U then chi y * f y + (1 - chi y) else 1)
          =ᶠ[nhds x] fun _ : ℝ => (1 : ℝ) := by
        filter_upwards [hV] with y hy
        by_cases hyU : y ∈ U
        · have hy0 : (chi : ℝ → ℝ) y = 0 := by
            by_contra hne
            exact hy (ball_subset_closedBall (chi.support_eq ▸ hne))
          simp [hyU, hy0]
        · simp [hyU]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · -- positivity
    intro x
    by_cases hx : x ∈ U
    · simp only [hx, if_pos]
      have h0 : 0 ≤ (chi : ℝ → ℝ) x := chi.nonneg
      have h1 : (chi : ℝ → ℝ) x ≤ 1 := chi.le_one
      have hfx : 0 < f x := hpos x hx
      rcases eq_or_lt_of_le h0 with h | h
      · rw [← h]; norm_num
      · nlinarith [mul_pos h hfx]
    · simp [hx]
  · -- the extension agrees with `f` on `[a, b]`
    intro x hx
    have hxU : x ∈ U := hIccU hx
    have hchi1 : (chi : ℝ → ℝ) x = 1 := chi.one_of_mem_closedBall (hIcc hx)
    simp [hxU, hchi1]

/-- **Smooth positive extension of the profile.**  A profile smooth and
positive on a neighbourhood of `[0, π]` agrees on `[0, π]` with a profile
smooth and positive on the whole line, which is the form in which the
statements of this project about the hairpin take it. -/
theorem exists_contDiff_pos_extension_pi {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo (-r) (Real.pi + r)))
    (hpos : ∀ x ∈ Ioo (-r) (Real.pi + r), 0 < f x) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ (∀ x, 0 < F x) ∧
      ∀ x ∈ Icc (0:ℝ) Real.pi, F x = f x := by
  have h := exists_contDiff_pos_extension (a := 0) (b := Real.pi) Real.pi_pos.le hr
    (f := f) (by simpa using hf) (by simpa using hpos)
  simpa using h

end ProfileExtension
