import UnitTangentIterates.AnchoredJacobiStableTransition
import UnitTangentIterates.RegularizingBackwardShadowingNoDiscard

/-!
# Physical uniqueness from triangular Jacobi comparison paths

The uniqueness paragraph of `thm:shadow` does not assume that the selected
inverse is globally non-expansive in a marked metric.  Instead, a comparison
path at a late terminal level is propagated backwards.  Its four components
remain bounded by one depth-independent multiple of the late tube radius, and
that radius tends to zero.

This file formalizes that exact last argument.  It also records the local
max-gauge invariance of the unanchored Jacobi estimates.  In particular, it
does not replace the paper's triangular estimates by a false weighted-sum
contraction.
-/

noncomputable section

open Filter Topology MarkedTopology
open AnchoredJacobiStableTransition

namespace RegularizingBackwardShadowingPhysicalUniqueness

/-- The fourth invariant coefficient in the max-type Jacobi tube gauge. -/
def rawS2Const (C2 M0 M1 : ℝ) : ℝ :=
  max 1 (C2 * (1 + M0 + M1))

/-- A component vector lies in the max-type tube of radius `r`. -/
structure RawRadius (M0 M1 M2 r : ℝ) (V : Components) : Prop where
  w : V.w ≤ r
  s0 : V.s0 ≤ M0 * r
  s1 : V.s1 ≤ M1 * r
  s2 : V.s2 ≤ M2 * r

/-- The raw Jacobi transition preserves the paper's max-type component tube.
This is the correct local non-expansiveness statement: `W` is retained while
higher components are reset from lower ones. -/
theorem RawJacobiBounds.rawRadius
    {front rear : ℝ → ℝ → ℝ} {C0 C1 C2 M0 M1 r : ℝ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hr : 0 ≤ r)
    (hM0 : M0 = max 1 C0)
    (hM1 : M1 = max 1 (C1 * (1 + M0)))
    (Hfront : RawRadius M0 M1 (rawS2Const C2 M0 M1) r
      (components front))
    (H : RawJacobiBounds front rear C0 C1 C2) :
    RawRadius M0 M1 (rawS2Const C2 M0 M1) r (components rear) := by
  have hM0C0 : C0 ≤ M0 := by rw [hM0]; exact le_max_right _ _
  have hM1C1 : C1 * (1 + M0) ≤ M1 := by
    rw [hM1]; exact le_max_right _ _
  have hM20 : C2 * (1 + M0 + M1) ≤ rawS2Const C2 M0 M1 :=
    le_max_right _ _
  refine ⟨H.w.trans Hfront.w, ?_, ?_, ?_⟩
  · calc
      S 0 rear ≤ C0 * W front 1 := H.s0
      _ ≤ C0 * r := mul_le_mul_of_nonneg_left Hfront.w hC0
      _ ≤ M0 * r := mul_le_mul_of_nonneg_right hM0C0 hr
  · have hsum : W front 1 + S 0 front ≤ (1 + M0) * r := by
      have hw : W front 1 ≤ r := Hfront.w
      have hs0 : S 0 front ≤ M0 * r := Hfront.s0
      nlinarith
    calc
      S 1 rear ≤ C1 * (W front 1 + S 0 front) := H.s1
      _ ≤ C1 * ((1 + M0) * r) := mul_le_mul_of_nonneg_left hsum hC1
      _ = (C1 * (1 + M0)) * r := by ring
      _ ≤ M1 * r := mul_le_mul_of_nonneg_right hM1C1 hr
  · have hsum : W front 1 + S 0 front + S 1 front ≤
        (1 + M0 + M1) * r := by
      have hw : W front 1 ≤ r := Hfront.w
      have hs0 : S 0 front ≤ M0 * r := Hfront.s0
      have hs1 : S 1 front ≤ M1 * r := Hfront.s1
      nlinarith
    calc
      S 2 rear ≤ C2 * (W front 1 + S 0 front + S 1 front) := H.s2
      _ ≤ C2 * ((1 + M0 + M1) * r) :=
        mul_le_mul_of_nonneg_left hsum hC2
      _ = (C2 * (1 + M0 + M1)) * r := by ring
      _ ≤ rawS2Const C2 M0 M1 * r :=
        mul_le_mul_of_nonneg_right hM20 hr

/-- The exact limit step in the paper's uniqueness proof.  A comparison bound
at fixed level `n` may be obtained by propagating a path from any later level
`N=n+k`; no metric non-expansiveness of the inverse map is assumed. -/
theorem unique_of_backward_comparison
    {M : Type*} [MetricSpace M]
    {X Y : ℕ → M} {radius : ℕ → ℝ} {C : ℝ}
    (hradius : Tendsto radius atTop (nhds 0))
    (hcompare : ∀ n k, dist (X n) (Y n) ≤ C * radius (n + k)) :
    X = Y := by
  funext n
  have hshift : Tendsto (fun k => radius (n + k)) atTop (nhds 0) := by
    have H := hradius.comp (Filter.tendsto_add_atTop_nat n)
    simpa [Function.comp, Nat.add_comm] using H
  have hlim : Tendsto (fun k => C * radius (n + k)) atTop (nhds 0) := by
    simpa using hshift.const_mul C
  have hzero : dist (X n) (Y n) ≤ 0 :=
    ge_of_tendsto' hlim (hcompare n)
  exact dist_le_zero.mp hzero

/-- Stable anchored Jacobi transitions imply the comparison estimate required
by `unique_of_backward_comparison`.  The final `distance_of_components` field
is the ordinary geometric estimate attached to the propagated comparison
path; all depth dependence is discharged here by
`AnchoredJacobiStableTransition.depth_uniform_components`. -/
theorem unique_of_anchored_component_comparisons
    {M : Type*} [MetricSpace M]
    {X Y : ℕ → M} {radius : ℕ → ℝ}
    {alpha MA NA : ℕ → ℝ}
    {Aw AM AN C0 C1 C2 Cmetric : ℝ}
    (B : DistortionBudget alpha MA NA Aw AM AN)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hCmetric : 0 ≤ Cmetric)
    (hradius0 : ∀ N, 0 ≤ radius N)
    (hradius : Tendsto radius atTop (nhds 0))
    (V : ℕ → ℕ → ℕ → Components)
    (hV : ∀ n N k, (V n N k).Nonnegative)
    (hinit : ∀ n N,
      (V n N 0).w ≤ radius N ∧
      (V n N 0).s0 ≤ radius N ∧
      (V n N 0).s1 ≤ radius N ∧
      (V n N 0).s2 ≤ radius N)
    (hstep : ∀ n N k, Transition (V n N k) (V n N (k + 1))
      (alpha k) (MA k) (NA k) C0 C1 C2)
    (distance_of_components : ∀ n k,
      dist (X n) (Y n) ≤ Cmetric *
        ((V n (n + k) k).w + (V n (n + k) k).s0 +
          (V n (n + k) k).s1 + (V n (n + k) k).s2)) :
    X = Y := by
  let E := stableConst Aw AM AN C0 C1 C2
  have hbound : ∀ n k,
      (V n (n + k) k).w ≤ E * radius (n + k) ∧
      (V n (n + k) k).s0 ≤ E * radius (n + k) ∧
      (V n (n + k) k).s1 ≤ E * radius (n + k) ∧
      (V n (n + k) k).s2 ≤ E * radius (n + k) := by
    intro n k
    exact depth_uniform_components B hC0 hC1 hC2 (hradius0 (n + k))
      (hV n (n + k)) (hinit n (n + k)) (hstep n (n + k)) k
  have hE0 : 0 ≤ E := by
    dsimp [E, stableConst]
    exact (Real.exp_pos Aw).le.trans (le_max_left _ _)
  apply unique_of_backward_comparison (C := 4 * Cmetric * E) hradius
  intro n k
  have hdist := distance_of_components n k
  obtain ⟨hw, hs0, hs1, hs2⟩ := hbound n k
  calc
    dist (X n) (Y n) ≤ Cmetric *
        ((V n (n + k) k).w + (V n (n + k) k).s0 +
          (V n (n + k) k).s1 + (V n (n + k) k).s2) := hdist
    _ ≤ Cmetric * (4 * E * radius (n + k)) := by
      apply mul_le_mul_of_nonneg_left _ hCmetric
      nlinarith
    _ = (4 * Cmetric * E) * radius (n + k) := by ring

end RegularizingBackwardShadowingPhysicalUniqueness
