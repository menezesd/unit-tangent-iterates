import Mathlib

/-! # Directional width stability under Hausdorff perturbation -/

open Set

namespace HausdorffWidthStability

/-- A set has lower and upper support values for a scalar projection, with
both extrema attained. -/
structure WidthWitness {E : Type*} (f : E → ℝ) (A : Set E) (lo hi : ℝ) : Prop where
  lower : ∀ x ∈ A, lo ≤ f x
  upper : ∀ x ∈ A, f x ≤ hi
  exists_lower : ∃ x ∈ A, f x = lo
  exists_upper : ∃ x ∈ A, f x = hi

/-- Symmetric pointwise matching formulation of Hausdorff distance at most
`d`. -/
structure HausdorffMatch {E : Type*} [PseudoMetricSpace E]
    (A B : Set E) (d : ℝ) : Prop where
  to_right : ∀ x ∈ A, ∃ y ∈ B, dist x y ≤ d
  to_left : ∀ y ∈ B, ∃ x ∈ A, dist x y ≤ d

/-- A Hausdorff perturbation of size `d` changes the width measured by a
`1`-Lipschitz projection by at most `2d`.  This is the elementary estimate used
in the paper's final noncircularity argument. -/
theorem abs_width_sub_width_le_two_mul
    {E : Type*} [PseudoMetricSpace E] {f : E → ℝ} {A B : Set E}
    {loA hiA loB hiB d : ℝ}
    (hf : LipschitzWith 1 f)
    (hA : WidthWitness f A loA hiA) (hB : WidthWitness f B loB hiB)
    (hmatch : HausdorffMatch A B d) :
    |(hiA - loA) - (hiB - loB)| ≤ 2 * d := by
  obtain ⟨xa, hxa, hfaxa⟩ := hA.exists_upper
  obtain ⟨yb, hyb, hfyb⟩ := hB.exists_upper
  obtain ⟨ya, hya, hxaya⟩ := hmatch.to_right xa hxa
  obtain ⟨xb, hxb, hybxb⟩ := hmatch.to_left yb hyb
  have hhiAB : hiA ≤ hiB + d := by
    have hlip := hf.dist_le_mul xa ya
    norm_num [Real.dist_eq, hfaxa] at hlip
    have := hB.upper ya hya
    nlinarith [le_trans (le_abs_self (hiA - f ya)) hlip]
  have hhiBA : hiB ≤ hiA + d := by
    have hlip := hf.dist_le_mul yb xb
    norm_num [Real.dist_eq, hfyb] at hlip
    rw [dist_comm] at hlip
    have := hA.upper xb hxb
    nlinarith [le_trans (le_abs_self (hiB - f xb)) hlip]
  obtain ⟨xal, hxal, hfaxal⟩ := hA.exists_lower
  obtain ⟨ybl, hybl, hfybl⟩ := hB.exists_lower
  obtain ⟨yal, hyal, hxalyal⟩ := hmatch.to_right xal hxal
  obtain ⟨xbl, hxbl, hyblxbl⟩ := hmatch.to_left ybl hybl
  have hloAB : loB ≤ loA + d := by
    have hlip := hf.dist_le_mul xal yal
    norm_num [Real.dist_eq, hfaxal] at hlip
    rw [abs_sub_comm] at hlip
    have := hB.lower yal hyal
    nlinarith [le_trans (le_abs_self (f yal - loA)) hlip]
  have hloBA : loA ≤ loB + d := by
    have hlip := hf.dist_le_mul ybl xbl
    norm_num [Real.dist_eq, hfybl] at hlip
    rw [abs_sub_comm, dist_comm] at hlip
    have := hA.lower xbl hxbl
    nlinarith [le_trans (le_abs_self (f xbl - loB)) hlip]
  rw [abs_le]
  constructor <;> linarith

/-- One-sided form used when only an upper bound for the perturbed width is
needed. -/
theorem width_le_width_add_two_mul
    {E : Type*} [PseudoMetricSpace E] {f : E → ℝ} {A B : Set E}
    {loA hiA loB hiB d : ℝ}
    (hf : LipschitzWith 1 f)
    (hA : WidthWitness f A loA hiA) (hB : WidthWitness f B loB hiB)
    (hmatch : HausdorffMatch A B d) :
    hiA - loA ≤ hiB - loB + 2 * d := by
  have h := abs_width_sub_width_le_two_mul hf hA hB hmatch
  linarith [le_trans (le_abs_self ((hiA - loA) - (hiB - loB))) h]

end HausdorffWidthStability
