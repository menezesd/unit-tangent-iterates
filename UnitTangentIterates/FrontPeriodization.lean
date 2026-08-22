import Mathlib

/-!
# The front periodization error

This file formalizes the self-contained core of the lemma *Front periodization
error* of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*.

The paper writes the front curvature of a periodized configuration as

`K_L = Y_L + G(Y_L) Y_L'`,  `G(z) = 1/√(1 - z²)`,  `Y_L = ∑_m y_m`,

while the isolated pulses contribute `K_*(s - mL) = y_m + G(y_m) y_m'`.  The
difference is therefore exactly `∑_m y_m' (G(Y_L) - G(y_m))`, and the Lipschitz
character of `G` on a fixed interval `[0,a]` with `a < 1`, together with the
relative derivative bound `|y_m'| ≤ D y_m`, turns this into the overlap sum
`C ∑_{m ≠ n} y_m y_n`.

Main results:

* `hasDerivAt_G`, `lipschitz_G` : `G(z) = (1 - z²)^{-1/2}` is Lipschitz on
  `[0,a]` with the explicit constant `a / ((1-a²)√(1-a²))`;
* `front_error_eq` : the exact identity
  `K_L - ∑ K_*(· - mL) = ∑_m y_m' (G(Y_L) - G(y_m))`;
* `front_error_le` : the resulting overlap bound
  `|K_L - ∑ K_*(· - mL)| ≤ Lip(a) · D · ∑_{m ≠ n} y_m y_n`.

Sums are taken over an arbitrary finite index set; in the paper the index set
is `ℤ`, and the passage to the infinite sum is the (already formalized)
summability of the periodized series.
-/

noncomputable section

open Real

namespace FrontPeriodization

/-- The profile `G(z) = 1/√(1 - z²)` appearing in the front curvature. -/
noncomputable def G (z : ℝ) : ℝ := (Real.sqrt (1 - z ^ 2))⁻¹

/-- The explicit Lipschitz constant of `G` on `[0,a]`. -/
noncomputable def lipConst (a : ℝ) : ℝ := a / ((1 - a ^ 2) * Real.sqrt (1 - a ^ 2))

lemma lipConst_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) : 0 ≤ lipConst a := by
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  have : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr ha2
  unfold lipConst
  positivity

/-- The derivative of `G(z) = (1 - z²)^{-1/2}` on `(-1,1)`. -/
theorem hasDerivAt_G {x : ℝ} (hx : |x| < 1) :
    HasDerivAt G (x / ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2))) x := by
  have h1 : 0 < 1 - x ^ 2 := by nlinarith [sq_abs x, abs_lt.mp hx]
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr h1
  have hd : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have hsq : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
      (-(2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x := hd.sqrt (ne_of_gt h1)
  have h := hsq.inv (ne_of_gt hs)
  convert h using 1
  rw [Real.sq_sqrt h1.le]
  field_simp

/-- **`G` is Lipschitz on `[0,a]`** with constant `a / ((1-a²)√(1-a²))`. -/
theorem lipschitz_G {a z w : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hz : z ∈ Set.Icc (0 : ℝ) a) (hw : w ∈ Set.Icc (0 : ℝ) a) :
    |G z - G w| ≤ lipConst a * |z - w| := by
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  have hsa : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr ha2
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) a,
      ‖x / ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2))‖ ≤ lipConst a := by
    intro x hx
    obtain ⟨hx0, hxa⟩ := hx
    have h1 : 0 < 1 - x ^ 2 := by nlinarith
    have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr h1
    have hmono : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - x ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine div_le_div₀ ha0 hxa (by positivity) ?_
    exact mul_le_mul (by nlinarith) hmono hsa.le (by nlinarith)
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) a,
      HasDerivWithinAt G (x / ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2))) (Set.Icc (0 : ℝ) a) x := by
    intro x hx
    have hx1 : |x| < 1 := by rw [abs_of_nonneg hx.1]; linarith [hx.2]
    exact (hasDerivAt_G hx1).hasDerivWithinAt
  have h := (convex_Icc (0 : ℝ) a).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound hw hz
  simpa [Real.norm_eq_abs] using h

section Sums

variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (y yp : ι → ℝ)

omit [DecidableEq ι] in
/-- **The exact front periodization identity.**  The difference between the
periodized front curvature `Y + G(Y)Y'` and the sum of the isolated
contributions `y_m + G(y_m) y_m'` is `∑_m y_m' (G(Y) - G(y_m))`. -/
theorem front_error_eq :
    ((∑ i ∈ s, y i) + G (∑ i ∈ s, y i) * (∑ i ∈ s, yp i))
        - ∑ i ∈ s, (y i + G (y i) * yp i)
      = ∑ i ∈ s, yp i * (G (∑ i ∈ s, y i) - G (y i)) := by
  simp only [Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf
  rw [Finset.sum_congr rfl (fun i _ => by ring : ∀ i ∈ s, G (y i) * yp i = yp i * G (y i))]

/-- **Front periodization error.**  If all pulses and their sum take values in
`[0,a]` with `a < 1`, and the relative derivative bound `|y_m'| ≤ D y_m` holds,
then the front periodization error is controlled by the overlap sum
`∑_{m ≠ n} y_m y_n`. -/
theorem front_error_le {a D : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hD : 0 ≤ D)
    (hy0 : ∀ i ∈ s, 0 ≤ y i) (hya : ∀ i ∈ s, y i ≤ a)
    (hY : (∑ i ∈ s, y i) ≤ a)
    (hyp : ∀ i ∈ s, |yp i| ≤ D * y i) :
    |((∑ i ∈ s, y i) + G (∑ i ∈ s, y i) * (∑ i ∈ s, yp i))
        - ∑ i ∈ s, (y i + G (y i) * yp i)|
      ≤ lipConst a * D * ∑ i ∈ s, ∑ j ∈ s.erase i, y i * y j := by
  have hY0 : 0 ≤ ∑ i ∈ s, y i := Finset.sum_nonneg hy0
  have hLip0 : 0 ≤ lipConst a := lipConst_nonneg ha0 ha1
  rw [front_error_eq s y yp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hyi0 : 0 ≤ y i := hy0 i hi
  have htail : (∑ i ∈ s, y i) - y i = ∑ j ∈ s.erase i, y j :=
    (Finset.sum_erase_eq_sub hi).symm
  have htail0 : 0 ≤ ∑ j ∈ s.erase i, y j :=
    Finset.sum_nonneg fun j hj => hy0 j (Finset.mem_of_mem_erase hj)
  have hGdiff : |G (∑ i ∈ s, y i) - G (y i)| ≤ lipConst a * ∑ j ∈ s.erase i, y j := by
    have := lipschitz_G ha0 ha1 (Set.mem_Icc.mpr ⟨hY0, hY⟩)
      (Set.mem_Icc.mpr ⟨hyi0, hya i hi⟩)
    rwa [htail, abs_of_nonneg htail0] at this
  calc |yp i * (G (∑ i ∈ s, y i) - G (y i))|
      = |yp i| * |G (∑ i ∈ s, y i) - G (y i)| := abs_mul _ _
    _ ≤ (D * y i) * (lipConst a * ∑ j ∈ s.erase i, y j) := by
        apply mul_le_mul (hyp i hi) hGdiff (abs_nonneg _) (by positivity)
    _ = lipConst a * D * ∑ j ∈ s.erase i, y i * y j := by
        rw [← Finset.mul_sum]; ring
end Sums

end FrontPeriodization
