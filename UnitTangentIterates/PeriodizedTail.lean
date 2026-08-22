import Mathlib
import UnitTangentIterates.MatchingEstimates

/-!
# The mass of the omitted translates equals the mass outside the cell

In the proof of the theorem *Curvature-measure matching* of *A Noncircular Oval
with Convex Unit-Tangent Iterates*, the third term of the matching split is
handled by the change of variables `u = x_H(s)` followed by the identity

`∫_{J_H} ∑_{j ≠ 0} K_*(u − jP) du = ∫_{ℝ ∖ J_H} K_*(v) dv`,

where `J_H` is a fundamental interval of length `P`: the translates `J_H − jP`,
`j ≠ 0`, tile the complement of `J_H`.  The right-hand side is then
exponentially small, because `K_*` is exponentially localized and the endpoints
of `J_H` are `±H/2 + O(1)`.

This file formalizes that identity and the resulting estimate.

Main results:

* `mem_cell_iff`, `pairwise_disjoint_cell`, `iUnion_cell_ne_zero` : the
  translates `J − jP` of the half-open cell `J = [p, p+P)` tile the line, the
  nonzero ones tiling the complement of `J`;
* `setIntegral_cell` : `∫_{J−jP} f = ∫_J f(· − jP)`;
* `integral_tsum_translates` : **the tiling identity**
  `∫_J ∑_{j≠0} f(u − jP) du = ∫_{ℝ∖J} f`;
* `integral_tsum_translates_le` : with an exponentially localized `f`, the
  omitted mass is at most `C(e^{αp} + e^{-α(p+P)})/α`.
-/

noncomputable section

open MeasureTheory Set

namespace PeriodizedTail

variable {p P : ℝ} {f : ℝ → ℝ}

/-- The translate `J − jP` of the half-open cell `J = [p, p+P)`. -/
def cell (p P : ℝ) (j : ℤ) : Set ℝ := Ico (p - j * P) (p - j * P + P)

@[simp] theorem cell_zero : cell p P 0 = Ico p (p + P) := by simp [cell]

theorem measurableSet_cell (j : ℤ) : MeasurableSet (cell p P j) := measurableSet_Ico

/-- A point lies in the translate `J − jP` exactly for one index `j`, namely
`j = -⌊(u-p)/P⌋`. -/
theorem mem_cell_iff (hP : 0 < P) (j : ℤ) (u : ℝ) :
    u ∈ cell p P j ↔ j = -⌊(u - p) / P⌋ := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ((-j : ℤ) : ℝ) ≤ (u - p) / P := by
      rw [le_div_iff₀ hP]; push_cast; linarith
    have h4 : (u - p) / P < (-j : ℤ) + 1 := by
      rw [div_lt_iff₀ hP]; push_cast; linarith
    have := Int.floor_eq_iff.mpr ⟨h3, h4⟩
    omega
  · rintro rfl
    have h1 : (⌊(u - p) / P⌋ : ℝ) ≤ (u - p) / P := Int.floor_le _
    have h2 : (u - p) / P < ⌊(u - p) / P⌋ + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hP] at h1
    rw [div_lt_iff₀ hP] at h2
    constructor <;> push_cast <;> [linarith; linarith]

theorem pairwise_disjoint_cell (hP : 0 < P) :
    Pairwise (Function.onFun Disjoint (cell p P)) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro u hi hj
  rw [mem_cell_iff hP] at hi hj
  exact hij (hi.trans hj.symm)

/-- **Tiling.**  The nonzero translates of the cell tile the complement of the
cell. -/
theorem iUnion_cell_ne_zero (hP : 0 < P) :
    (⋃ j : {j : ℤ // j ≠ 0}, cell p P (j : ℤ)) = (Ico p (p + P))ᶜ := by
  ext u
  simp only [mem_iUnion, mem_compl_iff, Subtype.exists]
  constructor
  · rintro ⟨j, hj, hu⟩ hmem
    rw [mem_cell_iff hP] at hu
    have h0 : (0 : ℤ) = -⌊(u - p) / P⌋ := by
      rw [← mem_cell_iff hP]
      simpa using hmem
    exact hj (hu.trans h0.symm)
  · intro hmem
    refine ⟨-⌊(u - p) / P⌋, ?_, (mem_cell_iff hP _ u).mpr rfl⟩
    intro h0
    apply hmem
    have : u ∈ cell p P 0 := (mem_cell_iff hP 0 u).mpr h0.symm
    simpa using this

/-- The integral over the translated cell is the integral over the cell of the
translated function. -/
theorem setIntegral_cell (f : ℝ → ℝ) (j : ℤ) :
    (∫ u in cell p P j, f u) = ∫ u in Ico p (p + P), f (u - j * P) := by
  have hind : ∀ u : ℝ, (Ico p (p + P)).indicator (fun u => f (u - j * P)) u
      = (cell p P j).indicator f (u - j * P) := by
    intro u
    by_cases hu : u ∈ Ico p (p + P)
    · have hu' : u - j * P ∈ cell p P j := by
        rcases hu with ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      rw [indicator_of_mem hu, indicator_of_mem hu']
    · have hu' : u - j * P ∉ cell p P j := by
        intro hc
        exact hu ⟨by have := hc.1; linarith, by have := hc.2; linarith⟩
      rw [indicator_of_notMem hu, indicator_of_notMem hu']
  calc (∫ u in cell p P j, f u) = ∫ u : ℝ, (cell p P j).indicator f u := by
        rw [integral_indicator (measurableSet_cell j)]
    _ = ∫ u : ℝ, (cell p P j).indicator f (u - j * P) :=
        (MeasureTheory.integral_sub_right_eq_self
          (fun u => (cell p P j).indicator f u) ((j : ℝ) * P)).symm
    _ = ∫ u : ℝ, (Ico p (p + P)).indicator (fun u => f (u - j * P)) u := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun u => (hind u).symm)
    _ = ∫ u in Ico p (p + P), f (u - j * P) := integral_indicator measurableSet_Ico

/-- **The tiling identity.**  For a nonnegative integrable `f`, the mass of the
omitted translates over one cell equals the mass of `f` outside the cell. -/
theorem integral_tsum_translates (hP : 0 < P) (hf : Integrable f) (hf0 : ∀ u, 0 ≤ f u) :
    (∫ u in Ico p (p + P), ∑' j : {j : ℤ // j ≠ 0}, f (u - (j : ℤ) * P))
      = ∫ u in (Ico p (p + P))ᶜ, f u := by
  set ι := {j : ℤ // j ≠ 0}
  have hmeas : ∀ i : ι, MeasurableSet (cell p P (i : ℤ)) := fun i => measurableSet_cell _
  have hdisj : Pairwise (Function.onFun Disjoint fun i : ι => cell p P (i : ℤ)) := by
    intro i j hij
    exact pairwise_disjoint_cell hP (fun hc => hij (Subtype.ext hc))
  have hunion : (⋃ i : ι, cell p P (i : ℤ)) = (Ico p (p + P))ᶜ := iUnion_cell_ne_zero hP
  have hint : IntegrableOn f (⋃ i : ι, cell p P (i : ℤ)) := hf.integrableOn
  have hsum := MeasureTheory.hasSum_integral_iUnion hmeas hdisj hint
  -- the same sum, written on the cell
  have hcell : ∀ i : ι, (∫ u in cell p P (i : ℤ), f u)
      = ∫ u in Ico p (p + P), f (u - (i : ℤ) * P) := fun i => setIntegral_cell f _
  have hsum' : HasSum (fun i : ι => ∫ u in Ico p (p + P), f (u - (i : ℤ) * P))
      (∫ u in (Ico p (p + P))ᶜ, f u) := by
    have := hsum
    rw [hunion] at this
    exact this.congr_fun (fun i => (hcell i).symm)
  -- interchange the sum and the integral
  have hFint : ∀ i : ι, Integrable (fun u => f (u - (i : ℤ) * P))
      (volume.restrict (Ico p (p + P))) :=
    fun i => (hf.comp_sub_right ((i : ℤ) * P)).integrableOn
  have hnormsummable : Summable fun i : ι =>
      ∫ u in Ico p (p + P), ‖f (u - (i : ℤ) * P)‖ := by
    refine hsum'.summable.congr (fun i => ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      simp [Real.norm_eq_abs, abs_of_nonneg (hf0 _)])
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ico p (p + P))) hFint hnormsummable
  rw [← hswap]
  exact hsum'.tsum_eq

/-- **The omitted mass is exponentially small.**  If `f` is nonnegative,
integrable and bounded by `Ce^{-α|·|}`, then the mass of the omitted translates
over the cell `[p, p+P)` is at most `C(e^{αp} + e^{-α(p+P)})/α`, provided the
cell contains the origin. -/
theorem integral_tsum_translates_le {C alpha : ℝ} (hP : 0 < P) (halpha : 0 < alpha)
    (hf : Integrable f) (hf0 : ∀ u, 0 ≤ f u)
    (hbd : ∀ s, |f s| ≤ C * Real.exp (-alpha * |s|))
    (hp : p ≤ 0) (hq : 0 ≤ p + P) :
    (∫ u in Ico p (p + P), ∑' j : {j : ℤ // j ≠ 0}, f (u - (j : ℤ) * P))
      ≤ C * Real.exp (alpha * p) / alpha + C * Real.exp (-alpha * (p + P)) / alpha := by
  rw [integral_tsum_translates hP hf hf0]
  have hsplit : (∫ u in (Ico p (p + P))ᶜ, f u) = (∫ u : ℝ, f u) - ∫ u in Ico p (p + P), f u := by
    have := MeasureTheory.integral_add_compl (μ := volume) (f := f)
      (s := Ico p (p + P)) measurableSet_Ico hf
    linarith [this]
  have hIoc : (∫ u in Ico p (p + P), f u) = ∫ u in p..(p + P), f u := by
    rw [intervalIntegral.integral_of_le (by linarith : p ≤ p + P)]
    rw [integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  rw [hsplit, hIoc]
  have habs := MatchingEstimates.abs_integral_compl_le (g := f) halpha hp hq hf hbd
  have := (abs_le.mp habs).2
  linarith

end PeriodizedTail
