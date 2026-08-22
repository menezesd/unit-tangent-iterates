import Mathlib
import UnitTangentIterates.PeriodizedTail
import UnitTangentIterates.L1Matching

/-!
# The integrated overlap of the pulses

In the proof of the theorem *Curvature-measure matching* of *A Noncircular Oval
with Convex Unit-Tangent Iterates* the front periodization error is controlled
by the **overlap sum** of the pulses, and the paper's estimate for it is

```
  ∫_{−L/2}^{L/2} ∑_{m ≠ n} y_m(s) y_n(s) ds ≤ C e^{−βL} ,     y_m(s) = y(s − mL) ,
```

obtained "by writing `n = m + q`, unfolding the sum over `m` to `ℝ`, and
summing the convolution estimate over `q ≠ 0`".

This file formalizes that step.  The convolution estimate itself
(`L1Matching.convolution_bound`) and the geometric summation over the
separations (`L1Matching.overlap_series_bound`) were already available; what is
added here is the unfolding:

* `iUnion_cell` : the translates of a cell of length `P` tile the line;
* `integral_tsum_translates_all` : hence
  `∫_{cell} ∑_{j ∈ ℤ} f(u − jP) du = ∫_ℝ f` for a nonnegative integrable `f`;
* `integrable_of_exp_bound` : a continuous function with an exponential
  majorant is integrable;
* `integral_overlap_pair` : for a fixed separation `q ≠ 0`, unfolding the sum
  over `m` gives `∫_{cell} ∑_m y_m y_{m+q} = ∫_ℝ y(s)y(s − qP) ds`;
* `pairwise_overlap_integral_le` : **the estimate**, in the form
  `∑_{q ≠ 0} ∫_{cell} ∑_m y_m y_{m+q} ≤ (8C²/(α−β)) e^{−βP}` (the sum over the
  separations is kept outside the integral).
-/

noncomputable section

open MeasureTheory Set

namespace OverlapIntegral

open PeriodizedTail

variable {p P : ℝ} {f y : ℝ → ℝ}

/-! ### Tiling by all translates of a cell -/

/-- **Tiling.**  The translates `J − jP` of the half-open cell `J = [p, p+P)`
cover the line. -/
theorem iUnion_cell (hP : 0 < P) : (⋃ j : ℤ, cell p P j) = univ := by
  ext u
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨-⌊(u - p) / P⌋, (mem_cell_iff hP _ u).mpr rfl⟩

/-- **The full tiling identity.**  For a nonnegative integrable `f`, the mass of
all translates of `f` over one cell is the total mass of `f`. -/
theorem integral_tsum_translates_all (hP : 0 < P) (hf : Integrable f) (hf0 : ∀ u, 0 ≤ f u) :
    (∫ u in Ico p (p + P), ∑' j : ℤ, f (u - (j : ℤ) * P)) = ∫ u : ℝ, f u := by
  have hmeas : ∀ i : ℤ, MeasurableSet (cell p P i) := fun i => measurableSet_cell _
  have hdisj : Pairwise (Function.onFun Disjoint fun i : ℤ => cell p P i) :=
    pairwise_disjoint_cell hP
  have hunion : (⋃ i : ℤ, cell p P i) = (univ : Set ℝ) := iUnion_cell hP
  have hint : IntegrableOn f (⋃ i : ℤ, cell p P i) := hf.integrableOn
  have hsum := MeasureTheory.hasSum_integral_iUnion hmeas hdisj hint
  rw [hunion, setIntegral_univ] at hsum
  have hcell : ∀ i : ℤ, (∫ u in cell p P i, f u)
      = ∫ u in Ico p (p + P), f (u - (i : ℤ) * P) := fun i => setIntegral_cell f _
  have hsum' : HasSum (fun i : ℤ => ∫ u in Ico p (p + P), f (u - (i : ℤ) * P))
      (∫ u : ℝ, f u) := hsum.congr_fun (fun i => (hcell i).symm)
  have hFint : ∀ i : ℤ, Integrable (fun u => f (u - (i : ℤ) * P))
      (volume.restrict (Ico p (p + P))) :=
    fun i => (hf.comp_sub_right ((i : ℤ) * P)).integrableOn
  have hnormsummable : Summable fun i : ℤ =>
      ∫ u in Ico p (p + P), ‖f (u - (i : ℤ) * P)‖ := by
    refine hsum'.summable.congr (fun i => ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      simp [Real.norm_eq_abs, abs_of_nonneg (hf0 _)])
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ico p (p + P))) hFint hnormsummable
  rw [← hswap]
  exact hsum'.tsum_eq

/-! ### Integrability from an exponential majorant -/

/-- A continuous function with an exponential majorant is integrable. -/
theorem integrable_of_exp_bound {C alpha : ℝ} (halpha : 0 < alpha) (hcont : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) :
    Integrable y := by
  have hC : 0 ≤ C := by
    have h := hyb 0
    have h0 := hy0 0
    simp at h
    linarith
  refine Integrable.mono ((L1Matching.integrable_expabs halpha).const_mul C)
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hy0 s),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ C * Real.exp (-alpha * |s|))]
  exact hyb s

/-! ### Unfolding one separation -/

/-- **Unfolding the sum over `m` for a fixed separation.**  For `q ≠ 0`, the
overlap of the pulses at separation `qP`, summed over one cell, is the total
overlap integral. -/
theorem integral_overlap_pair {C alpha : ℝ} (hP : 0 < P) (halpha : 0 < alpha)
    (hcont : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) (q : ℤ) :
    (∫ u in Ico p (p + P), ∑' m : ℤ,
        y (u - (m : ℤ) * P) * y (u - (m : ℤ) * P - (q : ℤ) * P))
      = ∫ s : ℝ, y s * y (s - (q : ℤ) * P) := by
  have hyint : Integrable y := integrable_of_exp_bound halpha hcont hy0 hyb
  have hC : 0 ≤ C := by
    have h := hyb 0
    have h0 := hy0 0
    simp at h
    linarith
  have hybound : ∀ s, y s ≤ C := by
    intro s
    refine (hyb s).trans ?_
    have : Real.exp (-alpha * |s|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg s])
    nlinarith
  have hfcont : Continuous fun s => y s * y (s - (q : ℤ) * P) :=
    hcont.mul (hcont.comp (continuous_id.sub continuous_const))
  have hfint : Integrable fun s => y s * y (s - (q : ℤ) * P) := by
    refine Integrable.mono (hyint.const_mul C) hfcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hy0 s) (hy0 _)),
      abs_of_nonneg (mul_nonneg hC (hy0 s))]
    calc y s * y (s - (q : ℤ) * P) ≤ y s * C :=
          mul_le_mul_of_nonneg_left (hybound _) (hy0 s)
      _ = C * y s := by ring
  have hf0 : ∀ s, 0 ≤ y s * y (s - (q : ℤ) * P) := fun s => mul_nonneg (hy0 s) (hy0 _)
  have h := integral_tsum_translates_all (p := p) (P := P)
    (f := fun s => y s * y (s - (q : ℤ) * P)) hP hfint hf0
  refine Eq.trans ?_ h
  refine setIntegral_congr_fun measurableSet_Ico (fun u _ => ?_)
  refine tsum_congr (fun m => ?_)
  ring_nf

/-! ### The estimate -/

/-- **The integrated overlap of the pulses.**  If `0 ≤ y ≤ Ce^{−α|·|}` and
`0 < β < α`, then over one cell of length `P` (with `e^{−βP} ≤ 1/2`) the total
overlap of distinct pulses is exponentially small:

`∑_{q≠0} ∫_{cell} ∑_{m} y(u − mP)y(u − mP − qP) du ≤ (8C²/(α−β)) e^{−βP}`.

This is the paper's estimate `∫_{−L/2}^{L/2} ∑_{m≠n} y_m y_n ≤ Ce^{−βL}`, with
`n = m + q`; the sum over the separations `q` is kept outside the integral, the
sum over `m` — the one the paper unfolds to the line — being inside. -/
theorem pairwise_overlap_integral_le {C alpha beta : ℝ} (hP : 0 < P) (halpha : 0 < alpha)
    (hcont : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hbeta : 0 < beta) (hba : beta < alpha) (hhalf : Real.exp (-(beta * P)) ≤ 1 / 2) :
    (∑' q : {q : ℤ // q ≠ 0}, ∫ u in Ico p (p + P), ∑' m : ℤ,
        y (u - (m : ℤ) * P) * y (u - (m : ℤ) * P - ((q : ℤ) : ℝ) * P))
      ≤ 4 * (2 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) := by
  have hC : 0 ≤ C := by
    have h := hyb 0
    have h0 := hy0 0
    simp at h
    linarith
  have hgap : 0 < alpha - beta := by linarith
  have hconst : 0 ≤ 2 * C ^ 2 / (alpha - beta) := by positivity
  -- the value of each inner integral
  have hpair : ∀ q : {q : ℤ // q ≠ 0},
      (∫ u in Ico p (p + P), ∑' m : ℤ,
          y (u - (m : ℤ) * P) * y (u - (m : ℤ) * P - ((q : ℤ) : ℝ) * P))
        = ∫ s : ℝ, y s * y (s - ((q : ℤ) : ℝ) * P) :=
    fun q => integral_overlap_pair hP halpha hcont hy0 hyb (q : ℤ)
  -- and its bound
  have hbound : ∀ q : {q : ℤ // q ≠ 0},
      (∫ u in Ico p (p + P), ∑' m : ℤ,
          y (u - (m : ℤ) * P) * y (u - (m : ℤ) * P - ((q : ℤ) : ℝ) * P))
        ≤ (2 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) ^ (q : ℤ).natAbs := by
    intro q
    rw [hpair q]
    refine (L1Matching.convolution_bound (r := ((q : ℤ) : ℝ) * P) hy0 hyb hbeta hba).trans ?_
    have habs : |((q : ℤ) : ℝ) * P| = ((q : ℤ).natAbs : ℝ) * P := by
      rw [abs_mul, abs_of_pos hP]
      congr 1
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num
    rw [habs]
    have hpow : Real.exp (-(beta * P)) ^ ((q : ℤ).natAbs)
        = Real.exp (-beta * (((q : ℤ).natAbs : ℝ) * P)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpow]
  -- nonnegativity of the terms
  have hnonneg : ∀ q : {q : ℤ // q ≠ 0},
      0 ≤ ∫ u in Ico p (p + P), ∑' m : ℤ,
        y (u - (m : ℤ) * P) * y (u - (m : ℤ) * P - ((q : ℤ) : ℝ) * P) := by
    intro q
    rw [hpair q]
    exact integral_nonneg (fun s => mul_nonneg (hy0 s) (hy0 _))
  -- the majorant, summed over the separations
  have hmaj : ∀ q : {q : ℤ // q ≠ 0},
      (2 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) ^ (q : ℤ).natAbs
        = (Set.indicator {q : ℤ | q ≠ 0}
            (fun q : ℤ => (2 * C ^ 2 / (alpha - beta))
              * Real.exp (-(beta * P)) ^ q.natAbs) (q : ℤ)) := by
    intro q
    rw [Set.indicator_of_mem (by exact q.2)]
  have hsummaj : Summable fun q : {q : ℤ // q ≠ 0} =>
      (2 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) ^ (q : ℤ).natAbs := by
    have hbase : Summable fun q : ℤ =>
        (if q = 0 then (0 : ℝ)
          else (2 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) ^ q.natAbs) :=
      Periodization.summable_ite_geom_int hconst (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by nlinarith))
    have hind : (fun q : ℤ =>
        (if q = 0 then (0 : ℝ)
          else (2 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) ^ q.natAbs))
        = Set.indicator {q : ℤ | q ≠ 0}
            (fun q : ℤ => (2 * C ^ 2 / (alpha - beta))
              * Real.exp (-(beta * P)) ^ q.natAbs) := by
      funext q
      by_cases hq : q = 0
      · simp [hq]
      · rw [Set.indicator_of_mem (by exact hq), if_neg hq]
    rw [hind] at hbase
    exact (summable_subtype_iff_indicator (s := {q : ℤ | q ≠ 0})).mpr hbase
  have hsummable : Summable fun q : {q : ℤ // q ≠ 0} =>
      ∫ u in Ico p (p + P), ∑' m : ℤ,
        y (u - (m : ℤ) * P) * y (u - (m : ℤ) * P - ((q : ℤ) : ℝ) * P) :=
    Summable.of_nonneg_of_le hnonneg hbound hsummaj
  -- compare with the geometric majorant and sum it
  have hle := Summable.tsum_le_tsum hbound hsummable hsummaj
  have hsub : (∑' q : {q : ℤ // q ≠ 0},
      (2 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) ^ (q : ℤ).natAbs)
      = ∑' q : ℤ, (if q = 0 then (0 : ℝ)
          else (2 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) ^ q.natAbs) := by
    have hsupp : Function.support (fun q : ℤ => if q = 0 then (0 : ℝ)
        else (2 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) ^ q.natAbs)
        ⊆ {q : ℤ | q ≠ 0} := by
      intro q hq
      by_contra hc
      simp only [Set.mem_setOf_eq, not_not] at hc
      simp [hc] at hq
    have h := tsum_subtype_eq_of_support_subset hsupp
    refine Eq.trans ?_ h
    exact tsum_congr (fun q => (if_neg q.2).symm)
  rw [hsub] at hle
  exact hle.trans (L1Matching.overlap_series_bound hconst hbeta hP hhalf)

end OverlapIntegral
