import Mathlib
import UnitTangentIterates.Periodization

/-!
# Ingredients of the curvature-measure matching

This file formalizes the self-contained analytic ingredients of the theorem
*Curvature-measure matching* of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates*.

The proof of that theorem rests on three computations:

* the convolution estimate `∫_ℝ y(s) y(s-r) ds ≤ C_β e^{-β|r|}` for an
  exponentially decaying pulse `y` and any `0 < β < α`;
* the exact rear curvature measure identity `k_H(x_H(s)) dx_H = Y_H(s) ds`,
  which in arclength form is `k_H(x_H(s)) c_H(s) = Y_H(s)`, and the associated
  change of variables `∫ c_H · (f ∘ x_H) = ∫_{J_H} f`;
* the splitting of the integrand `Y_H - c_H K̄_P(x_H)` into three pieces,
  each of which is estimated separately.

Main results:

* `integrable_expabs`, `integral_expabs` : `∫_ℝ e^{-c|s|} ds = 2/c`;
* `convolution_bound` : the convolution estimate with the explicit constant
  `2C²/(α-β)`;
* `rear_measure` : `k(x(s)) c(s) = Y(s)`;
* `integral_comp_rear` : the change of variables to the fundamental interval;
* `overlap_series_bound` : the geometric summation of the pairwise overlaps
  over the translation index;
* `matching_split` : the three-term accounting of the matching integrand.
-/

noncomputable section

open MeasureTheory Set Real

namespace L1Matching

/-! ### The two-sided exponential integral -/

variable {c : ℝ}

theorem integrableOn_Ioi_expabs (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-c * |s|)) (Ioi 0) := by
  apply (exp_neg_integrableOn_Ioi 0 hc).congr_fun _ measurableSet_Ioi
  intro x hx
  simp only
  rw [abs_of_pos (mem_Ioi.mp hx)]

theorem integrableOn_Iio_expabs (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-c * |s|)) (Iio 0) := by
  have h := (exp_neg_integrableOn_Ioi (0:ℝ) hc).comp_neg
  rw [show -(Ioi (0:ℝ)) = Iio 0 by simp] at h
  apply h.congr_fun _ measurableSet_Iio
  intro x hx
  simp only
  rw [abs_of_neg (mem_Iio.mp hx)]

theorem integrableOn_Iic_expabs (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-c * |s|)) (Iic 0) := by
  rw [← Iio_union_right (a := (0:ℝ)), integrableOn_union]
  exact ⟨integrableOn_Iio_expabs hc, by simp⟩

/-- The two-sided exponential is integrable on the line. -/
theorem integrable_expabs (hc : 0 < c) : Integrable (fun s : ℝ => Real.exp (-c * |s|)) := by
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0:ℝ)), integrableOn_union]
  refine ⟨integrableOn_Iio_expabs hc, ?_⟩
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_Ioi_expabs hc

/-- `∫_ℝ e^{-c|s|} ds = 2/c`. -/
theorem integral_expabs (hc : 0 < c) : ∫ s : ℝ, Real.exp (-c * |s|) = 2 / c := by
  have hIoi : ∫ s in Ioi (0:ℝ), Real.exp (-c * |s|) = 1 / c := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s : ℝ => Real.exp (-c * s))
      (fun x hx => by simp only; rw [abs_of_pos (mem_Ioi.mp hx)])]
    have h := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 hc
    simp at h
    rw [show (fun s : ℝ => Real.exp (-c * s)) = fun s => Real.exp (-(c * s)) by
      funext s; ring_nf, h, integral_exp_Iic_zero]
    simp [one_div]
  have hIic : ∫ s in Iic (0:ℝ), Real.exp (-c * |s|) = 1 / c := by
    have heven : (fun s : ℝ => Real.exp (-c * |(-s)|)) = fun s : ℝ => Real.exp (-c * |s|) := by
      funext s; rw [abs_neg]
    have h := integral_comp_neg_Iic (0:ℝ) (fun s : ℝ => Real.exp (-c * |s|))
    simp only [heven, neg_zero] at h
    rw [h, hIoi]
  rw [← intervalIntegral.integral_Iic_add_Ioi (integrableOn_Iic_expabs hc)
    (integrableOn_Ioi_expabs hc), hIic, hIoi]
  ring

/-! ### The convolution estimate -/

/-- **The convolution estimate.**  If `0 ≤ y ≤ C e^{-α|·|}` then, for every
`0 < β < α`, the overlap integral of two translates decays exponentially in the
separation:  `∫_ℝ y(s) y(s-r) ds ≤ (2C²/(α-β)) e^{-β|r|}`. -/
theorem convolution_bound {y : ℝ → ℝ} {C alpha beta r : ℝ}
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hbeta : 0 < beta) (hba : beta < alpha) :
    ∫ s : ℝ, y s * y (s - r) ≤ (2 * C ^ 2 / (alpha - beta)) * Real.exp (-beta * |r|) := by
  have hC : 0 ≤ C := by
    have h := hyb 0
    have h0 := hy0 0
    simp at h
    linarith
  have hgap : 0 < alpha - beta := by linarith
  set M : ℝ → ℝ := fun s =>
    (C ^ 2 * Real.exp (-beta * |r|)) * Real.exp (-(alpha - beta) * |s|) with hM
  have hMint : Integrable M := (integrable_expabs hgap).const_mul _
  have hpoint : ∀ s : ℝ, y s * y (s - r) ≤ M s := by
    intro s
    have h1 : y s * y (s - r) ≤ (C * Real.exp (-alpha * |s|)) * (C * Real.exp (-alpha * |s - r|)) :=
      mul_le_mul (hyb s) (hyb (s - r)) (hy0 _) (by positivity)
    refine h1.trans ?_
    have hkey : -alpha * |s| + -alpha * |s - r| ≤ -beta * |r| + -(alpha - beta) * |s| := by
      have htri : |r| ≤ |s| + |s - r| := by
        have : r = s - (s - r) := by ring
        calc |r| = |s - (s - r)| := by rw [← this]
          _ ≤ |s| + |s - r| := abs_sub _ _
      nlinarith [abs_nonneg (s - r), abs_nonneg s, abs_nonneg r]
    calc (C * Real.exp (-alpha * |s|)) * (C * Real.exp (-alpha * |s - r|))
        = C ^ 2 * Real.exp (-alpha * |s| + -alpha * |s - r|) := by
          rw [Real.exp_add]; ring
      _ ≤ C ^ 2 * Real.exp (-beta * |r| + -(alpha - beta) * |s|) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) (by positivity)
      _ = M s := by rw [hM]; rw [Real.exp_add]; ring
  have hmono : ∫ s : ℝ, y s * y (s - r) ≤ ∫ s : ℝ, M s :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => mul_nonneg (hy0 _) (hy0 _))
      hMint (Filter.Eventually.of_forall hpoint)
  refine hmono.trans ?_
  rw [hM, integral_const_mul, integral_expabs hgap]
  apply le_of_eq
  field_simp

/-- **Summation of the overlaps.**  Once each pair of pulses at separation
`|q|L` contributes at most `C e^{-βL|q|}`, the sum over all nonzero
separations is still `O(e^{-βL})`. -/
theorem overlap_series_bound {C beta L : ℝ} (hC : 0 ≤ C) (hbeta : 0 < beta) (hL : 0 < L)
    (hhalf : Real.exp (-(beta * L)) ≤ 1 / 2) :
    ∑' q : ℤ, (if q = 0 then (0:ℝ) else C * Real.exp (-(beta * L)) ^ q.natAbs)
      ≤ 4 * C * Real.exp (-(beta * L)) := by
  set t : ℝ := Real.exp (-(beta * L)) with ht
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  rw [Periodization.tsum_ite_geom_int hC ht0 ht1]
  have hinv : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hCt : 0 ≤ C * t := by positivity
  nlinarith

/-! ### The rear curvature measure -/

variable {k x cc Y : ℝ → ℝ}

/-- **The rear curvature measure identity.**  The rear curvature, read in the
rear arclength `u = x_H(s)`, satisfies `k(x(s)) c(s) = Y(s)`. -/
theorem rear_measure {s : ℝ} (hc : cc s ≠ 0) (hk : k (x s) = Y s / cc s) :
    k (x s) * cc s = Y s := by
  rw [hk, div_mul_cancel₀ _ hc]

/-- **Change of variables to the fundamental interval.**  If `x' = c` then
`∫_a^b c(s) f(x(s)) ds = ∫_{x a}^{x b} f(u) du`. -/
theorem integral_comp_rear {f : ℝ → ℝ} {a b : ℝ}
    (hx : ∀ t ∈ uIcc a b, HasDerivAt x (cc t) t) (hcc : ContinuousOn cc (uIcc a b))
    (hf : Continuous f) :
    (∫ s in a..b, cc s * f (x s)) = ∫ u in (x a)..(x b), f u := by
  simpa [Function.comp, smul_eq_mul] using
    intervalIntegral.integral_comp_smul_deriv (f := x) (f' := cc) (g := f) hx hcc hf

/-! ### The three-term accounting -/

/-- **The matching split.**  The paper writes
`Y_H - c_H K̄_P(x_H) = (Y_H - y) + (y - c_H K_*(x_H)) - c_H ∑_{j≠0} K_*(x_H - jP)`
and estimates the three pieces separately.  Given `L¹` bounds `e₁, e₂, e₃` for
the three pieces on the cell, the matching integrand is bounded by their sum. -/
theorem matching_split {A B D : ℝ → ℝ} {a b e1 e2 e3 : ℝ} (hab : a ≤ b)
    (hA : IntervalIntegrable A volume a b) (hB : IntervalIntegrable B volume a b)
    (hD : IntervalIntegrable D volume a b)
    (h1 : (∫ s in a..b, |A s|) ≤ e1) (h2 : (∫ s in a..b, |B s|) ≤ e2)
    (h3 : (∫ s in a..b, |D s|) ≤ e3) :
    (∫ s in a..b, |A s + B s - D s|) ≤ e1 + e2 + e3 := by
  have habs : ∀ f : ℝ → ℝ, IntervalIntegrable f volume a b →
      IntervalIntegrable (fun s => |f s|) volume a b := fun f hf => hf.abs
  have hsum : IntervalIntegrable (fun s => |A s| + |B s| + |D s|) volume a b :=
    ((habs A hA).add (habs B hB)).add (habs D hD)
  have hle : (∫ s in a..b, |A s + B s - D s|) ≤ ∫ s in a..b, (|A s| + |B s| + |D s|) := by
    apply intervalIntegral.integral_mono_on hab (habs _ ((hA.add hB).sub hD)) hsum
    intro s _
    calc |A s + B s - D s| ≤ |A s + B s| + |D s| := abs_sub _ _
      _ ≤ (|A s| + |B s|) + |D s| := by
          have := abs_add_le (A s) (B s)
          linarith
      _ = |A s| + |B s| + |D s| := by ring
  have hsplit : (∫ s in a..b, (|A s| + |B s| + |D s|))
      = (∫ s in a..b, |A s|) + (∫ s in a..b, |B s|) + ∫ s in a..b, |D s| := by
    rw [intervalIntegral.integral_add ((habs A hA).add (habs B hB)) (habs D hD),
      intervalIntegral.integral_add (habs A hA) (habs B hB)]
  rw [hsplit] at hle
  linarith

end L1Matching
