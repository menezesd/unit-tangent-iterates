import Mathlib
import UnitTangentIterates.FrontPeriodization
import UnitTangentIterates.OverlapIntegral

/-!
# The front periodization error, integrated over one period

`FrontPeriodization.lean` contains the pointwise core of the lemma *Front
periodization error* of *A Noncircular Oval with Convex Unit-Tangent Iterates*,
for a **finite** family of pulses: the exact identity

`K_L − ∑ K_*(· − mL) = ∑_m y_m' (G(Y_L) − G(y_m))`

and the resulting overlap bound `≤ Lip(a)·D·∑_{m ≠ n} y_m y_n`.

This file completes that lemma: the family is the full family of translates
`y_m(u) = y(u − mP)` of an exponentially decaying pulse, and the overlap bound
is integrated over one period, which is what the theorem
*Curvature-measure matching* consumes.  The result,

`∫_{cell} |K_P − ∑_m K_*(· − mP)| ≤ Lip(a)·D·(8C²/(α−β)) e^{−βP}`,

is the last of the four error terms of that theorem to be produced rather than
assumed.

Main results:

* `continuous_tsum_translates` : the periodization of a continuous,
  exponentially decaying function is continuous;
* `periodic_tsum_translates` : it is `P`-periodic;
* `front_error_tsum_le` : the pointwise bound, now for the infinite family;
* `integral_line_overlap_le` : `∫_ℝ y(s)(Y(s) − y(s)) ds ≤ (8C²/(α−β))e^{−βP}`;
* `integral_cell_overlap_le` : the same bound for the overlap over one cell;
* `front_periodization_error_cell_le` : **the front periodization error**;
* `front_periodization_error_exp` : the same, with the period `P` replaced by
  the separation `H` at the cost of a constant, in the exponential form the
  matching theorem uses.
-/

noncomputable section

open MeasureTheory Set Real

namespace FrontPeriodizationIntegral

open FrontPeriodization

variable {F y yp : ℝ → ℝ} {C alpha beta a D P p s : ℝ}

/-! ### Translates of an exponentially decaying function -/

/-- The translate `F(s − mP)` of an exponentially decaying function is
geometrically small in `m`, uniformly for `s` in a bounded set. -/
theorem abs_term_le (halpha : 0 < alpha) (hP : 0 < P)
    (hFb : ∀ s, |F s| ≤ C * Real.exp (-alpha * |s|)) (s : ℝ) (m : ℤ) :
    |F (s - m * P)| ≤ (C * Real.exp (alpha * |s|)) * (Real.exp (-alpha * P)) ^ m.natAbs := by
  have hC : 0 ≤ C := by
    have h := hFb 0
    have h0 := abs_nonneg (F 0)
    simp at h
    linarith
  have habs : ((m.natAbs : ℝ)) * P - |s| ≤ |s - m * P| := by
    have h1 : |(m : ℝ) * P| - |s| ≤ |(m : ℝ) * P - s| := abs_sub_abs_le_abs_sub _ _
    have h2 : |(m : ℝ) * P - s| = |s - (m : ℝ) * P| := abs_sub_comm _ _
    have h3 : |(m : ℝ) * P| = (m.natAbs : ℝ) * P := by
      rw [abs_mul, abs_of_pos hP]
      congr 1
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num
    rw [h2, h3] at h1
    linarith
  calc |F (s - m * P)| ≤ C * Real.exp (-alpha * |s - m * P|) := hFb _
    _ ≤ C * Real.exp (-alpha * ((m.natAbs : ℝ) * P - |s|)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = (C * Real.exp (alpha * |s|)) * (Real.exp (-alpha * P)) ^ m.natAbs := by
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        ring_nf

/-- Summability of the geometric majorant indexed by `ℤ`. -/
theorem summable_geom_natAbs {C' q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℤ => C' * q ^ m.natAbs) := by
  have hgeo : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hgeo.mul_left C'
  · have hsum : Summable (fun n : ℕ => C' * q ^ (n + 1)) := by
      simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using (hgeo.mul_left (C' * q))
    refine hsum.congr (fun n => ?_)
    have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [hn]

/-- The periodized series of an exponentially decaying function converges. -/
theorem summable_translates (halpha : 0 < alpha) (hP : 0 < P)
    (hFb : ∀ s, |F s| ≤ C * Real.exp (-alpha * |s|)) (s : ℝ) :
    Summable (fun m : ℤ => F (s - m * P)) := by
  have hq0 : (0:ℝ) ≤ Real.exp (-alpha * P) := (Real.exp_pos _).le
  have hq1 : Real.exp (-alpha * P) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  exact Summable.of_norm_bounded (summable_geom_natAbs hq0 hq1)
    (fun m => abs_term_le halpha hP hFb s m)

/-- The periodization is `P`-periodic. -/
theorem periodic_tsum_translates (F : ℝ → ℝ) (P : ℝ) :
    Function.Periodic (fun u => ∑' m : ℤ, F (u - m * P)) P := by
  intro u
  simp only
  have h := (Equiv.subRight (1 : ℤ)).tsum_eq (fun m : ℤ => F (u - m * P))
  rw [← h]
  refine tsum_congr (fun m => ?_)
  simp only [Equiv.subRight_apply]
  push_cast
  ring_nf

/-- The periodization of a continuous, exponentially decaying function is
continuous. -/
theorem continuous_tsum_translates (halpha : 0 < alpha) (hP : 0 < P)
    (hF : Continuous F) (hFb : ∀ s, |F s| ≤ C * Real.exp (-alpha * |s|)) :
    Continuous (fun u => ∑' m : ℤ, F (u - m * P)) := by
  have hC : 0 ≤ C := by
    have h := hFb 0
    have h0 := abs_nonneg (F 0)
    simp at h
    linarith
  have hq0 : (0:ℝ) ≤ Real.exp (-alpha * P) := (Real.exp_pos _).le
  have hq1 : Real.exp (-alpha * P) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  rw [continuous_iff_continuousAt]
  intro x
  have hnb : Ioo (x - 1) (x + 1) ∈ nhds x := Ioo_mem_nhds (by linarith) (by linarith)
  refine ContinuousOn.continuousAt ?_ hnb
  refine continuousOn_tsum (u := fun m : ℤ =>
      (C * Real.exp (alpha * (|x| + 1))) * (Real.exp (-alpha * P)) ^ m.natAbs)
    (fun m => ((hF.comp (continuous_id.sub continuous_const)).continuousOn)) ?_ ?_
  · exact summable_geom_natAbs hq0 hq1
  · intro m u hu
    have hux : |u| ≤ |x| + 1 := by
      rcases hu with ⟨h1, h2⟩
      rcases abs_cases u with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rcases abs_cases x with ⟨he', _⟩ | ⟨he', _⟩ <;> rw [he, he'] <;> linarith
    refine (abs_term_le halpha hP hFb u m).trans ?_
    have : Real.exp (alpha * |u|) ≤ Real.exp (alpha * (|x| + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hpow : (0:ℝ) ≤ (Real.exp (-alpha * P)) ^ m.natAbs := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC) hpow

/-- An exponentially decaying continuous function is integrable. -/
theorem integrable_of_exp_bound' (halpha : 0 < alpha) (hF : Continuous F)
    (hFb : ∀ s, |F s| ≤ C * Real.exp (-alpha * |s|)) : Integrable F := by
  refine Integrable.mono ((L1Matching.integrable_expabs halpha).const_mul C)
    hF.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  have hC : 0 ≤ C := by
    have h := hFb 0
    have h0 := abs_nonneg (F 0)
    simp at h
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ C * Real.exp (-alpha * |s|))]
  exact hFb s

/-! ### The pointwise error -/

section Pointwise

/-- The pulse is dominated by its periodization. -/
theorem le_tsum_translates (halpha : 0 < alpha) (hP : 0 < P)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) (u : ℝ) (m : ℤ) :
    y (u - m * P) ≤ ∑' j : ℤ, y (u - j * P) := by
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  exact (summable_translates halpha hP habs u).le_tsum m (fun j _ => hy0 _)

/-- **The front periodization error, pointwise, for the full family of
translates.**  This is `FrontPeriodization.front_error_le` with the finite
index set replaced by `ℤ`. -/
theorem front_error_tsum_le (halpha : 0 < alpha) (hP : 0 < P)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hYa : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a) (u : ℝ) :
    |((∑' m : ℤ, y (u - m * P))
          + G (∑' m : ℤ, y (u - m * P)) * (∑' m : ℤ, yp (u - m * P)))
        - ∑' m : ℤ, (y (u - m * P) + G (y (u - m * P)) * yp (u - m * P))|
      ≤ lipConst a * D * ∑' m : ℤ,
          y (u - m * P) * ((∑' j : ℤ, y (u - j * P)) - y (u - m * P)) := by
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have habsp : ∀ s, |yp s| ≤ (D * C) * Real.exp (-alpha * |s|) := by
    intro s
    refine (hypb s).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hyb s) hD
  set q : ℤ → ℝ := fun m => y (u - m * P) with hq
  set qp : ℤ → ℝ := fun m => yp (u - m * P) with hqp
  have hsq : Summable q := summable_translates halpha hP habs u
  have hsqp : Summable qp := summable_translates halpha hP habsp u
  set Y : ℝ := ∑' m : ℤ, q m with hY
  have hq0 : ∀ m, 0 ≤ q m := fun m => hy0 _
  have hqY : ∀ m, q m ≤ Y := fun m => hsq.le_tsum m (fun j _ => hq0 j)
  have hYle : Y ≤ a := hYa u
  have hY0 : 0 ≤ Y := le_trans (hq0 0) (hqY 0)
  have hqa : ∀ m, q m ≤ a := fun m => (hqY m).trans hYle
  have hLip0 : 0 ≤ lipConst a := lipConst_nonneg ha0 ha1
  -- the overlap series
  have hover : Summable (fun m => q m * (Y - q m)) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hq0 m) (by linarith [hqY m]))
      (fun m => ?_) (hsq.mul_left a)
    have : Y - q m ≤ a := by linarith [hq0 m]
    calc q m * (Y - q m) ≤ q m * a :=
          mul_le_mul_of_nonneg_left this (hq0 m)
      _ = a * q m := by ring
  -- the sum of the isolated contributions converges
  have hGa : ∀ z : ℝ, 0 ≤ z → z ≤ a → |G z| ≤ (Real.sqrt (1 - a ^ 2))⁻¹ := by
    intro z hz0 hza
    have ha2 : 0 < 1 - a ^ 2 := by nlinarith
    have hz2 : 0 < 1 - z ^ 2 := by nlinarith
    have hsa : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr ha2
    have hsz : 0 < Real.sqrt (1 - z ^ 2) := Real.sqrt_pos.mpr hz2
    have hmono : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - z ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [G, abs_of_nonneg (by positivity)]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hmono
  have hiso : Summable (fun m => q m + G (q m) * qp m) := by
    refine Summable.of_norm_bounded ((hsq.mul_left (1 + (Real.sqrt (1 - a ^ 2))⁻¹ * D)))
      (fun m => ?_)
    have h1 : |G (q m) * qp m| ≤ (Real.sqrt (1 - a ^ 2))⁻¹ * (D * q m) := by
      rw [abs_mul]
      exact mul_le_mul (hGa _ (hq0 m) (hqa m)) (hypb _) (abs_nonneg _)
        (by positivity)
    calc ‖q m + G (q m) * qp m‖ ≤ |q m| + |G (q m) * qp m| := abs_add_le _ _
      _ ≤ q m + (Real.sqrt (1 - a ^ 2))⁻¹ * (D * q m) := by
          rw [abs_of_nonneg (hq0 m)]; linarith
      _ = (1 + (Real.sqrt (1 - a ^ 2))⁻¹ * D) * q m := by ring
  have hsGY : Summable (fun m => G Y * qp m) := hsqp.mul_left _
  -- the exact identity
  have hsplit : (Y + G Y * (∑' m : ℤ, qp m)) - ∑' m : ℤ, (q m + G (q m) * qp m)
      = ∑' m : ℤ, qp m * (G Y - G (q m)) := by
    have h1 : G Y * (∑' m : ℤ, qp m) = ∑' m : ℤ, G Y * qp m := (tsum_mul_left).symm
    have h2 : Y + (∑' m : ℤ, G Y * qp m) = ∑' m : ℤ, (q m + G Y * qp m) := by
      rw [hY, ← hsq.tsum_add hsGY]
    rw [h1, h2, ← (hsq.add hsGY).tsum_sub hiso]
    exact tsum_congr (fun m => by ring)
  rw [hsplit]
  -- the termwise bound
  have hbound : ∀ m, ‖qp m * (G Y - G (q m))‖ ≤ lipConst a * D * (q m * (Y - q m)) := by
    intro m
    have hdiff : |G Y - G (q m)| ≤ lipConst a * (Y - q m) := by
      have h := lipschitz_G ha0 ha1 (Set.mem_Icc.mpr ⟨hY0, hYle⟩)
        (Set.mem_Icc.mpr ⟨hq0 m, hqa m⟩)
      rwa [show |Y - q m| = Y - q m from abs_of_nonneg (by linarith [hqY m])] at h
    calc ‖qp m * (G Y - G (q m))‖ = |qp m| * |G Y - G (q m)| := abs_mul _ _
      _ ≤ (D * q m) * (lipConst a * (Y - q m)) :=
          mul_le_mul (hypb _) hdiff (abs_nonneg _) (mul_nonneg hD (hq0 m))
      _ = lipConst a * D * (q m * (Y - q m)) := by ring
  have hsumnorm : Summable (fun m => ‖qp m * (G Y - G (q m))‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound
      (hover.mul_left (lipConst a * D))
  calc ‖∑' m : ℤ, qp m * (G Y - G (q m))‖
      ≤ ∑' m : ℤ, ‖qp m * (G Y - G (q m))‖ := norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' m : ℤ, lipConst a * D * (q m * (Y - q m)) :=
        hsumnorm.tsum_le_tsum hbound (hover.mul_left _)
    _ = lipConst a * D * ∑' m : ℤ, q m * (Y - q m) := tsum_mul_left

end Pointwise

/-! ### The overlap, integrated -/

/-- The overlap of two translates of an exponentially decaying pulse is
integrable. -/
theorem integrable_overlap (halpha : 0 < alpha) (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) (r : ℝ) :
    Integrable (fun s => y s * y (s - r)) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hyint : Integrable y := OverlapIntegral.integrable_of_exp_bound halpha hy hy0 hyb
  have hybound : ∀ s, y s ≤ C := by
    intro s
    refine (hyb s).trans ?_
    have : Real.exp (-alpha * |s|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg s])
    nlinarith
  have hfcont : Continuous fun s => y s * y (s - r) :=
    hy.mul (hy.comp (continuous_id.sub continuous_const))
  refine Integrable.mono (hyint.const_mul C) hfcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (hy0 s) (hy0 _)),
    abs_of_nonneg (mul_nonneg hC (hy0 s))]
  calc y s * y (s - r) ≤ y s * C := mul_le_mul_of_nonneg_left (hybound _) (hy0 s)
    _ = C * y s := by ring

/-- **The total overlap on the line.**  `∫_ℝ y(s)(Y(s) − y(s)) ds` is the sum
of the pairwise overlap integrals, hence exponentially small in the period. -/
theorem integral_line_overlap_le (halpha : 0 < alpha) (hP : 0 < P)
    (hbeta : 0 < beta) (hba : beta < alpha) (hhalf : Real.exp (-(beta * P)) ≤ 1 / 2)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) :
    (∫ s : ℝ, y s * ((∑' j : ℤ, y (s - j * P)) - y s))
      ≤ 8 * C ^ 2 / (alpha - beta) * Real.exp (-(beta * P)) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hgap : 0 < alpha - beta := by linarith
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  set K : ℝ := 2 * C ^ 2 / (alpha - beta) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set t : ℝ := Real.exp (-(beta * P)) with ht
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  -- the integrand as a sum over the nonzero separations
  set w : ℤ → ℝ → ℝ := fun j s => if j = 0 then 0 else y s * y (s - j * P) with hw
  have hpoint : ∀ s, y s * ((∑' j : ℤ, y (s - j * P)) - y s) = ∑' j : ℤ, w j s := by
    intro s
    have hsum : Summable (fun j : ℤ => y (s - j * P)) := summable_translates halpha hP habs s
    have hsplit := hsum.tsum_eq_add_tsum_ite (0 : ℤ)
    have hz : y (s - ((0 : ℤ) : ℝ) * P) = y s := by norm_num
    rw [hz] at hsplit
    have hdiff : (∑' j : ℤ, y (s - j * P)) - y s
        = ∑' j : ℤ, (if j = 0 then 0 else y (s - j * P)) := by rw [hsplit]; ring
    rw [hdiff, ← tsum_mul_left]
    refine tsum_congr (fun j => ?_)
    rw [hw]
    by_cases hj : j = 0 <;> simp [hj]
  -- each term is integrable
  have hwint : ∀ j : ℤ, Integrable (w j) := by
    intro j
    rw [hw]
    by_cases hj : j = 0
    · simp [hj]
    · simpa [hj] using integrable_overlap halpha hy hy0 hyb ((j : ℝ) * P)
  have hw0 : ∀ j : ℤ, ∀ s, 0 ≤ w j s := by
    intro j s
    rw [hw]
    by_cases hj : j = 0
    · simp [hj]
    · simp only [hj, if_false]
      exact mul_nonneg (hy0 s) (hy0 _)
  -- the pairwise bound
  have hwbound : ∀ j : ℤ, (∫ s : ℝ, w j s) ≤ (if j = 0 then (0:ℝ) else K * t ^ j.natAbs) := by
    intro j
    by_cases hj : j = 0
    · simp [hw, hj]
    · simp only [hw, hj, if_false]
      refine (L1Matching.convolution_bound (r := (j : ℝ) * P) hy0 hyb hbeta hba).trans ?_
      have habs' : |(j : ℝ) * P| = (j.natAbs : ℝ) * P := by
        rw [abs_mul, abs_of_pos hP]
        congr 1
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        norm_num
      rw [habs']
      have hpow : t ^ j.natAbs = Real.exp (-beta * ((j.natAbs : ℝ) * P)) := by
        rw [ht, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [hpow]
  have hnormsummable : Summable (fun j : ℤ => ∫ s : ℝ, ‖w j s‖) := by
    have heq : ∀ j : ℤ, (∫ s : ℝ, ‖w j s‖) = ∫ s : ℝ, w j s := by
      intro j
      exact integral_congr_ae (Filter.Eventually.of_forall fun s => by
        simp [Real.norm_eq_abs, abs_of_nonneg (hw0 j s)])
    refine Summable.of_nonneg_of_le (fun j => by
        rw [heq j]; exact integral_nonneg (fun s => hw0 j s))
      (fun j => by rw [heq j]; exact hwbound j)
      (Periodization.summable_ite_geom_int hK0 ht0 ht1)
  -- interchange the sum and the integral
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := (volume : Measure ℝ)) hwint hnormsummable
  have hsummable : Summable (fun j : ℤ => ∫ s : ℝ, w j s) := by
    have heq : ∀ j : ℤ, (∫ s : ℝ, ‖w j s‖) = ∫ s : ℝ, w j s := by
      intro j
      exact integral_congr_ae (Filter.Eventually.of_forall fun s => by
        simp [Real.norm_eq_abs, abs_of_nonneg (hw0 j s)])
    exact hnormsummable.congr heq
  calc (∫ s : ℝ, y s * ((∑' j : ℤ, y (s - j * P)) - y s))
      = ∫ s : ℝ, ∑' j : ℤ, w j s := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun s => hpoint s)
    _ = ∑' j : ℤ, ∫ s : ℝ, w j s := hswap.symm
    _ ≤ ∑' j : ℤ, (if j = 0 then (0:ℝ) else K * t ^ j.natAbs) :=
        hsummable.tsum_le_tsum hwbound (Periodization.summable_ite_geom_int hK0 ht0 ht1)
    _ ≤ 4 * K * t := L1Matching.overlap_series_bound hK0 hbeta hP hhalf
    _ = 8 * C ^ 2 / (alpha - beta) * Real.exp (-(beta * P)) := by
        rw [hK, ht]; ring

/-- A continuous periodic function is bounded above. -/
theorem exists_bound_of_periodic {f : ℝ → ℝ} (hP : 0 < P) (hf : Continuous f)
    (hper : Function.Periodic f P) : ∃ M, ∀ s, f s ≤ M := by
  obtain ⟨x, _, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := P)).exists_isMaxOn
    ⟨0, by simp [hP.le]⟩ hf.continuousOn
  refine ⟨f x, fun s => ?_⟩
  obtain ⟨u, hu, hfu⟩ := hper.exists_mem_Ico₀ hP s
  rw [hfu]
  exact hmax (Ico_subset_Icc_self hu)

/-- **The overlap over one cell.**  Unfolding the sum over the translates to
the line, the overlap of distinct pulses over one period is exponentially
small. -/
theorem integral_cell_overlap_le (halpha : 0 < alpha) (hP : 0 < P)
    (hbeta : 0 < beta) (hba : beta < alpha) (hhalf : Real.exp (-(beta * P)) ≤ 1 / 2)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) :
    (∫ u in Ico p (p + P), ∑' m : ℤ,
        y (u - m * P) * ((∑' j : ℤ, y (u - j * P)) - y (u - m * P)))
      ≤ 8 * C ^ 2 / (alpha - beta) * Real.exp (-(beta * P)) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  set Y : ℝ → ℝ := fun u => ∑' j : ℤ, y (u - j * P) with hYdef
  have hYcont : Continuous Y := continuous_tsum_translates halpha hP hy habs
  have hYper : Function.Periodic Y P := periodic_tsum_translates y P
  have hyY : ∀ u, y u ≤ Y u := by
    intro u
    have h := le_tsum_translates (y := y) (C := C) (alpha := alpha) (P := P)
      halpha hP hy0 hyb u 0
    simpa using h
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hP hYcont hYper
  have hM0 : 0 ≤ M := le_trans (le_trans (hy0 0) (hyY 0)) (hM 0)
  -- the overlap density on the line
  set F : ℝ → ℝ := fun s => y s * (Y s - y s) with hF
  have hFcont : Continuous F := hy.mul (hYcont.sub hy)
  have hF0 : ∀ s, 0 ≤ F s := fun s => mul_nonneg (hy0 s) (by linarith [hyY s])
  have hFb : ∀ s, |F s| ≤ (M * C) * Real.exp (-alpha * |s|) := by
    intro s
    rw [abs_of_nonneg (hF0 s)]
    have h1 : Y s - y s ≤ M := by linarith [hM s, hy0 s]
    calc F s ≤ y s * M := mul_le_mul_of_nonneg_left h1 (hy0 s)
      _ ≤ (C * Real.exp (-alpha * |s|)) * M :=
          mul_le_mul_of_nonneg_right (hyb s) hM0
      _ = (M * C) * Real.exp (-alpha * |s|) := by ring
  have hFint : Integrable F := integrable_of_exp_bound' halpha hFcont hFb
  -- the integrand is the sum of the translates of `F`
  have hrw : ∀ u : ℝ, (∑' m : ℤ, y (u - m * P) * (Y u - y (u - m * P)))
      = ∑' m : ℤ, F (u - m * P) := by
    intro u
    refine tsum_congr (fun m => ?_)
    rw [hF]
    simp only
    rw [hYper.sub_int_mul_eq m]
  calc (∫ u in Ico p (p + P), ∑' m : ℤ, y (u - m * P) * (Y u - y (u - m * P)))
      = ∫ u in Ico p (p + P), ∑' m : ℤ, F (u - m * P) := by
        exact setIntegral_congr_fun measurableSet_Ico (fun u _ => hrw u)
    _ = ∫ s : ℝ, F s := OverlapIntegral.integral_tsum_translates_all hP hFint hF0
    _ ≤ 8 * C ^ 2 / (alpha - beta) * Real.exp (-(beta * P)) :=
        integral_line_overlap_le halpha hP hbeta hba hhalf hy hy0 hyb

/-! ### The front periodization error -/

/-- `G` composed with a function with values in `[0,a]`, `a < 1`, is
continuous. -/
theorem continuous_G_comp {f : ℝ → ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hf : Continuous f)
    (hf0 : ∀ u, 0 ≤ f u) (hfa : ∀ u, f u ≤ a) : Continuous fun u => G (f u) := by
  have hne : ∀ u, Real.sqrt (1 - (f u) ^ 2) ≠ 0 := by
    intro u
    have h1 : 0 < 1 - (f u) ^ 2 := by nlinarith [hf0 u, hfa u]
    exact ne_of_gt (Real.sqrt_pos.mpr h1)
  simpa [G] using ((continuous_const.sub (hf.pow 2)).sqrt).inv₀ hne

/-- **Front periodization error.**  For an exponentially decaying pulse `y`
with `|y'| ≤ D y`, whose periodization `Y_P = ∑_m y(· − mP)` stays below
`a < 1`, the curvature `K_P = Y_P + G(Y_P)Y_P'` of the periodized
configuration differs from the sum `∑_m K_*(· − mP)` of the isolated
contributions by at most

`Lip(a)·D·(8C²/(α−β)) e^{−βP}`

in `L¹` over one period.  This is the fourth error term of the theorem
*Curvature-measure matching*. -/
theorem front_periodization_error_cell_le
    (halpha : 0 < alpha) (hP : 0 < P) (hbeta : 0 < beta) (hba : beta < alpha)
    (hhalf : Real.exp (-(beta * P)) ≤ 1 / 2)
    (hy : Continuous y) (hyp : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hYa : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a) :
    (∫ u in Ico p (p + P),
        |((∑' m : ℤ, y (u - m * P))
            + G (∑' m : ℤ, y (u - m * P)) * (∑' m : ℤ, yp (u - m * P)))
          - ∑' m : ℤ, (y (u - m * P) + G (y (u - m * P)) * yp (u - m * P))|)
      ≤ lipConst a * D * (8 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have habsp : ∀ s, |yp s| ≤ (D * C) * Real.exp (-alpha * |s|) := by
    intro s
    refine (hypb s).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hyb s) hD
  set Y : ℝ → ℝ := fun u => ∑' j : ℤ, y (u - j * P) with hYdef
  have hYcont : Continuous Y := continuous_tsum_translates halpha hP hy habs
  have hyY : ∀ u, y u ≤ Y u := by
    intro u
    have h := le_tsum_translates (y := y) (C := C) (alpha := alpha) (P := P)
      halpha hP hy0 hyb u 0
    simpa using h
  have hya : ∀ s, y s ≤ a := fun s => (hyY s).trans (hYa s)
  have hY0 : ∀ u, 0 ≤ Y u := fun u => (hy0 u).trans (hyY u)
  -- the periodized derivative and the isolated curvature profile
  set Yp : ℝ → ℝ := fun u => ∑' m : ℤ, yp (u - m * P) with hYpdef
  have hYpcont : Continuous Yp := continuous_tsum_translates halpha hP hyp habsp
  set Kstar : ℝ → ℝ := fun s => y s + G (y s) * yp s with hKstar
  have hGy : Continuous fun s => G (y s) := continuous_G_comp ha0 ha1 hy hy0 hya
  have hKcont : Continuous Kstar := hy.add (hGy.mul hyp)
  have hGa : ∀ z : ℝ, 0 ≤ z → z ≤ a → |G z| ≤ (Real.sqrt (1 - a ^ 2))⁻¹ := by
    intro z hz0 hza
    have ha2 : 0 < 1 - a ^ 2 := by nlinarith
    have hz2 : 0 < 1 - z ^ 2 := by nlinarith
    have hsa : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr ha2
    have hmono : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - z ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [G, abs_of_nonneg (by positivity)]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hmono
  have hKb : ∀ s, |Kstar s| ≤ ((1 + (Real.sqrt (1 - a ^ 2))⁻¹ * D) * C) * Real.exp (-alpha * |s|) := by
    intro s
    have h1 : |G (y s) * yp s| ≤ (Real.sqrt (1 - a ^ 2))⁻¹ * (D * y s) := by
      rw [abs_mul]
      exact mul_le_mul (hGa _ (hy0 s) (hya s)) (hypb s) (abs_nonneg _) (by positivity)
    have h2 : |Kstar s| ≤ y s + (Real.sqrt (1 - a ^ 2))⁻¹ * (D * y s) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (hy0 s)]
      linarith
    refine h2.trans ?_
    have h3 : y s + (Real.sqrt (1 - a ^ 2))⁻¹ * (D * y s)
        = (1 + (Real.sqrt (1 - a ^ 2))⁻¹ * D) * y s := by ring
    rw [h3, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hyb s) ?_
    have ha2 : 0 < 1 - a ^ 2 := by nlinarith
    have hsa : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr ha2
    positivity
  set Kbar : ℝ → ℝ := fun u => ∑' m : ℤ, Kstar (u - m * P) with hKbardef
  have hKbarcont : Continuous Kbar := continuous_tsum_translates halpha hP hKcont hKb
  -- the error and the overlap density are continuous, hence integrable on the cell
  have hGY : Continuous fun u => G (Y u) := continuous_G_comp ha0 ha1 hYcont hY0 hYa
  set E : ℝ → ℝ := fun u => |(Y u + G (Y u) * Yp u) - Kbar u| with hE
  have hEcont : Continuous E := (((hYcont.add (hGY.mul hYpcont)).sub hKbarcont)).abs
  have hEint : IntegrableOn E (Ico p (p + P)) :=
    (hEcont.integrableOn_Icc (a := p) (b := p + P)).mono_set Ico_subset_Icc_self
  set Om : ℝ → ℝ := fun u => ∑' m : ℤ, y (u - m * P) * (Y u - y (u - m * P)) with hOm
  have hOmcont : Continuous Om := by
    have hFcont : Continuous fun s => y s * (Y s - y s) := hy.mul (hYcont.sub hy)
    have hF0 : ∀ s, 0 ≤ y s * (Y s - y s) := fun s =>
      mul_nonneg (hy0 s) (by linarith [hyY s])
    have hFb : ∀ s, |y s * (Y s - y s)| ≤ (a * C) * Real.exp (-alpha * |s|) := by
      intro s
      rw [abs_of_nonneg (hF0 s)]
      have h1 : Y s - y s ≤ a := by linarith [hYa s, hy0 s]
      calc y s * (Y s - y s) ≤ y s * a := mul_le_mul_of_nonneg_left h1 (hy0 s)
        _ ≤ (C * Real.exp (-alpha * |s|)) * a :=
            mul_le_mul_of_nonneg_right (hyb s) ha0
        _ = (a * C) * Real.exp (-alpha * |s|) := by ring
    have hYper : Function.Periodic Y P := periodic_tsum_translates y P
    have hrw : Om = fun u => ∑' m : ℤ, (fun s => y s * (Y s - y s)) (u - m * P) := by
      funext u
      refine tsum_congr (fun m => ?_)
      simp only
      rw [hYper.sub_int_mul_eq m]
    rw [hrw]
    exact continuous_tsum_translates halpha hP hFcont hFb
  have hOmint : IntegrableOn Om (Ico p (p + P)) :=
    (hOmcont.integrableOn_Icc (a := p) (b := p + P)).mono_set Ico_subset_Icc_self
  have hLip0 : 0 ≤ lipConst a := lipConst_nonneg ha0 ha1
  -- integrate the pointwise bound
  have hpt : ∀ u ∈ Ico p (p + P), E u ≤ lipConst a * D * Om u := fun u _ =>
    front_error_tsum_le halpha hP hy0 hyb hD hypb ha0 ha1 hYa u
  calc (∫ u in Ico p (p + P), E u)
      ≤ ∫ u in Ico p (p + P), lipConst a * D * Om u :=
        setIntegral_mono_on hEint (hOmint.const_mul _) measurableSet_Ico hpt
    _ = lipConst a * D * ∫ u in Ico p (p + P), Om u := integral_const_mul _ _
    _ ≤ lipConst a * D * (8 * C ^ 2 / (alpha - beta) * Real.exp (-(beta * P))) :=
        mul_le_mul_of_nonneg_left
          (integral_cell_overlap_le halpha hP hbeta hba hhalf hy hy0 hyb)
          (mul_nonneg hLip0 hD)
    _ = lipConst a * D * (8 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P)) := by ring

/-! ### The error in the form the matching theorem consumes -/

/-- Splitting off the central term of a sum over `ℤ`. -/
theorem tsum_split_zero {f : ℤ → ℝ} (hf : Summable f) :
    ∑' m : ℤ, f m = f 0 + ∑' j : {j : ℤ // j ≠ 0}, f (j : ℤ) := by
  have h1 := hf.tsum_eq_add_tsum_ite (0 : ℤ)
  have hsupp : Function.support (fun m : ℤ => if m = 0 then (0 : ℝ) else f m)
      ⊆ {j : ℤ | j ≠ 0} := by
    intro m hm
    by_contra hc
    simp only [Set.mem_setOf_eq, not_not] at hc
    simp [hc] at hm
  have h2 := tsum_subtype_eq_of_support_subset hsupp
  have h3 : (∑' j : {j : ℤ // j ≠ 0}, f (j : ℤ))
      = ∑' j : {j : ℤ // j ∈ {j : ℤ | j ≠ 0}}, (if (j : ℤ) = 0 then (0 : ℝ) else f (j : ℤ)) :=
    tsum_congr (fun j => (if_neg j.2).symm)
  rw [h3, h2, h1]

/-- **Front periodization error, exponentially in the separation.**  The
integral of `|K_P − ∑_m K_*(· − mP)|` over one period of the periodized
configuration is at most `C₄e^{−βH}`, with
`C₄ = Lip(a)·D·(8C²/(α−β))e^{2βB}`, once the period `P` and the separation
`H` differ by at most `2B`.  This is exactly the fourth hypothesis of
`MatchingExponential.curvature_measure_matching_exp_of_pulse`, with
`K_* = y + G(y)y'` the isolated front curvature and
`K_P = Y_P + G(Y_P)Y_P'` the periodized one. -/
theorem front_periodization_error_exp {Kstar Kbar KP : ℝ → ℝ} {H B q : ℝ}
    (halpha : 0 < alpha) (hP : 0 < P) (hbeta : 0 < beta) (hba : beta < alpha)
    (hhalf : Real.exp (-(beta * P)) ≤ 1 / 2)
    (hy : Continuous y) (hyp : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hYa : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hKbar : ∀ u, Kbar u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P))
    (hKP : ∀ u, KP u = (∑' m : ℤ, y (u - m * P))
      + G (∑' m : ℤ, y (u - m * P)) * (∑' m : ℤ, yp (u - m * P)))
    (hPH : H - 2 * B ≤ P) :
    (∫ u in q..(q + P), |Kbar u - KP u|)
      ≤ (lipConst a * D * (8 * C ^ 2 / (alpha - beta)) * Real.exp (2 * beta * B))
        * Real.exp (-(beta * H)) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have habsp : ∀ s, |yp s| ≤ (D * C) * Real.exp (-alpha * |s|) := by
    intro s
    refine (hypb s).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hyb s) hD
  have hyY : ∀ u, y u ≤ ∑' j : ℤ, y (u - j * P) := by
    intro u
    have h := le_tsum_translates (y := y) (C := C) (alpha := alpha) (P := P)
      halpha hP hy0 hyb u 0
    simpa using h
  have hya : ∀ s, y s ≤ a := fun s => (hyY s).trans (hYa s)
  -- the isolated curvature profile decays exponentially, so its periodization
  -- may be split at the central term
  have hGa : ∀ z : ℝ, 0 ≤ z → z ≤ a → |G z| ≤ (Real.sqrt (1 - a ^ 2))⁻¹ := by
    intro z hz0 hza
    have ha2 : 0 < 1 - a ^ 2 := by nlinarith
    have hz2 : 0 < 1 - z ^ 2 := by nlinarith
    have hmono : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - z ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [G, abs_of_nonneg (by positivity)]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hmono
  have hKb : ∀ s, |Kstar s|
      ≤ ((1 + (Real.sqrt (1 - a ^ 2))⁻¹ * D) * C) * Real.exp (-alpha * |s|) := by
    intro s
    rw [hKstar s]
    have h1 : |G (y s) * yp s| ≤ (Real.sqrt (1 - a ^ 2))⁻¹ * (D * y s) := by
      rw [abs_mul]
      exact mul_le_mul (hGa _ (hy0 s) (hya s)) (hypb s) (abs_nonneg _) (by positivity)
    have h2 : |y s + G (y s) * yp s| ≤ y s + (Real.sqrt (1 - a ^ 2))⁻¹ * (D * y s) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (hy0 s)]
      linarith
    refine h2.trans ?_
    have h3 : y s + (Real.sqrt (1 - a ^ 2))⁻¹ * (D * y s)
        = (1 + (Real.sqrt (1 - a ^ 2))⁻¹ * D) * y s := by ring
    rw [h3, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hyb s) ?_
    have ha2 : 0 < 1 - a ^ 2 := by nlinarith
    have hsa : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr ha2
    positivity
  have hKbar' : ∀ u, Kbar u = ∑' m : ℤ, Kstar (u - m * P) := by
    intro u
    have hs : Summable (fun m : ℤ => Kstar (u - m * P)) :=
      summable_translates halpha hP hKb u
    rw [hKbar u, tsum_split_zero hs]
    norm_num
  -- the integrand is the one of the previous theorem
  have hpt : ∀ u, |Kbar u - KP u|
      = |((∑' m : ℤ, y (u - m * P))
            + G (∑' m : ℤ, y (u - m * P)) * (∑' m : ℤ, yp (u - m * P)))
          - ∑' m : ℤ, (y (u - m * P) + G (y (u - m * P)) * yp (u - m * P))| := by
    intro u
    rw [hKbar' u, hKP u, abs_sub_comm]
    congr 2
    exact tsum_congr (fun m => hKstar _)
  -- pass from the interval to the cell and apply the previous theorem
  have hcell := front_periodization_error_cell_le (y := y) (yp := yp) (C := C)
    (alpha := alpha) (beta := beta) (a := a) (D := D) (P := P) (p := q)
    halpha hP hbeta hba hhalf hy hyp hy0 hyb hD hypb ha0 ha1 hYa
  have hIco : (∫ u in q..(q + P), |Kbar u - KP u|)
      = ∫ u in Ico q (q + P), |Kbar u - KP u| := by
    rw [intervalIntegral.integral_of_le (by linarith : q ≤ q + P),
      integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  rw [hIco]
  have hcongr : (∫ u in Ico q (q + P), |Kbar u - KP u|)
      = ∫ u in Ico q (q + P),
        |((∑' m : ℤ, y (u - m * P))
            + G (∑' m : ℤ, y (u - m * P)) * (∑' m : ℤ, yp (u - m * P)))
          - ∑' m : ℤ, (y (u - m * P) + G (y (u - m * P)) * yp (u - m * P))| :=
    setIntegral_congr_fun measurableSet_Ico (fun u _ => hpt u)
  rw [hcongr]
  refine hcell.trans ?_
  have hconst : 0 ≤ lipConst a * D * (8 * C ^ 2 / (alpha - beta)) := by
    have := lipConst_nonneg ha0 ha1
    have hgap : 0 < alpha - beta := by linarith
    positivity
  have hexp : Real.exp (-(beta * P)) ≤ Real.exp (2 * beta * B) * Real.exp (-(beta * H)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc lipConst a * D * (8 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * P))
      ≤ lipConst a * D * (8 * C ^ 2 / (alpha - beta))
          * (Real.exp (2 * beta * B) * Real.exp (-(beta * H))) :=
        mul_le_mul_of_nonneg_left hexp hconst
    _ = (lipConst a * D * (8 * C ^ 2 / (alpha - beta)) * Real.exp (2 * beta * B))
          * Real.exp (-(beta * H)) := by ring

end FrontPeriodizationIntegral
