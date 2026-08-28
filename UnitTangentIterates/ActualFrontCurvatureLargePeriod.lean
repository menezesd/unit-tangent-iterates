import UnitTangentIterates.PeriodizationSup
import UnitTangentIterates.LargeSeparation
import UnitTangentIterates.ModelOrbitDefect

/-!
# A pointwise actual-curvature ceiling at large period

The matching constant may be a very coarse curvature bound.  This module
instead compares the actual periodized front curvature with the periodization
of the isolated intrinsic curvature.  The only nonlinear error is the overlap
of distinct pulse translates, and that overlap is exponentially small in the
period.
-/

noncomputable section

open Real Set FrontPeriodization

namespace ActualFrontCurvatureLargePeriod

/-- For a summable nonnegative family, its pairwise overlap is controlled by
twice the total mass times the mass outside any distinguished term. -/
theorem overlap_tsum_le_two_mul
    {q : ℤ → ℝ} (hq : Summable q) (hq0 : ∀ m, 0 ≤ q m) (i : ℤ) :
    (∑' m, q m * ((∑' j, q j) - q m)) ≤
      2 * (∑' j, q j) * ((∑' j, q j) - q i) := by
  let Y : ℝ := ∑' j, q j
  have hqiY : q i ≤ Y := hq.le_tsum i (fun j _ => hq0 j)
  have hY0 : 0 ≤ Y := le_trans (hq0 i) hqiY
  have hsq : Summable (fun m => q m ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg (q m)) (fun m => ?_)
      (hq.mul_left Y)
    have hqmY : q m ≤ Y := hq.le_tsum m (fun j _ => hq0 j)
    simpa [pow_two, mul_comm] using mul_le_mul_of_nonneg_left hqmY (hq0 m)
  have hover : Summable (fun m => q m * (Y - q m)) := by
    simpa [mul_sub, pow_two, mul_comm] using (hq.mul_left Y).sub hsq
  have heq : (∑' m, q m * (Y - q m)) = Y ^ 2 - ∑' m, q m ^ 2 := by
    rw [show (fun m => q m * (Y - q m)) =
      (fun m => Y * q m - q m ^ 2) by
        funext m
        ring]
    rw [(hq.mul_left Y).tsum_sub hsq, tsum_mul_left]
    dsimp [Y]
    ring
  have hi : q i ^ 2 ≤ ∑' m, q m ^ 2 :=
    hsq.le_tsum i (fun m _ => sq_nonneg (q m))
  change (∑' m, q m * (Y - q m)) ≤ 2 * Y * (Y - q i)
  rw [heq]
  nlinarith [sq_nonneg (Y - q i)]

variable {y yp Kstar : ℝ → ℝ}
  {C CK alpha P a D kiso kh Hstrip : ℝ}

/-- On the centered period cell, the actual model curvature is the isolated
curvature ceiling plus an explicit exponential translate-overlap error. -/
theorem modelCurvature_le_on_centered_cell
    (halpha : 0 < alpha) (hP : 0 < P)
    (hq : Real.exp (-alpha * P) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hK0 : ∀ s, 0 ≤ Kstar s)
    (hKb : ∀ s, Kstar s ≤ CK * Real.exp (-alpha * |s|))
    (hKiso : ∀ s, Kstar s ≤ kiso)
    {s : ℝ} (hs : |s| ≤ P / 2) :
    ModelOrbitDefect.modelCurvature y yp P s ≤
      kiso + (4 * CK + 8 * lipConst a * D * a * C) *
        Real.exp (-(alpha / 2) * P) := by
  let Y : ℝ := ∑' m : ℤ, y (s - m * P)
  let Kbar : ℝ := ∑' m : ℤ, Kstar (s - m * P)
  have hC0 : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hCK0 : 0 ≤ CK := Periodization.const_nonneg hK0 hKb
  have hyabs : ∀ u, |y u| ≤ C * Real.exp (-alpha * |u|) := fun u => by
    rw [abs_of_nonneg (hy0 u)]
    exact hyb u
  have hysum : Summable (fun m : ℤ => y (s - m * P)) :=
    FrontPeriodizationIntegral.summable_translates halpha hP hyabs s
  have hycentral : y s ≤ Y := by
    dsimp [Y]
    simpa using hysum.le_tsum (0 : ℤ) (fun m _ => hy0 _)
  have hY0 : 0 ≤ Y := le_trans (hy0 s) hycentral
  have hYle : Y ≤ a := hYa s
  have hytail : Y - y s ≤ 4 * C * Real.exp (-(alpha / 2) * P) := by
    exact (le_abs_self _).trans
      (Periodization.periodization_error_le halpha hy0 hyb hP hq hs)
  have hover := overlap_tsum_le_two_mul hysum (fun m => hy0 _) (0 : ℤ)
  have hover0 :
      (∑' m : ℤ, y (s - m * P) *
        ((∑' j : ℤ, y (s - j * P)) - y (s - m * P))) ≤
        2 * (∑' j : ℤ, y (s - j * P)) *
          ((∑' j : ℤ, y (s - j * P)) - y s) := by
    simpa using hover
  have hover' :
      (∑' m : ℤ, y (s - m * P) *
        (Y - y (s - m * P))) ≤
        8 * a * C * Real.exp (-(alpha / 2) * P) := by
    dsimp [Y] at hover ⊢
    have htail0 : 0 ≤ (∑' j : ℤ, y (s - j * P)) - y s := by
      simpa using sub_nonneg.mpr hycentral
    calc
      (∑' m : ℤ, y (s - m * P) *
          ((∑' j : ℤ, y (s - j * P)) - y (s - m * P)))
          ≤ 2 * (∑' j : ℤ, y (s - j * P)) *
              ((∑' j : ℤ, y (s - j * P)) - y s) := hover0
      _ ≤ 2 * a * (4 * C * Real.exp (-(alpha / 2) * P)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hYle (by norm_num)) hytail
          htail0 (by positivity)
      _ = 8 * a * C * Real.exp (-(alpha / 2) * P) := by ring
  have hfrontError := FrontPeriodizationIntegral.front_error_tsum_le
    halpha hP hy0 hyb hD hypb ha0 ha1 hYa s
  have hfrontError' :
      |ModelOrbitDefect.modelCurvature y yp P s - Kbar| ≤
        lipConst a * D *
          (8 * a * C * Real.exp (-(alpha / 2) * P)) := by
    rw [ModelOrbitDefect.modelCurvature]
    dsimp [Kbar]
    rw [show (∑' m : ℤ, Kstar (s - m * P)) =
      ∑' m : ℤ, (y (s - m * P) + G (y (s - m * P)) * yp (s - m * P)) by
        apply tsum_congr
        intro m
        exact hKstar _]
    exact hfrontError.trans
      (mul_le_mul_of_nonneg_left hover'
        (mul_nonneg (lipConst_nonneg ha0 ha1) hD))
  have hKtail := Periodization.periodization_error_le
    halpha hK0 hKb hP hq hs
  have hKbar : Kbar ≤ kiso + 4 * CK * Real.exp (-(alpha / 2) * P) := by
    dsimp [Kbar]
    have hle := le_abs_self
      ((∑' m : ℤ, Kstar (s - m * P)) - Kstar s)
    linarith [hKiso s]
  have hactual : ModelOrbitDefect.modelCurvature y yp P s ≤
      Kbar + lipConst a * D *
        (8 * a * C * Real.exp (-(alpha / 2) * P)) := by
    linarith [le_abs_self (ModelOrbitDefect.modelCurvature y yp P s - Kbar)]
  calc
    ModelOrbitDefect.modelCurvature y yp P s
        ≤ Kbar + lipConst a * D *
          (8 * a * C * Real.exp (-(alpha / 2) * P)) := hactual
    _ ≤ kiso + (4 * CK + 8 * lipConst a * D * a * C) *
          Real.exp (-(alpha / 2) * P) := by
      rw [mul_assoc, mul_assoc]
      nlinarith

/-- The centered estimate holds globally by periodicity. -/
theorem modelCurvature_le
    (halpha : 0 < alpha) (hP : 0 < P)
    (hq : Real.exp (-alpha * P) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hK0 : ∀ s, 0 ≤ Kstar s)
    (hKb : ∀ s, Kstar s ≤ CK * Real.exp (-alpha * |s|))
    (hKiso : ∀ s, Kstar s ≤ kiso) (u : ℝ) :
    ModelOrbitDefect.modelCurvature y yp P u ≤
      kiso + (4 * CK + 8 * lipConst a * D * a * C) *
        Real.exp (-(alpha / 2) * P) := by
  let KP := ModelOrbitDefect.modelCurvature y yp P
  have hper : Function.Periodic KP P :=
    ModelOrbitDefect.periodic_modelCurvature y yp P
  obtain ⟨v, hv, heq⟩ := hper.exists_mem_Ico₀ hP u
  change KP u ≤ _
  rw [heq]
  rcases le_or_gt v (P / 2) with h | h
  · apply modelCurvature_le_on_centered_cell halpha hP hq hy0 hyb hD hypb
      ha0 ha1 hYa hKstar hK0 hKb hKiso
    rw [abs_of_nonneg hv.1]
    exact h
  · have hshift := hper (v - P)
    simp only [sub_add_cancel] at hshift
    rw [hshift]
    apply modelCurvature_le_on_centered_cell halpha hP hq hy0 hyb hD hypb
      ha0 ha1 hYa hKstar hK0 hKb hKiso
    rw [abs_le]
    constructor <;> linarith [hv.2]

/-- One large-period threshold simultaneously enforces the geometric-series
hypothesis and any prescribed actual curvature ceiling above `kiso`. -/
theorem exists_threshold_modelCurvature_le
    (halpha : 0 < alpha)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ P, Hstrip ≤ P → ∀ u,
      (∑' m : ℤ, y (u - m * P)) ≤ a)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hK0 : ∀ s, 0 ≤ Kstar s)
    (hKb : ∀ s, Kstar s ≤ CK * Real.exp (-alpha * |s|))
    (hKiso : ∀ s, Kstar s ≤ kiso) (hgap : kiso < kh) :
    ∃ H0 : ℝ, 0 ≤ H0 ∧ ∀ P, H0 ≤ P →
      ∀ u, ModelOrbitDefect.modelCurvature y yp P u ≤ kh := by
  let A := 4 * CK + 8 * lipConst a * D * a * C
  obtain ⟨Hq, hHq0, hHq⟩ := LargeSeparation.exists_exp_threshold
    (C := (1 : ℝ)) halpha (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨He, hHe0, hHe⟩ := LargeSeparation.exists_exp_threshold
    (C := A) (by positivity : 0 < alpha / 2) (sub_pos.mpr hgap)
  let H0 := max 1 (max Hstrip (max Hq He))
  refine ⟨H0, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro P hP u
  have hP1 : 0 < P := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hP)
  have hstrip : Hstrip ≤ P :=
    (le_max_of_le_right (le_max_left _ _)).trans hP
  have hqP : Real.exp (-alpha * P) ≤ 1 / 2 := by
    have := hHq P ((le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))).trans hP)
    simpa using this
  have heP : A * Real.exp (-(alpha / 2) * P) ≤ kh - kiso :=
    hHe P ((le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))).trans hP)
  have hm := modelCurvature_le halpha hP1 hqP hy0 hyb hD hypb ha0 ha1
    (hYa P hstrip) hKstar hK0 hKb hKiso u
  dsimp [A] at heP ⊢
  linarith

end ActualFrontCurvatureLargePeriod
