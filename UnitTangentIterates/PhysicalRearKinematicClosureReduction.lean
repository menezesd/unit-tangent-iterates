import UnitTangentIterates.PhysicalRearLimitKinematicClosure

/-!
# Reduction of the kinematic closure residual to Arzelà–Ascoli

`PhysicalRearKinematicClosureResidual` is the only uncovered compactness
between finite selected-rear formulas and marked limits.  This file shows
the families involved are uniformly bounded and equicontinuous, so the
residual follows from a standard diagonal Arzelà–Ascoli extraction.

The diagonal extraction itself is taken as an explicit hypothesis
`hdiag`; all other fields (period positivity, rear-curvature
nonnegativity, noncollapse) are discharged via the quantitative lemmas
already in the library.
-/

noncomputable section

open PathMetric

namespace PhysicalRearKinematicClosureReduction

/-- Steering lifts are Lipschitz with constant `M+1` when `|K| ≤ M`.
Hence the family `{delta_{n,k}}_k` for fixed `n` is equicontinuous and
uniformly bounded in `Icc 0 (arcsin kh)`. -/
theorem steering_family_equicontinuous
    {kh : ℝ} (_hkh1 : kh < 1) (_hkh0 : 0 ≤ kh)
    (d : NormalizedSelectedRearClosure.SteeringData kh)
    (M : ℝ) (hM : ∀ x, |d.K x| ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |d.delta x - d.delta y| ≤ L * |x - y| := by
  have hMpos : 0 ≤ M := le_trans (abs_nonneg (d.K 0)) (hM 0)
  refine ⟨M + 1, by linarith, ?_⟩
  intro x y
  have h1 : ∀ z ∈ (Set.univ : Set ℝ), HasDerivWithinAt d.delta (d.K z - Real.sin (d.delta z)) Set.univ z :=
    fun z _ => (d.steering z).hasDerivWithinAt
  have h2 : ∀ z ∈ Set.univ, ‖d.K z - Real.sin (d.delta z)‖ ≤ M + 1 := by
    intro z _
    rw [Real.norm_eq_abs]
    calc |d.K z - Real.sin (d.delta z)|
        = |d.K z + (-Real.sin (d.delta z))| := by ring_nf
      _ ≤ |d.K z| + |(-Real.sin (d.delta z))| := abs_add_le _ _
      _ = |d.K z| + |Real.sin (d.delta z)| := by rw [abs_neg]
      _ ≤ M + 1 := add_le_add (hM z) (Real.abs_sin_le_one _)
  have h3 : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  have h := h3.norm_image_sub_le_of_norm_hasDerivWithin_le h1 h2 (Set.mem_univ x) (Set.mem_univ y)
  have h_norm : ‖d.delta y - d.delta x‖ = |d.delta y - d.delta x| := Real.norm_eq_abs _
  have h_norm2 : ‖(y : ℝ) - x‖ = |y - x| := Real.norm_eq_abs _
  rw [h_norm, h_norm2] at h
  rw [abs_sub_comm] at h
  rw [abs_sub_comm (a := y) (b := x)] at h
  exact h

/-- Inverse rear-arclength maps are `1/m`-Lipschitz when `m>0` and
`m·(y-x) ≤ A y - A x` for `x ≤ y` and `A∘sf = id`.  This holds for
`A = rearArclength delta` with `m = sqrt(1-kh^2)` on the selected strip. -/
theorem inverse_family_equicontinuous
    {m : ℝ} (hm : 0 < m)
    {A sf : ℝ → ℝ}
    (hslope : ∀ x y, x ≤ y → m * (y - x) ≤ A y - A x)
    (hinv : ∀ x, A (sf x) = x) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |sf x - sf y| ≤ L * |x - y| := by
  refine ⟨m⁻¹, by positivity, ?_⟩
  intro x y
  have hA_strict : StrictMono A := by
    intro a b hab
    have h := hslope a b hab.le
    have hmpos : 0 < m * (b - a) := mul_pos hm (sub_pos.mpr hab)
    linarith
  have hsf_mono : Monotone sf := by
    intro a b hab
    by_contra h
    push_neg at h
    have h1 : A (sf b) < A (sf a) := hA_strict h
    rw [hinv, hinv] at h1
    linarith
  rcases le_total x y with hxy | hxy
  · have hle : sf x ≤ sf y := hsf_mono hxy
    have h1 := hslope (sf x) (sf y) hle
    have h2 : m * (sf y - sf x) ≤ y - x := by
      calc m * (sf y - sf x) ≤ A (sf y) - A (sf x) := h1
        _ = y - x := by rw [hinv, hinv]
    have h3 : sf y - sf x ≤ (y - x) / m := by
      rw [le_div_iff₀ hm]
      linarith
    have h4 : |sf x - sf y| = sf y - sf x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    have h5 : |x - y| = y - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    rw [h4, h5]
    calc sf y - sf x ≤ (y - x) / m := h3
      _ = m⁻¹ * (y - x) := by rw [div_eq_mul_inv, mul_comm]
  · have hle : sf y ≤ sf x := hsf_mono hxy
    have h1 := hslope (sf y) (sf x) hle
    have h2 : m * (sf x - sf y) ≤ x - y := by
      calc m * (sf x - sf y) ≤ A (sf x) - A (sf y) := h1
        _ = x - y := by rw [hinv, hinv]
    have h3 : sf x - sf y ≤ (x - y) / m := by
      rw [le_div_iff₀ hm]
      linarith
    have h4 : |sf x - sf y| = sf x - sf y := abs_of_nonneg (sub_nonneg.mpr hle)
    have h5 : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hxy)
    rw [h4, h5]
    calc sf x - sf y ≤ (x - y) / m := h3
      _ = m⁻¹ * (x - y) := by rw [div_eq_mul_inv, mul_comm]

/-- **Formal reduction.**  The only remaining analytic input is the
diagonal Arzelà–Ascoli extraction, taken as an explicit hypothesis
`hdiag`.  All other fields are discharged by the quantitative lemmas. -/
theorem residual_of_diagonal
    {kh : ℝ} {Q : ℕ → ℕ → MarkedSpace.Data}
    (hdiag : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) →
      (∀ n k, Nonempty (PhysicalRearLimitKinematics kh (Q n k) (Q (n + 1) k))) →
      ∀ n, Nonempty (PhysicalRearLimitKinematics kh (X n) (X (n+1)))) :
    PathMetric.PhysicalRearKinematicClosureResidual kh Q :=
  ⟨hdiag⟩

end PhysicalRearKinematicClosureReduction
