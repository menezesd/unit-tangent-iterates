import UnitTangentIterates.ConfiguredGaugeEndpointLinearRadius
import UnitTangentIterates.ConstructedRowCPolynomialGrowth

/-!
# Growth of the gauge endpoint linear coefficient

For fixed curvature and cost caps, the marking linearization coefficient is
cubic in linearly growing period/length ceilings.  One power of `1 + H` is
absorbed into an arbitrarily small exponential, putting it in precisely the
quadratic-exponential class used by the diagonal large-separation theorem.
-/

noncomputable section

set_option maxHeartbeats 2000000

namespace ConfiguredGaugeEndpointCoefficientGrowth

open ConfiguredGaugeEndpointLinearRadius
  InterpolationVariableSpeedSelInvAdapter
  ConstructedRowCPolynomialGrowth

/-- Linear bounds for the three quantities which genuinely grow with the
configured separation. -/
structure LinearInputBounds
    (H ell Lmax L : ℕ → ℝ) where
  ellCoeff : ℝ
  maxCoeff : ℝ
  lengthCoeff : ℝ
  ellCoeff_nonneg : 0 ≤ ellCoeff
  maxCoeff_nonneg : 0 ≤ maxCoeff
  lengthCoeff_nonneg : 0 ≤ lengthCoeff
  H_nonneg : ∀ n, 0 ≤ H n
  ell_nonneg : ∀ n, 0 ≤ ell n
  max_nonneg : ∀ n, 0 ≤ Lmax n
  length_nonneg : ∀ n, 0 ≤ L n
  ell_le : ∀ n, ell n ≤ ellCoeff * (1 + H n)
  max_le : ∀ n, Lmax n ≤ maxCoeff * (1 + H n)
  length_le : ∀ n, L n ≤ lengthCoeff * (1 + H n)

/-- An explicit nonnegative cubic coefficient. -/
def cubicCoeff
    (B : LinearInputBounds H ell Lmax L)
    (kappa kappa2 M kb kL : ℝ) : ℝ :=
  let A := 2 * B.maxCoeff * kappa
  let C1 := B.ellCoeff * kappa * (Real.exp (kappa * M) + 1)
  let C2 := B.ellCoeff ^ 2 * Real.exp (2 * kappa * M) * kappa2
  A + (C1 + B.lengthCoeff * kb * A) +
    (C2 + kb * C1 * (2 * B.lengthCoeff + C1 * M) +
      B.lengthCoeff ^ 2 * (kL + kb ^ 2) * A)

theorem cubicCoeff_nonneg
    (B : LinearInputBounds H ell Lmax L)
    {kappa kappa2 M kb kL : ℝ}
    (hkappa : 0 ≤ kappa) (hkappa2 : 0 ≤ kappa2)
    (hM : 0 ≤ M) (hkb : 0 ≤ kb) (hkL : 0 ≤ kL) :
    0 ≤ cubicCoeff B kappa kappa2 M kb kL := by
  let A := 2 * B.maxCoeff * kappa
  let C1 := B.ellCoeff * kappa * (Real.exp (kappa * M) + 1)
  let C2 := B.ellCoeff ^ 2 * Real.exp (2 * kappa * M) * kappa2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by norm_num) B.maxCoeff_nonneg) hkappa
  have hC1 : 0 ≤ C1 := by
    dsimp [C1]
    exact mul_nonneg (mul_nonneg B.ellCoeff_nonneg hkappa)
      (add_nonneg (Real.exp_pos _).le zero_le_one)
  have hC2 : 0 ≤ C2 := by
    dsimp [C2]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hkappa2
  change 0 ≤ A + (C1 + B.lengthCoeff * kb * A) +
    (C2 + kb * C1 * (2 * B.lengthCoeff + C1 * M) +
      B.lengthCoeff ^ 2 * (kL + kb ^ 2) * A)
  exact add_nonneg
    (add_nonneg hA (add_nonneg hC1
      (mul_nonneg (mul_nonneg B.lengthCoeff_nonneg hkb) hA)))
    (add_nonneg
      (add_nonneg hC2
        (mul_nonneg (mul_nonneg hkb hC1)
          (add_nonneg (mul_nonneg (by norm_num) B.lengthCoeff_nonneg)
            (mul_nonneg hC1 hM))))
      (mul_nonneg
        (mul_nonneg (sq_nonneg _)
          (add_nonneg hkL (sq_nonneg _))) hA))

/-- The exact endpoint coefficient has a cubic polynomial envelope. -/
theorem endpointLinearCoeff_le_cubic
    (B : LinearInputBounds H ell Lmax L)
    {kappa kappa2 M kb kL : ℝ}
    (hkappa : 0 ≤ kappa) (hkappa2 : 0 ≤ kappa2)
    (hM : 0 ≤ M) (hkb : 0 ≤ kb) (hkL : 0 ≤ kL) :
    ∀ n,
      endpointLinearCoeff ell Lmax (fun _ ↦ kappa) (fun _ ↦ kappa2)
          L (fun _ ↦ kb) (fun _ ↦ kL) M n ≤
        cubicCoeff B kappa kappa2 M kb kL * (1 + H n) ^ 3 := by
  intro n
  let z := 1 + H n
  let A0 := 2 * B.maxCoeff * kappa
  let C10 := B.ellCoeff * kappa * (Real.exp (kappa * M) + 1)
  let C20 := B.ellCoeff ^ 2 * Real.exp (2 * kappa * M) * kappa2
  have hz1 : 1 ≤ z := by dsimp [z]; linarith [B.H_nonneg n]
  have hz0 : 0 ≤ z := zero_le_one.trans hz1
  have hA0 : 0 ≤ A0 := by
    dsimp [A0]
    exact mul_nonneg (mul_nonneg (by norm_num) B.maxCoeff_nonneg) hkappa
  have hC10 : 0 ≤ C10 := by
    dsimp [C10]
    exact mul_nonneg (mul_nonneg B.ellCoeff_nonneg hkappa)
      (add_nonneg (Real.exp_pos _).le zero_le_one)
  have hC20 : 0 ≤ C20 := by dsimp [C20]; positivity
  have hmaxBound : Lmax n ≤ B.maxCoeff * z := by
    simpa [z] using B.max_le n
  have hellBound : ell n ≤ B.ellCoeff * z := by
    simpa [z] using B.ell_le n
  have hlengthBound : L n ≤ B.lengthCoeff * z := by
    simpa [z] using B.length_le n
  have hAactual0 : 0 ≤ 2 * Lmax n * kappa :=
    mul_nonneg (mul_nonneg (by norm_num) (B.max_nonneg n)) hkappa
  have hC1actual0 : 0 ≤
      ell n * kappa * (Real.exp (kappa * M) + 1) :=
    mul_nonneg (mul_nonneg (B.ell_nonneg n) hkappa)
      (add_nonneg (Real.exp_pos _).le zero_le_one)
  have hA : 2 * Lmax n * kappa ≤ A0 * z := by
    calc
      2 * Lmax n * kappa ≤ 2 * (B.maxCoeff * z) * kappa := by gcongr
      _ = A0 * z := by dsimp [A0]; ring
  have hC1 : ell n * kappa * (Real.exp (kappa * M) + 1) ≤ C10 * z := by
    calc
      ell n * kappa * (Real.exp (kappa * M) + 1) ≤
          (B.ellCoeff * z) * kappa * (Real.exp (kappa * M) + 1) := by gcongr
      _ = C10 * z := by dsimp [C10]; ring
  have hellsq : ell n ^ 2 ≤ (B.ellCoeff * z) ^ 2 :=
    (sq_le_sq₀ (B.ell_nonneg n)
      (mul_nonneg B.ellCoeff_nonneg hz0)).2 (B.ell_le n)
  have hC2 : ell n ^ 2 * Real.exp (2 * kappa * M) * kappa2 ≤ C20 * z ^ 2 := by
    calc
      ell n ^ 2 * Real.exp (2 * kappa * M) * kappa2 ≤
          (B.ellCoeff * z) ^ 2 * Real.exp (2 * kappa * M) * kappa2 := by gcongr
      _ = C20 * z ^ 2 := by dsimp [C20]; ring
  have hLA : L n * kb * (2 * Lmax n * kappa) ≤
      B.lengthCoeff * kb * A0 * z ^ 2 := by
    have hcap0 : 0 ≤ B.lengthCoeff * z * kb :=
      mul_nonneg (mul_nonneg B.lengthCoeff_nonneg hz0) hkb
    calc
      L n * kb * (2 * Lmax n * kappa) ≤
          (B.lengthCoeff * z) * kb * (A0 * z) := by gcongr
      _ = B.lengthCoeff * kb * A0 * z ^ 2 := by ring
  have hinner : 2 * L n +
      (ell n * kappa * (Real.exp (kappa * M) + 1)) * M ≤
      (2 * B.lengthCoeff + C10 * M) * z := by
    calc
      2 * L n + (ell n * kappa * (Real.exp (kappa * M) + 1)) * M ≤
          2 * (B.lengthCoeff * z) + (C10 * z) * M := by gcongr
      _ = (2 * B.lengthCoeff + C10 * M) * z := by ring
  have hinner0 : 0 ≤ 2 * L n +
      (ell n * kappa * (Real.exp (kappa * M) + 1)) * M :=
    add_nonneg (mul_nonneg (by norm_num) (B.length_nonneg n))
      (mul_nonneg hC1actual0 hM)
  have hinnerCap0 : 0 ≤ 2 * B.lengthCoeff + C10 * M :=
    add_nonneg (mul_nonneg (by norm_num) B.lengthCoeff_nonneg)
      (mul_nonneg hC10 hM)
  have hC1inner : kb *
      (ell n * kappa * (Real.exp (kappa * M) + 1)) *
        (2 * L n + (ell n * kappa * (Real.exp (kappa * M) + 1)) * M) ≤
      kb * C10 * (2 * B.lengthCoeff + C10 * M) * z ^ 2 := by
    calc
      _ ≤ kb * (C10 * z) *
          ((2 * B.lengthCoeff + C10 * M) * z) := by gcongr
      _ = _ := by ring
  have hLsq : L n ^ 2 ≤ (B.lengthCoeff * z) ^ 2 :=
    (sq_le_sq₀ (B.length_nonneg n)
      (mul_nonneg B.lengthCoeff_nonneg hz0)).2 (B.length_le n)
  have hL2A : L n ^ 2 * (kL + kb ^ 2) * (2 * Lmax n * kappa) ≤
      B.lengthCoeff ^ 2 * (kL + kb ^ 2) * A0 * z ^ 3 := by
    calc
      _ ≤ (B.lengthCoeff * z) ^ 2 * (kL + kb ^ 2) * (A0 * z) := by gcongr
      _ = _ := by ring
  let E0 := cubicCoeff B kappa kappa2 M kb kL
  have hE0 : 0 ≤ E0 := cubicCoeff_nonneg B hkappa hkappa2 hM hkb hkL
  let mid0 := C10 + B.lengthCoeff * kb * A0
  let last0 := C20 + kb * C10 * (2 * B.lengthCoeff + C10 * M) +
    B.lengthCoeff ^ 2 * (kL + kb ^ 2) * A0
  have hmid0 : 0 ≤ mid0 := by
    dsimp [mid0]
    exact add_nonneg hC10
      (mul_nonneg (mul_nonneg B.lengthCoeff_nonneg hkb) hA0)
  have hlast0 : 0 ≤ last0 := by
    dsimp [last0]
    exact add_nonneg
      (add_nonneg hC20
        (mul_nonneg (mul_nonneg hkb hC10) hinnerCap0))
      (mul_nonneg
        (mul_nonneg (sq_nonneg _)
          (add_nonneg hkL (sq_nonneg _))) hA0)
  have hEexpand : E0 = A0 + mid0 + last0 := by
    dsimp [E0, cubicCoeff, A0, C10, C20, mid0, last0]
  have hA0E : A0 ≤ E0 := by
    rw [hEexpand]
    linarith
  have hmidE : C10 + B.lengthCoeff * kb * A0 ≤ E0 := by
    change mid0 ≤ E0
    rw [hEexpand]
    linarith
  have hlastE : C20 + kb * C10 * (2 * B.lengthCoeff + C10 * M) +
      B.lengthCoeff ^ 2 * (kL + kb ^ 2) * A0 ≤ E0 := by
    change last0 ≤ E0
    rw [hEexpand]
    linarith
  have hz13 : z ≤ z ^ 3 := by nlinarith [sq_nonneg (z - 1)]
  have hz23 : z ^ 2 ≤ z ^ 3 := by nlinarith [sq_nonneg z, sq_nonneg (z - 1)]
  have hfirst : 2 * Lmax n * kappa ≤ E0 * z ^ 3 :=
    hA.trans ((mul_le_mul_of_nonneg_right hA0E hz0).trans
      (mul_le_mul_of_nonneg_left hz13 hE0))
  have hmiddle :
      ell n * kappa * (Real.exp (kappa * M) + 1) +
        L n * kb * (2 * Lmax n * kappa) ≤ E0 * z ^ 3 := by
    calc
      _ ≤ (C10 + B.lengthCoeff * kb * A0) * z ^ 2 := by
        nlinarith [hC1, hLA, mul_nonneg hC10 hz0,
          mul_nonneg (mul_nonneg B.lengthCoeff_nonneg hkb) hA0]
      _ ≤ E0 * z ^ 2 := mul_le_mul_of_nonneg_right hmidE (sq_nonneg z)
      _ ≤ E0 * z ^ 3 := mul_le_mul_of_nonneg_left hz23 hE0
  have hlast :
      ell n ^ 2 * Real.exp (2 * kappa * M) * kappa2 +
        kb * (ell n * kappa * (Real.exp (kappa * M) + 1)) *
          (2 * L n + (ell n * kappa * (Real.exp (kappa * M) + 1)) * M) +
        L n ^ 2 * (kL + kb ^ 2) * (2 * Lmax n * kappa) ≤
      E0 * z ^ 3 := by
    have hC2' : ell n ^ 2 * Real.exp (2 * kappa * M) * kappa2 ≤
        C20 * z ^ 3 := hC2.trans (mul_le_mul_of_nonneg_left hz23 hC20)
    have hC1inner' := hC1inner.trans
      (mul_le_mul_of_nonneg_left hz23
        (mul_nonneg (mul_nonneg hkb hC10) hinnerCap0))
    calc
      _ ≤ C20 * z ^ 3 +
          (kb * C10 * (2 * B.lengthCoeff + C10 * M)) * z ^ 3 +
          (B.lengthCoeff ^ 2 * (kL + kb ^ 2) * A0) * z ^ 3 :=
        add_le_add (add_le_add hC2' hC1inner') hL2A
      _ = (C20 + kb * C10 * (2 * B.lengthCoeff + C10 * M) +
          B.lengthCoeff ^ 2 * (kL + kb ^ 2) * A0) * z ^ 3 := by ring
      _ ≤ E0 * z ^ 3 := mul_le_mul_of_nonneg_right hlastE (pow_nonneg hz0 3)
  change max (2 * Lmax n * kappa)
      (max
        (ell n * kappa * (Real.exp (kappa * M) + 1) +
          L n * kb * (2 * Lmax n * kappa))
        (ell n ^ 2 * Real.exp (2 * kappa * M) * kappa2 +
          kb * (ell n * kappa * (Real.exp (kappa * M) + 1)) *
            (2 * L n +
              (ell n * kappa * (Real.exp (kappa * M) + 1)) * M) +
          L n ^ 2 * (kL + kb ^ 2) * (2 * Lmax n * kappa))) ≤ _
  exact max_le hfirst (max_le hmiddle hlast)

/-- Cubic growth becomes the quadratic-times-small-exponential growth used by
`ExponentialDiagonalLargeSeparation`. -/
theorem exists_endpointLinearCoeff_growth_majorant
    (B : LinearInputBounds H ell Lmax L)
    {kappa kappa2 M kb kL gamma : ℝ}
    (hkappa : 0 ≤ kappa) (hkappa2 : 0 ≤ kappa2)
    (hM : 0 ≤ M) (hkb : 0 ≤ kb) (hkL : 0 ≤ kL)
    (hgamma : 0 < gamma) :
    ∃ E0 : ℝ, 0 ≤ E0 ∧ ∀ n,
      endpointLinearCoeff ell Lmax (fun _ ↦ kappa) (fun _ ↦ kappa2)
          L (fun _ ↦ kb) (fun _ ↦ kL) M n ≤
        E0 * (1 + H n) ^ 2 * Real.exp (gamma * H n) := by
  obtain ⟨A, hA0, hA⟩ := exists_one_add_pow_le_exp 1 hgamma
  let E0 := cubicCoeff B kappa kappa2 M kb kL * A
  have hcubic0 := cubicCoeff_nonneg B hkappa hkappa2 hM hkb hkL
  refine ⟨E0, mul_nonneg hcubic0 hA0, ?_⟩
  intro n
  have hz := hA (H n) (B.H_nonneg n)
  simp only [pow_one] at hz
  calc
    endpointLinearCoeff ell Lmax (fun _ ↦ kappa) (fun _ ↦ kappa2)
        L (fun _ ↦ kb) (fun _ ↦ kL) M n ≤
      cubicCoeff B kappa kappa2 M kb kL * (1 + H n) ^ 3 :=
        endpointLinearCoeff_le_cubic B hkappa hkappa2 hM hkb hkL n
    _ = cubicCoeff B kappa kappa2 M kb kL * (1 + H n) ^ 2 *
        (1 + H n) := by ring
    _ ≤ cubicCoeff B kappa kappa2 M kb kL * (1 + H n) ^ 2 *
        (A * Real.exp (gamma * H n)) := by gcongr
    _ = E0 * (1 + H n) ^ 2 * Real.exp (gamma * H n) := by
      dsimp [E0]
      ring

end ConfiguredGaugeEndpointCoefficientGrowth
