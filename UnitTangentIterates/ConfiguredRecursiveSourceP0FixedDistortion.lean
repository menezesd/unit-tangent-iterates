import UnitTangentIterates.ConfiguredRecursiveSourceP0ScalarStart
import UnitTangentIterates.ConfiguredActualHalfScalarChoice

/-!
# Fixed near-identity distortion ceilings for recursive sources

The terminal gauge flow supplies normalized marking jets with error at most
`1 / 2`.  Consequently its fixed-junction coefficients are bounded by the
universal values `MA0 = 3 / 2` and `NA0 = 1 / 2`.  These values are selected
before the scalar tail, and the widened row ceilings dominate every local
near-identity transition having the canonical raw row bounds.
-/

noncomputable section

namespace ConfiguredRecursiveSourceP0FixedDistortion

open ConfiguredApproximateDefectPathRowwise
  ConfiguredRecursiveSourceP0ScalarStart
  ConfiguredRowCeilingPolynomialEnvelopes

/-- Universal first-jet amplification for a marking whose jet error is at
most one half. -/
def MA0 : ℝ := 3 / 2

/-- Universal second-jet amplification for the same marking. -/
def NA0 : ℝ := 1 / 2

theorem MA0_nonnegative : 0 ≤ MA0 := by
  norm_num [MA0]

theorem NA0_nonnegative : 0 ≤ NA0 := by
  norm_num [NA0]

/-- Dependency-order-safe scalar choice: it is fixed before the large
separation tail and does not depend on any subsequently selected row. -/
def choice : ConfiguredActualHalfScalarChoice.Choice where
  MA0 := MA0
  NA0 := NA0
  MA0_nonnegative := MA0_nonnegative
  NA0_nonnegative := NA0_nonnegative

@[simp] theorem choice_MA0 : choice.MA0 = MA0 := rfl

@[simp] theorem choice_NA0 : choice.NA0 = NA0 := rfl

/-- The recursive scalar and large-separation package at the fixed universal
distortion ceilings. -/
theorem exists_scalarOutput_of_eps
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    Nonempty (Output choice.MA0 choice.NA0) :=
  exists_output_of_eps heps heps10
    choice.MA0_nonnegative choice.NA0_nonnegative

/-- All fixed-junction scalar coefficients produced by a nonnegative jet
error at most one half fit the universal choice. -/
theorem nearIdentity_coefficients
    {e : ℝ} (he0 : 0 ≤ e) (heHalf : e ≤ 1 / 2) :
    0 < 1 - e ∧ 1 ≤ 1 / (1 - e) ∧
      1 + e ≤ MA0 ∧ e ≤ NA0 := by
  have hden : 0 < 1 - e := by linarith
  refine ⟨hden, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hden]
    linarith
  · norm_num [MA0]
    linarith
  · simpa [NA0] using heHalf

/-- The fixed widened ceilings dominate the local reparametrized analytic
coefficients whenever the unanchored coefficients satisfy the canonical row
bounds.  This is the exact scalar reduction needed by a recursive
`RowSelection`; construction of the selected row and its jet estimate remain
separate geometric obligations. -/
theorem nearIdentity_majorants
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    {khat e rawP1 rawG1 rawCg : ℝ}
    (hkhat : 0 ≤ khat) (he0 : 0 ≤ e) (heHalf : e ≤ 1 / 2)
    (hP0 : 0 ≤ rawP1) (hG0 : 0 ≤ rawG1) (hCg0 : 0 ≤ rawCg)
    (hP : rawP1 ≤ rowP1 D n)
    (hG : rawG1 ≤ rowG1 D n)
    (hCg : rawCg ≤ rowCg D n) :
    rawP1 * (1 + e) ≤ wideP1 D choice.MA0 n ∧
      rawG1 * (1 + e) ^ 2 + rawP1 * e ≤
        wideG1 D choice.MA0 choice.NA0 n ∧
      rawCg * (1 + e) ^ 2 + khat * rawP1 * e ≤
        wideCgWithKhat D khat choice.MA0 choice.NA0 n := by
  have hM0 : 0 ≤ 1 + e := by linarith
  have hM : 1 + e ≤ choice.MA0 := by
    dsimp [choice, MA0]
    linarith
  have hN : e ≤ choice.NA0 := by
    simpa [choice, NA0] using heHalf
  have hchoiceM0 : 0 ≤ choice.MA0 := choice.MA0_nonnegative
  have hM2 : (1 + e) ^ 2 ≤ choice.MA0 ^ 2 :=
    (sq_le_sq₀ hM0 hchoiceM0).2 hM
  have hrowP0 := rowP1_nonneg D n
  have hrowG0 := rowG1_nonneg D n
  have hrowCg0 := rowCg_nonneg D n
  constructor
  · unfold wideP1 ConfiguredRichMapStageProvider.mapP1
    apply le_max_of_le_right
    exact mul_le_mul hP hM hM0 hrowP0
  constructor
  · unfold wideG1 ConfiguredRichMapStageProvider.mapG1
    apply le_max_of_le_right
    apply add_le_add
    · exact mul_le_mul hG hM2 (sq_nonneg _) hrowG0
    · exact mul_le_mul hP hN he0 hrowP0
  · unfold wideCgWithKhat
    apply le_max_of_le_right
    apply add_le_add
    · exact mul_le_mul hCg hM2 (sq_nonneg _) hrowCg0
    · simpa [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul hP hN he0 hrowP0) hkhat

end ConfiguredRecursiveSourceP0FixedDistortion
