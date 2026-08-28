import UnitTangentIterates.ConfiguredPhysicalDiagonalLargeSeparation
import UnitTangentIterates.ConfiguredVariableTerminalCapstone

/-!
# The configured physical-diagonal row budget

This is the scalar tube package associated with the perimeter-scaled diagonal
defect.  It is the non-amplifying analogue of the budget assembled in the
older weighted capstone.
-/

noncomputable section

open PathMetric MarkedSpace
open NormalPathC2IncrementVariableSpeed

namespace ConfiguredPhysicalDiagonalRowBudget

open ConfiguredInductiveTubeBudget
open ConstructedConfiguredInductiveTubeBudget
open ConstructedConfiguredInductiveTubeBudget.WeightedData
open ConfiguredPolynomialDiagonalStableRowDefectProvider
open ConfiguredRowCeilingPolynomialEnvelopes
open ConfiguredStableVariableTerminalCapstone
open ConfiguredVariableTerminalCapstone
open ExponentialDiagonalLargeSeparation
open VariableTerminalRowTubeAdapter

def conversion (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA : ℝ) : ℕ → ℝ :=
  ConfiguredStableVariableTerminalCapstone.rowConversion D
    (wideP1 D MA) (wideG1 D MA NA) (wideCg D MA NA)

/-- Row-distance conversion for a recursive path class whose curvature
ceiling is independent of the canonical configured `kstar`. -/
def conversionWithKhat (D : ConstructedConfiguredSequenceWeighted.Data)
    (khat MA NA : ℝ) : ℕ → ℝ :=
  fun n ↦ c2ConstVar (ConfiguredApproximateDefectPathRowwise.rowP0 D n)
    (wideP1 D MA n) khat
    (wideG1 D MA NA n) (wideCgWithKhat D khat MA NA n)

def radius (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA : ℝ) {Cw : ℝ}
    (L : Output D (conversion D MA NA) (physicalDefect D) Cw) : ℕ → ℝ :=
  rowRadius (shiftSequence (conversion D MA NA) L.N)
    (shiftSequence (physicalDefect D) L.N)

def rho (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA : ℝ) {Cw : ℝ}
    (L : Output D (conversion D MA NA) (physicalDefect D) Cw) : ℕ → ℝ :=
  ConstructedRowDefectLargeSeparation.rowRhoVariable
    (shift D L.N).model (radius D MA NA L)

def shiftedUpper (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA : ℝ) {Cw : ℝ}
    (L : Output D (conversion D MA NA) (physicalDefect D) Cw) : ℕ → ℝ :=
  fun n ↦ 2 * (shift D L.N).Hs n + radius D MA NA L n

theorem conversion_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (MA NA : ℝ)
    (N n : ℕ) :
    ConfiguredStableVariableTerminalCapstone.rowConversion (shift D N)
        (shiftSequence (wideP1 D MA) N)
        (shiftSequence (wideG1 D MA NA) N)
        (shiftSequence (wideCg D MA NA) N) n =
      shiftSequence (conversion D MA NA) N n := by
  rfl

/-- Radius reserved by an arbitrary diagonal large-separation output.  This
form is used when the conversion also includes the terminal marking defect. -/
def outputRadius (D : ConstructedConfiguredSequenceWeighted.Data)
    {Cdiag diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D Cdiag diagonal Cw) : ℕ → ℝ :=
  rowRadius (shiftSequence Cdiag L.N) (shiftSequence diagonal L.N)

def outputRho (D : ConstructedConfiguredSequenceWeighted.Data)
    {Cdiag diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D Cdiag diagonal Cw) : ℕ → ℝ :=
  ConstructedRowDefectLargeSeparation.rowRhoVariable
    (shift D L.N).model (outputRadius D L)

def outputUpper (D : ConstructedConfiguredSequenceWeighted.Data)
    {Cdiag diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D Cdiag diagonal Cw) : ℕ → ℝ :=
  fun n ↦ 2 * (shift D L.N).Hs n + outputRadius D L n

/-- The scalar row budget for any nonnegative diagonal and conversion.  In
the final application `Cdiag` is the sum of the path conversion and the
linear terminal-marking coefficient. -/
theorem exists_rowBudget_of_output
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {Cdiag diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D Cdiag diagonal Cw)
    (hCdiag : ∀ n, 0 ≤ Cdiag n) (hdiagonal : ∀ n, 0 ≤ diagonal n)
    (Q : ℕ → Data)
    (P1 G1 Cg : ℕ → ℝ)
    (hQperim : ∀ n, perim (Q n) = 2 * (shift D L.N).Hs n)
    (P0 : ℕ → ℝ :=
      ConfiguredApproximateDefectPathRowwise.rowP0 (shift D L.N))
    (khat : ℕ → ℝ := fun _ ↦ (shift D L.N).kstar) :
    Nonempty (RowBudget Q
      P0
      P1 khat G1 Cg
      (fun _ ↦ 2 * (shift D L.N).Hs 0)
      (fun _ ↦ chordBase (shift D L.N).model)
      (accBound (shift D L.N).model)
      (outputRadius D L) (outputRho D L) (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)) := by
  let D' := shift D L.N
  let A : ℕ → ℝ := shiftSequence Cdiag L.N
  let d : ℕ → ℝ := shiftSequence diagonal L.N
  let r : ℕ → ℝ := rowRadius A d
  let rho' : ℕ → ℝ :=
    ConstructedRowDefectLargeSeparation.rowRhoVariable D'.model r
  have hr0 : ∀ n, 0 ≤ r n := by
    intro n
    exact mul_nonneg (hCdiag (L.N + n))
      (ShadowingTails.tail_nonneg
        (fun k ↦ hdiagonal (L.N + (n + k))) 0)
  have hspeed : ∀ n, r n ≤ D'.Hs 0 := by
    intro n
    simpa [r, A, d, D'] using L.speed_tail n
  have hH0 : 0 < D'.Hs 0 := D'.separation_zero_pos
  have hkstar : 0 < D'.model.kstar := configured_kstar_pos D'.model
  have hchord : 0 < chordBase D'.model := by
    rw [chordBase_eq_min D'.model hkstar]
    exact lt_min hH0 (div_pos Real.pi_pos (mul_pos (by norm_num) hkstar))
  have hrho0 : ∀ n, 0 < rho' n := by
    intro n
    dsimp [rho', ConstructedRowDefectLargeSeparation.rowRhoVariable]
    apply lt_min
    · norm_num
    · exact div_pos hH0 (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
        (mul_pos (sq_pos_of_pos
          (mul_pos (by norm_num) (D'.model.separation_pos n))) hkstar)
        (hr0 n)))
  have haccRadius : ∀ n,
      (accBound D'.model n + r n) * rho' n ≤
        (2 * D'.Hs 0 - r n) / 2 := by
    intro n
    have hden : 0 < accBound D'.model n + r n :=
      add_pos_of_pos_of_nonneg (mul_pos
        (sq_pos_of_pos (mul_pos (by norm_num) (D'.model.separation_pos n))) hkstar)
        (hr0 n)
    have hmin := min_le_right (1 / 2 : ℝ)
      (D'.Hs 0 / (2 * (accBound D'.model n + r n)))
    have hm : (accBound D'.model n + r n) * rho' n ≤ D'.Hs 0 / 2 := by
      calc
        _ ≤ (accBound D'.model n + r n) *
            (D'.Hs 0 / (2 * (accBound D'.model n + r n))) :=
          mul_le_mul_of_nonneg_left hmin hden.le
        _ = D'.Hs 0 / 2 := by field_simp
    linarith [hspeed n]
  have hchord_le : chordBase D'.model ≤ D'.Hs 0 := by
    rw [chordBase_eq_min D'.model hkstar]
    exact min_le_left _ _
  refine ⟨{
    radius_nonnegative := hr0
    local_speed_positive := fun n ↦ by
      change 0 < 2 * D'.Hs 0 - r n
      linarith [hspeed n, hH0]
    target_speed := fun n ↦ by
      change D'.Hs 0 ≤ 2 * D'.Hs 0 - r n
      linarith [hspeed n]
    acceleration_nonnegative := fun n ↦ by
      exact (mul_pos (sq_pos_of_pos
        (mul_pos (by norm_num) (D'.model.separation_pos n))) hkstar).le
    rho_positive := hrho0
    rho_half := fun n ↦ min_le_left _ _
    acceleration_radius := haccRadius
    chord_nonnegative := (half_pos hchord).le
    chord_speed := fun n ↦ by
      change chordBase D'.model / 2 ≤ (2 * D'.Hs 0 - r n) / 2
      linarith [hchord_le, hspeed n]
    chord_margin := fun n ↦ by
      change 2 * r n ≤ (chordBase D'.model - chordBase D'.model / 2) * rho' n
      nlinarith [L.chord_tail n]
    upper_speed := fun n ↦ by
      unfold outputUpper outputRadius
      rw [hQperim n]
    }⟩

theorem exists_rowBudget
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA Cw : ℝ}
    (L : Output D (conversion D MA NA) (physicalDefect D) Cw)
    (Q : ℕ → Data)
    (hQperim : ∀ n, perim (Q n) = 2 * (shift D L.N).Hs n) :
    Nonempty (RowBudget Q
      (ConfiguredApproximateDefectPathRowwise.rowP0 (shift D L.N))
      (shiftSequence (wideP1 D MA) L.N)
      (fun _ ↦ (shift D L.N).kstar)
      (shiftSequence (wideG1 D MA NA) L.N)
      (shiftSequence (wideCg D MA NA) L.N)
      (fun _ ↦ 2 * (shift D L.N).Hs 0)
      (fun _ ↦ chordBase (shift D L.N).model)
      (accBound (shift D L.N).model)
      (radius D MA NA L) (rho D MA NA L) (shiftedUpper D MA NA L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)) := by
  let D' := shift D L.N
  let A : ℕ → ℝ := shiftSequence (conversion D MA NA) L.N
  let d : ℕ → ℝ := shiftSequence (physicalDefect D) L.N
  let r : ℕ → ℝ := rowRadius A d
  let rho' : ℕ → ℝ :=
    ConstructedRowDefectLargeSeparation.rowRhoVariable D'.model r
  let Cup : ℕ → ℝ :=
    fun n ↦ 2 * D'.Hs n + r n
  have hr0 : ∀ n, 0 ≤ r n := by
    intro n
    apply mul_nonneg
    · change 0 ≤ ConfiguredStableVariableTerminalCapstone.rowConversion D
        (wideP1 D MA) (wideG1 D MA NA) (wideCg D MA NA) (L.N + n)
      exact c2ConstVar_nonneg _ _ _ _ _
    · exact
      (ShadowingTails.tail_nonneg
        (fun k ↦ physicalDefect_nonneg D (L.N + (n + k))) 0)
  have hspeed : ∀ n, r n ≤ D'.Hs 0 := by
    intro n
    simpa [r, A, d, D'] using L.speed_tail n
  have hH0 : 0 < D'.Hs 0 := D'.separation_zero_pos
  have hkstar : 0 < D'.model.kstar := configured_kstar_pos D'.model
  have hchord : 0 < chordBase D'.model := by
    rw [chordBase_eq_min D'.model hkstar]
    exact lt_min hH0 (div_pos Real.pi_pos (mul_pos (by norm_num) hkstar))
  have hrho0 : ∀ n, 0 < rho' n := by
    intro n
    dsimp [rho', ConstructedRowDefectLargeSeparation.rowRhoVariable]
    apply lt_min
    · norm_num
    · exact div_pos hH0 (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
        (mul_pos (sq_pos_of_pos
          (mul_pos (by norm_num) (D'.model.separation_pos n))) hkstar)
        (hr0 n)))
  have haccRadius : ∀ n,
      (accBound D'.model n + r n) * rho' n ≤
        (2 * D'.Hs 0 - r n) / 2 := by
    intro n
    have hden : 0 < accBound D'.model n + r n :=
      add_pos_of_pos_of_nonneg (mul_pos
        (sq_pos_of_pos (mul_pos (by norm_num) (D'.model.separation_pos n))) hkstar)
        (hr0 n)
    have hmin := min_le_right (1 / 2 : ℝ)
      (D'.Hs 0 / (2 * (accBound D'.model n + r n)))
    have hm : (accBound D'.model n + r n) * rho' n ≤ D'.Hs 0 / 2 := by
      calc
        _ ≤ (accBound D'.model n + r n) *
            (D'.Hs 0 / (2 * (accBound D'.model n + r n))) :=
          mul_le_mul_of_nonneg_left hmin hden.le
        _ = D'.Hs 0 / 2 := by field_simp
    linarith [hspeed n]
  have hchord_le : chordBase D'.model ≤ D'.Hs 0 := by
    rw [chordBase_eq_min D'.model hkstar]
    exact min_le_left _ _
  refine ⟨{
    radius_nonnegative := hr0
    local_speed_positive := fun n ↦ by
      change 0 < 2 * D'.Hs 0 - r n
      linarith [hspeed n, hH0]
    target_speed := fun n ↦ by
      change D'.Hs 0 ≤ 2 * D'.Hs 0 - r n
      linarith [hspeed n]
    acceleration_nonnegative := fun n ↦ by
      exact (mul_pos (sq_pos_of_pos
        (mul_pos (by norm_num) (D'.model.separation_pos n))) hkstar).le
    rho_positive := hrho0
    rho_half := fun n ↦ min_le_left _ _
    acceleration_radius := haccRadius
    chord_nonnegative := (half_pos hchord).le
    chord_speed := fun n ↦ by
      change chordBase D'.model / 2 ≤ (2 * D'.Hs 0 - r n) / 2
      linarith [hchord_le, hspeed n]
    chord_margin := fun n ↦ by
      change 2 * r n ≤ (chordBase D'.model - chordBase D'.model / 2) * rho' n
      nlinarith [L.chord_tail n]
    upper_speed := fun n ↦ by
      unfold shiftedUpper radius
      rw [hQperim n]
    }⟩

end ConfiguredPhysicalDiagonalRowBudget
