import UnitTangentIterates.ConfiguredCanonicalPairSource
import UnitTangentIterates.VariableMarkedPhysicalLength
import UnitTangentIterates.ModelWidth

/-!
# Geometry of the gauge-first aligned configured fronts

The gauge-first recursion changes only normalized phase and a Euclidean rigid
motion.  This module records the elementary model geometry which survives
that presentation, and the exact row-zero identification used by the final
width argument.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredAlignedQGeometry

open ConfiguredGaugeFirstPhysicalSequence
  ConfiguredCanonicalPairSource

variable {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
  {kh C K : ℝ} {d : ℕ → ℝ}

variable (O : ConfiguredCanonicalPairSource.Output D Q kh C K d)
  (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
    ev (Q n) = TwoCapPairsAssembly.front
      (D.kappas n) D.model.thetaBase (D.Hs n))

abbrev aligned (n : ℕ) : Data :=
  ConfiguredGaugeFirstPhysicalSequence.alignedQ O.input hQ n

/-- The aligned front is literally the phase-shifted configured front followed
by the stored rigid motion. -/
theorem curve_eq (n : ℕ) (u : ℝ) :
    (aligned O hQ n).1 u =
      (presentations (S := O.input) (hQ := hQ) n).translation +
        (presentations (S := O.input) (hQ := hQ) n).rotation *
          (Q n).1
            (u + (presentations (S := O.input) (hQ := hQ) n).phase) := by
  rfl

/-- Phase and rigid transport preserve the configured perimeter. -/
theorem perim_eq (n : ℕ) : perim (aligned O hQ n) = 2 * D.Hs n := by
  let A := presentations (S := O.input) (hQ := hQ) n
  unfold aligned ConfiguredGaugeFirstPhysicalSequence.alignedQ
    ConfiguredGaugeFirstPhysicalSequence.Presentation.data
    RichStageDataPhaseRigidTransport.move
  change ‖A.rotation * (Q n).2.1 (0 + A.phase)‖ = 2 * D.Hs n
  rw [zero_add, norm_mul, A.rotation_norm, one_mul,
    (O.input.front_tube n).speed_const A.phase 0]
  simpa [perim] using (hQ n).1

/-- The full strict model margin from the inductive budget is invariant under
the stored phase and rigid presentation. -/
theorem strict_model_tube (n : ℕ) :
    IsTubeMember
      (commonC D + PullbackTubeTailBudget.radius C K d n) 0
      (ConfiguredInductiveTubeBudget.chordBase D.model)
      (aligned O hQ n) := by
  unfold aligned ConfiguredGaugeFirstPhysicalSequence.alignedQ
    ConfiguredGaugeFirstPhysicalSequence.Presentation.data
    RichStageDataPhaseRigidTransport.move
  exact MarkedRigid.isTubeMember_rigidData
    (presentations (S := O.input) (hQ := hQ) n).rotation_norm
    (MarkedShift.isTubeMember_shiftData (O.budget.model_mem n)
      (presentations (S := O.input) (hQ := hQ) n).phase)

/-- The normalized acceleration norm is unchanged by phase and rigid motion,
so the configured model acceleration ceiling applies verbatim. -/
theorem acceleration_le (n : ℕ) (u : ℝ) :
    ‖(aligned O hQ n).2.2 u‖ ≤
      ConfiguredInductiveTubeBudget.accBound D.model n := by
  let A := presentations (S := O.input) (hQ := hQ) n
  change ‖A.rotation * (Q n).2.2 (u + A.phase)‖ ≤ _
  rw [norm_mul, A.rotation_norm, one_mul]
  exact O.budget.model_acc n (u + A.phase)

/-- Every aligned configured front has bounded position range. -/
theorem bounded_range (n : ℕ) :
    Bornology.IsBounded (range (⇑(aligned O hQ n).1)) := by
  have htube := alignedQ_tube O.input hQ n
  exact CurveDistance.isBounded_range_of_periodic
    (continuous_iff_continuousAt.2 fun u =>
      (htube.hasDerivAt_curve u).continuousAt)
    htube.periodic one_pos

/-- The physical length of an aligned configured front is exactly its marked
perimeter, hence exactly `2 H_n`. -/
theorem totalLength_eq (n : ℕ) :
    MarkedReparam.totalLength (fun u => (aligned O hQ n).2.1 u) =
      2 * D.Hs n := by
  rw [VariableMarkedPhysicalLength.totalLength_eq_perim_of_tube
    (alignedQ_tube O.input hQ n), perim_eq O hQ n]

/-- The recursive presentation starts with the identity motion and zero phase.
-/
theorem aligned_zero : aligned O hQ 0 = Q 0 := by
  simp [aligned, ConfiguredGaugeFirstPhysicalSequence.alignedQ,
    ConfiguredGaugeFirstPhysicalSequence.presentations,
    ConfiguredGaugeFirstPhysicalSequence.initial,
    ConfiguredGaugeFirstPhysicalSequence.Presentation.data,
    RichStageDataPhaseRigidTransport.move]

/-- At row zero the aligned position range is exactly the configured model
front range. -/
theorem range_zero_eq_model :
    range (⇑(aligned O hQ 0).1) =
      range (TwoCapPairsAssembly.front
        (D.kappas 0) D.model.thetaBase (D.Hs 0)) := by
  rw [aligned_zero O hQ]
  calc
    range (⇑(Q 0).1) = range (ev (Q 0)) :=
      (MarkedSpace.range_ev_of_perim_ne_zero (by
        rw [(hQ 0).1]
        exact ne_of_gt (mul_pos (by norm_num) D.separation_zero_pos))).symm
    _ = range (TwoCapPairsAssembly.front
        (D.kappas 0) D.model.thetaBase (D.Hs 0)) :=
      congrArg range (hQ 0).2

/-- Consequently every row-zero model width estimate transfers without a
change of direction. -/
theorem width_zero_eq_model (e : ℂ) :
    Width.width (range (⇑(aligned O hQ 0).1)) e =
      Width.width (range (TwoCapPairsAssembly.front
        (D.kappas 0) D.model.thetaBase (D.Hs 0))) e := by
  rw [range_zero_eq_model O hQ]

end ConfiguredAlignedQGeometry
