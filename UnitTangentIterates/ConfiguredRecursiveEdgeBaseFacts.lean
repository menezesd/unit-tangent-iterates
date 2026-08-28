import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0ScalarStart
import UnitTangentIterates.TwoCapMarked
import UnitTangentIterates.ClosingArgument

/-!
# Paper-facing base facts for the edge-shifted recursion

The coherent edge recursion starts with the configured physical model at
index `1`.  This module records that model with its actual indexing and proves
the geometric facts used at the sliced capstone boundary: exact period and
turning data, ovality, and noncircularity.
-/

noncomputable section

open Set Function MarkedSpace

namespace ConfiguredRecursiveEdgeBaseFacts

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0Growth
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation

variable {MA NA : ℝ}

abbrev Output := ConfiguredRecursiveEdgeSourceP0ScalarStart.Output

/-- The configured data after the scalar construction discards its finite
prefix. -/
abbrev data (O : Output MA NA) : ConstructedConfiguredSequenceWeighted.Data :=
  shift O.E.data O.large.N

/-- The first physical model used by the successor-edge recursion. -/
def baseCurve (O : Output MA NA) : ℝ → ℂ :=
  TwoCapPairsAssembly.front ((data O).kappas 1)
    (data O).model.thetaBase ((data O).Hs 1)

/-- Its arclength period. -/
def basePeriod (O : Output MA NA) : ℝ := 2 * (data O).Hs 1

/-- Its canonical tangent angle. -/
def baseAngle (O : Output MA NA) : ℝ → ℝ :=
  TwoCapPairsAssembly.frontAngle ((data O).kappas 1)
    (data O).model.thetaBase

/-- Its prescribed curvature. -/
def baseCurvature (O : Output MA NA) : ℝ → ℝ := (data O).kappas 1

@[simp] theorem baseCurve_eq_ev (O : Output MA NA) :
    baseCurve O = ev (O.Q 1) := by
  exact (O.model_data 1).2.symm

@[simp] theorem basePeriod_eq_perim (O : Output MA NA) :
    basePeriod O = perim (O.Q 1) := by
  exact (O.model_data 1).1.symm

theorem basePeriod_pos (O : Output MA NA) : 0 < basePeriod O := by
  exact mul_pos (by norm_num) ((data O).model.separation_pos 1)

theorem baseCurvature_continuous (O : Output MA NA) :
    Continuous (baseCurvature O) :=
  (data O).model.curvature_continuous 1

theorem baseCurvature_periodic (O : Output MA NA) :
    Periodic (baseCurvature O) ((data O).Hs 1) :=
  (data O).model.curvature_periodic 1

theorem baseCurvature_pos (O : Output MA NA) (s : ℝ) :
    0 < baseCurvature O s :=
  (data O).model_curvature_pos 1 s

/-- The curvature turns through `π` on its configured half-period. -/
theorem base_half_turning (O : Output MA NA) :
    (∫ s in (0 : ℝ)..(data O).Hs 1, baseCurvature O s) = Real.pi :=
  (data O).model.total_turning 1

theorem baseCurve_periodic (O : Output MA NA) :
    Periodic (baseCurve O) (basePeriod O) := by
  exact TwoCapPairsAssembly.front_periodic
    (baseCurvature_continuous O) (baseCurvature_periodic O)
    (base_half_turning O)

theorem baseCurve_hasDerivAt (O : Output MA NA) (s : ℝ) :
    HasDerivAt (baseCurve O)
      (Complex.exp (Complex.I * (baseAngle O s : ℂ))) s := by
  exact TwoCapPairsAssembly.front_hasDerivAt
    (theta0 := (data O).model.thetaBase) (H := (data O).Hs 1)
    (baseCurvature_continuous O) s

theorem baseAngle_hasDerivAt (O : Output MA NA) (s : ℝ) :
    HasDerivAt (baseAngle O) (baseCurvature O s) s := by
  exact CurvatureInterpolation.hasDerivAt_tangentAngle
    (θ₀ := (data O).model.thetaBase) (baseCurvature_continuous O) s

/-- The tangent angle makes one complete positive turn over the physical
period. -/
theorem baseAngle_add_period (O : Output MA NA) (s : ℝ) :
    baseAngle O (s + basePeriod O) =
      baseAngle O s + 2 * Real.pi := by
  exact TwoCapMarked.frontAngle_add_period
    (baseCurvature_continuous O) (baseCurvature_periodic O)
    (base_half_turning O) s

theorem baseAngle_strictMono (O : Output MA NA) :
    StrictMono (baseAngle O) := by
  refine strictMono_of_deriv_pos fun s => ?_
  rw [(baseAngle_hasDerivAt O s).deriv]
  exact baseCurvature_pos O s

theorem baseCurve_injOn (O : Output MA NA) :
    InjOn (baseCurve O) (Ico 0 (basePeriod O)) := by
  have hAngleContinuous : Continuous (baseAngle O) :=
    continuous_iff_continuousAt.2 fun s =>
      (baseAngle_hasDerivAt O s).differentiableAt.continuousAt
  have h := ConvexEmbedded.injOn_Ico_of_turning_one
    (v := fun _ => (1 : ℝ))
    (fun s => by simpa using baseCurve_hasDerivAt O s)
    (fun _ => one_pos) hAngleContinuous (baseAngle_strictMono O)
    (baseAngle_add_period O) (baseCurve_periodic O) 0
  simpa using h

/-- The configured stage-`1` physical base is an oval, with its displayed
tangent angle and curvature as witnesses. -/
theorem base_isOval (O : Output MA NA) :
    MainTheoremConditional.IsOval (ev (O.Q 1)) := by
  rw [← baseCurve_eq_ev O]
  exact ⟨basePeriod O, basePeriod_pos O, baseCurve_periodic O,
    baseCurve_injOn O, baseAngle O, baseCurve_hasDerivAt O,
    baseCurvature O, baseAngle_hasDerivAt O, baseCurvature_pos O⟩

private def baseRadius (O : Output MA NA) : ℝ :=
  rowRadius
    (shiftSequence
      (edgeCombinedConversion O.E.data MA NA (analyticKhat O.E.data)
        sourceKh O.Mend) O.large.N)
    (shiftSequence (edgePhysicalDefect O.E.data) O.large.N) 0

private theorem baseRadius_nonneg (O : Output MA NA) : 0 ≤ baseRadius O := by
  unfold baseRadius rowRadius
  exact mul_nonneg
    (edgeCombinedConversion_nonnegative O.E.data sourceKh_nonnegative
      sourceKh_lt_one (O.large.N + 0))
    (ShadowingTails.tail_nonneg
      (fun k => edgePhysicalDefect_nonnegative O.E.data
        (O.large.N + (0 + k))) 0)

private theorem base_width_le (O : Output MA NA) :
    Width.width (range (baseCurve O)) (O.direction (O.large.N + 1)) ≤ O.Cw := by
  simpa [baseCurve, data, shift, Nat.add_assoc] using
    O.model_width (O.large.N + 1)

private theorem base_width_gap (O : Output MA NA) :
    O.Cw < basePeriod O / Real.pi := by
  have hr : 0 ≤ baseRadius O := baseRadius_nonneg O
  have hgap : O.Cw + 2 * baseRadius O <
      (2 * (data O).Hs 0 - baseRadius O) / Real.pi := by
    simpa [baseRadius, data] using O.large.width_gap
  have hdrop : (2 * (data O).Hs 0 - baseRadius O) / Real.pi ≤
      (2 * (data O).Hs 0) / Real.pi := by
    apply (div_le_div_iff_of_pos_right Real.pi_pos).2
    linarith
  have h0 : O.Cw < (2 * (data O).Hs 0) / Real.pi :=
    lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg (by norm_num) hr))
      (hgap.trans_le hdrop)
  have h01 : (data O).Hs 0 ≤ (data O).Hs 1 :=
    (data O).separation_lower 1
  have hmono : (2 * (data O).Hs 0) / Real.pi ≤
      basePeriod O / Real.pi := by
    apply (div_le_div_iff_of_pos_right Real.pi_pos).2
    dsimp [basePeriod]
    linarith
  exact h0.trans_le hmono

/-- The configured stage-`1` physical base is not a circle of its own
perimeter.  The conclusion is stated on its actual marked curve. -/
theorem base_not_circle (O : Output MA NA) :
    ¬ ClosingArgument.IsCircleOfPerimeter
      (range (ev (O.Q 1))) (perim (O.Q 1)) := by
  rw [← baseCurve_eq_ev O, ← basePeriod_eq_perim O]
  exact ClosingArgument.not_isCircleOfPerimeter_of_width_lt
    (O.direction_unit (O.large.N + 1))
    ((base_width_le O).trans_lt (base_width_gap O))

/-- Single paper-facing package consumed by the edge-sliced capstone. -/
structure Facts (O : Output MA NA) : Prop where
  perim_eq : perim (O.Q 1) = basePeriod O
  period_pos : 0 < basePeriod O
  periodic : Periodic (ev (O.Q 1)) (basePeriod O)
  half_turning :
    (∫ s in (0 : ℝ)..(data O).Hs 1, baseCurvature O s) = Real.pi
  full_turning : ∀ s, baseAngle O (s + basePeriod O) =
    baseAngle O s + 2 * Real.pi
  oval : MainTheoremConditional.IsOval (ev (O.Q 1))
  not_circle : ¬ ClosingArgument.IsCircleOfPerimeter
    (range (ev (O.Q 1))) (perim (O.Q 1))

def facts (O : Output MA NA) : Facts O where
  perim_eq := (basePeriod_eq_perim O).symm
  period_pos := basePeriod_pos O
  periodic := by simpa [baseCurve_eq_ev O] using baseCurve_periodic O
  half_turning := base_half_turning O
  full_turning := baseAngle_add_period O
  oval := base_isOval O
  not_circle := base_not_circle O

end ConfiguredRecursiveEdgeBaseFacts
