import UnitTangentIterates.ConfiguredGaugeFirstPhysicalSequence
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricRowCanonicalEndpointCap
import UnitTangentIterates.ConfiguredCorrelatedBaseColumnCap
import UnitTangentIterates.ConfiguredRowCeilingPolynomialEnvelopes
import UnitTangentIterates.ConfiguredMarkingAwareMergedEndpointGrowth
import UnitTangentIterates.ConfiguredRecursiveEdgeWeightedEffectiveError
import UnitTangentIterates.ConstructedRowDefectLargeSeparation

/-!
# The configured models form a summable selected-inverse pseudo-orbit

The gauge-first interpolation ends at its actual nonaffinely marked rear.
The retained physical terminal is nevertheless the literal canonical selected
inverse of the next aligned model.  The marking correction is therefore used
only in the metric comparison; it is never promoted to a recursive source.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredSelectedInversePseudoOrbit

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredApproximateDefectPathRowwise
  ConfiguredApproximateDefectPathRowwiseCost
  ConfiguredCorrelatedBaseColumnCap
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredMarkingAwareMergedEndpointGrowth
  ConfiguredRecursiveEdgeWeightedEffectiveError
  ConfiguredRowCeilingPolynomialEnvelopes
  ConstructedRowCPolynomialGrowth
  ConstructedRowDefectLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareGeometricRowCanonicalEndpointCap
  NormalPathC2IncrementVariableSpeed
  RichStageDataPhaseRigidTransport

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → Data} {kh c dlt : ℝ}

/-- The exact rowwise metric conversion: variable-speed path comparison plus
the nonaffine terminal marking correction. -/
def pathConversion (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  c2ConstVar (rowP0 D n) (rowP1 D n) D.kstar (rowG1 D n) (rowCg D n)

def pseudoOrbitConversion
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n : ℕ) : ℝ :=
  pathConversion D n + baseEndpointConversion D M n

def metricDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n : ℕ) : ℝ :=
  pseudoOrbitConversion D M n * rowDefect D n

theorem pathConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ pathConversion D n :=
  c2ConstVar_nonneg _ _ _ _ _

theorem baseEndpointConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n : ℕ) :
    0 ≤ baseEndpointConversion D M n := by
  unfold baseEndpointConversion
  have hk : 0 ≤ baseKappa D := by
    unfold baseKappa
    exact mul_nonneg (by norm_num) D.kstar_nonneg
  have hfirst : 0 ≤ baseFirstCoeff D M n := by
    unfold baseFirstCoeff
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (D.model.separation_pos n).le) hk)
      (by positivity)
  exact (mul_nonneg (by norm_num) hfirst).trans (le_max_left _ _)

theorem pseudoOrbitConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n : ℕ) :
    0 ≤ pseudoOrbitConversion D M n :=
  add_nonneg (pathConversion_nonnegative D n)
    (baseEndpointConversion_nonnegative D M n)

theorem metricDefect_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n : ℕ) :
    0 ≤ metricDefect D M n :=
  mul_nonneg (pseudoOrbitConversion_nonnegative D M n)
    (ConfiguredRowDefectProvider.rowDefect_nonneg D n)

/-- The retained physical terminal is the canonical selected inverse as
complete marked data.  This is stronger than the range identity used by the
older finite-column route. -/
theorem richTerminal_eq_selInv
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) (n : ℕ) :
    (richStage S hQ 1 C n).terminalBase =
      SelectedInverseMap.selInv kh (alignedQ S hQ (n + 1)) := by
  let A := presentations (S := S) (hQ := hQ) n
  let r := rearPhase S hQ A
  obtain ⟨K⟩ := physicalStep S A r
  have hnext : alignedQ S hQ (n + 1) = (next S A r).data := by
    simp [alignedQ, presentations, A, r, rearPhase]
  have hrear : IsTubeMember (S.carrier n).c 0 (S.carrier n).dlt
      (move A.translation A.rotation r (S.carrier n).data) :=
    MarkedRigid.isTubeMember_rigidData A.rotation_norm
      (MarkedShift.isTubeMember_shiftData (S.carrier n).tube r)
  rw [(richStage_spec S hQ 1 C n).1, hnext]
  exact rear_eq_selInv_of_physicalKinematics S.kh_nonneg S.kh_lt_one K
    S.c_pos (by simpa [hnext] using alignedQ_tube S hQ (n + 1)) hrear

/-- The actual gauge endpoint differs from the canonical physical terminal by
only the explicit reanchored marking modulus. -/
theorem movedRear_dist_richTerminal_le
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) (n : ℕ) :
    dist (movedRear S hQ n) (richStage S hQ 1 C n).terminalBase ≤
      baseTransportMarkingBound D n := by
  let A := presentations (S := S) (hQ := hQ) n
  let W := output S hQ n
  have H := W.transported_endpoint_dist A.phase A.translation A.rotation
    A.rotation_norm
  rw [(richStage_spec S hQ 1 C n).1]
  rw [← terminalBase_eq_physicalRear S hQ n]
  simpa [movedRear, move, A, W] using H

/-- One configured interpolation edge is a genuine metric pseudo-orbit step
for the global selected inverse.  The recosted/remarked physical curve occurs
only as the middle point in the triangle inequality. -/
theorem dist_aligned_selInv_le_metricDefect
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {M : ℝ}
    (hH0 : 1 ≤ D.Hs 0) (hM : ∀ n, rowDefect D n ≤ M) (n : ℕ) :
    dist (alignedQ S hQ n)
        (SelectedInverseMap.selInv kh (alignedQ S hQ (n + 1))) ≤
      metricDefect D M n := by
  let R := richStage S hQ 1 C n
  let Cp := pathConversion D n
  have hpath : dist (alignedQ S hQ n) (movedRear S hQ n) ≤
      Cp * PathMetric.NormalPath.cost R.stage.increment := by
    exact dist_le_cost_variableSpeed R.stage.increment
      (alignedQ_tube S hQ n).hasDerivAt_curve R.stage.rear_curve_deriv
      (alignedQ_tube S hQ n).hasDerivAt_vel R.stage.rear_vel_deriv
      R.stage.increment_geometry
  have hcost : PathMetric.NormalPath.cost R.stage.increment ≤ rowDefect D n := by
    simpa [R, ConfiguredRowDefectProvider.error,
      PathMetric.WeightedRecursiveDefect.pullbackError] using
        R.stage.increment_cost
  have hend : dist (movedRear S hQ n)
      (SelectedInverseMap.selInv kh (alignedQ S hQ (n + 1))) ≤
        baseEndpointConversion D M n * rowDefect D n := by
    rw [← richTerminal_eq_selInv S hQ C n]
    exact (movedRear_dist_richTerminal_le S hQ C n).trans
      (baseTransportMarkingBound_le D hH0 hM n)
  calc
    dist (alignedQ S hQ n)
        (SelectedInverseMap.selInv kh (alignedQ S hQ (n + 1))) ≤
        dist (alignedQ S hQ n) (movedRear S hQ n) +
          dist (movedRear S hQ n)
            (SelectedInverseMap.selInv kh (alignedQ S hQ (n + 1))) :=
      dist_triangle _ _ _
    _ ≤ Cp * rowDefect D n +
        baseEndpointConversion D M n * rowDefect D n :=
      add_le_add (hpath.trans (mul_le_mul_of_nonneg_left hcost
        (pathConversion_nonnegative D n))) hend
    _ = metricDefect D M n := by
      simp [metricDefect, pseudoOrbitConversion, Cp]
      ring

theorem exists_pathConversion_growth_majorant
    (D : ConstructedConfiguredSequenceWeighted.Data) {gamma : ℝ}
    (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      pathConversion D n ≤
        C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  simpa [pathConversion] using
    (exists_c2ConstVar_growth_majorant (pmin := pmin D)
      (fun n ↦ (D.model.separation_pos n).le) (pmin_pos D)
      (rowP0_lower D) (rowP1Envelope D) (rowKstarEnvelope D)
      (rowG1Envelope D) (rowCgEnvelope D) hgamma)

/-- The complete configured metric defect is summable.  Polynomial growth of
the path and marking conversions consumes only half of the exponential decay
already available in `rowDefect`. -/
theorem metricDefect_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) {M : ℝ} (hM : 0 ≤ M) :
    Summable (metricDefect D M) := by
  let gamma : ℝ := D.model.beta / 16
  let absorb : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 4
  let finalRate : ℝ := D.model.beta / 8
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  have hgamma : 0 < gamma := div_pos hbeta (by norm_num)
  have habsorb : 0 < absorb := div_pos hbeta (by norm_num)
  have hb : 0 < b := div_pos hbeta (by norm_num)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_pathConversion_growth_majorant D hgamma
  obtain ⟨Ce, hCe0, hCe⟩ :=
    exists_baseEndpointConversion_growth_majorant D hM hgamma
  let C0 := Cp + Ce
  have hC0 : 0 ≤ C0 := add_nonneg hCp0 hCe0
  have hCgrowth : ∀ n, pseudoOrbitConversion D M n ≤
      C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
    intro n
    dsimp [pseudoOrbitConversion, C0]
    nlinarith [hCp n, hCe n,
      mul_nonneg (pow_nonneg (by linarith [(D.model.separation_pos n).le]) 2)
        (Real.exp_pos (gamma * D.Hs n)).le]
  let A := rowDefectExpConst D
  have hA : 0 ≤ A := rowDefectExpConst_nonneg D
  have hdecay : ∀ n, rowDefect D n ≤
      A * Real.exp (-(b * D.Hs n)) := by
    intro n
    simpa [A, b] using rowDefect_le_exp D n
  obtain ⟨E, hE0, hE⟩ := exists_one_add_pow_le_exp 2 habsorb
  have hmajor : Summable (fun n : ℕ ↦
      (C0 * E * A) * Real.exp (-(finalRate * D.Hs n))) := by
    exact (ModelDefectSummable.summable_exp_neg_of_growth
      (by dsimp [finalRate]; positivity) D.deltaStep_pos
      D.separation_linear).mul_left (C0 * E * A)
  apply Summable.of_nonneg_of_le (metricDefect_nonnegative D M) (fun n ↦ ?_) hmajor
  have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
  have hpoly := hE (D.Hs n) hH
  have hmul := mul_le_mul (hCgrowth n) (hdecay n)
    (ConfiguredRowDefectProvider.rowDefect_nonneg D n)
    (mul_nonneg
      (mul_nonneg hC0 (pow_nonneg (by linarith) 2))
      (Real.exp_pos _).le)
  calc
    metricDefect D M n ≤
        (C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) *
          (A * Real.exp (-(b * D.Hs n))) := hmul
    _ ≤ (C0 * (E * Real.exp (absorb * D.Hs n)) *
          Real.exp (gamma * D.Hs n)) *
          (A * Real.exp (-(b * D.Hs n))) := by
      gcongr
    _ = (C0 * E * A) *
          (Real.exp (absorb * D.Hs n) * Real.exp (gamma * D.Hs n) *
            Real.exp (-(b * D.Hs n))) := by ring
    _ = (C0 * E * A) * Real.exp (-(finalRate * D.Hs n)) := by
      congr 1
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [gamma, absorb, b, finalRate]
      ring

end ConfiguredSelectedInversePseudoOrbit
