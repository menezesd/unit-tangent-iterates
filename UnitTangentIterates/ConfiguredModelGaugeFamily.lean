import Mathlib
import UnitTangentIterates.ModelGaugeControlledFamilyChooser
import UnitTangentIterates.ModelOrbitDefectMarked
import UnitTangentIterates.ModelDefectSummable
import UnitTangentIterates.UnconditionalAssemblyRemainder
import UnitTangentIterates.ControlledJunctionTailLimit
import UnitTangentIterates.FrontFrenetTubeCompatibility

noncomputable section

open Set Function Topology MarkedSpace MainTheoremConditional

namespace PathMetric

structure PhysicalRearLimitReconstructionFamily (Q : ℕ → ℕ → Data) : Prop where
  reconstruct : ∀ (X : ℕ → Data),
    (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) → ∀ n,
    ∃ (kap P theta0 : ℝ)
      (d : NormalizedSelectedRearClosure.SteeringData kap) (sf : ℝ → ℝ),
      0 ≤ kap ∧ kap < 1 ∧ 0 < P ∧ Continuous d.K ∧
      (∃ D : RearArclengthInverseBridge.Data
          (NormalizedSteeringPhysicalRescaling.deltaPhys d P) sf P,
        (∀ s, HasDerivAt (ev (X (n + 1)))
          (Complex.exp (Complex.I *
            (NormalizedSteeringPhysicalRescaling.thetaPhys d P theta0 s : ℂ))) s) ∧
        (∀ x, ev (X n) x = RearTrack.rearTrack (ev (X (n + 1)))
          (NormalizedSteeringPhysicalRescaling.thetaPhys d P theta0)
          (NormalizedSteeringPhysicalRescaling.deltaPhys d P) (sf x)) ∧
        perim (X n) = D.rearPeriod ∧
        (∀ x, 0 ≤ SelectedRearFrenetChain.rearK d P sf x) ∧
        (∃ x, SelectedRearFrenetChain.rearK d P sf x ≠ 0))

def PhysicalRearLimitReconstructionFamily.limitStrictness
    {Q : ℕ → ℕ → Data} {c dlt : ℝ}
    (F : PhysicalRearLimitReconstructionFamily Q) (hc : 0 < c)
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k)) :
    ∀ (X : ℕ → Data), (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) →
      ∀ n, UnconditionalAssembly.LimitStrictnessData (X n) := by
  intro X hX n
  have hne : Nonempty (UnconditionalAssembly.LimitStrictnessData (X n)) := by
    obtain ⟨kap, P, theta0, d, sf, hkap0, hkap1, hP, hK, D,
      hfront, hrear, hper, hk0, hkne⟩ := F.reconstruct X hX n
    have hp : IsTubeMember c 0 dlt (X (n + 1)) :=
      (MarkedSpace.isClosed_tube c 0 dlt).mem_of_tendsto
        (hX (n + 1)) (Filter.Eventually.of_forall (htube (n + 1)))
    let C := SelectedRearFrenetChain.rearFrenetCore_of_physicalRear d
      hkap0 hkap1 hP hK D hfront hrear hper hk0 hkne
    exact ⟨FrontFrenetTubeCompatibility.limitStrictness_of_rearCore_and_successor_tube
      d sf C hp hc hkap0 hkap1 hK hfront rfl rfl⟩
  exact hne.some

/-- The exact physical rear reconstruction already carries the realized
unit-tangent range orbit; no positive-curvature selected-inverse theorem is
needed. -/
theorem PhysicalRearLimitReconstructionFamily.rangeOrbit
    {Q : ℕ → ℕ → Data} (F : PhysicalRearLimitReconstructionFamily Q)
    (X : ℕ → Data)
    (hX : ∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) :
    ∀ n, range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n))) := by
  intro n
  obtain ⟨kap, P, theta0, d, sf, hkap0, hkap1, hP, hK, D,
    hfront, hrear, hper, hk0, hkne⟩ := F.reconstruct X hX n
  let C := SelectedRearFrenetChain.rearFrenetCore_of_physicalRear d
    hkap0 hkap1 hP hK D hfront hrear hper hk0 hkne
  have hpoint : ∀ x, UnitTangent.unitTangentMap (ev (X n)) x =
      ev (X (n + 1)) (sf x) := by
    intro x
    rw [UnitTangent.unitTangentMap, (C.curve_deriv x).deriv, hrear x]
    exact RearTrack.unitTangentMap_rearTrack (F := ev (X (n + 1)))
      (Θ := NormalizedSteeringPhysicalRescaling.thetaPhys d P theta0)
      (δ := NormalizedSteeringPhysicalRescaling.deltaPhys d P) (sf x)
  have hsfsurj : Surjective sf := by
    intro s
    exact ⟨RearTrack.rearArclength
      (NormalizedSteeringPhysicalRescaling.deltaPhys d P) s, D.leftInverse s⟩
  apply Set.Subset.antisymm
  · rintro z ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := hsfsurj s
    exact ⟨x, hpoint x⟩
  · rintro z ⟨x, rfl⟩
    exact ⟨sf x, (hpoint x).symm⟩

/-- Pointwise representative identification plus the concrete physical rear
family supplies all representative closing fields at once. -/
theorem PhysicalRearLimitReconstructionFamily.representativeClosing
    {Q : ℕ → ℕ → Data} {R : ℕ → ℝ → ℂ}
    (F : PhysicalRearLimitReconstructionFamily Q)
    (hpoint : ∀ (X : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) →
      ∀ n, ev (X n) = R n)
    (X : ℕ → Data)
    (hX : ∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) :
    (∀ (Z : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (Z n))) →
      ∀ n, range (ev (Z n)) = range (R n)) ∧
    (∀ (Z : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (Z n))) → ∀ n,
      range (UnitTangent.unitTangentMap (ev (Z n))) =
        range (UnitTangent.unitTangentMap (R n))) ∧
    (∀ n, range (R (n + 1)) =
      range (UnitTangent.unitTangentMap (R n))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ n
    rw [hpoint Z hZ n]
  · intro Z hZ n
    rw [hpoint Z hZ n]
  · intro n
    rw [← hpoint X hX (n + 1), ← hpoint X hX n]
    exact F.rangeOrbit X hX n

/-- Pointwise identification of the marked limits with a fixed representative
family automatically supplies both range transports.  A single realized
limit orbit then transfers its unit-tangent range orbit to the fixed
representatives, eliminating the three separate closing hypotheses. -/
theorem representative_closing_of_pointwise_limit_orbit
    {Q : ℕ → ℕ → Data} {R : ℕ → ℝ → ℂ}
    (hpoint : ∀ (X : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) →
      ∀ n, ev (X n) = R n)
    (X : ℕ → Data)
    (hX : ∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n)))
    (horbit : ∀ n, range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n)))) :
    (∀ (Z : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (Z n))) →
      ∀ n, range (ev (Z n)) = range (R n)) ∧
    (∀ (Z : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (Z n))) → ∀ n,
      range (UnitTangent.unitTangentMap (ev (Z n))) =
        range (UnitTangent.unitTangentMap (R n))) ∧
    (∀ n, range (R (n + 1)) =
      range (UnitTangent.unitTangentMap (R n))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ n
    rw [hpoint Z hZ n]
  · intro Z hZ n
    rw [hpoint Z hZ n]
  · intro n
    rw [← hpoint X hX (n + 1), ← hpoint X hX n]
    exact horbit n

/-- Summability is preserved by the paper's diagonal pullback shift `n+k`. -/
theorem summable_modelDefect_shift {d : ℕ → ℝ} (hd : Summable d) (n : ℕ) :
    Summable (fun k => d (n + k)) := by
  simpa [Nat.add_comm] using (summable_nat_add_iff (f := d) n).mpr hd

/-- Recursive interpolation/gauge outputs dominated by one model-orbit defect
sequence.  `ModelOrbitDefectMarked.summable_markedDefect` and
`ModelDefectSummable.summable_model_defect` are the two canonical producers of
the `defect_summable` field. -/
structure ConfiguredModelRecursiveOutputs
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    (Q : ℕ → ℕ → Data) (P0 P1 khat G1 Cg M N C0 : ℝ) where
  stages : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg
  junction : ∀ n k, ReparamJunctionCertificate
    (p' := Q n k) (q' := Q n (k + 1)) (stages.stage n k).path
  junctionC2 : ∀ n k, ReparamC2Certificate (stages.stage n k).path
    (stages.stage n k).c2 (junction n k)
  junction_M : ∀ n k, (junction n k).M = M
  junction_N : ∀ n k, (junction n k).N = N
  reparam_cost : ∀ n k,
    reparamCostConst (junction n k).m (junction n k).M (junction n k).N ≤ C0
  defect : ℕ → ℝ
  defect_nonneg : ∀ j, 0 ≤ defect j
  defect_summable : Summable defect
  stage_nonneg : ∀ n k, 0 ≤
    (if stages.useInterpolation n k then stages.interpolationError n k
      else stages.gaugeError n k)
  stage_le_modelDefect : ∀ n k,
    (if stages.useInterpolation n k then stages.interpolationError n k
      else stages.gaugeError n k) ≤ defect (n + k)

/-- Paper-indexed gauge family from configured-model matching defects.  The
error at orbit level `n`, pullback stage `k`, is exactly `C0*d(n+k)` after the
endpoint reparameterization cost. -/
def ConfiguredModelRecursiveOutputs.toGaugeControlledFamily
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    {model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps}
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg M N C0 : ℝ}
    (O : ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg M N C0)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hC0 : 0 ≤ C0) :
    GaugeControlledFamily Q P0 (P1 * M) khat
      (G1 * M ^ 2 + P1 * N) (Cg * M ^ 2 + khat * P1 * N) :=
  GaugeControlledFamily.ofModelRecursiveOutputs O.stages O.junction O.junctionC2
    O.junction_M O.junction_N hP0 hP1 hkhat hG1 hCg hM hN
    (fun n k => O.defect (n + k)) hC0 O.reparam_cost
    (fun n k => O.defect_nonneg (n + k))
    (fun n => summable_modelDefect_shift O.defect_summable n)
    O.stage_nonneg O.stage_le_modelDefect

/-- Existence form used by the paper-facing assembly.  All analytic
summability bookkeeping is discharged by the configured matching-defect
package; the remaining data are the concrete interpolation/gauge outputs and
their endpoint correspondence certificates. -/
theorem exists_gaugeControlledFamily_of_configuredModel
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg M N C0 : ℝ}
    (O : ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg M N C0)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hC0 : 0 ≤ C0) :
    ∃ G : GaugeControlledFamily Q P0 (P1 * M) khat
      (G1 * M ^ 2 + P1 * N) (Cg * M ^ 2 + khat * P1 * N),
      G.error = fun n k => C0 * O.defect (n + k) := by
  refine ⟨O.toGaugeControlledFamily hP0 hP1 hkhat hG1 hCg hM hN hC0, rfl⟩

/-- A gauge-controlled family with summable variable-speed stages has a
simultaneously chosen marked limit at every orbit level.  This is the limit
witness needed to transfer the concrete physical rear orbit to a fixed
representative family; it is constructed from the controlled family rather
than exposed as an additional capstone hypothesis. -/
theorem GaugeControlledFamily.exists_limit_family
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg c kmin dlt : ℝ}
    (G : GaugeControlledFamily Q P0 P1 khat G1 Cg)
    (hconst : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (htube : ∀ n k, IsTubeMember c kmin dlt (Q n k)) :
    ∃ X : ℕ → Data,
      ∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n)) := by
  have hex : ∀ n, ∃ X : Data,
      Filter.Tendsto (Q n) Filter.atTop (nhds X) := by
    intro n
    obtain ⟨X, hX, hrest⟩ := exists_limit_of_summable_controlledJunctions
      (G.sequence n) (G.error_nonneg n) (G.error_summable n)
      (G.path_cost n) hconst
      (controlledJunction_distances_variableSpeed
        (G.sequence n) (htube n) (G.variableSpeed n))
      (htube n)
      (fun Y hY => (MarkedSpace.isClosed_tube c kmin dlt).mem_of_tendsto hY
        (Filter.Eventually.of_forall (htube n)))
    exact ⟨X, hX⟩
  refine ⟨fun n => Classical.choose (hex n), ?_⟩
  intro n
  exact Classical.choose_spec (hex n)

/-- Single paper-facing assembly from configured recursive interpolation/gauge
outputs.  The controlled family, shifted summable tail, initial closeness, and
perimeter lower estimate are all constructed internally. -/
theorem paper_main_theorem_of_configuredModelRecursiveOutputs
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {R : ℕ → ℝ → ℂ}
    {P0 P1 khat G1 Cg M N C0 c dlt Cw : ℝ}
    (O : ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg M N C0)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hC0 : 0 ≤ C0) (hc : 0 < c) (hdlt : 0 < dlt)
    (hmetric : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
        (Cg * M ^ 2 + khat * P1 * N))
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k))
    (hstrict : ∀ (X : ℕ → Data), (∀ n, Filter.Tendsto (Q n) Filter.atTop (𝓝 (X n))) →
      ∀ n, UnconditionalAssembly.LimitStrictnessData (X n))
    (hrepresentative : ∀ (X : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (𝓝 (X n))) →
      ∀ n, range (ev (X n)) = range (R n))
    (htangentRepresentative : ∀ (X : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (𝓝 (X n))) → ∀ n,
      range (UnitTangent.unitTangentMap (ev (X n))) =
        range (UnitTangent.unitTangentMap (R n)))
    (hRorbit : ∀ n,
      range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n)))
    (hmodel : ev (Q 0 0) =
      TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
    (hmodelPerim : perim (Q 0 0) = 2 * Hs 0)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))) Complex.I ≤ Cw)
    (hgap : Cw + 2 *
        (NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (fun k => C0 * O.defect k) 0) <
      (2 * Hs 0 -
        NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (fun k => C0 * O.defect k) 0) / Real.pi) :
    ∃ (Gamma : ℕ → ℝ → ℂ) (L : ℝ),
      IsOval (Gamma 0) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L ∧
      (∀ n, IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      0 < L ∧ Periodic (Gamma 0) L := by
  let G := O.toGaugeControlledFamily hP0 hP1 hkhat hG1 hCg hM hN hC0
  have hGerror : G.error = fun n k => C0 * O.defect (n + k) := rfl
  have hgap' : Cw + 2 *
        (NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (G.error 0) 0) <
      (2 * Hs 0 -
        NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (G.error 0) 0) / Real.pi := by
    simpa [hGerror] using hgap
  let C := GaugeControlledClosingInputsNonnegative.ofConfiguredModelFrontGaugeTail model G
    hc hdlt hmetric htube hstrict hrepresentative htangentRepresentative hRorbit
    hmodel hmodelPerim hwidth hgap'
  exact paper_main_theorem_of_gaugeControlledFamilyNonnegative model G hmetric C

/-- Paper-facing configured recursive assembly with strictness reconstructed
from the concrete physical selected-rear data rather than supplied as an
arbitrary callback. -/
theorem paper_main_theorem_of_configuredModelRecursiveOutputs_physicalRear
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {R : ℕ → ℝ → ℂ}
    {P0 P1 khat G1 Cg M N C0 c dlt Cw : ℝ}
    (O : ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg M N C0)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hC0 : 0 ≤ C0) (hc : 0 < c) (hdlt : 0 < dlt)
    (hmetric : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
        (Cg * M ^ 2 + khat * P1 * N))
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k))
    (hrear : PhysicalRearLimitReconstructionFamily Q)
    (hrepresentative : ∀ (X : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) →
      ∀ n, range (ev (X n)) = range (R n))
    (htangentRepresentative : ∀ (X : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) → ∀ n,
      range (UnitTangent.unitTangentMap (ev (X n))) =
        range (UnitTangent.unitTangentMap (R n)))
    (hRorbit : ∀ n,
      range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n)))
    (hmodel : ev (Q 0 0) =
      TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
    (hmodelPerim : perim (Q 0 0) = 2 * Hs 0)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)))
        Complex.I ≤ Cw)
    (hgap : Cw + 2 *
        (NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (fun k => C0 * O.defect k) 0) <
      (2 * Hs 0 -
        NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (fun k => C0 * O.defect k) 0) / Real.pi) :
    ∃ (Gamma : ℕ → ℝ → ℂ) (L : ℝ),
      IsOval (Gamma 0) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L ∧
      (∀ n, IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      0 < L ∧ Periodic (Gamma 0) L := by
  exact paper_main_theorem_of_configuredModelRecursiveOutputs model O
    hP0 hP1 hkhat hG1 hCg hM hN hC0 hc hdlt hmetric htube
    (hrear.limitStrictness hc htube) hrepresentative htangentRepresentative
    hRorbit hmodel hmodelPerim hwidth hgap

/-- Final configured-model capstone.  Concrete physical rear reconstruction
automatically supplies limit strictness and its realized unit-tangent orbit.
Pointwise identification with the paper's representative curves then supplies
both range transports and the representative orbit through
`PhysicalRearLimitReconstructionFamily.representativeClosing`.  Thus none of
the former strictness, representative-range, tangent-range, or orbit callbacks
remain as independent assumptions. -/
theorem paper_main_theorem_of_configuredModelRecursiveOutputs_final
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {R : ℕ → ℝ → ℂ}
    {P0 P1 khat G1 Cg M N C0 c dlt Cw : ℝ}
    (O : ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg M N C0)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hC0 : 0 ≤ C0) (hc : 0 < c) (hdlt : 0 < dlt)
    (hmetric : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
        (Cg * M ^ 2 + khat * P1 * N))
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k))
    (hrear : PhysicalRearLimitReconstructionFamily Q)
    (hpoint : ∀ (X : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X n))) →
      ∀ n, ev (X n) = R n)
    (hmodel : ev (Q 0 0) =
      TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
    (hmodelPerim : perim (Q 0 0) = 2 * Hs 0)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)))
        Complex.I ≤ Cw)
    (hgap : Cw + 2 *
        (NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (fun k => C0 * O.defect k) 0) <
      (2 * Hs 0 -
        NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (fun k => C0 * O.defect k) 0) / Real.pi) :
    ∃ (Gamma : ℕ → ℝ → ℂ) (L : ℝ),
      IsOval (Gamma 0) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L ∧
      (∀ n, IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      0 < L ∧ Periodic (Gamma 0) L := by
  let G := O.toGaugeControlledFamily hP0 hP1 hkhat hG1 hCg hM hN hC0
  obtain ⟨X, hX⟩ := G.exists_limit_family hmetric htube
  obtain ⟨hrepresentative, htangentRepresentative, hRorbit⟩ :=
    hrear.representativeClosing hpoint X hX
  exact paper_main_theorem_of_configuredModelRecursiveOutputs_physicalRear
    model O hP0 hP1 hkhat hG1 hCg hM hN hC0 hc hdlt hmetric htube hrear
    hrepresentative htangentRepresentative hRorbit hmodel hmodelPerim hwidth hgap

/-- Representative-free final capstone.  The representative curves are the
marked metric limits constructed from the controlled family itself.  Any
other simultaneous limit agrees with them by uniqueness of limits, so no
external representative-identification callback is needed. -/
theorem paper_main_theorem_of_configuredModelRecursiveOutputs_representativeFree
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data}
    {P0 P1 khat G1 Cg M N C0 c dlt Cw : ℝ}
    (O : ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg M N C0)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hC0 : 0 ≤ C0) (hc : 0 < c) (hdlt : 0 < dlt)
    (hmetric : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
        (Cg * M ^ 2 + khat * P1 * N))
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k))
    (hrear : PhysicalRearLimitReconstructionFamily Q)
    (hmodel : ev (Q 0 0) =
      TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0))
    (hmodelPerim : perim (Q 0 0) = 2 * Hs 0)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) model.thetaBase (Hs 0)))
        Complex.I ≤ Cw)
    (hgap : Cw + 2 *
        (NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (fun k => C0 * O.defect k) 0) <
      (2 * Hs 0 -
        NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 (P1 * M) khat (G1 * M ^ 2 + P1 * N)
            (Cg * M ^ 2 + khat * P1 * N) *
          ShadowingTails.tail (fun k => C0 * O.defect k) 0) / Real.pi) :
    ∃ (Gamma : ℕ → ℝ → ℂ) (L : ℝ),
      IsOval (Gamma 0) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L ∧
      (∀ n, IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      0 < L ∧ Periodic (Gamma 0) L := by
  let G := O.toGaugeControlledFamily hP0 hP1 hkhat hG1 hCg hM hN hC0
  obtain ⟨X, hX⟩ := G.exists_limit_family hmetric htube
  let R : ℕ → ℝ → ℂ := fun n => ev (X n)
  have hpoint : ∀ (X' : ℕ → Data),
      (∀ n, Filter.Tendsto (Q n) Filter.atTop (nhds (X' n))) →
      ∀ n, ev (X' n) = R n := by
    intro X' hX' n
    have heq : X' n = X n := tendsto_nhds_unique (hX' n) (hX n)
    simpa [R, heq]
  exact paper_main_theorem_of_configuredModelRecursiveOutputs_final
    model O hP0 hP1 hkhat hG1 hCg hM hN hC0 hc hdlt hmetric htube hrear
    hpoint hmodel hmodelPerim hwidth hgap

end PathMetric
