import Mathlib
import UnitTangentIterates.CompatibleSelectedRearJunction
import UnitTangentIterates.ConfiguredModelGaugeFamily

/-! # Weighted defects for recursively transported stages

The pullback stage at `(n,k)` is obtained by transporting the model defect at
index `n+k` through the selected-rear map `k` times.  If one transport costs a
factor `K`, its honest majorant is therefore `K^k d(n+k)`, not merely
`d(n+k)`.  This file isolates the corresponding summability bookkeeping and
connects a single family of actual controlled outputs to the existing
configured-model interface.
-/

noncomputable section

open Function Set Filter Topology MarkedSpace

namespace PathMetric

namespace WeightedRecursiveDefect

/-- The one-index defect after allowing up to `n` recursive transports. -/
def weightedDefect (K : ℝ) (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  K ^ n * d n

/-- The actual error of the `k`-th pullback stage at orbit level `n`. -/
def pullbackError (K : ℝ) (d : ℕ → ℝ) (n k : ℕ) : ℝ :=
  K ^ k * d (n + k)

theorem weightedDefect_nonneg {K : ℝ} {d : ℕ → ℝ}
    (hK : 0 ≤ K) (hd : ∀ n, 0 ≤ d n) (n : ℕ) :
    0 ≤ weightedDefect K d n :=
  mul_nonneg (pow_nonneg hK n) (hd n)

theorem pullbackError_nonneg {K : ℝ} {d : ℕ → ℝ}
    (hK : 0 ≤ K) (hd : ∀ n, 0 ≤ d n) (n k : ℕ) :
    0 ≤ pullbackError K d n k :=
  mul_nonneg (pow_nonneg hK k) (hd (n + k))

/-- If `K >= 1`, the two-index recursive error is bounded by the shifted
one-index weighted defect.  This is the comparison required by
`ConfiguredModelRecursiveOutputs.stage_le_modelDefect`. -/
theorem pullbackError_le_weightedDefect_shift
    {K : ℝ} {d : ℕ → ℝ} (hK : 1 ≤ K) (hd : ∀ n, 0 ≤ d n)
    (n k : ℕ) :
    pullbackError K d n k ≤ weightedDefect K d (n + k) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hpow : 0 ≤ K ^ k := pow_nonneg hK0 k
  have hkn : 1 ≤ K ^ n := one_le_pow₀ hK
  have hmul : K ^ k * d (n + k) ≤ K ^ n * (K ^ k * d (n + k)) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hkn (mul_nonneg hpow (hd (n + k)))
  rw [pullbackError, weightedDefect, pow_add]
  exact hmul.trans_eq (by ring)

/-- Summability of the one-index weighted defect implies summability of every
pullback row.  No nonexpansiveness hypothesis is used; the natural assumption
here is `1 <= K`, since a smaller transport factor can first be enlarged to
`max 1 K`. -/
theorem summable_pullbackError_of_summable_weighted
    {K : ℝ} {d : ℕ → ℝ} (hK : 1 ≤ K) (hd : ∀ n, 0 ≤ d n)
    (hsum : Summable (weightedDefect K d)) :
    ∀ n, Summable (pullbackError K d n) := by
  intro n
  have hshift : Summable (fun k => weightedDefect K d (n + k)) := by
    simpa [Nat.add_comm] using hsum.comp_injective (add_right_injective n)
  exact Summable.of_nonneg_of_le
    (fun k => pullbackError_nonneg (zero_le_one.trans hK) hd n k)
    (pullbackError_le_weightedDefect_shift hK hd n) hshift

/-- Geometric domination of the model defect gives the precise recursive
summability criterion `K*q < 1`, allowing `K > 1`. -/
theorem summable_pullbackError_of_geometric
    {K D q : ℝ} {d : ℕ → ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hq : 0 ≤ q) (hKq : K * q < 1)
    (hd : ∀ n, 0 ≤ d n) (hdgeo : ∀ n, d n ≤ D * q ^ n) :
    ∀ n, Summable (pullbackError K d n) := by
  have hgeom : Summable (fun k : ℕ => (K * q) ^ k) :=
    summable_geometric_of_lt_one (mul_nonneg hK hq) hKq
  intro n
  have hmajor : ∀ k,
      pullbackError K d n k ≤ D * q ^ n * (K * q) ^ k := by
    intro k
    have hle := mul_le_mul_of_nonneg_left (hdgeo (n + k)) (pow_nonneg hK k)
    rw [pullbackError]
    calc
      K ^ k * d (n + k) ≤ K ^ k * (D * q ^ (n + k)) := hle
      _ = D * q ^ n * (K * q) ^ k := by rw [pow_add, mul_pow]; ring
  exact Summable.of_nonneg_of_le
    (fun k => pullbackError_nonneg hK hd n k) hmajor
    (hgeom.mul_left (D * q ^ n))

/-- The corresponding one-index weighted defect is itself summable under the
same geometric hypothesis. -/
theorem summable_weightedDefect_of_geometric
    {K D q : ℝ} {d : ℕ → ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hq : 0 ≤ q) (hKq : K * q < 1)
    (hd : ∀ n, 0 ≤ d n) (hdgeo : ∀ n, d n ≤ D * q ^ n) :
    Summable (weightedDefect K d) := by
  have hgeom : Summable (fun n : ℕ => (K * q) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg hK hq) hKq
  have hmajor : ∀ n, weightedDefect K d n ≤ D * (K * q) ^ n := by
    intro n
    have hle := mul_le_mul_of_nonneg_left (hdgeo n) (pow_nonneg hK n)
    rw [weightedDefect]
    calc
      K ^ n * d n ≤ K ^ n * (D * q ^ n) := hle
      _ = D * (K * q) ^ n := by rw [mul_pow]; ring
  exact Summable.of_nonneg_of_le (weightedDefect_nonneg hK hd) hmajor
    (hgeom.mul_left D)

/-- Forget the name of the constructor: a gauge-controlled output has exactly
the same fields as an interpolation-controlled output.  This is used only to
fill the legacy two-alternative record; the selected stage below is always the
single supplied gauge output. -/
def gaugeOutputToInterpolation
    {p q : Data} {P0 P1 khat G1 Cg E : ℝ}
    (G : GaugeControlledJunctionOutput p q P0 P1 khat G1 Cg E) :
    InterpolationControlledJunctionOutput p q P0 P1 khat G1 Cg E where
  path := G.path
  c2 := G.c2
  start := G.start
  finish := G.finish
  variableSpeed := G.variableSpeed
  cost_le := G.cost_le

/-- Embed one actual output per `(n,k)` into the older recursive-stage record.
Both shape fields point to the same path, and the Boolean selector is fixed to
the gauge-shaped field, so no unconstructed alternative is introduced. -/
def modelStagesOfSingleOutputs
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg K : ℝ} {d : ℕ → ℝ}
    (G : ∀ n k, GaugeControlledJunctionOutput (Q n k) (Q n (k + 1))
      P0 P1 khat G1 Cg (pullbackError K d n k)) :
    ModelRecursiveControlledStages Q P0 P1 khat G1 Cg where
  interpolationError := pullbackError K d
  gaugeError := pullbackError K d
  interpolation := fun n k => gaugeOutputToInterpolation (G n k)
  selectedRearGauge := G
  useInterpolation := fun _ _ => false

/-- A single family of actual controlled stages, together with a summable
weighted defect, gives `ConfiguredModelRecursiveOutputs`.  Endpoint markings
are already literal in the output types, hence the only junction used here is
the concrete identity junction.  Its current common cost ceiling is `3`.
-/
def configuredRecursiveOutputsOfSingleWeightedStages
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg K : ℝ} {d : ℕ → ℝ}
    (G : ∀ n k, GaugeControlledJunctionOutput (Q n k) (Q n (k + 1))
      P0 P1 khat G1 Cg (pullbackError K d n k))
    (hK : 1 ≤ K) (hd : ∀ n, 0 ≤ d n)
    (hsum : Summable (weightedDefect K d)) :
    ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg 1 0 3 := by
  let A := modelStagesOfSingleOutputs G
  let J : ∀ n k, ReparamJunctionCertificate
      (p' := Q n k) (q' := Q n (k + 1)) (A.stage n k).path :=
    fun n k => reparamJunctionCertificate_of_compatible_affine_endpoints rfl rfl
  refine
    { stages := A
      junction := J
      junctionC2 := fun n k =>
        reparamC2Certificate_of_compatible_affine_endpoints (A.stage n k).c2
      junction_M := fun _ _ => rfl
      junction_N := fun _ _ => rfl
      reparam_cost := ?_
      defect := weightedDefect K d
      defect_nonneg := weightedDefect_nonneg (zero_le_one.trans hK) hd
      defect_summable := hsum
      stage_nonneg := ?_
      stage_le_modelDefect := ?_ }
  · intro n k
    norm_num [J, reparamCostConst,
      reparamJunctionCertificate_of_compatible_affine_endpoints]
  · intro n k
    simpa [A, modelStagesOfSingleOutputs, pullbackError] using
      pullbackError_nonneg (zero_le_one.trans hK) hd n k
  · intro n k
    simpa [A, modelStagesOfSingleOutputs] using
      pullbackError_le_weightedDefect_shift hK hd n k

/-- Geometric form of the single-output adapter. -/
def configuredRecursiveOutputsOfSingleGeometricStages
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg K D q : ℝ} {d : ℕ → ℝ}
    (G : ∀ n k, GaugeControlledJunctionOutput (Q n k) (Q n (k + 1))
      P0 P1 khat G1 Cg (pullbackError K d n k))
    (hK1 : 1 ≤ K) (hD : 0 ≤ D) (hq : 0 ≤ q) (hKq : K * q < 1)
    (hd : ∀ n, 0 ≤ d n) (hdgeo : ∀ n, d n ≤ D * q ^ n) :
    ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg 1 0 3 :=
  configuredRecursiveOutputsOfSingleWeightedStages model G hK1 hd
    (summable_weightedDefect_of_geometric (zero_le_one.trans hK1) hD hq hKq hd hdgeo)

/-- Feed geometric weighted-defect summability directly into the existing
single-output variable-speed pullback limit theorem. -/
theorem exists_markedLimit_of_variableSpeed_transport_geometric
    {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K D q c dlt P0 P1 khat G1 Cg : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hq : 0 ≤ q) (hKq : K * q < 1)
    (hd : ∀ n, 0 ≤ d n) (hdgeo : ∀ n, d n ≤ D * q ^ n)
    (hbase : ∀ n, ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
      NormalPath.cost Lambda ≤ d n ∧
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg Lambda)
    (htransport : ∀ {p r : Data} (Gamma : NormalPath p r),
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg Gamma →
      ∃ Delta : NormalPath (B p) (B r),
        NormalPath.cost Delta ≤ K * NormalPath.cost Gamma ∧
        NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
          P0 P1 khat G1 Cg Delta)
    (hC : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B) :
    ∀ n, ∃ X : Data,
      IsTubeMember c 0 dlt X ∧
      Tendsto (TubePullbackLimit.pullback B Q n) atTop (nhds X) ∧
      dist (Q n) X ≤ ShadowingTails.tail
        (fun k => NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 P1 khat G1 Cg * pullbackError K d n k) 0 := by
  simpa [pullbackError] using
    UnconditionalAssembly.PaperFaithfulAssemblyRemainder.exists_markedLimit_of_variableSpeed_transport
      hK (summable_pullbackError_of_geometric hK hD hq hKq hd hdgeo)
      hbase htransport hC hmem hBcont

/-! ## Actual-stage transport

The geometric construction in the paper produces the finitely transported
increment at each `(n,k)` directly.  In particular, it does not require a
transport operation on every normal path between arbitrary marked data.  The
following interface retains exactly those constructed paths and is therefore
strictly weaker than the unrestricted `htransport` premise above. -/

/-- The already-constructed path between two consecutive coherently marked
finite stages.  The nodes are dependent choices rather than literal iterates
of one map on marked data.  `range_edge` records the selected-inverse
coherence which survives a cyclic or nonaffine change of marking. -/
structure ActualPullbackStages
    (Q : ℕ → Data) (P : ℕ → ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg : ℕ → ℝ) where
  base : ∀ n, P n 0 = Q n
  path : ∀ n k, NormalPath
    (P n k) (P n (k + 1))
  cost_le : ∀ n k, NormalPath.cost (path n k) ≤ e n k
  variableSpeed : ∀ n k,
    NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) (path n k)
  range_edge : ∀ n k,
    range ((P n (k + 1)).1) =
      range (UnitTangent.unitTangentMap (ev (P (n + 1) k)))

/-- Summable actual transported increments give the simultaneous marked
limits.  No action of `B` on arbitrary paths, and no continuity of `B`, is
used.  This is the exact convergence interface for a dependent physical
finite-stage construction. -/
theorem exists_markedLimit_of_actual_pullback_stages
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg : ℕ → ℝ} {c dlt : ℝ}
    (hsum : ∀ n, Summable (e n))
    (H : ActualPullbackStages Q P e P0 P1 khat G1 Cg)
    (hC : ∀ n, 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n))
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (P n k)) :
    ∃ X : ℕ → Data,
      (∀ n, IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (P n) atTop (nhds (X n))) ∧
      (∀ n, dist (Q n) (X n) ≤ ShadowingTails.tail
        (fun k => NormalPathC2IncrementVariableSpeed.c2ConstVar
          (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * e n k) 0) := by
  let C : ℕ → ℝ := fun n =>
    NormalPathC2IncrementVariableSpeed.c2ConstVar
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
  have hstep : ∀ n k,
      dist (P n k) (P n (k + 1)) ≤
        C n * e n k := by
    intro n k
    let Gamma := H.path n k
    have hdist := NormalPathC2IncrementVariableSpeed.dist_le_cost_variableSpeed
      Gamma (hmem n k).hasDerivAt_curve (hmem n (k + 1)).hasDerivAt_curve
      (hmem n k).hasDerivAt_vel (hmem n (k + 1)).hasDerivAt_vel
      (H.variableSpeed n k)
    exact hdist.trans (mul_le_mul_of_nonneg_left (H.cost_le n k) (hC n))
  have hlim : ∀ n, ∃ x : Data,
      Tendsto (P n) atTop (nhds x) ∧
      ∀ k, dist (P n k) x ≤
        ShadowingTails.tail (fun j => C n * e n j) k := by
    intro n
    obtain ⟨x, hx, hxd⟩ := ShadowingTails.exists_limit_of_summable_increments
      (C := 1) ((hsum n).mul_left (C n)) (fun k => by simpa using hstep n k)
    exact ⟨x, hx, fun k => by simpa using hxd k⟩
  choose X hXlim hXdist using hlim
  have hXmem : ∀ n, IsTubeMember c 0 dlt (X n) := by
    intro n
    exact (MarkedSpace.isClosed_tube c 0 dlt).mem_of_tendsto (hXlim n)
      (Eventually.of_forall (hmem n))
  refine ⟨X, hXmem, hXlim, ?_⟩
  intro n
  have h := hXdist n 0
  rw [H.base n] at h
  simpa [C] using h

/-- Geometric-decay form of the actual-stage convergence theorem. -/
theorem exists_markedLimit_of_actual_pullback_stages_geometric
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {d : ℕ → ℝ}
    {K D q P0 P1 khat G1 Cg c dlt : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hq : 0 ≤ q) (hKq : K * q < 1)
    (hd : ∀ n, 0 ≤ d n) (hdgeo : ∀ n, d n ≤ D * q ^ n)
    (H : ActualPullbackStages Q P (fun n k => K ^ k * d (n + k))
      (fun _ => P0) (fun _ => P1) (fun _ => khat) (fun _ => G1) (fun _ => Cg))
    (hC : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (P n k)) :
    ∃ X : ℕ → Data,
      (∀ n, IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (P n) atTop (nhds (X n))) ∧
      (∀ n, dist (Q n) (X n) ≤ ShadowingTails.tail
        (fun k => NormalPathC2IncrementVariableSpeed.c2ConstVar
          P0 P1 khat G1 Cg * (K ^ k * d (n + k))) 0) := by
  have hsum := summable_pullbackError_of_geometric hK hD hq hKq hd hdgeo
  apply exists_markedLimit_of_actual_pullback_stages
    (H := H) (hC := fun _ => hC) (hmem := hmem)
  intro n
  simpa [pullbackError] using hsum n

end WeightedRecursiveDefect

end PathMetric
