import Mathlib
import UnitTangentIterates.InterpolationControlledJunctionOutput
import UnitTangentIterates.ModelDefectSummable
import UnitTangentIterates.VariableSpeedReparamTransport

noncomputable section

open Set Function MarkedSpace

namespace PathMetric

open NormalPath NormalPathC2IncrementVariableSpeed

/-- Concrete recursive-stage data for the paper indices: `n` is the unit-
tangent orbit level and `k` is the pullback/approximation stage.  Interpolation
outputs and selected-rear gauge outputs share a downstream shape; `stage`
records the constructor correspondence choosing the one whose endpoints are
literally `Q n k` and `Q n (k+1)`. -/
structure ModelRecursiveControlledStages
    (Q : ℕ → ℕ → Data) (P0 P1 khat G1 Cg : ℝ) where
  interpolationError : ℕ → ℕ → ℝ
  gaugeError : ℕ → ℕ → ℝ
  interpolation : ∀ n k,
    InterpolationControlledJunctionOutput (Q n k) (Q n (k + 1))
      P0 P1 khat G1 Cg (interpolationError n k)
  selectedRearGauge : ∀ n k,
    GaugeControlledJunctionOutput (Q n k) (Q n (k + 1))
      P0 P1 khat G1 Cg (gaugeError n k)
  /-- The paper's recursive constructor decides which certified deformation
  is used at `(n,k)`.  Keeping this Boolean choice explicit avoids silently
  swapping orbit and pullback indices. -/
  useInterpolation : ℕ → ℕ → Bool

/-- The selected stage and its corresponding uninflated defect majorant. -/
def ModelRecursiveControlledStages.stage
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg : ℝ}
    (A : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg) (n k : ℕ) :
    GaugeControlledJunctionOutput (Q n k) (Q n (k + 1)) P0 P1 khat G1 Cg
      (if A.useInterpolation n k then A.interpolationError n k else A.gaugeError n k) := by
  split
  · exact (A.interpolation n k).toGaugeShape
  · exact A.selectedRearGauge n k

/-- Endpoint-diffeomorphism certificates completing every chosen recursive
stage. -/
structure ModelRecursiveEndpointDiffeomorphisms
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg : ℝ}
    (A : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg)
    (P0' P1' khat' G1' Cg' : ℝ) where
  junction : ∀ n k, ReparamJunctionCertificate
    (p' := Q n k) (q' := Q n (k + 1)) (A.stage n k).path
  c2 : ∀ n k, ReparamC2Certificate (A.stage n k).path
    (A.stage n k).c2 (junction n k)
  /-- Common enlarged variable-speed bounds after endpoint
  reparameterization. -/
  variableSpeed : ∀ n k, IsVariableSpeedNormalPath P0' P1' khat' G1' Cg'
    (reparamAtJunction (A.stage n k).path (A.stage n k).c2 (junction n k))

/-- Construct the endpoint package from the base-stage variable-speed
certificate when all endpoint diffeomorphisms use the chosen common derivative
ceilings `M,N`. -/
def ModelRecursiveEndpointDiffeomorphisms.ofBaseVariableSpeed
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg M N : ℝ}
    (A : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg)
    (J : ∀ n k, ReparamJunctionCertificate
      (p' := Q n k) (q' := Q n (k + 1)) (A.stage n k).path)
    (C : ∀ n k, ReparamC2Certificate (A.stage n k).path
      (A.stage n k).c2 (J n k))
    (hJM : ∀ n k, (J n k).M = M) (hJN : ∀ n k, (J n k).N = N)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ModelRecursiveEndpointDiffeomorphisms A P0 (P1 * M) khat
      (G1 * M ^ 2 + P1 * N) (Cg * M ^ 2 + khat * P1 * N) where
  junction := J
  c2 := C
  variableSpeed := by
    intro n k
    simpa [hJM n k, hJN n k] using
      isVariableSpeedNormalPath_reparamAtJunction (A.stage n k).c2 (J n k)
        (A.stage n k).variableSpeed hP0 hP1 hkhat hG1 hCg
        (by simpa [hJM n k] using hM) (by simpa [hJN n k] using hN)

/-- Assemble the exact controlled sequence at orbit level `n`. -/
def controlledJunctionSequenceOfModelStages
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg P0' P1' khat' G1' Cg' : ℝ}
    (A : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg)
    (D : ModelRecursiveEndpointDiffeomorphisms A P0' P1' khat' G1' Cg') (n : ℕ) :
    ControlledJunctionSequence (Q n) :=
  controlledJunctionSequenceOfGauge (A.stage n) (D.junction n) (D.c2 n)

/-- Smart constructor for the full gauge-controlled family.  The majorant `e`
is normally the explicit exponential sequence supplied by
`ModelDefectSummable`; the two inequalities are the only constructor-specific
comparison still needed between interpolation/gauge costs and that common
model defect. -/
def GaugeControlledFamily.ofModelRecursiveStages
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg P0' P1' khat' G1' Cg' C0 : ℝ}
    (A : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg)
    (D : ModelRecursiveEndpointDiffeomorphisms A P0' P1' khat' G1' Cg')
    (e : ℕ → ℕ → ℝ)
    (hC0 : 0 ≤ C0)
    (hconst : ∀ n k, reparamCostConst
      (D.junction n k).m (D.junction n k).M (D.junction n k).N ≤ C0)
    (he0 : ∀ n k, 0 ≤ e n k)
    (hesum : ∀ n, Summable (e n))
    (hstage0 : ∀ n k, 0 ≤
      (if A.useInterpolation n k then A.interpolationError n k else A.gaugeError n k))
    (hstage : ∀ n k,
      (if A.useInterpolation n k then A.interpolationError n k else A.gaugeError n k) ≤ e n k) :
    GaugeControlledFamily Q P0' P1' khat' G1' Cg' := by
  let S : ∀ n, ControlledJunctionSequence (Q n) :=
    fun n => controlledJunctionSequenceOfModelStages A D n
  refine GaugeControlledFamily.ofSequences S (fun n k => C0 * e n k)
    (fun n k => mul_nonneg hC0 (he0 n k)) (fun n => (hesum n).mul_left C0) ?_ ?_
  · intro n k
    have hrawsum : Summable (fun j =>
        if A.useInterpolation n j then A.interpolationError n j else A.gaugeError n j) :=
      Summable.of_nonneg_of_le (hstage0 n) (hstage n) (hesum n)
    have hb := (controlledJunctionSequenceOfGauge_costs (A.stage n)
      (D.junction n) (D.c2 n) hC0 (hconst n) (hstage0 n) hrawsum).1 k
    exact hb.trans (mul_le_mul_of_nonneg_left (hstage n k) hC0)
  · intro n k
    exact D.variableSpeed n k

/-- Full recursive-family constructor from the interpolation/gauge stage
outputs and their endpoint diffeomorphisms.  Reparameterized variable-speed
geometry is derived internally; externally one supplies only uniform scalar
bounds and domination by a summable model-defect majorant. -/
def GaugeControlledFamily.ofModelRecursiveOutputs
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg M N C0 : ℝ}
    (A : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg)
    (J : ∀ n k, ReparamJunctionCertificate
      (p' := Q n k) (q' := Q n (k + 1)) (A.stage n k).path)
    (C : ∀ n k, ReparamC2Certificate (A.stage n k).path
      (A.stage n k).c2 (J n k))
    (hJM : ∀ n k, (J n k).M = M) (hJN : ∀ n k, (J n k).N = N)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (e : ℕ → ℕ → ℝ) (hC0 : 0 ≤ C0)
    (hconst : ∀ n k,
      reparamCostConst (J n k).m (J n k).M (J n k).N ≤ C0)
    (he0 : ∀ n k, 0 ≤ e n k) (hesum : ∀ n, Summable (e n))
    (hstage0 : ∀ n k, 0 ≤
      (if A.useInterpolation n k then A.interpolationError n k else A.gaugeError n k))
    (hstage : ∀ n k,
      (if A.useInterpolation n k then A.interpolationError n k else A.gaugeError n k) ≤ e n k) :
    GaugeControlledFamily Q P0 (P1 * M) khat
      (G1 * M ^ 2 + P1 * N) (Cg * M ^ 2 + khat * P1 * N) := by
  let D := ModelRecursiveEndpointDiffeomorphisms.ofBaseVariableSpeed A J C hJM hJN
    hP0 hP1 hkhat hG1 hCg hM hN
  exact GaugeControlledFamily.ofModelRecursiveStages A D e hC0 hconst he0 hesum
    hstage0 hstage

end PathMetric
