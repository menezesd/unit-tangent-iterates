import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorBoundsScale

/-!
# Composition-scaled exact recursive successors

The minimal exact-successor density dominates the path density, but it need
not dominate the first two derivatives after composition with the chosen flow.
The scalar package below records one sound row-dependent multiplier and the
single scaled-mass estimate needed to compare the actual flow costs with their
mass-one ceilings.
-/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  (W : ChosenPath Gamma A E.Phi a b)
  (S : ExactSelected A (kap := kap))
  (R : PreTransport S)
  (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
  (T : ShiftedTransport R G)

private theorem sourceConst_nonnegative (hkap0 : 0 ≤ kap) :
    0 ≤ FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst (kh := kh) (kap := kap) := by
  apply RearJacobiSourceCost.jacobiSourceConst_nonneg
  exact one_div_pos.mpr (by
    dsimp [FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.derivativeConst,
      FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
    positivity)

/-- Scalar data for a composition-stable exact successor.  The two coefficient
inequalities are evaluated at total source mass one; `scaled_mass_le_one`
places the actual scaled source below that ceiling. -/
structure Scalar extends
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.Scalar (A := A) (kap := kap) (P0Next := P0Next)
      (khatNext := khatNext) (QmaxNext := QmaxNext) where
  coeff : ℝ
  coeff_ge_one : 1 ≤ coeff
  scaled_mass_le_one :
    (∫ t in (0 : ℝ)..W.Delta.T,
      coeff * FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.density W (kap := kap) t) ≤ 1
  coeff_first :
    2 * GaugeFlowDerivCost.costP1 QmaxNext
      (GaugeMarkedDataOfRearFamily.rearKappa1 kap) 1 ≤ coeff
  coeff_second :
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst (kh := kh) (kap := kap) + 2) *
          GaugeFlowDerivCost.costP1 QmaxNext
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap) 1 ^ 2 +
        2 * GaugeFlowDerivCost.costG1 QmaxNext
          (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
          (GaugeMarkedDataOfRearFamily.rearKappa2 kap) 1 ≤ coeff

/-- The exact-successor bounds with the composition-stable density. -/
def scaledBounds (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (C : Scalar (A := A) (kap := kap) (P0Next := P0Next)
      (khatNext := khatNext) (QmaxNext := QmaxNext) W)
    (hP0 : 0 < P0Next) :
    Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1 :=
  (FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.bounds W S R G T hkap0 hkap1 C.toScalar hP0).scale
    C.coeff C.coeff_ge_one (sourceConst_nonnegative (kh := kh) hkap0)

/-- The scaled source satisfies both density hypotheses used by the composed
normal `C²` estimate. -/
theorem scaledBounds_composition_budgets
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (C : Scalar (A := A) (kap := kap) (P0Next := P0Next)
      (khatNext := khatNext) (QmaxNext := QmaxNext) W)
    (hP0 : 0 < P0Next) :
    let B := scaledBounds W S R G T hkap0 hkap1 C hP0
    let M := ∫ s in (0 : ℝ)..W.Delta.T, B.m s
    (∀ t, 2 * (W.Delta.m t / Real.sqrt (1 - kap ^ 2)) *
          GaugeFlowDerivCost.costP1
            (rearArclength (delta S G.q 0) (period A 0))
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap) M ≤ B.m t) ∧
      (∀ t,
        (B.Dd t + 2 * (W.Delta.m t / Real.sqrt (1 - kap ^ 2))) *
              GaugeFlowDerivCost.costP1
                (rearArclength (delta S G.q 0) (period A 0))
                (GaugeMarkedDataOfRearFamily.rearKappa1 kap) M ^ 2 +
            2 * (W.Delta.m t / Real.sqrt (1 - kap ^ 2)) *
              GaugeFlowDerivCost.costG1
                (rearArclength (delta S G.q 0) (period A 0))
                (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
                (GaugeMarkedDataOfRearFamily.rearKappa2 kap) M ≤ B.m t) := by
  dsimp only
  let B0 := FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.bounds W S R G T hkap0 hkap1 C.toScalar hP0
  let B := scaledBounds W S R G T hkap0 hkap1 C hP0
  let M := ∫ s in (0 : ℝ)..W.Delta.T, B.m s
  let ell := rearArclength (delta S G.q 0) (period A 0)
  let k1 := GaugeMarkedDataOfRearFamily.rearKappa1 kap
  let k2 := GaugeMarkedDataOfRearFamily.rearKappa2 kap
  let p := GaugeFlowDerivCost.costP1 ell k1 M
  let p1 := GaugeFlowDerivCost.costP1 QmaxNext k1 1
  let g := GaugeFlowDerivCost.costG1 ell k1 k2 M
  let g1 := GaugeFlowDerivCost.costG1 QmaxNext k1 k2 1
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg W.Delta.T_pos.le
    (fun t _ ↦ B.density_nonnegative t)
  have hM1 : M ≤ 1 := by
    simpa [M, B, scaledBounds, Bounds.scale] using C.scaled_mass_le_one
  have hell0 : 0 ≤ ell := (B0.rear_period_pos 0).le
  have hell : ell ≤ QmaxNext := B0.rear_period_le 0
  have hk10 : 0 ≤ k1 :=
    GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1
  have hk20 : 0 ≤ k2 :=
    GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hkap0 hkap1
  have hp : p ≤ p1 := by
    simpa [p, p1, ell, k1] using
      GaugeFlowDerivCost.costP1_le hell0 hell hk10 hM0 hM1
  have hg : g ≤ g1 := by
    simpa [g, g1, ell, k1, k2] using
      GaugeFlowDerivCost.costG1_le hell0 hell hk10 hk20 hM0 hM1
  have hp0 : 0 ≤ p := by
    unfold p GaugeFlowDerivCost.costP1
    exact mul_nonneg hell0 (Real.exp_pos _).le
  have hp10 : 0 ≤ p1 := hp0.trans hp
  have hg0 : 0 ≤ g := by
    unfold g GaugeFlowDerivCost.costG1
    exact mul_nonneg (sq_nonneg _) (mul_nonneg hk20 hM0)
  have hg10 : 0 ≤ g1 := hg0.trans hg
  have hd0 := sourceConst_nonnegative (kh := kh) hkap0
  constructor
  · intro t
    have hr0 := B0.density_nonnegative t
    have hdom := B0.density_domination t
    have hrho0 : 0 ≤ W.Delta.m t / Real.sqrt (1 - kap ^ 2) :=
      div_nonneg (W.Delta.m_nonneg t) (Real.sqrt_nonneg _)
    have hfirst : 2 * p1 ≤ C.coeff := C.coeff_first
    change 2 * (W.Delta.m t / Real.sqrt (1 - kap ^ 2)) * p ≤
      C.coeff * B0.m t
    nlinarith
  · intro t
    have hr0 := B0.density_nonnegative t
    have hdom := B0.density_domination t
    have hrho0 : 0 ≤ W.Delta.m t / Real.sqrt (1 - kap ^ 2) :=
      div_nonneg (W.Delta.m_nonneg t) (Real.sqrt_nonneg _)
    have hDd := B0.Dd_le t
    have hsecond :
        (FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst (kh := kh) (kap := kap) + 2) * p1 ^ 2 +
            2 * g1 ≤ C.coeff := C.coeff_second
    have hpsq : p ^ 2 ≤ p1 ^ 2 := (sq_le_sq₀ hp0 hp10).2 hp
    change
      (B0.Dd t + 2 * (W.Delta.m t / Real.sqrt (1 - kap ^ 2))) * p ^ 2 +
          2 * (W.Delta.m t / Real.sqrt (1 - kap ^ 2)) * g ≤
        C.coeff * B0.m t
    have hfac :
        B0.Dd t + 2 * (W.Delta.m t / Real.sqrt (1 - kap ^ 2)) ≤
          (FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst (kh := kh) (kap := kap) + 2) * B0.m t := by
      have hdeq : B0.d = FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst (kh := kh) (kap := kap) := rfl
      rw [hdeq] at hDd
      nlinarith
    have hupper0 : 0 ≤
        (FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst
          (kh := kh) (kap := kap) + 2) * B0.m t :=
      mul_nonneg (add_nonneg hd0 (by norm_num)) hr0
    have hterm1 :
        (B0.Dd t + 2 * (W.Delta.m t / Real.sqrt (1 - kap ^ 2))) * p ^ 2 ≤
          ((FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst (kh := kh) (kap := kap) + 2) * p1 ^ 2) *
            B0.m t := by
      calc
        _ ≤ ((FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst (kh := kh) (kap := kap) + 2) * B0.m t) *
              p1 ^ 2 := mul_le_mul hfac hpsq (sq_nonneg p) hupper0
        _ = _ := by ring
    have hterm2 :
        2 * (W.Delta.m t / Real.sqrt (1 - kap ^ 2)) * g ≤
          (2 * g1) * B0.m t := by nlinarith
    nlinarith [hterm1, hterm2,
      mul_le_mul_of_nonneg_right hsecond hr0]

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale
