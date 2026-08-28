import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource

/-!
# Density scaling for exact recursive successor bounds

The exact successor geometry is independent of the dominating density stored
in its marking-aware source.  This module enlarges that density while leaving
the geometric fields and the Jacobi derivative majorant unchanged.  It is the
generic operation needed to absorb composed-flow derivative costs at every
recursive row.
-/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  {W : ChosenPath Gamma A E.Phi a b}
  {S : ExactSelected A (kap := kap)}
  {R : PreTransport S}
  {G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R)}
  {T : ShiftedTransport R G}
  {hkap0 : 0 ≤ kap} {hkap1 : kap < 1}

/-- Enlarge only the dominating density of an exact-successor bounds package.
All geometric estimates remain valid because the multiplier is at least one.
-/
def Bounds.scale
    (B : Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1)
    (C : ℝ) (hC : 1 ≤ C) (hd0 : 0 ≤ B.d) :
    Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1 where
  Kx := B.Kx
  Dd := B.Dd
  m := fun t ↦ C * B.m t
  kx := B.kx
  d := B.d
  curvature_le := B.curvature_le
  rear_period_pos := B.rear_period_pos
  rear_period_le := B.rear_period_le
  tangential1_bound t x := by
    have hm0 := B.density_nonnegative t
    have hm : B.m t ≤ C * B.m t := by nlinarith
    exact (B.tangential1_bound t x).trans
      (mul_le_mul_of_nonneg_left hm
        (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1))
  tangential2_bound t x := by
    have hm0 := B.density_nonnegative t
    have hm : B.m t ≤ C * B.m t := by nlinarith
    exact (B.tangential2_bound t x).trans
      (mul_le_mul_of_nonneg_left hm
        (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hkap0 hkap1))
  tangential_period_bound := B.tangential_period_bound
  rearKappa1_le := B.rearKappa1_le
  Kx_bound := B.Kx_bound
  Kx_nonnegative := B.Kx_nonnegative
  Kx_le := B.Kx_le
  gS_bound := B.gS_bound
  Dd_le t := by
    have hm0 := B.density_nonnegative t
    have hm : B.m t ≤ C * B.m t := by nlinarith
    exact (B.Dd_le t).trans (mul_le_mul_of_nonneg_left hm hd0)
  density_continuous := continuous_const.mul B.density_continuous
  density_nonnegative t := mul_nonneg (by linarith) (B.density_nonnegative t)
  density_support t ht := by rw [B.density_support t ht, mul_zero]
  density_domination t := by
    have hm0 := B.density_nonnegative t
    have hm : B.m t ≤ C * B.m t := by nlinarith
    exact (B.density_domination t).trans hm
  numerical_A := B.numerical_A
  numerical_K := B.numerical_K

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource

