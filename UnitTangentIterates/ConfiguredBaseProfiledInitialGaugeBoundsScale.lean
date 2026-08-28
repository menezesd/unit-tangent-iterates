import UnitTangentIterates.ConfiguredBaseProfiledInitialGaugeResidual

/-! # Density scaling for the initial-value gauge source -/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredBaseProfiledInitialGaugeResidual

/-- Enlarge only the dominating density in an initial-gauge bounds package. -/
def Bounds.scale
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data} {n : ℕ}
    {A : ConfiguredApproximateDefectPathActualTerminal.RearCarrier D n}
    {W : ConfiguredApproximateDefectPathActualTerminal.Output D Q n A}
    {P0 kh khat Qmax : ℝ} {H : ConfiguredActualSubunitCurvature.Certificate D}
    {S : ConfiguredBaseProfiledResidualConstructor.ExactSelected H}
    {P : ConfiguredBaseExactSelectedPreTransport.PreTransport W H S}
    {G : RearOwnFrameGaugeFlowInitialValue.Gauge
      (ConfiguredBaseExactSelectedInitialGaugeTransport.xi P)}
    {T : ConfiguredBaseExactSelectedInitialGaugeTransport.ShiftedTransport P G}
    (B : Bounds W P0 kh khat Qmax S P G T) (C : ℝ) (hC : 1 ≤ C)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hd0 : 0 ≤ B.d) :
    Bounds W P0 kh khat Qmax S P G T where
  Kx := B.Kx
  Dd := B.Dd
  m := fun t ↦ C * B.m t
  kx := B.kx
  d := B.d
  rear_period_pos := B.rear_period_pos
  rear_period_le := B.rear_period_le
  tangential1_bound t x := by
    have hm0 := B.density_nonnegative t
    have hm : B.m t ≤ C * B.m t := by nlinarith
    exact (B.tangential1_bound t x).trans
      (mul_le_mul_of_nonneg_left hm
        (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkh0 hkh1))
  tangential2_bound t x := by
    have hm0 := B.density_nonnegative t
    have hm : B.m t ≤ C * B.m t := by nlinarith
    exact (B.tangential2_bound t x).trans
      (mul_le_mul_of_nonneg_left hm
        (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hkh0 hkh1))
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

end ConfiguredBaseProfiledInitialGaugeResidual
