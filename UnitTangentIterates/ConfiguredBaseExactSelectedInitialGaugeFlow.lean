import UnitTangentIterates.ConfiguredBaseExactSelectedGaugeFlow
import UnitTangentIterates.RearOwnFrameGaugeFlowInitialValue

/-! # Configured selected-rear gauge flow through a prescribed marking -/

noncomputable section

open Function Set RearTrack PathMetric

namespace ConfiguredBaseExactSelectedInitialGaugeFlow

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseExactSelectedPreTransport
  ConfiguredBaseExactSelectedGaugeFlow
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseProfiledResidualConstructor.ExactSelected
  ConfiguredBaseProfiledSelectedRearReanchoring
  RearFamilyFrame RearOwnArclength

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}
  {H : ConfiguredActualSubunitCurvature.Certificate D}

theorem exists_gaugeAt (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (P : PreTransport W H S) (q0 : ℝ) : Nonempty
    (RearOwnFrameGaugeFlowInitialValue.GaugeAt
      (frameTangential P.Ydot (psiR W S)) q0) := by
  obtain ⟨M, hM0, hM⟩ := W.increment.exists_bound_m
  let L := GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * M
  have hkappa0 : 0 ≤ GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 :=
    GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
      ((H.front_nonnegative n 0).trans (H.front_le n 0)) H.k0_lt_one
  have hL : 0 ≤ L := mul_nonneg hkappa0 hM0
  apply RearOwnFrameGaugeFlowInitialValue.exists_gaugeAt
    (tangential W S P) hL
  intro t x
  exact (raw_xi1_bound W S P t x).trans
    (mul_le_mul_of_nonneg_left (hM t) hkappa0)

structure GenuineReanchoredAt (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (S : ExactSelected (n := n) H) (q0 : ℝ) where
  preTransport : PreTransport W H S
  gauge : RearOwnFrameGaugeFlowInitialValue.Gauge
    (frameTangential preTransport.Ydot (psiR W S))
  gauge_q0 : gauge.q0 = q0

theorem exists_genuineReanchoredAt (W : Output D Q n A)
    (S : ExactSelected (n := n) H) (q0 : ℝ) :
    Nonempty (GenuineReanchoredAt W H S q0) := by
  let P : PreTransport W H S :=
    ConfiguredBaseExactSelectedPreTransport.exact W S
  obtain ⟨G⟩ := exists_gaugeAt W S P q0
  exact ⟨⟨P, G.toGauge, rfl⟩⟩

theorem GenuineReanchoredAt.initial
    {W : Output D Q n A} {S : ExactSelected (n := n) H} {q0 : ℝ}
    (R : GenuineReanchoredAt W H S q0) : R.gauge.q 0 = q0 := by
  rw [R.gauge.initial, R.gauge_q0]

end ConfiguredBaseExactSelectedInitialGaugeFlow

