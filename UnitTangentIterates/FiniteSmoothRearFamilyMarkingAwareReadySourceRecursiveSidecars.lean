import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSourceStopping
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars

/-!
# Fresh recursive sidecars for an assembled ready source
-/

noncomputable section

open Set MarkedSpace PathMetric RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareReadySourceRecursiveSidecars

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSourceStopping
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds
  FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars

/-- The spatial certificate used definitionally by `ReadySource.source`. -/
def spatialCertificate
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A) (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (D : Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1) :
    SpatialFrameRegularity W.Delta
      (source (P0Next := P0Next) (khatNext := khatNext) (QmaxNext := QmaxNext)
        W S R G hkap0 hkap1 T D).Ydot
      (source (P0Next := P0Next) (khatNext := khatNext) (QmaxNext := QmaxNext)
        W S R G hkap0 hkap1 T D).Theta
      (source (P0Next := P0Next) (khatNext := khatNext) (QmaxNext := QmaxNext)
        W S R G hkap0 hkap1 T D).delta
      (source (P0Next := P0Next) (khatNext := khatNext) (QmaxNext := QmaxNext)
        W S R G hkap0 hkap1 T D).sf
      (source (P0Next := P0Next) (khatNext := khatNext) (QmaxNext := QmaxNext)
        W S R G hkap0 hkap1 T D).P
      (source (P0Next := P0Next) (khatNext := khatNext) (QmaxNext := QmaxNext)
        W S R G hkap0 hkap1 T D).m kap QmaxNext := by
  let H := geometricSpatialFrames S R G T hkap0 hkap1
  have hpsi : rearOwnAngle
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.Theta S G.q)
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.delta S G.q)
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sf S G.q) =
      shiftedPsi R G := by
    funext t x
    exact FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.psi_eq_shift
      S G.q t x
  exact
    { tangential := H.1
      normal := H.2
      tangential1_bound := D.tangential1_bound
      tangential2_bound := D.tangential2_bound
      tangential_period_bound := by
        intro t x hx
        simpa only [source, hpsi] using D.tangential_period_bound t x hx }

/-- Every assembled ready source carries fresh, source-indexed finite bounds
for the next Taylor-free steering selection. -/
theorem exists_selectionBounds
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A) (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (D : Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1)
    (hP0 : 0 < P0Next)
    (hPl : ∀ t, P0Next ≤ (source (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G hkap0 hkap1 T D).P t) :
    Nonempty (SelectionBounds (source (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G hkap0 hkap1 T D)) := by
  let B := source (P0Next := P0Next) (khatNext := khatNext)
    (QmaxNext := QmaxNext) W S R G hkap0 hkap1 T D
  have hn : ∀ t ∉ Ioo (0 : ℝ) W.Delta.T,
      frameNormal B.Ydot (rearOwnAngle B.Theta B.delta B.sf) t = fun _ ↦ 0 :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.normal_stopped_of_source B
  exact FiniteSmoothRearFamilyMarkingAwareExactSourceStopping.exists_selectionBounds
    B (spatialCertificate W S R G hkap0 hkap1 T D) hn hP0 hPl

/-- The strengthened exact sidecar of a ready source. -/
noncomputable def recursiveSidecars
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A) (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (D : Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1)
    (hP0 : 0 < P0Next)
    (hPl : ∀ t, P0Next ≤ (source (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G hkap0 hkap1 T D).P t) :
    RecursiveExactSidecars (source (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G hkap0 hkap1 T D) :=
  RecursiveExactSidecars.ofSource _
    (Classical.choice (exists_selectionBounds W S R G hkap0 hkap1 T D hP0 hPl))

end FiniteSmoothRearFamilyMarkingAwareReadySourceRecursiveSidecars
