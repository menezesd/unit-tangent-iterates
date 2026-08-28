import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
import UnitTangentIterates.CanonicalNormalPathRecost

/-!
# Direct exact successor source on the canonical recost

Unlike generic source transport, this construction does not add the old
source envelope.  Its internal source density is exactly the canonical
recost density divided by the selected-inverse cosine floor.
-/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  (W : ChosenPath Gamma A E.Phi a b)
  (S : ExactSelected A (kap := kap))
  (R : PreTransport S)
  (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
  (T : ShiftedTransport R G)
  (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
  (C : Scalar (A := A) (kap := kap) (P0Next := P0Next)
    (khatNext := khatNext) (QmaxNext := QmaxNext))
  (hP0 : 0 < P0Next)
  (hC2 : C2NormalPathData W.Delta)
  (heta : Continuous (uncurry W.Delta.eta))
  (heta1 : Continuous (uncurry hC2.eta1))
  (heta2 : Continuous (uncurry hC2.eta2))

def carrier : NormalPath a b :=
  CanonicalNormalPathRecost.recost W.Delta hC2 heta heta1 heta2

def density (t : ℝ) : ℝ :=
  (carrier W hC2 heta heta1 heta2).m t / Real.sqrt (1 - kap ^ 2)

def rawBounds :
    Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1 :=
  bounds W S R G T hkap0 hkap1 C hP0

def rawSource : MarkingAwareSource W.Delta P0Next kap khatNext QmaxNext :=
  source W S R G hkap0 hkap1 T
    (rawBounds W S R G T hkap0 hkap1 C hP0)

/-- The four genuinely canonical-density estimates needed to replace the
raw exact source envelope. -/
structure DirectBounds : Prop where
  tangential1_bound : ∀ t x,
    |(geometricSpatialFrames S R G T hkap0 hkap1).1.xi1 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa1 kap *
        density (kap := kap) W hC2 heta heta1 heta2 t
  tangential2_bound : ∀ t x,
    |(geometricSpatialFrames S R G T hkap0 hkap1).1.xi2 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa2 kap *
        density (kap := kap) W hC2 heta heta1 heta2 t
  tangential_period_bound : ∀ t, ∀ x ∈ Icc (0 : ℝ)
      (rearArclength (delta S G.q t) (period A t)),
    |frameTangential (Ydot R G) (shiftedPsi R G) t x| ≤
      GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap *
        (carrier W hC2 heta heta1 heta2).m t
  gS_bound : ∀ t x, |gS R G t x| ≤
    (2 * (rawSource W S R G T hkap0 hkap1 C hP0).d) *
      density (kap := kap) W hC2 heta heta1 heta2 t
  numerical_K :
    ((2 * (rawSource W S R G T hkap0 hkap1 C hP0).d) + 2) +
        khatNext ^ 2 + 2 *
          GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap *
            (rawSource W S R G T hkap0 hkap1 C hP0).kx ≤
      1 / P0Next ^ 2 + khatNext ^ 2

/-- The direct nonadditive exact source. -/
def directSource (B : DirectBounds W S R G T hkap0 hkap1 C hP0
    hC2 heta heta1 heta2) :
    MarkingAwareSource (carrier W hC2 heta heta1 heta2)
      P0Next kap khatNext QmaxNext := by
  let U := rawSource W S R G T hkap0 hkap1 C hP0
  let Delta' := carrier W hC2 heta heta1 heta2
  let dens := density (kap := kap) W hC2 heta heta1 heta2
  have hsqrt : 0 < Real.sqrt (1 - kap ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have hpsi : rearOwnAngle U.Theta U.delta U.sf = shiftedPsi R G := by
    funext t x
    exact psi_eq_shift S G.q t x
  refine
    { U with
      m := dens
      Dd := fun t ↦ (2 * U.d) * dens t
      d := 2 * U.d
      frame_regularity := FrameRegularity.spatial
        { tangential := (geometricSpatialFrames S R G T hkap0 hkap1).1
          normal := (geometricSpatialFrames S R G T hkap0 hkap1).2
          tangential1_bound := B.tangential1_bound
          tangential2_bound := B.tangential2_bound
          tangential_period_bound := by simpa [hpsi] using
            B.tangential_period_bound }
      eta_link := ?_
      etaF_bound := ?_
      Dd_le := fun _ ↦ le_rfl
      density_continuous := ?_
      density_nonnegative := ?_
      density_support := ?_
      density_domination := fun _ ↦ le_rfl
      gS_bound := B.gS_bound
      numerical_K := B.numerical_K }
  · intro t u
    simpa [Delta', carrier] using U.eta_link t u
  · let M : MarkingCertificate Delta' U.etaF U.P :=
      { phi := U.phi
        phi1 := U.phi1
        phi2 := U.phi2
        eta_link := by
          intro t u
          simpa [Delta', carrier] using U.eta_link t u
        shift := U.phi_shift
        deriv := U.phi_deriv
        deriv2 := U.phi1_deriv
        phi1_continuous := U.phi1_continuous
        phi2_continuous := U.phi2_continuous }
    exact M.etaF_bound U.period_pos
  · exact Delta'.cont_m.div_const _
  · intro t
    exact div_nonneg (Delta'.m_nonneg t) hsqrt.le
  · intro t ht
    change Delta'.m t / Real.sqrt (1 - kap ^ 2) = 0
    rw [Delta'.m_stop t ht]
    simp

/-- Slice facts transport directly because `directSource` changes only the
source envelope, while the carrier recost preserves `T` and `eta`. -/
def directSlice
    (B : DirectBounds W S R G T hkap0 hkap1 C hP0 hC2 heta heta1 heta2)
    (F : AnalyticSuccessorSliceFacts
      (rawSource W S R G T hkap0 hkap1 C hP0)) :
    AnalyticSuccessorSliceFacts
      (directSource W S R G T hkap0 hkap1 C hP0 hC2 heta heta1 heta2 B) := by
  let U := rawSource W S R G T hkap0 hkap1 C hP0
  let D := directSource W S R G T hkap0 hkap1 C hP0
    hC2 heta heta1 heta2 B
  refine
    { periodUpper := F.periodUpper
      periodLower_pos := F.periodLower_pos
      period_lower := by simpa [D, U, directSource] using F.period_lower
      period_upper := by simpa [D, U, directSource] using F.period_upper
      etaFs := F.etaFs
      etaF_deriv := by simpa [D, U, directSource] using F.etaF_deriv
      etaFs_continuous := F.etaFs_continuous
      etaF_periodic := by simpa [D, U, directSource] using F.etaF_periodic
      rearNormal_c2 := by simpa [D, U, directSource] using F.rearNormal_c2
      normal_stopped := ?_
      markingLower := F.markingLower
      markingUpper := F.markingUpper
      marking_increment := by
        simpa [D, U, directSource] using F.marking_increment
      markingLower_pos := F.markingLower_pos
      marking_lower := by
        simpa [D, U, directSource, carrier,
          CanonicalNormalPathRecost.recost] using F.marking_lower
      markingUpper_nonnegative := F.markingUpper_nonnegative
      marking_upper := by
        simpa [D, U, directSource, carrier,
          CanonicalNormalPathRecost.recost] using F.marking_upper
      marked_bdd0 := ?_
      marked_bdd1 := ?_ }
  · intro t ht
    have ht' : t ∉ Ioo (0 : ℝ) W.Delta.T := by
      simpa [carrier, CanonicalNormalPathRecost.recost] using ht
    simpa [D, U, directSource] using F.normal_stopped t ht'
  · intro t
    simpa [D, directSource, carrier, CanonicalNormalPathRecost.recost] using
      F.marked_bdd0 t
  · intro t
    simpa [D, directSource, carrier, CanonicalNormalPathRecost.recost] using
      F.marked_bdd1 t

def directAnalyticSuccessor
    (B : DirectBounds W S R G T hkap0 hkap1 C hP0 hC2 heta heta1 heta2)
    (F : AnalyticSuccessorSliceFacts
      (rawSource W S R G T hkap0 hkap1 C hP0)) :
    AnalyticSuccessor (carrier W hC2 heta heta1 heta2) A
      P0Next kap khatNext QmaxNext :=
  AnalyticSuccessor.exact
    (directSource W S R G T hkap0 hkap1 C hP0 hC2 heta heta1 heta2 B)
    (directSlice W S R G T hkap0 hkap1 C hP0 hC2 heta heta1 heta2 B F)

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
