import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierScalar
import UnitTangentIterates.ConfiguredRecursiveEdgeWeightedBaseGaugeHistoryMajor

/-! # Multiplier closing with the finite-history jet tail retained -/

noncomputable section

namespace ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing

open ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput
  ConfiguredRecursiveEdgeRecostMultiplierScalar
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeWeightedBaseGaugeHistoryMajor
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteHistoryMajorBudget

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    choice.MA0 choice.NA0}
  {O : GaugeOutput J}

/-- The existing recost closing output plus the one further scalar tail needed
by constant finite histories. -/
structure Output (R : RecostClosingOutput J O) where
  historyShift : ℕ
  toClosing : RecostClosingOutput J O
  totalShift_eq : toClosing.totalShift = R.totalShift + historyShift
  jet_half : ∀ q,
    combinedHistoryMajor toClosing.data J.scalar.Mend
      distortionTotal physicalTransitionCeilings.C0
      physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
      (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2) q ≤ 1 / 2
  jet_total : ∀ q,
    (q + 1 : ℕ) *
      combinedHistoryMajor toClosing.data J.scalar.Mend
        distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
          physicalTransitionCeilings.C1 physicalTransitionCeilings.C2) q ≤
      distortionTotal

theorem nonempty (R : RecostClosingOutput J O) : Nonempty (Output R) := by
  obtain ⟨N, hN⟩ := exists_shift_combinedHistoryMajor_bounds R.data
    (MA := choice.MA0) (NA := choice.NA0) (M := J.scalar.Mend)
    (E0 := distortionTotal) (C0 := physicalTransitionCeilings.C0)
    (C1 := physicalTransitionCeilings.C1)
    (C2 := physicalTransitionCeilings.C2)
    (Dtarget := configuredSourceMassTarget distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2)
    choice.MA0_nonnegative choice.NA0_nonnegative J.scalar.Mend_positive.le
    (configuredSourceMassTarget_nonnegative distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2)
    distortionTotal_pos
  let P := R.preShift + R.large.N + N
  obtain ⟨L⟩ := ConfiguredRecursiveEdgeFullRecostMetricDiagonal.exists_fullRecostMetricOutputAfter
    O.data P (E0 := distortionTotal) (C0 := physicalTransitionCeilings.C0)
    (C1 := physicalTransitionCeilings.C1)
    (C2 := physicalTransitionCeilings.C2)
    choice.MA0_nonnegative choice.NA0_nonnegative J.scalar.Mend_positive.le
    J.scalar.Cw_nonnegative
  let Rc : RecostClosingOutput J O := {
    preShift := P
    large := L
    mass_small := fun q => by
      simpa [P, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        R.mass_small (N + L.N + q) }
  have hmajor (q : ℕ) :
      combinedHistoryMajor Rc.data J.scalar.Mend distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2
          (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
            physicalTransitionCeilings.C1 physicalTransitionCeilings.C2) q =
        combinedHistoryMajor (shift R.data N) J.scalar.Mend distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2
          (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
            physicalTransitionCeilings.C1 physicalTransitionCeilings.C2) (L.N + q) := by
    change
      combinedHistoryMajor
          (shift (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data J)
            Rc.totalShift) J.scalar.Mend distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2
          (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
            physicalTransitionCeilings.C1 physicalTransitionCeilings.C2) q =
        combinedHistoryMajor
          (shift
            (shift (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data J)
              R.totalShift) N) J.scalar.Mend distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2
          (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
            physicalTransitionCeilings.C1 physicalTransitionCeilings.C2) (L.N + q)
    simp only [combinedHistoryMajor_shift]
    congr 1
    simp [Rc, P, RecostClosingOutput.totalShift, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  exact ⟨{
    historyShift := N + L.N
    toClosing := Rc
    totalShift_eq := by
      simp [Rc, P, RecostClosingOutput.totalShift, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    jet_half := fun q => by rw [hmajor]; exact (hN (L.N + q)).1
    jet_total := fun q => by
      rw [hmajor]
      have hnon := combinedHistoryMajor_nonnegative (shift R.data N)
        J.scalar.Mend distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
          physicalTransitionCeilings.C1 physicalTransitionCeilings.C2)
        (configuredSourceMassTarget_nonnegative distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2) (L.N + q)
      have hfactor : (q + 1 : ℝ) ≤ (L.N + q + 1 : ℕ) := by
        exact_mod_cast Nat.add_le_add_right (Nat.le_add_left q L.N) 1
      convert (mul_le_mul_of_nonneg_right hfactor hnon).trans
        (hN (L.N + q)).2 using 1 <;> norm_num }⟩

namespace Output

def totalShift {R : RecostClosingOutput J O} (H : Output R) : ℕ :=
  H.toClosing.totalShift

def data {R : RecostClosingOutput J O} (H : Output R) :=
  H.toClosing.data

@[simp] theorem totalShift_eq_base {R : RecostClosingOutput J O} (H : Output R) :
    H.totalShift = R.totalShift + H.historyShift := H.totalShift_eq

@[simp] theorem toClosing_totalShift {R : RecostClosingOutput J O} (H : Output R) :
    H.toClosing.totalShift = H.totalShift := rfl

@[simp] theorem toClosing_data {R : RecostClosingOutput J O} (H : Output R) :
    H.toClosing.data = H.data := rfl

def epsDiag {R : RecostClosingOutput J O} (H : Output R) (q : ℕ) : ℝ :=
  combinedHistoryMajor H.data J.scalar.Mend distortionTotal
    physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
    physicalTransitionCeilings.C2
    (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
      physicalTransitionCeilings.C1 physicalTransitionCeilings.C2) q

theorem epsDiag_nonnegative {R : RecostClosingOutput J O}
    (H : Output R) (q : ℕ) : 0 ≤ H.epsDiag q :=
  combinedHistoryMajor_nonnegative H.data J.scalar.Mend distortionTotal
    physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
    physicalTransitionCeilings.C2
    (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
      physicalTransitionCeilings.C1 physicalTransitionCeilings.C2)
    (configuredSourceMassTarget_nonnegative distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2) q

theorem recostJetMajor_le_epsDiag {R : RecostClosingOutput J O}
    (H : Output R) (q : ℕ) :
    recostJetMajor H.data J.scalar.Mend distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 q ≤ H.epsDiag q := by
  exact le_add_of_nonneg_right (combinedGaugeMajor_nonnegative H.data
    J.scalar.Mend _ (configuredSourceMassTarget_nonnegative distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2) q)

theorem baseGaugeMajor_le_epsDiag {R : RecostClosingOutput J O}
    (H : Output R) (q : ℕ) :
    combinedGaugeMajor H.data J.scalar.Mend
      (configuredSourceMassTarget distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2) q ≤
      H.epsDiag q := by
  exact le_add_of_nonneg_left (recostJetMajor_nonnegative H.data
    J.scalar.Mend distortionTotal physicalTransitionCeilings.C0
    physicalTransitionCeilings.C1 physicalTransitionCeilings.C2 q)

theorem epsDiag_half {R : RecostClosingOutput J O}
    (H : Output R) (q : ℕ) : H.epsDiag q ≤ 1 / 2 := H.jet_half q

theorem epsDiag_total {R : RecostClosingOutput J O}
    (H : Output R) (q : ℕ) :
    (q + 1 : ℕ) * H.epsDiag q ≤ distortionTotal := H.jet_total q

theorem epsDiag_quarter {R : RecostClosingOutput J O}
    (H : Output R) (q : ℕ) : H.epsDiag q ≤ 1 / 4 := by
  have hfactor : (1 : ℝ) ≤ (q + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
  have htotal : H.epsDiag q ≤ distortionTotal := by
    simpa using (mul_le_mul_of_nonneg_right hfactor (H.epsDiag_nonnegative q)).trans
      (H.epsDiag_total q)
  exact htotal.trans (by
    have h :=
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth
    linarith)

/-- The abstract history major for any depth `k` on total diagonal `q`. -/
def historyBudget {R : RecostClosingOutput J O}
    (H : Output R) (q k : ℕ) (hk : k ≤ q) : MajorBudget distortionTotal :=
  MajorBudget.ofSegment k (H.epsDiag_nonnegative q) (H.epsDiag_half q) <| by
    have hcast : (k + 1 : ℝ) ≤ (q + 1 : ℕ) := by
      exact_mod_cast Nat.add_le_add_right hk 1
    have Htotal := (mul_le_mul_of_nonneg_right hcast (H.epsDiag_nonnegative q)).trans
      (H.epsDiag_total q)
    convert Htotal using 1 <;> norm_num

@[simp] theorem historyBudget_major_of_le
    {R : RecostClosingOutput J O} (H : Output R)
    (q k j : ℕ) (hk : k ≤ q) (hj : j ≤ k) :
    (H.historyBudget q k hk).major j = H.epsDiag q :=
  FiniteDiagonalSegmentMajor.segmentMajor_eq hj

/-- Existing metric errors restricted to the further tail. -/
def error {R : RecostClosingOutput J O}
    (H : Output R) (n k : ℕ) : ℝ :=
  H.toClosing.error n k

theorem error_nonnegative {R : RecostClosingOutput J O} (H : Output R) :
    ∀ n k, 0 ≤ H.error n k := H.toClosing.error_nonnegative

theorem error_summable {R : RecostClosingOutput J O} (H : Output R) :
    ∀ n, Summable (H.error n) := H.toClosing.error_summable

/-- The multiplier source-mass bound survives the additional tail. -/
theorem mass_small {R : RecostClosingOutput J O}
    (H : Output R) (q : ℕ) :
    multiplierRecostSourceAllowance H.data distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 q ≤ 1 := by
  exact mass_small_final H.toClosing q

end Output

end ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
