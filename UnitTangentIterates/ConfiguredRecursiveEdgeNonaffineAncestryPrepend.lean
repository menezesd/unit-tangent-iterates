import UnitTangentIterates.ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
import UnitTangentIterates.ConfiguredRecursiveEdgeGaugeMajorantShift

/-! # Prepending a diagonal nonaffine ancestry

An ancestry over `O.shiftOutput 1` uses `O.major (j+1)` at its local index
`j`.  It can therefore be placed after a new index-zero link over `O` without
casting either output record or any analytic source.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeNonaffineAncestryPrepend

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
  ConfiguredRecursiveEdgeNonaffineChosenMajorSplitHistory

variable {MA NA Etotal Dtarget : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {O : Output RJ Etotal Dtarget}

/-- Add one component before an existing component chain. -/
def prependV {p q : Data} {Gamma : NormalPath p q} {depth : ℕ} {d : ℝ}
    (H : Ancestry (O.shiftOutput 1) Gamma depth d)
    (head : Components) : ℕ → Components
  | 0 => head
  | j + 1 => H.V j

@[simp] theorem prependV_zero
    {p q : Data} {Gamma : NormalPath p q} {depth : ℕ} {d : ℝ}
    (H : Ancestry (O.shiftOutput 1) Gamma depth d)
    (head : Components) : prependV H head 0 = head := rfl

@[simp] theorem prependV_succ
    {p q : Data} {Gamma : NormalPath p q} {depth : ℕ} {d : ℝ}
    (H : Ancestry (O.shiftOutput 1) Gamma depth d)
    (head : Components) (j : ℕ) : prependV H head (j + 1) = H.V j := rfl

/-- Reindex one retained link from the one-row shifted output. -/
def NonaffineChosenLink.unshiftSucc
    {V : ℕ → Components} {j : ℕ}
    (L : NonaffineChosenLink (O.shiftOutput 1) V j) :
    NonaffineChosenLink O (fun i => if i = 0 then V 0 else V (i - 1))
      (j + 1) where
  p := L.p
  q := L.q
  a := L.a
  b := L.b
  Gamma := L.Gamma
  P0 := L.P0
  khat := L.khat
  Qmax := L.Qmax
  source := L.source
  applied := L.applied
  chosen := L.chosen
  sourceSlice := L.sourceSlice
  P0Next := L.P0Next
  khatNext := L.khatNext
  QmaxNext := L.QmaxNext
  targetPath := L.targetPath
  target := L.target
  targetSlice := L.targetSlice
  target_eta_eq := L.target_eta_eq
  target_period_eq := L.target_period_eq
  target_phi1_eq := L.target_phi1_eq
  epsPrev := L.epsPrev
  epsCur := L.epsCur
  sourceJets := L.sourceJets
  chosenJets := L.chosenJets
  epsPrev_le := by simpa [Nat.add_comm] using L.epsPrev_le
  epsCur_le := by simpa [Nat.add_assoc, Nat.add_comm] using L.epsCur_le
  source_eq := by
    simpa [Nat.succ_ne_zero] using L.source_eq
  target_eq := by
    simpa [Nat.succ_ne_zero, Nat.add_assoc] using L.target_eq
  rawTransition := L.rawTransition

/-- Prepend a genuine index-zero link and retain the complete old ancestry at
indices `1,...,depth+1`.  The terminal component is unchanged. -/
def Ancestry.prepend
    {p q p' q' : Data} {Gamma : NormalPath p q} {Gamma' : NormalPath p' q'}
    {depth : ℕ} {d : ℝ}
    (H : Ancestry (O.shiftOutput 1) Gamma depth d)
    (baseJ : ℝ → ℝ → ℝ) (baseP : ℝ → ℝ) (baseEta : ℝ → ℝ → ℝ)
    (head : Components)
    (head_eq : head =
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison.markedPhysicalComponents
        baseJ baseP baseEta)
    (head_nonnegative : head.Nonnegative)
    (head_le : head.w ≤ d ∧ head.s0 ≤ d ∧ head.s1 ≤ d ∧ head.s2 ≤ d)
    (first : NonaffineChosenLink O (prependV H head) 0) :
    Ancestry O Gamma' (depth + 1) d where
  V := prependV H head
  baseJ := baseJ
  baseP := baseP
  baseEta := baseEta
  base_eq := head_eq
  d_nonnegative := H.d_nonnegative
  components_nonnegative := by
    intro i hi
    cases i with
    | zero => exact head_nonnegative
    | succ i =>
        rw [prependV_succ]
        exact H.components_nonnegative i (by omega)
  initial_le := head_le
  links := by
    intro i hi
    cases i with
    | zero => exact first
    | succ i =>
        have hiold : i < depth := by omega
        let L :=
          ConfiguredRecursiveEdgeNonaffineAncestryPrepend.NonaffineChosenLink.unshiftSucc
            (O := O) (H.links i hiold)
        exact
          { L with
            source_eq := by simpa [L, prependV] using L.source_eq
            target_eq := by simpa [L, prependV] using L.target_eq }

/-- Concrete endpoint wrapper for `Ancestry.prepend`. -/
def ConcreteAncestry.prepend
    {p q p' q' : Data} {Gamma : NormalPath p q} {Gamma' : NormalPath p' q'}
    {depth : ℕ} {d : ℝ}
    (H : ConcreteAncestry (O := O.shiftOutput 1) Gamma depth d)
    (baseJ : ℝ → ℝ → ℝ) (baseP : ℝ → ℝ) (baseEta : ℝ → ℝ → ℝ)
    (head : Components)
    (head_eq : head =
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison.markedPhysicalComponents
        baseJ baseP baseEta)
    (head_nonnegative : head.Nonnegative)
    (head_le : head.w ≤ 2 * d ∧ head.s0 ≤ 2 * d ∧
      head.s1 ≤ 2 * d ∧ head.s2 ≤ 2 * d)
    (heta : Gamma'.eta = Gamma.eta)
    (first : NonaffineChosenLink O (prependV H.ancestry head) 0) :
    ConcreteAncestry (O := O) Gamma' (depth + 1) d where
  ancestry := Ancestry.prepend H.ancestry baseJ baseP baseEta head head_eq
    head_nonnegative head_le first
  terminalJ := H.terminalJ
  terminalP := H.terminalP
  terminal_eq := by
    simpa [Ancestry.prepend, prependV, heta] using H.terminal_eq

end ConfiguredRecursiveEdgeNonaffineAncestryPrepend
