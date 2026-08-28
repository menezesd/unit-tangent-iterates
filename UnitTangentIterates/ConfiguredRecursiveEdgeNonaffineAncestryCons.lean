import UnitTangentIterates.ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
import UnitTangentIterates.ConfiguredRecursiveEdgeGaugeMajorantShift

/-! # Prepending a row-local link to concrete nonaffine ancestry -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeNonaffineAncestryCons

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
  ConfiguredRecursiveEdgeNonaffineChosenMajorSplitHistory

variable {MA NA Etotal Dtarget : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {O : Output RJ Etotal Dtarget}

/-- Prepend one component to a finite ancestry vector. -/
def consV (head : Components) (V : ℕ → Components) : ℕ → Components
  | 0 => head
  | j + 1 => V j

@[simp] theorem consV_zero (head : Components) (V : ℕ → Components) :
    consV head V 0 = head := rfl

@[simp] theorem consV_succ (head : Components) (V : ℕ → Components)
    (j : ℕ) : consV head V (j + 1) = V j := rfl

/-- Reindex an old tail link by one place.  The analytic source, chosen path,
and transition are unchanged.  Only the component indices and the two local
major indices change; `shiftOutput_major` proves those bounds definitionally
from the common unshifted output. -/
def NonaffineChosenLink.reindexShift
    {V : ℕ → Components} {n j : ℕ}
    (L : NonaffineChosenLink (O.shiftOutput (n + 1)) V j)
    (head : Components) :
    NonaffineChosenLink (O.shiftOutput n) (consV head V) (j + 1) where
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
  epsPrev_le := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using L.epsPrev_le
  epsCur_le := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using L.epsCur_le
  source_eq := by simpa using L.source_eq
  target_eq := by simpa [Nat.add_assoc] using L.target_eq
  rawTransition := L.rawTransition

namespace NonaffineChosenLink

variable {V : ℕ → Components} {n j : ℕ}
  (L : NonaffineChosenLink (O.shiftOutput (n + 1)) V j)
  (head : Components)

@[simp] theorem reindexShift_source :
    (L.reindexShift head).source = L.source := rfl

@[simp] theorem reindexShift_target :
    (L.reindexShift head).target = L.target := rfl

@[simp] theorem reindexShift_epsPrev :
    (L.reindexShift head).epsPrev = L.epsPrev := rfl

@[simp] theorem reindexShift_epsCur :
    (L.reindexShift head).epsCur = L.epsCur := rfl

@[simp] theorem reindexShift_Gamma :
    (L.reindexShift head).Gamma = L.Gamma := rfl

@[simp] theorem reindexShift_targetPath :
    (L.reindexShift head).targetPath = L.targetPath := rfl

end NonaffineChosenLink

variable {p q : Data} {Gamma : NormalPath p q}
  {depth n : ℕ} {oldDefect newDefect : ℝ}

/-- Prepend a new row-local link to ancestry already based at the next shifted
output.  The old link at `j` becomes the new link at `j+1`; the terminal path
and terminal component are unchanged. -/
def ConcreteAncestry.cons
    (H : ConcreteAncestry (O := O.shiftOutput (n + 1))
      Gamma depth oldDefect)
    (head : Components)
    (baseJ : ℝ → ℝ → ℝ) (baseP : ℝ → ℝ)
    (baseEta : ℝ → ℝ → ℝ)
    (hbase : head = markedPhysicalComponents baseJ baseP baseEta)
    (hnewDefect : 0 ≤ newDefect)
    (hhead : head.Nonnegative)
    (hinitial : head.w ≤ 2 * newDefect ∧
      head.s0 ≤ 2 * newDefect ∧ head.s1 ≤ 2 * newDefect ∧
      head.s2 ≤ 2 * newDefect)
    (L : NonaffineChosenLink (O.shiftOutput n)
      (consV head H.ancestry.V) 0) :
    ConcreteAncestry (O := O.shiftOutput n) Gamma (depth + 1) newDefect where
  ancestry :=
    { V := consV head H.ancestry.V
      baseJ := baseJ
      baseP := baseP
      baseEta := baseEta
      base_eq := hbase
      d_nonnegative := mul_nonneg (by norm_num) hnewDefect
      components_nonnegative := by
        intro i hi
        cases i with
        | zero => exact hhead
        | succ j =>
            rw [consV_succ]
            exact H.ancestry.components_nonnegative j (by omega)
      initial_le := hinitial
      links := by
        intro i hi
        cases i with
        | zero => exact L
        | succ j =>
            exact (H.ancestry.links j (by omega)).reindexShift head }
  terminalJ := H.terminalJ
  terminalP := H.terminalP
  terminal_eq := by
    simpa using H.terminal_eq

namespace ConcreteAncestry

variable
  (H : ConcreteAncestry (O := O.shiftOutput (n + 1))
    Gamma depth oldDefect)
  (head : Components)
  (baseJ : ℝ → ℝ → ℝ) (baseP : ℝ → ℝ)
  (baseEta : ℝ → ℝ → ℝ)
  (hbase : head = markedPhysicalComponents baseJ baseP baseEta)
  (hnewDefect : 0 ≤ newDefect)
  (hhead : head.Nonnegative)
  (hinitial : head.w ≤ 2 * newDefect ∧
    head.s0 ≤ 2 * newDefect ∧ head.s1 ≤ 2 * newDefect ∧
    head.s2 ≤ 2 * newDefect)
  (L : NonaffineChosenLink (O.shiftOutput n)
    (consV head H.ancestry.V) 0)

private abbrev C := H.cons head baseJ baseP baseEta hbase hnewDefect
  hhead hinitial L

@[simp] theorem cons_V_zero : (C H head baseJ baseP baseEta hbase hnewDefect
    hhead hinitial L).ancestry.V 0 = head := rfl

@[simp] theorem cons_V_succ (j : ℕ) :
    (C H head baseJ baseP baseEta hbase hnewDefect hhead hinitial L).ancestry.V
      (j + 1) = H.ancestry.V j := rfl

@[simp] theorem cons_baseJ :
    (C H head baseJ baseP baseEta hbase hnewDefect hhead hinitial L).ancestry.baseJ =
      baseJ := rfl

@[simp] theorem cons_baseP :
    (C H head baseJ baseP baseEta hbase hnewDefect hhead hinitial L).ancestry.baseP =
      baseP := rfl

@[simp] theorem cons_baseEta :
    (C H head baseJ baseP baseEta hbase hnewDefect hhead hinitial L).ancestry.baseEta =
      baseEta := rfl

@[simp] theorem cons_terminalJ :
    (C H head baseJ baseP baseEta hbase hnewDefect hhead hinitial L).terminalJ =
      H.terminalJ := rfl

@[simp] theorem cons_terminalP :
    (C H head baseJ baseP baseEta hbase hnewDefect hhead hinitial L).terminalP =
      H.terminalP := rfl

@[simp] theorem cons_head_link :
    (C H head baseJ baseP baseEta hbase hnewDefect hhead hinitial L).ancestry.links
      0 (by omega) = L := rfl

end ConcreteAncestry

end ConfiguredRecursiveEdgeNonaffineAncestryCons
