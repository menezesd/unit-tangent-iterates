import UnitTangentIterates.ConfiguredRecursiveEdgeNonaffineChosenMajorSplitHistory

/-! # Structural extension of nonaffine Jacobian ancestry -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeNonaffineAncestryExtension

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeNonaffineChosenMajorSplitHistory

variable {MA NA Etotal Dtarget K0 K1 K2 : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ Etotal Dtarget}

/-- Transport a link along equality of the two component entries it uses. -/
def NonaffineChosenLink.castComponents
    {V V' : ℕ → Components} {j : ℕ}
    (L : NonaffineChosenLink O V j)
    (hsource : V' j = V j) (htarget : V' (j + 1) = V (j + 1)) :
    NonaffineChosenLink O V' j where
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
  epsPrev_le := L.epsPrev_le
  epsCur_le := L.epsCur_le
  source_eq := hsource.trans L.source_eq
  target_eq := htarget.trans L.target_eq
  rawTransition := L.rawTransition

variable {p q p' q' : Data} {Gamma : NormalPath p q}
  {Gamma' : NormalPath p' q'} {depth : ℕ} {d : ℝ}

/-- Keep the established chain through `depth` and use the new target at all
later indices.  Only `depth + 1` is observable in the appended ancestry. -/
def extendV (H : Ancestry O Gamma depth d) (target : Components) (
    i : ℕ) : Components :=
  if i ≤ depth then H.V i else target

@[simp] theorem extendV_of_le
    (H : Ancestry O Gamma depth d) (target : Components)
    {i : ℕ} (hi : i ≤ depth) :
    extendV H target i = H.V i := by
  simp [extendV, hi]

@[simp] theorem extendV_succ
    (H : Ancestry O Gamma depth d) (target : Components) :
    extendV H target (depth + 1) = target := by
  simp [extendV]

/-- Append one nonaffine link, preserving all previous links by component
transport and installing its target component at the new endpoint. -/
def Ancestry.snoc
    (H : Ancestry O Gamma depth d) (target : Components)
    (htarget : target.Nonnegative)
    (L : NonaffineChosenLink O (extendV H target) depth) :
    Ancestry O Gamma' (depth + 1) d where
  V := extendV H target
  baseJ := H.baseJ
  baseP := H.baseP
  baseEta := H.baseEta
  base_eq := by simpa using H.base_eq
  d_nonnegative := H.d_nonnegative
  components_nonnegative := by
    intro i hi
    by_cases hle : i ≤ depth
    · rw [extendV_of_le H target hle]
      exact H.components_nonnegative i hle
    · have hieq : i = depth + 1 := by omega
      subst i
      simpa using htarget
  initial_le := by simpa using H.initial_le
  links := by
    intro i hi
    by_cases hlt : i < depth
    · apply NonaffineChosenLink.castComponents (H.links i hlt)
      · exact extendV_of_le H target (Nat.le_of_lt hlt)
      · exact extendV_of_le H target (Nat.succ_le_of_lt hlt)
    · have hle : i ≤ depth := by omega
      have hge : depth ≤ i := Nat.le_of_not_gt hlt
      have : i = depth := Nat.le_antisymm hle hge
      subst i
      exact L

end ConfiguredRecursiveEdgeNonaffineAncestryExtension
