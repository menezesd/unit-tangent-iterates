import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly
import UnitTangentIterates.TerminalMarkingCompactness

/-!
# Uniform Harnack closure from near-identity presented markings

For a fixed triangular row, the terminal marking at depth `k` relates the
physical presentation at that same depth to the selected marked endpoint.  It
is not the composition of all earlier terminal markings.  Therefore a common
near-identity tail gives fixed derivative constants directly:

`|dpsi - 1| <= eps <= 1/2` implies `1/2 <= dpsi <= 3/2`.

Together with `|ddpsi| <= eps`, this is precisely the rowwise compactness
interface of `TerminalMarkingCompactness`.  Summability is needed upstream to
choose the common half-tail, not to form a product of marking derivatives.
-/

noncomputable section

open Filter Set Topology MarkedSpace

namespace FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure

open FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  GaugeRearFamilyVariableTerminal

/-- Near-identity data for all physical/marked terminal pairs. -/
structure Bounds (base rear : ℕ → ℕ → Data) (eps : ℕ → ℕ → ℝ) where
  eps_nonnegative : ∀ n k, 0 ≤ eps n k
  eps_le_half : ∀ n k, eps n k ≤ 1 / 2
  marking : ∀ n k, OrientedReparametrization (base n k) (rear n k)
    (1 - eps n k) (1 + eps n k)
  basepoint : ∀ n k, (marking n k).psi 0 = 0
  psi_hasDerivAt : ∀ n k u,
    HasDerivAt (marking n k).psi ((marking n k).dpsi u) u
  ddpsi : ℕ → ℕ → ℝ → ℝ
  dpsi_hasDerivAt : ∀ n k u,
    HasDerivAt (marking n k).dpsi (ddpsi n k u) u
  ddpsi_bound : ∀ n k u, |ddpsi n k u| ≤ eps n k

/-- A presented sliced core whose provider retains the exact near-identity
jets of every actual selected row. -/
structure Construction
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (jetError : ℕ → ℕ → ℝ) where
  current0 : ℕ → Data
  base : CorrelatedColumn Q current0 e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2
  baseSlice : SlicedCorrelatedColumn base
  base_eq : ∀ n, base.column.step.next n = Q n
  provider : PresentedNearIdentitySlicedProvider Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2 jetError

namespace Construction

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
  {jetError : ℕ → ℕ → ℝ}

def core
    (A : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 jetError) :
    ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 where
  current0 := A.current0
  base := A.base
  baseSlice := A.baseSlice
  base_eq := A.base_eq
  provider := A.provider.slicedProvider

/-- Physical terminal presentations paired with the actual marked columns.
Depth zero is the configured base marking. -/
def physicalRows
    (A : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 jetError) (n : ℕ) : ℕ → Data
  | 0 => Q n
  | k + 1 =>
      ((A.provider.rows (A.core.state k).column (A.core.state k).sliced).row n).presented

/-- The jet error belonging to the marking at a displayed column depth. -/
def displayedJetError
    (_A : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 jetError) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => jetError n (k + 1)

/-- The exact actual selected rows construct the abstract uniform
near-identity marking bounds without any choice of unrelated terminals. -/
def markingBounds
    (A : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 jetError)
    (hhalf : ∀ n k, jetError n (k + 1) ≤ 1 / 2) :
    Bounds A.physicalRows A.core.columns A.displayedJetError where
  eps_nonnegative := by
    intro n k
    cases k with
    | zero => simp [displayedJetError]
    | succ k =>
        simpa [displayedJetError, A.core.state_depth k] using
          (A.provider.nearIdentity (A.core.state k).column
            (A.core.state k).sliced n).eps_nonnegative
  eps_le_half := by
    intro n k
    cases k with
    | zero => norm_num [displayedJetError]
    | succ k => exact hhalf n k
  marking := by
    intro n k
    cases k with
    | zero =>
        exact
          { psi := fun u => u
            dpsi := fun _ => 1
            position := fun _ => by
              simp [physicalRows, ConstructionCore.columns_zero]
            velocity := fun _ => by
              simp [physicalRows, ConstructionCore.columns_zero]
            translate := fun u => by ring
            lower := fun _ => by simp [displayedJetError]
            upper := fun _ => by simp [displayedJetError] }
    | succ k =>
        let R := (A.provider.rows (A.core.state k).column
          (A.core.state k).sliced).row n
        let J := A.provider.nearIdentity (A.core.state k).column
          (A.core.state k).sliced n
        have hrear : A.core.columns n (k + 1) = R.output.jets.rear := by
          change ((A.core.state (k + 1)).column.column.step.next n) = _
          rw [A.core.state_succ k]
          rfl
        rw [hrear]
        have hdepth : (A.core.state k).depth = k := A.core.state_depth k
        exact
          { psi := R.output.marking.psi
            dpsi := R.output.marking.dpsi
            position := R.output.marking.position
            velocity := R.output.marking.velocity
            translate := R.output.marking.translate
            lower := fun u => by
              have h := neg_le_of_abs_le (J.dpsi u)
              have h' : -jetError n (k + 1) ≤
                  R.output.marking.dpsi u - 1 := by
                simpa [hdepth] using h
              change 1 - jetError n (k + 1) ≤ R.output.marking.dpsi u
              linarith
            upper := fun u => by
              have h := le_of_abs_le (J.dpsi u)
              have h' : R.output.marking.dpsi u - 1 ≤
                  jetError n (k + 1) := by
                simpa [hdepth] using h
              change R.output.marking.dpsi u ≤ 1 + jetError n (k + 1)
              linarith }
  basepoint := by
    intro n k
    cases k with
    | zero => rfl
    | succ k =>
        exact ((A.provider.rows (A.core.state k).column
          (A.core.state k).sliced).row n).output.psi_zero
  psi_hasDerivAt := by
    intro n k u
    cases k with
    | zero => exact hasDerivAt_id u
    | succ k =>
        exact ((A.provider.rows (A.core.state k).column
          (A.core.state k).sliced).row n).output.psi_deriv u
  ddpsi := fun n k => match k with
    | 0 => fun _ => 0
    | k + 1 => ((A.provider.rows (A.core.state k).column
        (A.core.state k).sliced).row n).output.ddpsi
  dpsi_hasDerivAt := by
    intro n k u
    cases k with
    | zero => simpa using (hasDerivAt_const (x := u) (c := (1 : ℝ)))
    | succ k =>
        exact ((A.provider.rows (A.core.state k).column
          (A.core.state k).sliced).row n).output.dpsi_deriv u
  ddpsi_bound := by
    intro n k u
    cases k with
    | zero => simp [displayedJetError]
    | succ k =>
        simpa [displayedJetError, A.core.state_depth k] using
          (A.provider.nearIdentity (A.core.state k).column
            (A.core.state k).sliced n).ddpsi u

end Construction

namespace Bounds

variable {base rear : ℕ → ℕ → Data} {eps : ℕ → ℕ → ℝ}

/-- Forget the varying sharper bounds and retain fixed bounds valid throughout
the common scalar half-tail. -/
def fixedMarking (B : Bounds base rear eps) (n k : ℕ) :
    OrientedReparametrization (base n k) (rear n k) (1 / 2) (3 / 2) where
  psi := (B.marking n k).psi
  dpsi := (B.marking n k).dpsi
  position := (B.marking n k).position
  velocity := (B.marking n k).velocity
  translate := (B.marking n k).translate
  lower u := by
    have h := (B.marking n k).lower u
    linarith [B.eps_le_half n k]
  upper u := by
    have h := (B.marking n k).upper u
    linarith [B.eps_le_half n k]

/-- The exact compactness package consumed by terminal Harnack closure. -/
def rowwiseMarkingBounds (B : Bounds base rear eps) :
    RowwiseNormalizedMarkingBounds base rear where
  lambda := fun _ => 1 / 2
  Lambda := fun _ => 3 / 2
  secondBound := fun _ => 1 / 2
  lambda_pos := fun _ => by norm_num
  secondBound_nonneg := fun _ => by norm_num
  reparametrization := B.fixedMarking
  basepoint := B.basepoint
  psi_hasDerivAt := B.psi_hasDerivAt
  ddpsi := B.ddpsi
  dpsi_hasDerivAt := B.dpsi_hasDerivAt
  ddpsi_bound := fun n k u =>
    (B.ddpsi_bound n k u).trans (B.eps_le_half n k)

/-- Near-identity markings and finite physical pullback kinematics give the
uniform limit-Harnack callback required by the presented sliced assembly. -/
def harnackClosed
    (B : Bounds base rear eps)
    {X : ℕ → Data} {kh cb db : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (htube : ∀ n k, IsTubeMember cb 0 db (base n k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh base)
    (hbaseLimit : ∀ n, Tendsto (base n) atTop (nhds (X n))) :
    ∀ n x, Tendsto (rear n) atTop (nhds x) →
      (∀ k, VariableMarkedTube.ArclengthHarnackCertificate (rear n k)) →
      VariableMarkedTube.ArclengthHarnackCertificate x := by
  let compact := B.rowwiseMarkingBounds
  let limitReparam : ∀ n x, Tendsto (rear n) atTop (nhds x) →
      LimitOrientedReparametrization (X n) x := by
    intro n x hx
    exact limitOrientedReparametrization_of_rowwise_bounds
      (compact.lambda_pos n) (compact.secondBound_nonneg n)
      (compact.reparametrization n) (hbaseLimit n) hx
      (compact.basepoint n) (compact.psi_hasDerivAt n)
      (compact.ddpsi n) (compact.dpsi_hasDerivAt n)
      (compact.ddpsi_bound n)
  exact harnackClosed_of_finitePullbackLimit hkh0 hkh1 hcb hdb
    htube finite hbaseLimit limitReparam

/-- Stronger paper-facing closure retaining oriented arclength
representatives, obtained from the same fixed near-identity bounds. -/
def orientedRepresentativeClosed
    (B : Bounds base rear eps)
    {X : ℕ → Data} {kh cb db : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (htube : ∀ n k, IsTubeMember cb 0 db (base n k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh base)
    (hbaseLimit : ∀ n, Tendsto (base n) atTop (nhds (X n))) :
    ∀ n x, Tendsto (rear n) atTop (nhds x) →
      VariableMarkedTube.OrientedArclengthRepresentative x := by
  let compact := B.rowwiseMarkingBounds
  let limitReparam : ∀ n x, Tendsto (rear n) atTop (nhds x) →
      LimitOrientedReparametrization (X n) x := by
    intro n x hx
    exact limitOrientedReparametrization_of_rowwise_bounds
      (compact.lambda_pos n) (compact.secondBound_nonneg n)
      (compact.reparametrization n) (hbaseLimit n) hx
      (compact.basepoint n) (compact.psi_hasDerivAt n)
      (compact.ddpsi n) (compact.dpsi_hasDerivAt n)
      (compact.ddpsi_bound n)
  exact orientedRepresentativeClosed_of_finitePullbackLimit
    hkh0 hkh1 hcb hdb htube finite hbaseLimit limitReparam

/-- One-call construction of the presented cap family.  The scalar inputs are
exactly nonnegativity and summability of the configured row error; all uniform
Harnack content comes from the fixed near-identity bounds and physical
pullback closure above. -/
def capFamily
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal khRow Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      khRow Qmax a MA NA K0 K1 K2}
    {X : ℕ → Data} {kh cb db : ℝ}
    (B : Bounds base F.columns eps)
    (error_nonnegative : ∀ n k, 0 ≤ e n k)
    (error_summable : ∀ n, Summable (e n))
    (variableTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (F.columns n k))
    (finiteHarnack : ∀ n k,
      VariableMarkedTube.ArclengthHarnackCertificate (F.columns n k))
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (physicalTube : ∀ n k, IsTubeMember cb 0 db (base n k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh base)
    (physicalLimit : ∀ n, Tendsto (base n) atTop (nhds (X n))) :
    CapFamily F :=
  CapFamily.ofScalarAndHarnackClosure
    error_nonnegative error_summable variableTube finiteHarnack
    (B.harnackClosed hkh0 hkh1 hcb hdb physicalTube finite physicalLimit)

end Bounds

end FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure
