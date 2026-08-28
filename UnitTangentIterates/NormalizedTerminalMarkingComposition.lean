import UnitTangentIterates.GaugeRearFamilyRichTerminalStage

/-!
# Composition of normalized terminal markings

The gauge construction produces a new terminal marking at every recursive
depth.  This file retains the exact first and second spatial jets under
composition and packages their cumulative distortion along each finite
pullback row.
-/

noncomputable section

open Function MarkedSpace

namespace NormalizedTerminalMarkingComposition

open GaugeRearFamilyVariableTerminal GaugeRearFamilyRichTerminalStage

/-- A normalized positively oriented reparametrization with its second jet. -/
structure NormalizedC2Marking
    (base rear : Data) (lambda Lambda : ℝ) where
  lambda_pos : 0 < lambda
  marking : OrientedReparametrization base rear lambda Lambda
  ddpsi : ℝ → ℝ
  psi_deriv : ∀ u, HasDerivAt marking.psi (marking.dpsi u) u
  dpsi_deriv : ∀ u, HasDerivAt marking.dpsi (ddpsi u) u
  ddpsi_cont : Continuous ddpsi
  psi_zero : marking.psi 0 = 0

namespace NormalizedC2Marking

/-- The identity normalized marking. -/
def refl (p : Data) : NormalizedC2Marking p p 1 1 where
  lambda_pos := one_pos
  marking :=
    { psi := id
      dpsi := fun _ => 1
      position := fun _ => rfl
      velocity := fun u => by simp
      translate := fun u => by simp [id]
      lower := fun _ => le_rfl
      upper := fun _ => le_rfl }
  ddpsi := fun _ => 0
  psi_deriv := fun u => hasDerivAt_id u
  dpsi_deriv := fun u => hasDerivAt_const u 1
  ddpsi_cont := continuous_const
  psi_zero := rfl

/-- Exact C2 chain rule for two consecutive normalized markings. -/
def compose
    {p q r : Data} {lambda₁ Lambda₁ lambda₂ Lambda₂ : ℝ}
    (A : NormalizedC2Marking p q lambda₁ Lambda₁)
    (B : NormalizedC2Marking q r lambda₂ Lambda₂) :
    NormalizedC2Marking p r (lambda₁ * lambda₂) (Lambda₁ * Lambda₂) := by
  let psi : ℝ → ℝ := A.marking.psi ∘ B.marking.psi
  let dpsi : ℝ → ℝ := fun u =>
    B.marking.dpsi u * A.marking.dpsi (B.marking.psi u)
  let ddpsi : ℝ → ℝ := fun u =>
    A.ddpsi (B.marking.psi u) * B.marking.dpsi u ^ 2 +
      A.marking.dpsi (B.marking.psi u) * B.ddpsi u
  have hpsi : ∀ u, HasDerivAt psi (dpsi u) u := by
    intro u
    simpa [psi, dpsi, smul_eq_mul] using
      (A.psi_deriv (B.marking.psi u)).scomp u (B.psi_deriv u)
  have hdpsi : ∀ u, HasDerivAt dpsi (ddpsi u) u := by
    intro u
    have hleft :=
      (A.dpsi_deriv (B.marking.psi u)).scomp u (B.psi_deriv u)
    have hprod := (B.dpsi_deriv u).mul hleft
    convert hprod using 1 <;> simp [dpsi, ddpsi, smul_eq_mul] <;> ring
  have hApsi : Continuous A.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (A.psi_deriv u).continuousAt
  have hAdpsi : Continuous A.marking.dpsi :=
    continuous_iff_continuousAt.2 fun u => (A.dpsi_deriv u).continuousAt
  have hBpsi : Continuous B.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (B.psi_deriv u).continuousAt
  have hBdpsi : Continuous B.marking.dpsi :=
    continuous_iff_continuousAt.2 fun u => (B.dpsi_deriv u).continuousAt
  have hddpsi : Continuous ddpsi := by
    dsimp [ddpsi]
    exact ((A.ddpsi_cont.comp hBpsi).mul (hBdpsi.pow 2)).add
      ((hAdpsi.comp hBpsi).mul B.ddpsi_cont)
  let R : OrientedReparametrization p r
      (lambda₁ * lambda₂) (Lambda₁ * Lambda₂) :=
    { psi := psi
      dpsi := dpsi
      position := by
        intro u
        rw [B.marking.position u, A.marking.position (B.marking.psi u)]
        rfl
      velocity := by
        intro u
        rw [B.marking.velocity u,
          A.marking.velocity (B.marking.psi u)]
        simp only [psi, comp_apply, dpsi, Complex.ofReal_mul]
        ring
      translate := by
        intro u
        simp only [psi, comp_apply, B.marking.translate u,
          A.marking.translate (B.marking.psi u)]
      lower := by
        intro u
        simpa [dpsi, mul_comm] using mul_le_mul
          (A.marking.lower (B.marking.psi u))
          (B.marking.lower u) B.lambda_pos.le
          (A.lambda_pos.le.trans (A.marking.lower (B.marking.psi u)))
      upper := by
        intro u
        simpa [dpsi, mul_comm] using mul_le_mul
          (A.marking.upper (B.marking.psi u))
          (B.marking.upper u)
          (B.lambda_pos.le.trans (B.marking.lower u))
          (A.lambda_pos.le.trans (A.marking.lower (B.marking.psi u)) |>.trans
            (A.marking.upper (B.marking.psi u))) }
  exact
    { lambda_pos := mul_pos A.lambda_pos B.lambda_pos
      marking := R
      ddpsi := ddpsi
      psi_deriv := hpsi
      dpsi_deriv := hdpsi
      ddpsi_cont := hddpsi
      psi_zero := by simp only [R, psi, comp_apply, B.psi_zero, A.psi_zero] }

/-- The explicit composite second-jet formula. -/
theorem compose_ddpsi
    {p q r : Data} {lambda₁ Lambda₁ lambda₂ Lambda₂ : ℝ}
    (A : NormalizedC2Marking p q lambda₁ Lambda₁)
    (B : NormalizedC2Marking q r lambda₂ Lambda₂) (u : ℝ) :
    (compose A B).ddpsi u =
      A.ddpsi (B.marking.psi u) * B.marking.dpsi u ^ 2 +
        A.marking.dpsi (B.marking.psi u) * B.ddpsi u := rfl

/-- Second-jet bounds compose with the usual C2 chain-rule constant. -/
theorem abs_ddpsi_compose_le
    {p q r : Data} {lambda₁ Lambda₁ lambda₂ Lambda₂ N₁ N₂ : ℝ}
    (A : NormalizedC2Marking p q lambda₁ Lambda₁)
    (B : NormalizedC2Marking q r lambda₂ Lambda₂)
    (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hdd₁ : ∀ u, |A.ddpsi u| ≤ N₁)
    (hdd₂ : ∀ u, |B.ddpsi u| ≤ N₂) (u : ℝ) :
    |(compose A B).ddpsi u| ≤ N₁ * Lambda₂ ^ 2 + Lambda₁ * N₂ := by
  have hd₁ : 0 ≤ A.marking.dpsi (B.marking.psi u) :=
    A.lambda_pos.le.trans (A.marking.lower (B.marking.psi u))
  have hd₂ : 0 ≤ B.marking.dpsi u :=
    B.lambda_pos.le.trans (B.marking.lower u)
  have hL₁ : 0 ≤ Lambda₁ :=
    hd₁.trans (A.marking.upper (B.marking.psi u))
  have hL₂ : 0 ≤ Lambda₂ := hd₂.trans (B.marking.upper u)
  calc
    |(compose A B).ddpsi u| ≤
        |A.ddpsi (B.marking.psi u) * B.marking.dpsi u ^ 2| +
          |A.marking.dpsi (B.marking.psi u) * B.ddpsi u| := by
      rw [compose_ddpsi]
      simpa only [Real.norm_eq_abs] using norm_add_le
        (A.ddpsi (B.marking.psi u) * B.marking.dpsi u ^ 2)
        (A.marking.dpsi (B.marking.psi u) * B.ddpsi u)
    _ ≤ N₁ * Lambda₂ ^ 2 + Lambda₁ * N₂ := by
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hd₁,
        abs_of_nonneg hd₂]
      gcongr
      · exact hdd₁ _
      · exact B.marking.upper u
      · exact A.marking.upper _
      · exact hdd₂ u

/-- Forget a rich gauge-stage output down to its normalized C2 marking. -/
def ofRichStage
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    {J : GaugeFlowMarkedTerminalJets.TerminalJets xi xiX xiXX Phi ell L T base}
    {p front : Data} {bound P0 kh khat M c C dlt : ℝ}
    (S : RichStageOutput J p front bound P0 kh khat M c C dlt) :
    NormalizedC2Marking base J.rear S.lambda S.Lambda where
  lambda_pos := S.lambda_pos
  marking := S.marking
  ddpsi := S.ddpsi
  psi_deriv := S.psi_deriv
  dpsi_deriv := S.dpsi_deriv
  ddpsi_cont := S.ddpsi_cont
  psi_zero := S.psi_zero

end NormalizedC2Marking

/-- Sequence-facing marking data on every finite pullback row.  Depth zero is
the canonical representative of that row. -/
structure FinitePullbackMarkingFamily (Q : ℕ → ℕ → Data) where
  lambda : ℕ → ℕ → ℝ
  Lambda : ℕ → ℕ → ℝ
  stage : ∀ n k, NormalizedC2Marking (Q n k) (Q n (k + 1))
    (lambda n k) (Lambda n k)

namespace FinitePullbackMarkingFamily

def cumulativeLambda {Q : ℕ → ℕ → Data}
    (F : FinitePullbackMarkingFamily Q) (n k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, F.lambda n j

def cumulativeUpper {Q : ℕ → ℕ → Data}
    (F : FinitePullbackMarkingFamily Q) (n k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, F.Lambda n j

/-- Compose all terminal markings from the canonical depth-zero member of a
row to its `k`-th finite pullback. -/
def depthMarking {Q : ℕ → ℕ → Data}
    (F : FinitePullbackMarkingFamily Q) (n : ℕ) : ∀ k,
    NormalizedC2Marking (Q n 0) (Q n k)
      (F.cumulativeLambda n k) (F.cumulativeUpper n k)
  | 0 => by
      simpa [cumulativeLambda, cumulativeUpper] using
        NormalizedC2Marking.refl (Q n 0)
  | k + 1 => by
      simpa [cumulativeLambda, cumulativeUpper, Finset.prod_range_succ] using
        NormalizedC2Marking.compose (F.depthMarking n k) (F.stage n k)

end FinitePullbackMarkingFamily

end NormalizedTerminalMarkingComposition
