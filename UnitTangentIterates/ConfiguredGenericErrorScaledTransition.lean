import UnitTangentIterates.ConfiguredAffineGaugeScaledTransition

/-! A generic-error version of the configured physical-component transition. -/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredGenericErrorScaledTransition

open ConfiguredApproximateDefectPathRowwise
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  NormalizedMarkingControlledJunction
  ArclengthScaledJacobiTransition
  AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds

/-- Only the affine analytic data used by the scaled transition.  In
particular, the recursive error function is completely arbitrary. -/
structure AffineInput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {e : ℕ → ℕ → ℝ} {c dlt : ℝ}
    {P1 G1 Cg C : ℕ → ℝ}
    {Q current : ℕ → Data} {k : ℕ}
    (S : ColumnStep Q current e k (rowP0 D) P1 (fun _ => D.kstar)
      G1 Cg C c dlt) (n : ℕ) where
  affineRear : Data
  rear : Data
  terminalBase : Data
  affinePath : NormalPath (S.richStage n).terminalBase affineRear
  affineC2 : C2NormalPathData affinePath
  finish : ∀ u,
    affinePath.X affinePath.T ((S.richStage n).marking.marking.psi u) = rear.1 u

/-- The configured physical-component transition, independent of the scalar
error used by the surrounding recursive scheme. -/
theorem transition
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {e : ℕ → ℕ → ℝ} {c dlt : ℝ}
    {P1 G1 Cg C : ℕ → ℝ}
    {Q current : ℕ → Data} {k n : ℕ}
    (S : ColumnStep Q current e k (rowP0 D) P1 (fun _ => D.kstar)
      G1 Cg C c dlt)
    (I : AffineInput D S n)
    (frontC2 : C2NormalPathData (S.richStage (n + 1)).stage.increment)
    (hfront0 : Continuous (uncurry (S.richStage (n + 1)).stage.increment.eta))
    (hfront1 : Continuous (uncurry frontC2.eta1))
    (hfront2 : Continuous (uncurry frontC2.eta2))
    (hrear0 : Continuous (uncurry I.affinePath.eta))
    (hrear1 : Continuous (uncurry I.affineC2.eta1))
    (hrear2 : Continuous (uncurry I.affineC2.eta2))
    {C0 C1 C2 mA MA NA : ℝ} (hC0 : 0 ≤ C0)
    (hPF : 0 ≤ perim (S.richStage (n + 1)).terminalBase)
    (hPR : 0 ≤ perim I.terminalBase)
    (B : DensityBounds
      (perim (S.richStage (n + 1)).terminalBase) (perim I.terminalBase)
      (S.richStage (n + 1)).stage.increment.eta I.affinePath.eta C0 C1 C2)
    (A : ControlledAnchoringBounds (S.richStage n).marking mA MA NA) :
    let hstart : ∀ u,
        I.affinePath.X 0 ((S.richStage n).marking.marking.psi u) =
          (S.next n).1 u := fun u => by
          rw [I.affinePath.start]
          exact ((S.richStage n).marking.marking.position u).symm
    let J := controlledJunction I.affinePath (S.richStage n).marking A
      hstart I.finish
    Transition
      (physicalComponents (perim (S.richStage (n + 1)).terminalBase)
        (S.richStage (n + 1)).stage.increment.eta)
      (physicalComponents (perim I.terminalBase)
        (reparamAtJunction I.affinePath I.affineC2 J).eta)
      (1 / J.m) J.M J.N C0 C1 C2 := by
  dsimp only
  let hstart : ∀ u,
      I.affinePath.X 0 ((S.richStage n).marking.marking.psi u) =
        (S.next n).1 u := fun u => by
    rw [I.affinePath.start]
    exact ((S.richStage n).marking.marking.position u).symm
  let J := controlledJunction I.affinePath (S.richStage n).marking A
    hstart I.finish
  let hraw : AnalyticInput
      (perim (S.richStage (n + 1)).terminalBase) (perim I.terminalBase)
      (S.richStage (n + 1)).stage.increment.eta I.affinePath.eta C0 C1 C2 :=
    AnalyticInput.of_jointC2_densityBounds frontC2 I.affineC2
      hfront0 hfront1 hfront2 hrear0 hrear1 hrear2 hPF hC0 B
  let hsource : FunctionalIntegrable I.affinePath.eta :=
    PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      I.affineC2 hrear0 hrear1 hrear2
  let htarget : FunctionalIntegrable
      (reparamAtJunction I.affinePath I.affineC2 J).eta :=
    PeriodicSupNormFunctionalIntegrable.functionalIntegrable_comp_of_jointC2
      I.affineC2 hrear0 hrear1 hrear2 J.phi_deriv J.phi1_deriv
      J.phi1_cont J.phi2_cont J.phi_add_one J.phi1_periodic J.phi2_periodic
  exact transition_of_raw_and_junction I.affinePath I.affineC2 J hPR
    hraw hsource htarget

end ConfiguredGenericErrorScaledTransition
