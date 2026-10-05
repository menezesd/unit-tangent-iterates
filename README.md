# Formalization of "A Noncircular Oval with Convex Unit-Tangent Iterates"

This repository contains a Lean 4 / Mathlib formalization of the paper:

> Dean Menezes, *A Noncircular Oval with Convex Unit-Tangent Iterates*
> (`noncircular_oval_unit_tangent_iterates.tex` in this repository).

The main theorem is proved unconditionally, with no `sorry`s and no custom
axioms: `Ovals.exists_noncircular_oval_iterates_ovals` in
`UnitTangentIterates/Main.lean` depends only on the three standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`). The plane is modelled as `ℂ`,
and the whole development lives in the `Ovals` namespace, spread over 63
files (about 12,700 lines).

---

## Building and verifying the project

### Prerequisites
* Lean 4 toolchain: `leanprover/lean4:v4.28.0`
* Lake build system

### Verification commands
```bash
# Build everything
lake build UnitTangentIterates

# Build just the main theorem
lake build UnitTangentIterates.Main
```

To check which axioms the main theorem depends on:
```bash
cat > UnitTangentIterates/CheckAxioms.lean << 'EOF'
import UnitTangentIterates.Main
#print axioms Ovals.exists_noncircular_oval_iterates_ovals
EOF
lake env lean UnitTangentIterates/CheckAxioms.lean
rm UnitTangentIterates/CheckAxioms.lean
```

---

## Proof outline and module map

`UnitTangentIterates/Main.lean` derives Theorem 1.1 from an infinite orbit of
ovals of bounded width (`exists_ovalOrbit_bounded_width`, assembled in
`Assembly.lean`) together with the fact that a circle's iterates grow without
bound, so cannot stay thin (`Reduction.lean`).

**Section 1 — definitions and the main theorem**
| Module | Content |
| :--- | :--- |
| `Defs.lean` | The unit-tangent transform `𝒯γ = γ + γ'/‖γ'‖`, signed curvature, `IsOval`, `IsCircle`. |
| `Main.lean` | Theorem 1.1. |

**Section 2 — one tangent step: rear and front tracks**
| Module | Content |
| :--- | :--- |
| `Circle.lean` | `𝒯` sends a circle of radius `r` to one of radius `√(r²+1)`; all iterates of a circle are ovals. |
| `Steering.lean` | The steering equation `δ' = K − sin δ`: unique periodic solution with `0 ≤ δ < π/2`, proved by a Banach fixed point argument. |
| `Resolvent.lean` | The periodic resolvent of `1 + d/dx`, used to solve the steering equation. |
| `RearFront.lean` | The selected rear `R` with `𝒯R = F` and rear curvature between `0` and `κ/√(1−κ²)`. |
| `SelectedRear.lean` | Smooth dependence: the selected rear of a smooth oval is a smooth oval. |

**Section 3 — a translating hairpin**
| Module | Content |
| :--- | :--- |
| `Translator.lean` | Lemma 3.1: the translator equation, and `𝒯C = C + (V,0)` for hairpins. |
| `HairpinOperator.lean` | Lemma 3.2: the monotone operator `𝒫`. |
| `Barriers.lean` | Lemma 3.3: explicit barrier inequalities. |
| `HairpinExistence.lean`, `HairpinCurve.lean` | Theorem 3.4: existence of a smooth, strictly convex, embedded translating hairpin with `V > 0`. |
| `Pulse.lean`, `PulseAux.lean`, `PulseRear.lean`, `PulseFront.lean`, `PulseAbstract.lean` | Lemma 3.5: the hairpin's curvature pulse `y`, with `0 ≤ y ≤ b < 1`, `y ≤ Ae^{-a\|t\|}`, `\|y'\| ≤ Dy`, and `∫ y = π`. |

**Section 4 — exact two-cap pairs**
| Module | Content |
| :--- | :--- |
| `Periodization.lean`, `PeriodizationEstimates.lean`, `PeriodizationIntegral.lean` | Lemma 4.1: the periodization `Y_H` of `y`, its derivatives, and its mass `∫₀^H Y_H = ∫_ℝ y`. |
| `FrontError.lean` | Lemma 4.2: the front periodization error is `O(e^{-βL})`. |
| `CurveFromCurvature.lean` | Centrally symmetric closed curves built from a prescribed periodic curvature. |
| `ClosedPairs.lean`, `PeriodizedPairs.lean` | Proposition 4.3: the exact pair `𝒯R_H = F_H`, both centrally symmetric with positive curvature. |
| `PerimeterAsymptotics.lean` | `P(H) = H − Δ + O(e^{-βH})`, with `Δ > 0`. |
| `CurvatureBound.lean` | The curvature bound on the periodized models. |
| `Width.lean`, `WidthBound.lean` | Lemma 4.4: the closed fronts have width bounded independently of `H`. |

**Section 5 — curvature-measure matching**
| Module | Content |
| :--- | :--- |
| `FrontMatching.lean`, `RearMatching.lean`, `Matching.lean` | Theorem 5.1: `∫ \|k_H − K_{P(H)}\| ≤ Ce^{-βH}`, front and rear halves. |

**Section 6 — regularizing backward shadowing**
| Module | Content |
| :--- | :--- |
| `Interpolation.lean` | Lemma 6.1: the interpolation path between two centrally symmetric ovals. |
| `Jacobi.lean`, `JacobiEstimates.lean` | Lemma 6.2: the Jacobi equation for the rear's normal velocity, and the fixed-time estimates (6.5)–(6.7). |
| `WeightedResolvent.lean`, `ResolventBounds.lean` | `L¹`/`L^∞` bounds for the resolvent and for `w' + βw = f`. |
| `WeightedSteering.lean`, `ParamSteering.lean`, `UDiff.lean` | The steering equation in an arbitrary parameter, and its differentiable dependence on that parameter. |
| `ShadowIntrinsic.lean`, `ShadowRegularity.lean`, `ShadowContinuity.lean` | The selected inverse `𝓑` on intrinsic (half-perimeter, curvature) data: qualitative properties, Lipschitz regularity, one-derivative gain, continuity. |
| `ShadowRep.lean`, `ShadowPath.lean`, `ShadowInterp.lean`, `ShadowEstimates.lean` | Normalized ovals and paths between them, in intrinsic data form. |
| `ShadowMax.lean`, `ShadowLimitTools.lean` | Growth bounds and ultrafilter-limit tools used to pass to the limit. |
| `ShadowChain.lean`, `ModelChain.lean`, `ShadowNodes.lean`, `ShadowLimit.lean`, `ShadowOrbit.lean`, `ShadowRearCurve.lean` | The backward iterates of a model chain, their limit along an ultrafilter, and the resulting orbit of ovals. |
| `Shadowing.lean` | **Theorem 6.4** (backward shadowing): a model chain of small total defect is shadowed by an exact orbit of ovals, with the width bound passing to the limit. |

**Section 7 — proof of the main theorem**
| Module | Content |
| :--- | :--- |
| `PeriodRecursion.lean`, `PeriodSequence.lean` | The period recursion `P(H_{n+1}) = H_n`, `H_n ≥ H_0 + (Δ/2)n` (7.1). |
| `ModelDefects.lean` | The total model defect `∑ e_n ≤ Ce^{-βH_0}` (7.2). |
| `Assembly.lean` | Assembling the closed models into a model chain and applying Theorem 6.4. |
| `Reduction.lean` | Rears are never wider than their fronts; a circle's iterates grow like `√n`, so cannot stay thin. |
| `Reparam.lean` | Reparametrization invariance of `𝒯` and curvature; orbits up to reparametrization give Theorem 1.1. |
| `Embedded.lean` | Closed curves of total turning `2π` are embedded (used by `CurveFromCurvature` and the limit argument). |
| `Noncircular.lean` | The width/Hausdorff-distance argument excluding a circle. |
