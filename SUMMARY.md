# Formalization Summary: *A Noncircular Oval with Convex Unit-Tangent Iterates*

Technical overview of the Lean 4 formalization of Dean Menezes' paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*.

---

## 1. Global project status

* **Main theorem:** proved **unconditionally** — `Ovals.exists_noncircular_oval_iterates_ovals`
  (`UnitTangentIterates/Main.lean`) depends only on `propext`, `Classical.choice`, `Quot.sound`.
* **Modules:** 63 files, about 12,700 lines.
* **`sorry` count:** 0. **Custom `axiom` count:** 0.
* **Build:** `lake build UnitTangentIterates` compiles cleanly.

The plane is modelled as `ℂ`. Everything lives in the `Ovals` namespace.

---

## 2. How the proof is assembled

`Main.lean` reduces Theorem 1.1 to a single statement:

```
exists_ovalOrbit_bounded_width :
  ∃ (X : ℕ → ℝ → ℂ) (p : ℕ → ℝ) (φ : ℕ → ℝ → ℝ) (W : ℝ),
    IsOvalOrbit X p φ ∧ (∀ n, every pair of points of X n is within W in some fixed direction)
```

i.e. an infinite orbit `X (n+1) = 𝒯 (X n) ∘ φₙ` of ovals, up to increasing reparametrizations,
all lying in strips of one common width `W`. Given this orbit:

* `Ovals.main_of_orbit` (`Reparam.lean`) turns it into an honest iterate orbit
  `𝒯ⁿ Γ₀ = X n ∘ Φₙ` of `Γ₀ = X 0`, so every `𝒯ⁿ Γ₀` is an oval.
* `Ovals.not_isCircle_of_iterates_width_le` (`Reduction.lean`) rules out `Γ₀` being a circle:
  the iterates of a circle of radius `r` are circles of radius `√(r² + n)`
  (`Ovals.norm_unitTangentTransform_sub_center`), so they cannot all fit in a strip of width `W`.

`Assembly.lean` proves `exists_ovalOrbit_bounded_width` itself, by building a *model chain*
(`Ovals.ModelChain`) of closed curves from the hairpin's pulse and feeding it to Theorem 6.4
(`Ovals.backward_shadowing`, `Shadowing.lean`).

---

## 3. Section-by-section map

### Section 2 — one tangent step
* `Ovals.steering_exists` (`Steering.lean`): the steering equation `δ' = K − sin δ` has a
  unique `L`-periodic solution with `0 ≤ δ < π/2`, proved via the Banach fixed point theorem
  on the periodic resolvent (`Resolvent.lean`) rather than the paper's period-map argument.
* `Ovals.unitTangentTransform_rearCurve` (`RearFront.lean`): the rear curve built from `F`,
  `Θ`, `δ` satisfies `𝒯 R = F`.
* `Ovals.isOval_selectedRear` (`SelectedRear.lean`): the selected rear of a smooth oval is
  again a smooth oval.

### Section 3 — a translating hairpin
* `Translator.lean`: the translator equation makes `g = θ + d` an increasing diffeomorphism
  of `(0, π)`, with `𝒯 C(θ) = C(g(θ)) + (V, 0)`.
* `HairpinOperator.lean`: the monotone operator `𝒫`.
* `Barriers.lean`: explicit barrier inequalities for `0 < ε ≤ 1/10`.
* `Ovals.hairpinIter_spec` (`HairpinExistence.lean`) and `HairpinCurve.lean`: a smooth,
  strictly convex, embedded hairpin between the barriers, with `𝒯 C = C + (V, 0)`, `V > 0`.
* `Ovals.pulse_exists` (`Pulse.lean`, built from `PulseAux.lean`, `PulseRear.lean`,
  `PulseFront.lean`, `PulseAbstract.lean`): the hairpin's curvature pulse `y` satisfies
  `0 ≤ y ≤ b < 1`, `y ≤ A e^{-a|t|}`, `|y'| ≤ Dy`, `∫ y = π`.

### Section 4 — exact two-cap pairs
* `Periodization.lean`, `PeriodizationEstimates.lean`, `PeriodizationIntegral.lean`: the
  periodization `Y_H = ∑_m y(· − mH)` is `C^r`-close to `y` on `|s| ≤ H/2` up to `O(e^{-βH})`,
  and `∫₀^H Y_H = ∫_ℝ y`.
* `Ovals.hasDerivAt_angleOfCurvature` et al. (`CurveFromCurvature.lean`): the closed curve
  built from a periodic curvature of total mass `π` is centrally symmetric.
* `ClosedPairs.lean`, `PeriodizedPairs.lean`: the exact pair `𝒯 R_H = F_H`, with `0 < Y_H < 1`
  for large `H`.
* `PerimeterAsymptotics.lean`: `P(H) = H − Δ + O(e^{-βH})`, `Δ > 0`.
* `Ovals.periodized_width_bounded` (`WidthBound.lean`, via `Width.lean`): the fronts' width is
  bounded independently of `H` (Lemma 4.4).

### Section 5 — curvature-measure matching
* `Ovals.curvature_matching` (`Matching.lean`, combining `FrontMatching.lean` and
  `RearMatching.lean`): `∫ |k_H − K_{P(H)}| ≤ C e^{-βH}` (Theorem 5.1).

### Section 6 — regularizing backward shadowing
* `Interpolation.lean` (Lemma 6.1): the constant-speed interpolation path between two
  centrally symmetric ovals, with bounds on the normal velocity.
* `Jacobi.lean`, `JacobiEstimates.lean` (Lemma 6.2): the Jacobi equation for the rear's
  normal velocity and the fixed-time estimates, including `ℓ ≥ 2π / tan A` on the rear
  perimeter (`Ovals.rear_perimeter_ge`).
* `WeightedResolvent.lean`, `ResolventBounds.lean`: `L¹`/`L^∞` bounds behind those estimates.
* `WeightedSteering.lean`, `ParamSteering.lean`, `UDiff.lean`: the steering equation in an
  arbitrary path parameter, and its differentiable dependence on that parameter.
* `ShadowIntrinsic.lean`, `ShadowRegularity.lean` (`Ovals.rearF_lipschitz`,
  `Ovals.rearδ_contDiff`, `Ovals.rearInv_contDiff`): the selected inverse `𝓑` on
  (half-perimeter, curvature) data gains one derivative per application, and its rear
  curvature is Lipschitz with constant `L/cos³(arcsin κ)`.
* `ShadowContinuity.lean`: `𝓑` is continuous — convergent half-perimeters and uniformly
  convergent curvatures give convergent rear half-perimeters and pointwise convergent rear
  curvatures.
* `ShadowRep.lean`, `ShadowPath.lean`, `ShadowInterp.lean`, `ShadowEstimates.lean`,
  `ShadowMax.lean`, `ShadowLimitTools.lean`: normalized ovals, paths between them, and the
  ultrafilter-limit tools (equi-Lipschitz pointwise convergence is uniform; the curve with a
  given curvature depends continuously on it).
* `ShadowChain.lean`, `ModelChain.lean`, `ShadowNodes.lean`, `ShadowLimit.lean`,
  `ShadowOrbit.lean`, `ShadowRearCurve.lean`: the backward iterates `𝓑^{N-n} Q_N` of a model
  chain stay in a fixed tube and converge along a nonprincipal ultrafilter in `N` to an exact
  orbit `X_n = 𝒯 X_{n+1}`.
* `Ovals.backward_shadowing` (`Shadowing.lean`, **Theorem 6.4**): for every `κ₀ < 1` there is
  `η > 0` such that any model chain with curvatures `≤ κ₀` and total defect `≤ η` is shadowed
  by an exact orbit of ovals, and the width bound passes to the limit.

### Section 7 — proof of the main theorem
* `Ovals.period_recursion`, `Ovals.defect_tail_le` (`PeriodRecursion.lean`,
  `PeriodSequence.lean`): the sequence `P(H_{n+1}) = H_n` with `H_n ≥ H_0 + (Δ/2)n` (7.1).
* `Ovals.model_defects_small` (`ModelDefects.lean`): the total defect `∑ e_n ≤ C e^{-βH_0}`
  (7.2).
* `Ovals.exists_ovalOrbit_bounded_width` (`Assembly.lean`): the fronts `Q_n = F_{H_n}` and
  rears `A_n = R_{H_{n+1}}` form a model chain with curvatures `≤ 1/10`, small total defect,
  and bounded width; `backward_shadowing` yields the thin orbit.
* `Ovals.width_le_of_unitTangent`, `Ovals.not_isCircle_of_iterates_width_le`
  (`Reduction.lean`): rears are never wider than their fronts, and a circle's iterates cannot
  stay thin.
* `Ovals.main_of_orbit` (`Reparam.lean`): reparametrization invariance of `𝒯` and curvature
  turns the thin orbit into Theorem 1.1.
* `Ovals.injOn_curveOfCurvature`, `Ovals.isOval_curveOfCurvature` (`Embedded.lean`): a closed
  curve of total turning `2π` and nonnegative curvature is embedded — used wherever a curve is
  built from prescribed curvature data.
* `Ovals.circle_perimeter_le` (`Noncircular.lean`): a circle within Hausdorff distance `d` of a
  set of width `W` has perimeter at most `π(W + 2d)`.
