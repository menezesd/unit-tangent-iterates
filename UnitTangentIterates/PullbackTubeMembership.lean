import UnitTangentIterates.TubePullbackLimit

/-!
# Tube membership of the pullbacks

The geometric path scheme takes

```
  hmem : ∀ n k, IsTubeMember c 0 dlt (TubePullbackLimit.pullback B Q n k) ,
```

a doubly-indexed family of conditions.  Since `pullback B Q n k = B^[k] (Q (n+k))`,
it reduces to two single facts: that `B` maps the tube into itself, and that each
`Qₙ` lies in it.

* `isTubeMember_iterate` — membership survives iterating an invariant map;
* `isTubeMember_pullback_of_invariant` — hence `hmem` follows.

So `hmem` is a property of the **map**, not a family of separate checks.  What
it asks of the selected inverse is that it preserve the six tube fields:
the two derivative relations, closedness, constant speed, `0 ≤ κ` — which is
where the floor-free tube pays off, since the *closed* condition is preserved
where a strict one need not be — and the chord bound.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real MarkedSpace

namespace TubePullbackLimit

/-- Tube membership is preserved by iterating an invariant map. -/
theorem isTubeMember_iterate {c kmin dlt : ℝ} {B : Data → Data}
    (hBinv : ∀ p, IsTubeMember c kmin dlt p → IsTubeMember c kmin dlt (B p)) :
    ∀ k p, IsTubeMember c kmin dlt p → IsTubeMember c kmin dlt (B^[k] p) := by
  intro k
  induction k with
  | zero => intro p hp; simpa using hp
  | succ k ih =>
      intro p hp
      rw [Function.iterate_succ_apply]
      exact ih (B p) (hBinv p hp)

/-- **Tube membership of the pullbacks, from tube invariance of `B`.**  The
pullbacks are `B^[k] (Q (n+k))`, so if `B` maps the tube into itself and every
`Qₙ` lies in it, so does every pullback.  This is what makes `hmem` a property
of the *map* rather than a family of separate checks. -/
theorem isTubeMember_pullback_of_invariant {c kmin dlt : ℝ}
    {B : Data → Data} {Q : ℕ → Data}
    (hBinv : ∀ p, IsTubeMember c kmin dlt p → IsTubeMember c kmin dlt (B p))
    (hQ : ∀ n, IsTubeMember c kmin dlt (Q n)) :
    ∀ n k, IsTubeMember c kmin dlt (pullback B Q n k) := fun n k =>
  isTubeMember_iterate hBinv k _ (hQ (n + k))

end TubePullbackLimit
