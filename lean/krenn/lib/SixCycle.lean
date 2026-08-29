import Mathlib
import ColourPerMatching

/-!
# Six vertices carry a two-colour solution

The conjecture asserts that beyond four vertices no more than two colours are
possible.  Two are, and this file shows it at six vertices by colouring the
matchings of a cycle.

A cycle on an even number of vertices has exactly two perfect matchings, the two
alternating ones, and they are disjoint.  Colour each edge by the parity of its
position, so that each alternating matching is a whole colour class, and leave the
chords uncoloured — an uncoloured edge weighs zero, so a matching using one is
never admitted.  Both hypotheses of the colouring construction then hold, and the
kernel checks them.

`CycleSolution` now proves this at every even vertex count, by the same idea
argued rather than decided.  This file is kept as an independent check: it reaches
the six-vertex case through a different colouring — position parity rather than
membership of an alternating matching — and by kernel decision rather than by
proof, so agreement between the two is evidence for both.

This is the companion to the four-vertex result: there the vertex set itself had
only three matchings, here a subgraph is chosen with only two.  Together they show
the construction is not confined to the exceptional count, and that the conjecture's
bound of two colours is attained rather than merely permitted.
-/

namespace SixCycle

open Amplitude ColourPerMatching

/-- The six-cycle's edges, coloured by position parity; chords stay uncoloured. -/
def ec (u v : Fin 6) : Option (Fin 2) :=
  if v = u + 1 then some ⟨u.val % 2, Nat.mod_lt _ (by norm_num)⟩
  else if u = v + 1 then some ⟨v.val % 2, Nat.mod_lt _ (by norm_num)⟩
  else none

theorem ec_comm : ∀ u v : Fin 6, ec u v = ec v u := by decide

set_option maxRecDepth 40000 in
/-- A matching all of whose edges are cycle edges is one of the two alternating
ones, and those do not mix colours. -/
theorem ec_mono : ∀ σ ∈ pairings (Fin 6), (∀ x, (ec x (σ x)).isSome) →
    ∀ x y : Fin 6, ∀ k l : Fin 2,
      ec x (σ x) = some k → ec y (σ y) = some l → k = l := by
  decide

set_option maxRecDepth 40000 in
/-- Each of the two colours is worn by exactly one matching. -/
theorem ec_uniq : ∀ k : Fin 2,
    ((pairings (Fin 6)).filter (fun σ => ∀ x, ec x (σ x) = some k)).card = 1 := by
  decide

set_option maxRecDepth 40000 in
/-- **Six vertices carry a two-colour solution**: every constant colouring has
amplitude one and every other colouring amplitude zero. -/
theorem spec :
    (∀ k : Fin 2, amplitude (weightOf ec ec_comm) (Amplitude.const k) = 1) ∧
      (∀ c : Fin 6 → Fin 2, ¬ (∀ x y : Fin 6, c x = c y) →
        amplitude (weightOf ec ec_comm) c = 0) :=
  amplitude_spec ec ec_comm ec_mono (by decide)

end SixCycle
