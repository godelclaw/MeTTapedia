import Mathlib
import Mettapedia.Combinatorics.Matching.GHZ.ColorPerMatching

/-!
# Four vertices genuinely admit three colours

The conjecture concerns six vertices and upward, and excludes four.  That exclusion
is necessary rather than assumed: four vertices carry a solution in three colours.

The construction is an instance of colouring the matchings, and it works because of
a coincidence peculiar to four vertices.  They have exactly three perfect
matchings, and those are the three nonzero classes under exclusive-or — the vertex
set is a Klein four-group and the matchings are the cosets of its three subgroups
of order two.  So every matching is a whole colour class, none mixes colours, and
each colour is worn by exactly one matching.  Both hypotheses of the general
construction hold, and the kernel checks them directly.

From six vertices upward the coincidence fails: matchings exist whose edges lie in
different classes, and such a matching would be admitted by a colouring constant on
each of its edges without being constant overall.  That bounds this construction,
not the problem.
-/

namespace GHZ.FourVertexConstruction


open Amplitude _root_.ColourPerMatching GHZ.ColorPerMatching

/-- The colour an edge carries: the exclusive-or class of its endpoints, which for
four vertices names one of the three perfect matchings. -/
def edgeColor (u v : Fin 4) : Fin 3 :=
  ⟨((u.val ^^^ v.val) + 2) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem edgeColor_comm (u v : Fin 4) : edgeColor u v = edgeColor v u := by
  simp [edgeColor, Nat.xor_comm]

/-- The colouring as a total (everywhere-defined) partial colouring. -/
def ec (u v : Fin 4) : Option (Fin 3) := some (edgeColor u v)

theorem ec_comm (u v : Fin 4) : ec u v = ec v u := by rw [ec, ec, edgeColor_comm]

/-- No matching of four vertices mixes colours. -/
theorem edgeColor_mono :
    ∀ σ ∈ pairings (Fin 4), (∀ x, (ec x (σ x)).isSome) → ∀ x y : Fin 4, ∀ k l : Fin 3,
      ec x (σ x) = some k → ec y (σ y) = some l → k = l := by
  decide

/-- Each colour is worn by exactly one matching. -/
theorem edgeColor_uniq : ∀ k : Fin 3,
    ((pairings (Fin 4)).filter
      (fun σ => ∀ x, some (edgeColor x (σ x)) = some k)).card = 1 := by
  decide

/-- **Four vertices carry a three-colour solution.** -/
theorem isGHZ : GHZ.Configuration.isGHZ (weightOf ec ec_comm) :=
  isGHZ_of_coloring ec ec_comm edgeColor_mono (by decide)

/-- **The conjecture's restriction to six vertices and upward is necessary.** -/
theorem solvable_two : GHZ.Configuration.solvable 2 := ⟨_, isGHZ⟩

end GHZ.FourVertexConstruction
