import Mettapedia.GraphTheory.FourColor.MarkedSquareObservable

/-!
# A physical reduction for a boundary equality observation

The full erased-colour profile and an equality test against boundary port 2
have different physical requirements. The latter is preserved exactly by
replacing the four square vertices by a digon on ports 0 and 1, together
with a wire joining ports 2 and 3. The internal marked edge becomes one
edge of the digon. Suppressing that digon changes the observation from
equality to inequality of the two wire colours.

These are exact local fibres and their composition with arbitrary exterior
fibres. They do not assert closure of an ambient minimal-counterexample
class, or transport to an arbitrary remote marked edge.
-/

namespace Mettapedia.GraphTheory.FourColor.MarkedSquareBoundaryReduction

open MarkedSquareObservable

/-- Five physical edges: two parallel edges, two edges to ports 0 and 1,
and the wire between ports 2 and 3. -/
abbrev DigonWireColoring := Fin 5 → Color

/-- The first two vertices are internal; the remaining four are the
labelled degree-one boundary vertices. Parallel edges are intentional. -/
def endpoints : Fin 5 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 1), (0, 2), (1, 3), (4, 5)]

def IsDigonWireExtension (w : SquareBoundaryWord) (c : DigonWireColoring) : Prop :=
  ProperColorTriple (c 2) (c 0) (c 1) ∧
  ProperColorTriple (c 3) (c 0) (c 1) ∧ c 4 ≠ 0 ∧
  c 2 = w 0 ∧ c 3 = w 1 ∧ c 4 = w 2 ∧ c 4 = w 3
  deriving Decidable

def reduceColoring (w : SquareBoundaryWord) (x : SquareInternalColoring) :
    DigonWireColoring := ![x 0, x 1, w 0, w 1, w 2]

def expandColoring (w : SquareBoundaryWord) (c : DigonWireColoring) :
    SquareInternalColoring := ![c 0, c 1, w 0, c 1]

set_option maxHeartbeats 0 in
theorem reduce_valid : ∀ w x,
    IsSquareExtension w x ∧ x 0 = w 2 →
    IsDigonWireExtension w (reduceColoring w x) ∧ reduceColoring w x 0 = w 2 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem expand_valid : ∀ w c,
    IsDigonWireExtension w c ∧ c 0 = w 2 →
    IsSquareExtension w (expandColoring w c) ∧ expandColoring w c 0 = w 2 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem expand_reduce : ∀ w x,
    IsSquareExtension w x ∧ x 0 = w 2 →
    expandColoring w (reduceColoring w x) = x := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem reduce_expand : ∀ w c,
    IsDigonWireExtension w c ∧ c 0 = w 2 →
    reduceColoring w (expandColoring w c) = c := by
  decide +kernel

/-- Exact physical-edge colouring correspondence for the particular
observation that edge 0 equals nonincident boundary port 2. -/
def equalityEquiv (w : SquareBoundaryWord) :
    {x // IsSquareExtension w x ∧ x 0 = w 2} ≃
    {c // IsDigonWireExtension w c ∧ c 0 = w 2} where
  toFun x := ⟨reduceColoring w x.1, reduce_valid w x.1 x.2⟩
  invFun c := ⟨expandColoring w c.1, expand_valid w c.1 c.2⟩
  left_inv x := Subtype.ext (expand_reduce w x.1 x.2)
  right_inv c := Subtype.ext (reduce_expand w c.1 c.2)

theorem equality_count (w : SquareBoundaryWord) :
    Fintype.card {x // IsSquareExtension w x ∧ x 0 = w 2} =
    Fintype.card {c // IsDigonWireExtension w c ∧ c 0 = w 2} :=
  Fintype.card_congr (equalityEquiv w)

/-- All exterior information is retained: the map changes only the internal
fibre over the exterior's full boundary word. -/
def exteriorEquiv {Exterior : Type*} (boundary : Exterior → SquareBoundaryWord) :
    ((a : Exterior) × {x // IsSquareExtension (boundary a) x ∧ x 0 = boundary a 2}) ≃
    ((a : Exterior) × {c // IsDigonWireExtension (boundary a) c ∧ c 0 = boundary a 2}) :=
  Equiv.sigmaCongrRight fun a => equalityEquiv (boundary a)

/-- The seam diagram after suppression is the 01|23 pairing. The carried
observation is now inequality, not equality or an unmarked positive count. -/
def UnequalWires (w : SquareBoundaryWord) : Prop :=
  w.Nonzero ∧ w 0 = w 1 ∧ w 2 = w 3 ∧ w 0 ≠ w 2
  deriving Decidable

def uniqueDigonColoring (w : SquareBoundaryWord) : DigonWireColoring :=
  ![w 2, w 0 + w 2, w 0, w 1, w 2]

set_option maxHeartbeats 0 in
theorem digon_observation_iff : ∀ w c,
    (IsDigonWireExtension w c ∧ c 0 = w 2) ↔
      UnequalWires w ∧ c = uniqueDigonColoring w := by
  decide +kernel

def suppressionEquiv (w : SquareBoundaryWord) :
    {c // IsDigonWireExtension w c ∧ c 0 = w 2} ≃ {_u : Unit // UnequalWires w} where
  toFun c := ⟨(), ((digon_observation_iff w c.1).mp c.2).1⟩
  invFun u := ⟨uniqueDigonColoring w, (digon_observation_iff w _).mpr ⟨u.2, rfl⟩⟩
  left_inv c := Subtype.ext (((digon_observation_iff w c.1).mp c.2).2.symm)
  right_inv _ := Subtype.ext (Subsingleton.elim _ _)

theorem suppressed_count (w : SquareBoundaryWord) :
    Fintype.card {x // IsSquareExtension w x ∧ x 0 = w 2} =
      if UnequalWires w then 1 else 0 := by
  rw [equality_count, Fintype.card_congr (suppressionEquiv w)]
  by_cases h : UnequalWires w <;> simp [h]

theorem zero_iff (w : SquareBoundaryWord) :
    (¬ ∃ x, IsSquareExtension w x ∧ x 0 = w 2) ↔ ¬ UnequalWires w := by
  constructor
  · intro h hw
    let c : {c // IsDigonWireExtension w c ∧ c 0 = w 2} :=
      (suppressionEquiv w).symm ⟨(), hw⟩
    exact h ⟨((equalityEquiv w).symm c).1, ((equalityEquiv w).symm c).2⟩
  · rintro h ⟨x, hx⟩
    exact h (((suppressionEquiv w) ((equalityEquiv w) ⟨x, hx⟩)).2)

/-- The diagonal sector cannot be discarded from the new generating floor:
the suppressed wires are colourable but their inequality target is empty. -/
theorem all_red_suppressed_target_empty :
    SquareReductionSide.Compatible .join01_23 redBoundary ∧
      ¬ UnequalWires redBoundary := by decide

end Mettapedia.GraphTheory.FourColor.MarkedSquareBoundaryReduction
