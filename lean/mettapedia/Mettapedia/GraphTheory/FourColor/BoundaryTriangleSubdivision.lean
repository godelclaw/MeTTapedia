import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.SetTheory.Cardinal.Finite
import Mettapedia.GSLT.Core.RelationalRouteSemantics
import Mettapedia.GSLT.Core.ProofRelevantPresentation

/-!
# Colouring witnesses for a boundary-triangle subdivision

Delete an edge `a-b` and insert a fresh vertex joined to `a`, `b` and `c`.
Every four-colouring extends while retaining all original vertex colours.
When `a,b,c` form a triangle, this is a bijection onto the target colourings
which still distinguish `a` and `b`. The new colour is then uniquely determined.

The GSLT route interpretation below retains these chosen witnesses at every
step. It does not require every possible new boundary colour to work. The
graph theorem is independent of an embedding: using the operation on a planar
boundary additionally requires the specified triangle to be a boundary face.
No reducibility or arbitrary-graph colouring theorem is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

universe u

def fourth (a b c : Fin 4) : Fin 4 :=
  if a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 then 0
  else if a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 then 1
  else if a ≠ 2 ∧ b ≠ 2 ∧ c ≠ 2 then 2
  else 3

theorem fourth_ne (a b c : Fin 4) :
    fourth a b c ≠ a ∧ fourth a b c ≠ b ∧ fourth a b c ≠ c := by
  revert a b c
  decide +kernel

theorem fourth_unique (a b c d : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : d ≠ a) (hb : d ≠ b) (hc : d ≠ c) : d = fourth a b c := by
  revert a b c d
  decide +kernel

variable {V : Type u}

def removed (a b x y : V) : Prop := (x = a ∧ y = b) ∨ (x = b ∧ y = a)

def subdivide (G : SimpleGraph V) (a b c : V) : SimpleGraph (Option V) where
  Adj
    | some x, some y => G.Adj x y ∧ ¬ removed a b x y
    | none, some y => y = a ∨ y = b ∨ y = c
    | some x, none => x = a ∨ x = b ∨ x = c
    | none, none => False
  symm := ⟨by
    intro x y adjacent
    cases x <;> cases y
    · exact adjacent
    · exact adjacent
    · exact adjacent
    · refine ⟨adjacent.1.symm, ?_⟩
      intro h
      exact adjacent.2 (by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [removed])⟩
  loopless := ⟨by
    intro x
    cases x
    · exact id
    · exact fun h => G.loopless.irrefl _ h.1⟩

variable (G : SimpleGraph V) (a b c : V)

/-- All retained vertices keep their actual colours. -/
def extend (coloring : G.Coloring (Fin 4)) : (subdivide G a b c).Coloring (Fin 4) :=
  .mk (fun vertex => match vertex with
    | some v => coloring v
    | none => fourth (coloring a) (coloring b) (coloring c)) (by
      intro x y adjacent
      cases x with
      | none =>
        cases y with
        | none => exact False.elim adjacent
        | some y =>
          rcases adjacent with rfl | rfl | rfl
          · exact (fourth_ne _ _ _).1
          · exact (fourth_ne _ _ _).2.1
          · exact (fourth_ne _ _ _).2.2
      | some x =>
        cases y with
        | none =>
          rcases adjacent with rfl | rfl | rfl
          · exact (fourth_ne _ _ _).1.symm
          · exact (fourth_ne _ _ _).2.1.symm
          · exact (fourth_ne _ _ _).2.2.symm
        | some y => exact coloring.valid adjacent.1)

@[simp] theorem extend_some (coloring : G.Coloring (Fin 4)) (v : V) :
    extend G a b c coloring (some v) = coloring v := rfl

@[simp] theorem extend_none (coloring : G.Coloring (Fin 4)) :
    extend G a b c coloring none = fourth (coloring a) (coloring b) (coloring c) := rfl

def restrict {C : Type*} (coloring : (subdivide G a b c).Coloring C)
    (distinct : coloring (some a) ≠ coloring (some b)) : G.Coloring C :=
  .mk (fun v => coloring (some v)) (by
    intro x y adjacent
    by_cases h : removed a b x y
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact distinct
      · exact distinct.symm
    · exact coloring.valid ⟨adjacent, h⟩)

theorem restrict_extend (hab : G.Adj a b) (coloring : G.Coloring (Fin 4)) :
    restrict G a b c (extend G a b c coloring) (coloring.valid hab) = coloring := by
  ext
  rfl

theorem extend_restrict (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (coloring : (subdivide G a b c).Coloring (Fin 4))
    (distinct : coloring (some a) ≠ coloring (some b)) :
    extend G a b c (restrict G a b c coloring distinct) = coloring := by
  let old := restrict G a b c coloring distinct
  have fresh (v : V) (hv : v = a ∨ v = b ∨ v = c) :
      coloring none ≠ old v := coloring.valid hv
  apply DFunLike.ext
  intro vertex
  cases vertex with
  | some v => rfl
  | none =>
    exact (fourth_unique (old a) (old b) (old c) (coloring none)
      (old.valid hab) (old.valid hac) (old.valid hbc)
      (fresh a (Or.inl rfl)) (fresh b (Or.inr (Or.inl rfl)))
      (fresh c (Or.inr (Or.inr rfl)))).symm

/-- Exact witness equivalence; unrestricted target colourings may also
identify the endpoints of the deleted edge. -/
def coloringEquiv (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    G.Coloring (Fin 4) ≃
      {coloring : (subdivide G a b c).Coloring (Fin 4) //
        coloring (some a) ≠ coloring (some b)} where
  toFun coloring := ⟨extend G a b c coloring, coloring.valid hab⟩
  invFun coloring := restrict G a b c coloring.val coloring.property
  left_inv coloring := restrict_extend G a b c hab coloring
  right_inv coloring := Subtype.ext (extend_restrict G a b c hab hac hbc
    coloring.val coloring.property)

theorem coloring_card (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    Nat.card (G.Coloring (Fin 4)) =
      Nat.card {coloring : (subdivide G a b c).Coloring (Fin 4) //
        coloring (some a) ≠ coloring (some b)} :=
  Nat.card_congr (coloringEquiv G a b c hab hac hbc)

theorem extend_boundary {Port : Type*} (ports : Port → V) (word : Port → Fin 4)
    (coloring : G.Coloring (Fin 4)) (prescribed : ∀ p, coloring (ports p) = word p) :
    ∀ p, extend G a b c coloring (some (ports p)) = word p := prescribed

namespace Operational

open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.RelationalRouteSemantics Mettapedia.GSLT.ProofRelevantPresentation

structure Object where
  Vertex : Type u
  graph : SimpleGraph Vertex

inductive Step : Object.{u} → Object.{u} → Type (u + 1) where
  | triangle (source : Object.{u}) (a b c : source.Vertex)
      (hab : source.graph.Adj a b) (hac : source.graph.Adj a c)
      (hbc : source.graph.Adj b c) :
      Step source ⟨Option source.Vertex, subdivide source.graph a b c⟩

/-- The operation is structurally permitted without assuming a colouring. -/
def theory : GSLT.{u + 1} where
  Term := Object.{u}
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := Nonempty (Step source target)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def presentation : StepPresentation theory.{u} where
  Evidence := Step
  erases_iff := fun _ _ => Iff.rfl

def retained : {source target : Object.{u}} → Step source target →
    source.Vertex → target.Vertex
  | _, _, .triangle _ _ _ _ _ _ _ => some

def transport : {source target : Object.{u}} → Step source target →
    source.graph.Coloring (Fin 4) → target.graph.Coloring (Fin 4)
  | _, _, .triangle source a b c _ _ _ => extend source.graph a b c

theorem transport_retained {source target : Object.{u}} (step : Step source target)
    (coloring : source.graph.Coloring (Fin 4)) (v : source.Vertex) :
    transport step coloring (retained step v) = coloring v := by
  cases step
  rfl

def semantics : Semantics Step.{u} where
  State object := object.graph.Coloring (Fin 4)
  step event before after := ULift.{u, 0} (PLift (∀ v, after (retained event v) = before v))

def retainedRoute : {source target : Object.{u}} →
    Route Step source target → source.Vertex → target.Vertex
  | _, _, .refl _ => id
  | _, _, .cons event rest => retainedRoute rest ∘ retained event

/-- Chosen compatible witnesses compose along arbitrary finite histories of
these actual graph operations. The starting colouring is an explicit input. -/
noncomputable def liftRoute : {source target : Object.{u}} →
    (route : Route Step source target) → (coloring : source.graph.Coloring (Fin 4)) →
    Σ result : target.graph.Coloring (Fin 4), semantics.Witness route coloring result
  | _, _, .refl _, coloring => ⟨coloring, ⟨⟨rfl⟩⟩⟩
  | _, _, .cons event rest, coloring =>
      let middle := transport event coloring
      let tail := liftRoute rest middle
      ⟨tail.1, ⟨middle, ⟨⟨transport_retained event coloring⟩⟩, tail.2⟩⟩

theorem liftRoute_retained : {source target : Object.{u}} →
    (route : Route Step source target) → (coloring : source.graph.Coloring (Fin 4)) →
    (v : source.Vertex) →
    (liftRoute route coloring).1 (retainedRoute route v) = coloring v
  | _, _, .refl _, _, _ => rfl
  | _, _, .cons event rest, coloring, v =>
      (liftRoute_retained rest (transport event coloring) (retained event v)).trans
        (transport_retained event coloring v)

end Operational
end Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision
