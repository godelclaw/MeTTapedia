import MettapediaFourColor.BoundaryEarRepair
import Mettapedia.GSLT.Core.RelationalRouteSemantics
import Mettapedia.GSLT.Core.ProofRelevantPresentation

/-!
# One core repair through arbitrarily many ears

The operations construct literal graphs with ordered boundary vertices. A
route transports the joint starting relation, proves Kempe repair at its final
boundary, and recovers an actual compatible colouring at every intermediate
graph. Its size grows by exactly one vertex per step. No embedding, occurrence
in an arbitrary map, or catalogue coverage is inferred from the graph syntax.
-/

namespace FourColor.BoundaryEarGSLT

open KempeBoundarySplit BoundaryEarRepair
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.RelationalRouteSemantics Mettapedia.GSLT.ProofRelevantPresentation

universe u

structure Object where
  Vertex : Type u
  graph : SimpleGraph Vertex
  first : Vertex
  second : Vertex
  tail : List Vertex
  edge : graph.Adj first second

def Object.boundary (p : Object.{u}) : List p.Vertex := p.first :: p.second :: p.tail

def grow (p : Object.{u}) : Object.{u} where
  Vertex := Option p.Vertex
  graph := ear p.graph p.first p.second
  first := some p.first
  second := none
  tail := some p.second :: p.tail.map some
  edge := Or.inl rfl

instance (p : Object.{u}) [Finite p.Vertex] : Finite (grow p).Vertex :=
  inferInstanceAs (Finite (Option p.Vertex))

inductive Step : Object.{u} → Object.{u} → Type (u + 1) where
  | ear (p : Object.{u}) : Step p (grow p)

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

def pullback : {a b : Object.{u}} → Step a b →
    b.graph.Coloring Color → a.graph.Coloring Color
  | _, _, .ear _, k => restrict k

def semantics : Semantics Step.{u} where
  State p := p.graph.Coloring Color
  step event before after := ULift.{u, 0} (PLift (pullback event after = before))

/-- Every final witness supplies the compatible intermediate witnesses. -/
noncomputable def recover : {a b : Object.{u}} → (route : Route Step a b) →
    (k : b.graph.Coloring Color) →
    Σ initial : a.graph.Coloring Color, semantics.Witness route initial k
  | _, _, .refl _, k => ⟨k, ⟨⟨rfl⟩⟩⟩
  | _, _, .cons event rest, k =>
    let tail := recover rest k
    ⟨pullback event tail.1, ⟨tail.1, ⟨⟨rfl⟩⟩, tail.2⟩⟩

/-- The pair is retained at each step, before existential witnesses are hidden. -/
def Input : {a b : Object.{u}} → Route Step a b →
    (List Color → Prop) → List Color → Prop
  | _, _, .refl _, P => P
  | _, _, .cons _ rest, P => Input rest (Split P)

private theorem split_inhabited {P : List Color → Prop}
    (h : ∃ et, P et ∧ et ≠ [] ∧ (0 : Color) ∉ et) :
    ∃ et, Split P et ∧ et ≠ [] ∧ (0 : Color) ∉ et := by
  obtain ⟨et, hP, hne, hz⟩ := h
  cases et with
  | nil => exact False.elim (hne rfl)
  | cons c t =>
    have hc : c ≠ 0 := fun he => hz (by simp [he])
    obtain ⟨a, b, ha, hb, hab, rfl⟩ :
        ∃ a b : Color, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ a + b = c := by
      revert hc
      cases c <;> decide
    refine ⟨a :: b :: t, ⟨a, b, t, rfl, ha, hb, hab, hP⟩, by simp, ?_⟩
    simpa only [List.mem_cons, not_or, ne_eq, eq_comm] using
      And.intro ha (And.intro hb (fun h => hz (List.mem_cons_of_mem _ h)))

/-- Nonempty proper seed relations stay nonempty through every finite route. -/
theorem input_inhabited {a b : Object.{u}} (route : Route Step a b)
    {P : List Color → Prop} (h : ∃ et, P et ∧ et ≠ [] ∧ (0 : Color) ∉ et) :
    ∃ et, Input route P et ∧ et ≠ [] ∧ (0 : Color) ∉ et := by
  induction route generalizing P with
  | refl => exact h
  | cons _ _ ih => exact ih (split_inhabited h)

/-- One core repair proof covers every finite route of these actual operations. -/
theorem repair {a b : Object.{u}} (route : Route Step a b)
    {P : List Color → Prop}
    (base : ∀ et, P et → KempeCoclosure (GraphTrace a.graph a.boundary) et)
    (et : List Color) (start : Input route P et) :
    KempeCoclosure (GraphTrace b.graph b.boundary) et := by
  induction route generalizing P with
  | refl => exact base et start
  | @cons a middle b event rest ih =>
    cases event with
    | ear =>
      exact ih (BoundaryEarRepair.repair a.graph a.first a.second a.tail a.edge base)
        start

/-- Repair returns an actual final colouring and its complete GSLT history. -/
theorem repair_with_history {a b : Object.{u}} (route : Route Step a b)
    {P Q : List Color → Prop}
    (base : ∀ et, P et → KempeCoclosure (GraphTrace a.graph a.boundary) et)
    (et : List Color) (start : Input route P et) (closed : KempeClosed Q) (outside : Q et) :
    ∃ k : b.graph.Coloring Color, ∃ initial : a.graph.Coloring Color,
      Q (trace (b.boundary.map k)) ∧ semantics.Supports route initial k := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := repair route base et start Q closed outside
  exact ⟨k, (recover route k).1, hk, ⟨(recover route k).2⟩⟩

theorem finite_target {a b : Object.{u}} (route : Route Step a b) :
    Finite a.Vertex → Finite b.Vertex := by
  induction route with
  | refl => exact fun h => h
  | cons event rest ih =>
    intro h
    cases event
    let := h
    exact ih inferInstance

/-- The literal vertex count certifies strict descent when a nonempty collar is erased. -/
theorem size {a b : Object.{u}} (route : Route Step a b) :
    Finite a.Vertex → Nat.card b.Vertex = Nat.card a.Vertex + route.length := by
  induction route with
  | refl => exact fun _ => by simp [Route.length]
  | cons event rest ih =>
    intro h
    cases event
    let := h
    rw [ih inferInstance]
    change Nat.card (Option _) + rest.length = _
    rw [BoundaryEarRepair.size]
    simp [Route.length, Nat.add_assoc, Nat.add_comm 1]

theorem strict {a b : Object.{u}} (route : Route Step a b) [Finite a.Vertex]
    (nonempty : 0 < route.length) : Nat.card a.Vertex < Nat.card b.Vertex := by
  rw [size route inferInstance]
  omega

/-- These families contain routes of every length. -/
def iterate (a : Object.{u}) : (n : ℕ) → Σ b, Route Step a b
  | 0 => ⟨a, .refl a⟩
  | n + 1 =>
    let tail := iterate (grow a) n
    ⟨tail.1, .cons (.ear a) tail.2⟩

theorem iterate_length (a : Object.{u}) (n : ℕ) : (iterate a n).2.length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simpa only [iterate, Route.length] using congrArg (· + 1) (ih (grow a))

end FourColor.BoundaryEarGSLT
