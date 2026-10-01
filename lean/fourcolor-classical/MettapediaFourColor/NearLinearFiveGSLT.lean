import MettapediaFourColor.NearLinearFiveRepair
import Mathlib.Tactic.FinCases

/-!
# Compatible construction histories for the five-entry family

The events are the actual certified boundary insertions. A route carries
one colouring witness at each intermediate graph. The two insertion orders
from D0370 to D0604 give the same final colouring, including the new vertices.
These construction histories do not assert an executable Kempe-swap history.
-/

namespace FourColor.NearLinearFiveGSLT

open NearLinearFiveData KempeBoundarySplit
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.RelationalRouteSemantics Mettapedia.GSLT.ProofRelevantPresentation

def lift0370_0464 (k : input0370.graph.Coloring (Fin 4)) : input0464.graph.Coloring (Fin 4) :=
  BoundaryRepairTransport.coloring insert0370_0464 (extend input0370.graph 9 8 16 k)

@[simp] theorem retained0370_0464 (k : input0370.graph.Coloring (Fin 4)) (v : Fin 21) :
    lift0370_0464 k (insert0370_0464 (some v)) = k v := by
  simp only [lift0370_0464, BoundaryRepairTransport.coloring_apply, extend_some]

def lift0370_0465 (k : input0370.graph.Coloring (Fin 4)) : input0465.graph.Coloring (Fin 4) :=
  BoundaryRepairTransport.coloring insert0370_0465 (extend input0370.graph 6 5 20 k)

@[simp] theorem retained0370_0465 (k : input0370.graph.Coloring (Fin 4)) (v : Fin 21) :
    lift0370_0465 k (insert0370_0465 (some v)) = k v := by
  simp only [lift0370_0465, BoundaryRepairTransport.coloring_apply, extend_some]

def lift0465_0604 (k : input0465.graph.Coloring (Fin 4)) : input0604.graph.Coloring (Fin 4) :=
  BoundaryRepairTransport.coloring insert0465_0604 (extend input0465.graph 4 3 16 k)

@[simp] theorem retained0465_0604 (k : input0465.graph.Coloring (Fin 4)) (v : Fin 22) :
    lift0465_0604 k (insert0465_0604 (some v)) = k v := by
  simp only [lift0465_0604, BoundaryRepairTransport.coloring_apply, extend_some]

def lift0464_0604 (k : input0464.graph.Coloring (Fin 4)) : input0604.graph.Coloring (Fin 4) :=
  BoundaryRepairTransport.coloring insert0464_0604 (extend input0464.graph 4 3 16 k)

@[simp] theorem retained0464_0604 (k : input0464.graph.Coloring (Fin 4)) (v : Fin 22) :
    lift0464_0604 k (insert0464_0604 (some v)) = k v := by
  simp only [lift0464_0604, BoundaryRepairTransport.coloring_apply, extend_some]

def lift3202_0604 (k : input3202.graph.Coloring (Fin 4)) : input0604.graph.Coloring (Fin 4) :=
  BoundaryRepairTransport.coloring insert3202_0604 (extend input3202.graph 5 4 16 k)

@[simp] theorem retained3202_0604 (k : input3202.graph.Coloring (Fin 4)) (v : Fin 22) :
    lift3202_0604 k (insert3202_0604 (some v)) = k v := by
  simp only [lift3202_0604, BoundaryRepairTransport.coloring_apply, extend_some]

inductive Piece where
  | p0370 | p0464 | p0465 | p0604 | p3202
  deriving DecidableEq

def Vertex : Piece → Type
  | .p0370 => Fin 21
  | .p0604 => Fin 23
  | _ => Fin 22

def graph : (p : Piece) → SimpleGraph (Vertex p)
  | .p0370 => input0370.graph
  | .p0464 => input0464.graph
  | .p0465 => input0465.graph
  | .p0604 => input0604.graph
  | .p3202 => input3202.graph

inductive Event : Piece → Piece → Type where
  | e0370_0464 : Event .p0370 .p0464
  | e0370_0465 : Event .p0370 .p0465
  | e0465_0604 : Event .p0465 .p0604
  | e0464_0604 : Event .p0464 .p0604
  | e3202_0604 : Event .p3202 .p0604

def theory : GSLT where
  Term := Piece
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := Nonempty (Event source target)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def presentation : StepPresentation theory where
  Evidence := Event
  erases_iff := fun _ _ => Iff.rfl

abbrev State (p : Piece) := (graph p).Coloring (Fin 4)

def transport : {p q : Piece} → Event p q → State p → State q
  | _, _, .e0370_0464 => lift0370_0464
  | _, _, .e0370_0465 => lift0370_0465
  | _, _, .e0465_0604 => lift0465_0604
  | _, _, .e0464_0604 => lift0464_0604
  | _, _, .e3202_0604 => lift3202_0604

def retained : {p q : Piece} → Event p q → Vertex p → Vertex q
  | _, _, .e0370_0464, v => insert0370_0464 (some v)
  | _, _, .e0370_0465, v => insert0370_0465 (some v)
  | _, _, .e0465_0604, v => insert0465_0604 (some v)
  | _, _, .e0464_0604, v => insert0464_0604 (some v)
  | _, _, .e3202_0604, v => insert3202_0604 (some v)

theorem transport_retained {p q : Piece} (e : Event p q) (k : State p) (v : Vertex p) :
    transport e k (retained e v) = k v := by
  cases e with
  | e0370_0464 => exact retained0370_0464 k v
  | e0370_0465 => exact retained0370_0465 k v
  | e0465_0604 => exact retained0465_0604 k v
  | e0464_0604 => exact retained0464_0604 k v
  | e3202_0604 => exact retained3202_0604 k v


def semantics : Semantics Event where
  State := State
  step event before after := ULift (PLift (after = transport event before))

def leftRoute : Route Event .p0370 .p0604 :=
  .cons .e0370_0464 (.cons .e0464_0604 (.refl _))

def rightRoute : Route Event .p0370 .p0604 :=
  .cons .e0370_0465 (.cons .e0465_0604 (.refl _))

/-- Commutation includes both inserted colours, not just the retained vertices. -/
theorem coloring_square (k : input0370.graph.Coloring (Fin 4)) :
    lift0464_0604 (lift0370_0464 k) = lift0465_0604 (lift0370_0465 k) := by
  ext v
  fin_cases v <;> rfl

theorem left_history (k : input0370.graph.Coloring (Fin 4)) :
    semantics.Supports leftRoute k (lift0464_0604 (lift0370_0464 k)) := by
  exact ⟨⟨lift0370_0464 k, ⟨⟨rfl⟩⟩,
    lift0464_0604 (lift0370_0464 k), ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩⟩⟩

theorem right_history (k : input0370.graph.Coloring (Fin 4)) :
    semantics.Supports rightRoute k (lift0464_0604 (lift0370_0464 k)) := by
  rw [coloring_square]
  exact ⟨⟨lift0370_0465 k, ⟨⟨rfl⟩⟩,
    lift0465_0604 (lift0370_0465 k), ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩⟩⟩

def fourColors (k : input0370.graph.Coloring Color) : input0370.graph.Coloring (Fin 4) :=
  SimpleGraph.recolorOfEquiv input0370.graph ConfigurationFaceGraph.colorEquiv.symm k

/-- Exterior repair and both construction paths retain the same actual witness. -/
theorem compatible_histories (et : List Color) (hlen : et.length = 12)
    (hzero : (0 : Color) ∉ et) (hsum : et.sum = 0)
    (Q : List Color → Prop) (closed : KempeClosed Q) (outside : Q et) :
    ∃ es, ∃ k : input0370.graph.Coloring Color,
      es = trace (boundary0370.map k) ∧ Q es ∧
      ∃ result : input0604.graph.Coloring (Fin 4),
        semantics.Supports leftRoute (fourColors k) result ∧
        semantics.Supports rightRoute (fourColors k) result ∧
        ∀ v, result (insert0464_0604 (some (insert0370_0464 (some v)))) = fourColors k v := by
  obtain ⟨es, ⟨k, hk⟩, hQ⟩ := NearLinearFiveRepair.repair0370 et hlen hzero hsum Q closed outside
  refine ⟨es, k, hk, hQ, lift0464_0604 (lift0370_0464 (fourColors k)),
    left_history _, right_history _, ?_⟩
  intro v
  simp only [retained0464_0604, retained0370_0464]

end FourColor.NearLinearFiveGSLT
