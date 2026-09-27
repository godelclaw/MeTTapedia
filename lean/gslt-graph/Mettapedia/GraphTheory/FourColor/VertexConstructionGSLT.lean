import Mettapedia.GSLT.Core.RelationalRouteSemantics
import Mettapedia.GSLT.Core.ProofRelevantPresentation
import Mettapedia.GraphTheory.FourColor.VertexCodeTrace

/-!
# Operational semantics of actual cubic vertex constructions

Interface sizes are the states of a GSLT. Its authored events retain the
entire valid vertex code, including persistent wires; its semantic steps
forget only the event label. A route therefore retains the construction even
when several different attachments have the same input and output sizes.

The relational interpretation records the intermediate colour words and each
local acceptance proof. For existing nonempty vertex traces, interpretation
is equivalent to an actual colouring of the decoded tangle. This imports the
literal decoder's theorem rather than postulating a realization callback.
Incidence validity alone does not assert planarity of a construction.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexConstructionGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.ProofRelevantPresentation
open Mettapedia.GSLT.RelationalRouteSemantics
open TubeSlab.VertexTransfer VertexCodePartition VertexCodeRealization VertexCodeTrace

/-- A finite attachment instruction with all incidence obligations checked. -/
abbrev Event (left right : Nat) := {code : Code left right // Valid code}

/-- Structural steps do not require a colouring to exist. -/
def theory : GSLT where
  Term := Nat
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun left right => Nonempty (Event left right)
  rewrites_resp_left := by
    intro left left' right equal event
    subst left'
    exact ⟨right, event, rfl⟩
  rewrites_resp_right := by
    intro left right right' event equal
    subst right'
    exact event

/-- Retain the actual code rather than only an arity transition. -/
def presentation : StepPresentation theory where
  Evidence := Event
  erases_iff := fun _ _ => Iff.rfl

def colouring : Semantics Event where
  State width := Fin width → Color
  step event x y := PLift (CodeAccepts event.val x y)

def single {left right : Nat} (event : Event left right) : Route Event left right :=
  .cons event (.refl right)

theorem supports_single_iff {left right : Nat} (event : Event left right)
    (x : Fin left → Color) (y : Fin right → Color) :
    colouring.Supports (single event) x y ↔ CodeAccepts event.val x y := by
  constructor
  · rintro ⟨⟨middle, accepted, equal⟩⟩
    cases equal.down.down
    exact accepted.down
  · intro accepted
    exact ⟨⟨y, ⟨accepted⟩, ⟨⟨rfl⟩⟩⟩⟩

/-- Interpret a physical construction trace as its ordered authored route. -/
def route : {right : Nat} → Trace right → Route Event 0 right
  | _, .first code valid => single ⟨code, valid⟩
  | _, .step before code valid => (route before).append (single ⟨code, valid⟩)

/-- Compatible route witnesses are exactly the existing finite evaluator. -/
theorem supports_route_iff {right : Nat} (trace : Trace right)
    (y : Fin right → Color) :
    colouring.Supports (route trace) Fin.elim0 y ↔ trace.Evaluates y := by
  induction trace with
  | first code valid => exact supports_single_iff ⟨code, valid⟩ Fin.elim0 y
  | step before code valid ih =>
      exact (colouring.supports_append_iff (route before)
        (single ⟨code, valid⟩) Fin.elim0 y).trans
        (exists_congr fun x => and_congr (ih x)
          (supports_single_iff ⟨code, valid⟩ x y))

/-- The operational semantics has the exact literal graph-colouring meaning. -/
theorem supports_realization_iff {right : Nat} (trace : Trace right)
    (y : Fin right → Color) :
    colouring.Supports (route trace) Fin.elim0 y ↔ Supports trace.realize y :=
  (supports_route_iff trace y).trans (trace.support_exact y).symm

/-- Empty terminal interface means an actual colouring of the closed object. -/
theorem closed_realization_iff (trace : Trace 0) :
    colouring.Supports (route trace) Fin.elim0 Fin.elim0 ↔
      ∃ color, trace.realize.IsTaitColoring color :=
  (supports_route_iff trace Fin.elim0).trans trace.closed_exact.symm

/-- A certified change of construction transports literal boundary support. -/
theorem replacement_preserves_support {right : Nat} {first second : Trace right}
    (replacement : colouring.Replacement (route first) (route second))
    {word : Fin right → Color} (supported : Supports first.realize word) :
    Supports second.realize word :=
  (supports_realization_iff second word).mp
    (colouring.supports_of_replacement replacement
      ((supports_realization_iff first word).mpr supported))

/-- The direction needed by a reductive proof: a witness transport from the
smaller construction to the original reconstructs an original colouring. -/
theorem reconstruct_closed {smaller original : Trace 0}
    (reconstruction : colouring.Replacement (route smaller) (route original))
    (coloured : ∃ color, smaller.realize.IsTaitColoring color) :
    ∃ color, original.realize.IsTaitColoring color :=
  (closed_realization_iff original).mp
    (colouring.supports_of_replacement reconstruction
      ((closed_realization_iff smaller).mpr coloured))

end Mettapedia.GraphTheory.FourColor.VertexConstructionGSLT
