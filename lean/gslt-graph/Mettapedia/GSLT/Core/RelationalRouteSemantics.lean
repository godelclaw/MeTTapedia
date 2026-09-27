import Mettapedia.GSLT.Core.LooseRelationEquipment
import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# Compatible witnesses along operational routes

A step may relate several source and target states, or none. Interpreting a
route retains every intermediate state and each local witness. Concatenation
is interpreted by the existing composition of proof-relevant relations.

A witness map between two routes extends through every serial context and
through composites of authored rewrite cells. No totality or path-lifting
assumption is imposed on the individual step relations.
-/

namespace Mettapedia.GSLT.RelationalRouteSemantics

open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LooseRelationEquipment

universe uObj uStep u uCell

/-- States at interfaces and a witness relation for each authored step. -/
structure Semantics {Object : Type uObj} (Step : Object → Object → Type uStep) where
  State : Object → Type u
  step : {source target : Object} → Step source target →
    Loose (State source) (State target)

namespace Semantics

noncomputable section

variable {Object : Type uObj} {Step : Object → Object → Type uStep}
variable (semantics : Semantics.{uObj, uStep, u} Step)

/-- All the compatible choices along a specified route, retained as data. -/
def Witness (semantics : Semantics.{uObj, uStep, u} Step) : {source target : Object} → Route Step source target →
    Loose (semantics.State source) (semantics.State target)
  | _, _, .refl _ => identity
  | _, _, .cons event rest => comp (semantics.step event) (semantics.Witness rest)

/-- Splitting a route at a chosen interface gives exactly one intermediate
state and a witness for each side. This equivalence retains multiplicities. -/
def appendEquiv {a b c : Object} (first : Route Step a b)
    (second : Route Step b c) (x : semantics.State a) (z : semantics.State c) :
    semantics.Witness (first.append second) x z ≃
      comp (semantics.Witness first) (semantics.Witness second) x z := by
  induction first with
  | refl => exact (compIdentityLeft (semantics.Witness second) x z).symm
  | @cons a middle b event rest ih =>
      exact (Equiv.sigmaCongrRight fun y =>
        Equiv.prodCongr (Equiv.refl _) (ih second y)).trans
        (compAssoc (semantics.step event) (semantics.Witness rest)
          (semantics.Witness second) x z).symm

/-- The support of the witness relation forgets witnesses only at the end. -/
def Supports {a b : Object} (route : Route Step a b)
    (x : semantics.State a) (y : semantics.State b) : Prop :=
  Nonempty (semantics.Witness route x y)

theorem supports_append_iff {a b c : Object} (first : Route Step a b)
    (second : Route Step b c) (x : semantics.State a) (z : semantics.State c) :
    semantics.Supports (first.append second) x z ↔
      ∃ y, semantics.Supports first x y ∧ semantics.Supports second y z := by
  constructor
  · rintro ⟨witness⟩
    obtain ⟨y, left, right⟩ := semantics.appendEquiv first second x z witness
    exact ⟨y, ⟨left⟩, ⟨right⟩⟩
  · rintro ⟨y, ⟨left⟩, ⟨right⟩⟩
    exact ⟨(semantics.appendEquiv first second x z).symm ⟨y, left, right⟩⟩

/-- A route replacement which preserves its exterior states and transports
actual witnesses. The direction of this map matters for reconstruction. -/
abbrev Replacement {a b : Object} (first second : Route Step a b) :=
  Cell id id (semantics.Witness first) (semantics.Witness second)

def replaceAfter {a b c : Object} (initial : Route Step a b)
    {first second : Route Step b c} (replacement : semantics.Replacement first second) :
    semantics.Replacement (initial.append first) (initial.append second) where
  map := fun {x z} witness =>
    (semantics.appendEquiv initial second x z).symm
      ((Cell.hcomp (Cell.id (semantics.Witness initial)) replacement).map
        (semantics.appendEquiv initial first x z witness))

def replaceBefore {a b c : Object} {first second : Route Step a b}
    (replacement : semantics.Replacement first second) (suffix : Route Step b c) :
    semantics.Replacement (first.append suffix) (second.append suffix) where
  map := fun {x z} witness =>
    (semantics.appendEquiv second suffix x z).symm
      ((Cell.hcomp replacement (Cell.id (semantics.Witness suffix))).map
        (semantics.appendEquiv first suffix x z witness))

/-- Replacing a middle route is sound in every well-typed serial context. -/
def replaceInContext {a b c d : Object} (initial : Route Step a b)
    {first second : Route Step b c} (replacement : semantics.Replacement first second)
    (suffix : Route Step c d) :
    semantics.Replacement ((initial.append first).append suffix)
      ((initial.append second).append suffix) :=
  semantics.replaceBefore (semantics.replaceAfter initial replacement) suffix

/-- Local witness transports interpret all finite composites and serial
whiskerings of the authored rewrite cells. -/
def interpretCells (semantics : Semantics.{uObj, uStep, u} Step)
    {Generator : {a b : Object} → Route Step a b → Route Step a b → Type uCell}
    (onGenerator : ∀ {a b} {first second : Route Step a b},
      Generator first second → semantics.Replacement first second) :
    {a b : Object} → {first second : Route Step a b} →
      GeneratedTwoCell Generator first second → semantics.Replacement first second
  | _, _, _, _, .refl route => Cell.id (semantics.Witness route)
  | _, _, _, _, .generator cell => onGenerator cell
  | _, _, _, _, .vertical first second =>
      Cell.vcomp (semantics.interpretCells onGenerator first)
        (semantics.interpretCells onGenerator second)
  | _, _, _, _, .whiskerLeft initial cell =>
      semantics.replaceAfter initial (semantics.interpretCells onGenerator cell)
  | _, _, _, _, .whiskerRight suffix cell =>
      semantics.replaceBefore (semantics.interpretCells onGenerator cell) suffix

theorem supports_of_replacement {a b : Object} {first second : Route Step a b}
    (replacement : semantics.Replacement first second)
    {x : semantics.State a} {y : semantics.State b}
    (supported : semantics.Supports first x y) : semantics.Supports second x y := by
  obtain ⟨witness⟩ := supported
  exact ⟨replacement.map witness⟩

/-- A terminal observation restricts the compatible choices by the entire
remaining route, without requiring all possible states to extend. -/
def Viable {a b : Object} (route : Route Step a b)
    (terminal : semantics.State b → Prop) (x : semantics.State a) : Prop :=
  ∃ y, semantics.Supports route x y ∧ terminal y

/-- Backward viability composes exactly. This is a criterion, not an
assertion that the resulting viable set is nonempty. -/
theorem viable_append_iff {a b c : Object} (first : Route Step a b)
    (second : Route Step b c) (terminal : semantics.State c → Prop)
    (x : semantics.State a) :
    semantics.Viable (first.append second) terminal x ↔
      semantics.Viable first (semantics.Viable second terminal) x := by
  constructor
  · rintro ⟨z, supported, final⟩
    obtain ⟨y, left, right⟩ := (semantics.supports_append_iff first second x z).mp supported
    exact ⟨y, left, z, right, final⟩
  · rintro ⟨y, left, z, right, final⟩
    exact ⟨z, (semantics.supports_append_iff first second x z).mpr ⟨y, left, right⟩,
      final⟩

end
end Semantics
end Mettapedia.GSLT.RelationalRouteSemantics
