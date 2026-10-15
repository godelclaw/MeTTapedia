import Mettapedia.OSLF.Syntax.RhoCanonicalNamePairs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Complete finite quotation-origin catalogues on rho equation classes

The canonical name either exposes a process body or is a bound name. Readback
of an exposed body supplies one origin; dropping the supplied name always
supplies an origin by the source name equation. These actual source process
classes form a catalogue of at most two members. Completeness is proved from
canonical equality reflection and the actual sorted readback, rather than
assuming quotation is injective or selecting arbitrary raw representatives.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoFiniteQuotationOrigins

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding RhoIntrinsicReadback RhoCanonicalNamePairs
open MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

local instance processClassDecision (context : Ctx sig) : DecidableEq (Process context) :=
  equationClassDecision context Srt.pr

def dropBody : Pattern → Option Pattern
  | .apply "PDrop" [name] => some name
  | _ => none

theorem dropBody_shape {pattern name : Pattern} (readout : dropBody pattern = some name) :
    pattern = .apply "PDrop" [name] := by
  unfold dropBody at readout
  split at readout
  · simp_all only [Option.some.injEq]
  · cases readout

def bodyOrigin (context : Ctx sig) : Pattern → Option (Process context)
  | .apply "NQuote" [body] => readProcessClass context body
  | _ => none

theorem bodyOrigin_sound {context : Ctx sig} {name : Name context} {process : Process context}
    (readout : bodyOrigin context (encodeEquationClass name) = some process) :
    quote process = name := by
  unfold bodyOrigin at readout
  split at readout
  · next body same =>
      have decoded := read_encoded_equation_class name
      change readNameClass context (encodeEquationClass name) = some name at decoded
      rw [same, readNameClass_quote, readout] at decoded
      exact Option.some.inj decoded
  · cases readout

theorem bodyOrigin_of_not_drop {context : Ctx sig} (process : Process context)
    (notDrop : ∀ name, encodeEquationClass process ≠ .apply "PDrop" [name]) :
    bodyOrigin context (encodeEquationClass (quote process)) = some process := by
  rw [encode_quote, normalizeQuote_eq_quote_of_not_drop notDrop]
  change readProcessClass context (encodeEquationClass process) = some process
  exact read_encoded_equation_class process

theorem quotation_fibre_complete {context : Ctx sig} (name : Name context)
    (process : Process context) (readout : quote process = name) :
    process = drop name ∨ bodyOrigin context (encodeEquationClass name) = some process := by
  cases dropped : dropBody (encodeEquationClass process) with
  | some child =>
    have shape := dropBody_shape dropped
    have decoded := read_encoded_equation_class process
    change readProcessClass context (encodeEquationClass process) = some process at decoded
    rw [shape, readProcessClass_drop] at decoded
    obtain ⟨childName, _, processReadout⟩ := Option.map_eq_some_iff.mp decoded
    have sameName : childName = name :=
      (quote_drop childName).symm.trans ((congrArg quote processReadout).trans readout)
    exact Or.inl (processReadout.symm.trans (congrArg drop sameName))
  | none =>
    have notDrop : ∀ child, encodeEquationClass process ≠ .apply "PDrop" [child] := by
      intro child same
      rw [same] at dropped
      cases dropped
    have decoded := bodyOrigin_of_not_drop process notDrop
    rw [readout] at decoded
    exact Or.inr decoded

def origins {context : Ctx sig} (name : Name context) : Finset (Process context) :=
  match bodyOrigin context (encodeEquationClass name) with
  | none => {drop name}
  | some process => {drop name, process}

theorem mem_origins {context : Ctx sig} (name : Name context) (process : Process context) :
    process ∈ origins name ↔
      process = drop name ∨ bodyOrigin context (encodeEquationClass name) = some process := by
  unfold origins
  split
  · next absent =>
    rw [Finset.mem_singleton]
    constructor
    · exact Or.inl
    · rintro (direct | impossible)
      · exact direct
      · rw [absent] at impossible
        cases impossible
  · next body readout =>
    rw [Finset.mem_insert, Finset.mem_singleton, readout]
    simp only [Option.some.injEq]
    constructor
    · rintro (direct | same)
      · exact Or.inl direct
      · exact Or.inr same.symm
    · rintro (direct | same)
      · exact Or.inl direct
      · exact Or.inr same.symm

theorem quotation_fibre_iff {context : Ctx sig} (name : Name context) (process : Process context) :
    quote process = name ↔ process ∈ origins name := by
  rw [mem_origins]
  constructor
  · exact quotation_fibre_complete name process
  · rintro (rfl | readout)
    · exact quote_drop name
    · exact bodyOrigin_sound readout

theorem origins_card_le_two {context : Ctx sig} (name : Name context) : (origins name).card ≤ 2 := by
  unfold origins
  split
  · rw [Finset.card_singleton]
    exact Nat.le_succ 1
  · next body readout =>
    simpa only [Finset.card_singleton] using
      Finset.card_insert_le (drop name) ({body} : Finset (Process context))

def originEquiv {context : Ctx sig} (name : Name context) :
    Origin name ≃ {process : Process context // process ∈ origins name} where
  toFun := fun origin => ⟨origin.val, (quotation_fibre_iff name origin.val).mp origin.property⟩
  invFun := fun member => ⟨member.val, (quotation_fibre_iff name member.val).mpr member.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem origin_card_eq_catalogue {context : Ctx sig} (name : Name context) :
    Nat.card (Origin name) = (origins name).card := by
  rw [Nat.card_congr (originEquiv name)]
  exact Nat.card_eq_finsetCard _

theorem origin_card_le_two {context : Ctx sig} (name : Name context) : Nat.card (Origin name) ≤ 2 := by
  rw [origin_card_eq_catalogue]
  exact origins_card_le_two name

theorem visible_body_origin : bodyOrigin [] (encodeEquationClass (quote visible)) = some visible := rfl

theorem visible_two_origins : (origins (quote visible)).card = 2 := by
  rw [origins, visible_body_origin]
  exact Finset.card_pair suspended_not_visible

def openName : Name [Srt.nm] := project (.var .zero)

theorem bound_name_no_body : bodyOrigin [Srt.nm] (encodeEquationClass openName) = none := rfl

theorem bound_name_one_origin : (origins openName).card = 1 := by
  rw [origins, bound_name_no_body]
  exact Finset.card_singleton _

end Mettapedia.OSLF.Binding.RhoFiniteQuotationOrigins
