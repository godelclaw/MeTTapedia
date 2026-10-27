import Mettapedia.Algorithms.Compression.SourceFrame
import Mathlib.Tactic

/-!
# Transporting helper ports and rigid source locals

The existing source term carries two disjoint variable families during helper
construction: parameter ports and rigid local ordinals. Compilation places the
locals after the ports; expansion rebases them after the destination entry
frame. Arguments may be terms, so expansion is genuine parallel substitution,
not only variable renaming. No new term or binding calculus is introduced.

The reconstruction law does not establish arbitrary argument readiness or
binding admission. The source profile separately establishes lexical scope,
and the argument-sharing laws separately require established input values.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.LocalFrames

open SourceFrame

variable {V W : Type}

mutual
def substitute (images : V → Term W) : Term V → Term W
  | .var index => images index
  | .literal kind bytes => .literal kind bytes
  | .expr children => .expr (substituteList images children)

def substituteList (images : V → Term W) : List (Term V) → List (Term W)
  | [] => []
  | first :: rest => substitute images first :: substituteList images rest
end

theorem substitute_rename {U : Type} (code : U → V) (images : V → Term W)
    (source : Term U) :
    substitute images (SourceFrame.rename code source) =
      substitute (fun index => images (code index)) source := by
  induction source using Term.rec
    (motive_2 := fun children => substituteList images (children.map (SourceFrame.rename code)) =
      substituteList (fun index => images (code index)) children) with
  | var value => simp only [SourceFrame.rename, substitute]
  | literal kind bytes => simp only [SourceFrame.rename, substitute]
  | expr children result => simpa only [SourceFrame.rename, substitute] using congrArg Term.expr result
  | nil => rfl
  | cons first rest firstResult restResult =>
      simp only [List.map_cons, substituteList, firstResult, restResult]

def address (ports : Nat) : Fin ports ⊕ Nat → Nat
  | .inl port => port.val
  | .inr ordinal => ports + ordinal

def compile {ports : Nat} (body : Term (Fin ports ⊕ Nat)) : Term Nat :=
  SourceFrame.rename (address ports) body

def image (arguments : List (Term Nat)) (entry : Nat) (index : Nat) : Term Nat :=
  if present : index < arguments.length then arguments[index] else .var (entry + (index - arguments.length))

def expand (arguments : List (Term Nat)) (entry : Nat) (body : Term Nat) : Term Nat :=
  substitute (image arguments entry) body

def interpretVariable (arguments : List (Term Nat)) (entry : Nat) :
    Fin arguments.length ⊕ Nat → Term Nat
  | .inl port => arguments[port.val]
  | .inr ordinal => .var (entry + ordinal)

def interpret (arguments : List (Term Nat)) (entry : Nat)
    (body : Term (Fin arguments.length ⊕ Nat)) : Term Nat :=
  substitute (interpretVariable arguments entry) body

theorem image_port (arguments : List (Term Nat)) (entry : Nat) (port : Fin arguments.length) :
    image arguments entry port.val = arguments[port.val] := by
  simp [image, port.isLt]

theorem image_local (arguments : List (Term Nat)) (entry ordinal : Nat) :
    image arguments entry (arguments.length + ordinal) = .var (entry + ordinal) := by
  simp [image, show ¬arguments.length + ordinal < arguments.length by omega]

theorem expand_compile (arguments : List (Term Nat)) (entry : Nat)
    (body : Term (Fin arguments.length ⊕ Nat)) :
    expand arguments entry (compile body) = interpret arguments entry body := by
  rw [expand, compile, substitute_rename]
  have same : (fun index => image arguments entry (address arguments.length index)) =
      interpretVariable arguments entry := by
    funext index
    cases index with
    | inl port => exact image_port arguments entry port
    | inr ordinal => exact image_local arguments entry ordinal
  rw [same]
  rfl

theorem address_injective (ports : Nat) : Function.Injective (address ports) := by
  intro first second same
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          apply congrArg Sum.inl
          apply Fin.ext
          exact same
      | inr second => simp only [address] at same; have := first.isLt; omega
  | inr first =>
      cases second with
      | inl second => simp only [address] at same; have := second.isLt; omega
      | inr second => exact congrArg Sum.inr (Nat.add_left_cancel same)

theorem argument_avoids_locals (arguments : List (Term Nat)) (entry : Nat)
    (namesBound : ∀ port : Fin arguments.length, ∀ index ∈ SourceFrame.occurrences arguments[port.val],
      index < entry) (port : Fin arguments.length) (ordinal : Nat) :
    entry + ordinal ∉ SourceFrame.occurrences arguments[port.val] := by
  intro present
  have := namesBound port _ present
  omega

def unshiftedAddress {ports : Nat} : Fin ports ⊕ Nat → Nat
  | .inl port => port.val
  | .inr ordinal => ordinal

theorem unshifted_names_capture :
    let port : Fin 1 ⊕ Nat := .inl ⟨0, by decide⟩
    let boundName : Fin 1 ⊕ Nat := .inr 0
    port ≠ boundName ∧ unshiftedAddress port = unshiftedAddress boundName ∧
      address 1 port ≠ address 1 boundName := by decide

end Mettapedia.Algorithms.Compression.LocalFrames
