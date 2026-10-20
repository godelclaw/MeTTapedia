import Mettapedia.GSLT.Dynamics.ArrayFold
import Mettapedia.GSLT.Core.OperationalReadback

/-!
# Array fold lowering in the shared operational correspondence framework

The same readback and forward contracts used for language implementations
apply to bounded array folds. Each arbitrary target step reads back to one
source fold step, while each source step lifts from every related array slice.
The framework's existing path theorems then cover complete and partial runs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ArrayFold

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting

variable {Item Acc : Type}

def theory (operation : Acc → Item → Acc) : GSLT where
  Term := State Item Acc
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := step? operation source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def compile : OrderedListFold.State Item Acc → State Item Acc
  | .active entries accumulator => .active (StackSlice.ofList entries) accumulator
  | .done result => .done result

@[simp] theorem decode_compile (source : OrderedListFold.State Item Acc) :
    decode (compile source) = source := by
  cases source <;> simp [compile, decode]

/-- Two-sided correspondence from every related slice, including slices with
a nonzero start. No target-only transition is ignored. -/
def correspondence (operation : Acc → Item → Acc) :
    OperationalCorrespondence (OrderedListFold.theory operation) (theory operation) where
  related source target := source = decode target
  readStep := by
    intro origin current next related transition
    subst origin
    refine Or.inr ⟨decode next, ?_, rfl⟩
    apply (step_correspondence operation current (decode next)).1
    change step? operation current = some next at transition
    rw [transition]
    rfl
  forward := by
    intro origin after current related transition
    subst origin
    have lifted := (step_correspondence operation current after).2 transition
    cases executed : step? operation current with
    | none => simp [executed] at lifted
    | some next =>
        have decoded : decode next = after := by
          rw [executed] at lifted
          exact Option.some.inj lifted
        exact ⟨next, ⟨.cons ⟨executed⟩ (.refl next)⟩, decoded.symm⟩

/-- Compilation produces the same relation used by the generic path laws. -/
theorem compiled_related (operation : Acc → Item → Acc)
    (source : OrderedListFold.State Item Acc) :
    (correspondence operation).related source (compile source) := (decode_compile source).symm

end Mettapedia.GSLT.Dynamics.ArrayFold
