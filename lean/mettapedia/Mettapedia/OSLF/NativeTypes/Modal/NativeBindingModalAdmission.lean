import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingLocalValues
import Mettapedia.OSLF.NativeTypes.Generation.NativeModalHeaders

/-!
# Computed semantic admission for native operational projections

Program carriers must be authored object sorts. Local focus and capture
prefixes are independently decoded into base-sort binder scopes, and each
complete native carrier must have a binding spine. These checks distinguish
formation of native arrow syntax from its earned authored-body reading.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalAdmission

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation
open NativeBindingLocalValues NativeEventDeclarations

variable {plan : Plan}

/-- Traverse a finite dependent family, retaining original index order. -/
def allFin? : {n : Nat} → {A : Fin n → Type} →
    (∀ index, Option (A index)) → Option (∀ index, A index)
  | 0, _, _ => some (fun index => index.elim0)
  | n + 1, A, candidate => do
      let first ← candidate 0
      let rest ← allFin? (A := fun index : Fin n => A index.succ)
        (fun index => candidate index.succ)
      pure (Fin.cases first rest)

theorem allFin?_complete {n : Nat} {A : Fin n → Type} (candidate : ∀ index, Option (A index))
    (complete : ∀ index, ∃ value, candidate index = some value) :
    ∃ values, allFin? candidate = some values := by
  induction n with
  | zero => exact ⟨_, rfl⟩
  | succ n ih =>
      obtain ⟨first, firstFound⟩ := complete 0
      obtain ⟨rest, restFound⟩ := ih (A := fun index : Fin n => A index.succ)
        (fun index => candidate index.succ) (fun index => complete index.succ)
      simp only [allFin?, firstFound, restFound]
      exact ⟨_, rfl⟩

def objectSort? (carrier : NativeSignature.Carrier plan.snapshot.language) :
    Option {position : Fin plan.snapshot.language.types.length | carrier = .sort position} :=
  match carrier with
  | .sort position => some ⟨position, rfl⟩
  | .function _ _ => none

theorem objectSort?_complete (carrier : NativeSignature.Carrier plan.snapshot.language)
    (position : Fin plan.snapshot.language.types.length) (base : carrier = .sort position) :
    ∃ decoded, objectSort? carrier = some decoded := by
  cases base
  exact ⟨_, rfl⟩

structure Admitted (header : NativeModalHeaders.Header plan) where
  programPosition : Fin plan.snapshot.language.types.length
  program : header.program = .sort programPosition
  focus : Shape (schema plan header.origin).focusBound (schema plan header.origin).focusCarrier
    header.focusArgument
  rely : ∀ index : Fin header.rely.length,
    Shape header.rely[index].slot.dependencies header.rely[index].slot.expected header.rely[index].carrier
  matched : ∀ index : Fin header.matched.length,
    Shape header.matched[index].slot.dependencies header.matched[index].slot.expected header.matched[index].carrier

def parameter? {authored : Rules.Schema plan} (parameter : NativeModalParameters.Parameter authored) :
    Option (Shape parameter.slot.dependencies parameter.slot.expected parameter.carrier) :=
  shape? parameter.slot.dependencies parameter.slot.expected parameter.carrier
    (NativeModalParameters.source authored parameter)

def check? (header : NativeModalHeaders.Header plan) : Option (Admitted header) := do
  let program ← objectSort? header.program
  if represented : header.focusArgument.source =
      (schema plan header.origin).focusBound.reverse.foldr TypeExpr.arrow
        (schema plan header.origin).focusCarrier then
    let focus ← shape? _ _ header.focusArgument represented
    let rely ← allFin? (fun index : Fin header.rely.length => parameter? header.rely[index])
    let matched ← allFin? (fun index : Fin header.matched.length => parameter? header.matched[index])
    pure ⟨program.val, program.property, focus, rely, matched⟩
  else none

theorem check?_complete {header : NativeModalHeaders.Header plan} (admitted : Admitted header) :
    ∃ decoded, check? header = some decoded := by
  obtain ⟨program, programFound⟩ := objectSort?_complete header.program
    admitted.programPosition admitted.program
  obtain ⟨focus, focusFound⟩ := shape?_complete admitted.focus admitted.focus.represented
  obtain ⟨rely, relyFound⟩ := allFin?_complete
    (fun index : Fin header.rely.length => parameter? header.rely[index])
    (fun index => shape?_complete (admitted.rely index) (NativeModalParameters.source _ _))
  obtain ⟨matched, matchedFound⟩ := allFin?_complete
    (fun index : Fin header.matched.length => parameter? header.matched[index])
    (fun index => shape?_complete (admitted.matched index) (NativeModalParameters.source _ _))
  unfold check?
  simp only [programFound, admitted.focus.represented, ↓reduceDIte,
    focusFound, relyFound, matchedFound]
  exact ⟨_, rfl⟩

theorem check?_exact (header : NativeModalHeaders.Header plan) :
    (∃ decoded, check? header = some decoded) ↔ Nonempty (Admitted header) := by
  constructor
  · rintro ⟨decoded, _⟩
    exact ⟨decoded⟩
  · rintro ⟨admitted⟩
    exact check?_complete admitted

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalAdmission
