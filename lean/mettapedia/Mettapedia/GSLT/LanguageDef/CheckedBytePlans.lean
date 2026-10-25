import Mettapedia.GSLT.LanguageDef.CheckedBytes

/-!
# Admission of recorded byte-buffer permission plans

The input is the permission projection printed by Cesta, not parsed C text.
Scalar computations are erased. Every possible branch is checked, and every
loop backedge, break and continue must restore the entry permissions. A return
discharges local obligations after recording an owned or borrowed result.

Native signatures are conditional contracts. This checker does not establish
their implementations, scalar typing, the source-to-plan projection or C
printing fidelity. Those are separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CheckedBytes

inductive Slot where
  | unit | boolean | u8 | u16 | u32 | u64 | usize | read | write | own
  deriving DecidableEq, Repr

def Slot.permission : Slot → Option Kind
  | .read => some .read
  | .write => some .write
  | .own => some .own
  | _ => none

structure Signature where
  name : String
  params : List Slot
  result : Slot
  sourceParameter : Option Nat := none
  effects : List String := []
  obligation : Option String := none
  allocator : Option (String × String) := none
  deriving DecidableEq, Repr

def transfersOwner (s : Signature) : Bool := s.result == .own || s.params.contains .own

def signatureValid (s : Signature) : Bool :=
  !s.name.isEmpty && !(s.params.contains .unit) && s.effects.Nodup &&
  (match s.result.permission, s.sourceParameter with
   | some .read, some index =>
       s.params[index]? == some .read || s.params[index]? == some .write
   | some .write, some index => s.params[index]? == some .write
   | some .read, none | some .write, none => false
   | _, none => true
   | _, some _ => false) &&
  (match s.obligation with | none => true | some text => !text.isEmpty) &&
  (!transfersOwner s || s.allocator.isSome) &&
  (match s.allocator with
   | none => true
   | some (allocate, release) => !allocate.isEmpty && !release.isEmpty && allocate != release)

inductive Action where
  | acquire (id : Nat) (kind : Kind)
  | borrow (id source : Nat) (kind : Kind) (copy : Bool := false)
  | move (id source : Nat) (kind : Kind)
  | read (id : Nat) (writing : Bool := false)
  | endView (id : Nat) (kind : Kind)
  | drop (id : Nat) (kind : Kind)
  | take (id : Nat)
  | ownResult (id : Nat)
  | borrowResult (source root : Nat) (kind : Kind)
  | invoke (name : String) (arguments : List (Nat × Kind))
  deriving DecidableEq, Repr

def ready (s : State) : Bool := !s.ownedResult && s.borrowedResult.isNone

def require (condition : Bool) : Option Unit := if condition then some () else none

def initial (signature : Signature) : State :=
  let cells := signature.params.zipIdx.filterMap fun (slot, id) =>
    slot.permission.map fun kind => Binding.mk id kind id []
  { cells := cells, external := cells.filterMap fun binding =>
      if binding.kind.loan then some binding.root else none }

def canPass (s : State) (binding : Binding) (mode : Kind) : Bool :=
  match mode with
  | .read => decide (CanAccess s binding false)
  | .write => decide (CanAccess s binding true)
  | .own => binding.kind == .own && decide (Unborrowed s binding.root)
  | .local => false

def callBindings (s : State) : List (Nat × Kind) → Option (List (Binding × Kind))
  | [] => some []
  | (id, mode) :: rest => do
      let binding ← s.find id
      require (canPass s binding mode)
      let others ← callBindings s rest
      pure ((binding, mode) :: others)

def Compatible (first second : Binding × Kind) : Prop :=
  first.1.root ≠ second.1.root ∨ first.2 = .read ∧ second.2 = .read

instance (first second : Binding × Kind) : Decidable (Compatible first second) := by
  unfold Compatible
  infer_instance

/-- Primitive permission transition. Range checks are a separate byte-index
obligation; the projection records which root authorizes each access. -/
def transition (environment : List Signature) (caller : Signature)
    (s : State) (action : Action) : Option State := do
  match action with
  | .acquire id kind =>
      require (ready s && kind.owner && decide (Fresh s id))
      require (kind != .own || (caller.effects.contains "heap" && caller.allocator.isSome))
      pure { s with cells := ⟨id, kind, id, []⟩ :: s.cells }
  | .borrow id source kind copying =>
      require (ready s && kind.loan && decide (Fresh s id))
      let binding ← s.find source
      require (decide (CanAccess s binding (kind == .write)))
      require (!copying || (kind == .read && binding.kind == .read))
      let parents := if copying then binding.ancestors else source :: binding.ancestors
      pure { s with cells := ⟨id, kind, binding.root, parents⟩ :: s.cells }
  | .move id source kind =>
      require (ready s && decide (Fresh s id))
      let binding ← s.find source
      require (binding.kind == kind)
      require (if kind.owner then decide (Unborrowed s binding.root)
        else decide (NoChildren s source))
      pure { s.erase source with cells := { binding with id := id } :: (s.erase source).cells }
  | .read id writing =>
      require (ready s)
      let binding ← s.find id
      require (decide (CanAccess s binding writing))
      pure s
  | .endView id kind =>
      let binding ← s.find id
      require (binding.kind == kind && kind.loan && decide (NoChildren s id))
      pure (s.erase id)
  | .drop id kind =>
      let binding ← s.find id
      require (binding.kind == kind && kind.owner && decide (Unborrowed s binding.root))
      require (kind != .own || (caller.effects.contains "heap" && caller.allocator.isSome))
      pure (s.erase id)
  | .take id =>
      require (ready s)
      let binding ← s.find id
      require (binding.kind == .own && decide (Unborrowed s binding.root))
      pure { s.erase id with ownedResult := true }
  | .ownResult id =>
      require (s.ownedResult && s.borrowedResult.isNone && decide (Fresh s id))
      pure { s with cells := ⟨id, .own, id, []⟩ :: s.cells, ownedResult := false }
  | .borrowResult source root kind =>
      require (ready s && caller.result.permission == some kind && kind.loan && caller.sourceParameter == some root)
      let binding ← s.find source
      require (binding.root == root && decide (CanAccess s binding (kind == .write)))
      pure { s with borrowedResult := some (root, kind) }
  | .invoke name arguments =>
      require (ready s)
      let target ← environment.find? (fun signature => signature.name == name)
      require (arguments.map Prod.snd == target.params.filterMap Slot.permission)
      require (target.effects.all caller.effects.contains)
      require (!transfersOwner target || target.allocator == caller.allocator)
      let bindings ← callBindings s arguments
      require (decide (bindings.Pairwise Compatible))
      let consumed := arguments.filterMap fun (id, kind) => if kind == .own then some id else none
      pure { s with
        cells := s.cells.filter (fun binding => !consumed.contains binding.id)
        ownedResult := target.result == .own }

/-- State validation makes independently supplied plans checkable, even if
their producer omitted an ownership transition or forged a parent chain. -/
def apply (environment : List Signature) (caller : Signature)
    (s : State) (action : Action) : Option State := do
  require (decide (Valid s))
  let next ← transition environment caller s action
  require (decide (Valid next))
  pure next

inductive Plan where
  | done
  | step (action : Action) (next : Plan)
  | ret
  | breakLoop
  | continueLoop
  | branch (yes no next : Plan)
  | loop (body next : Plan)
  deriving DecidableEq, Repr

inductive ExitKind where
  | normal | returned | broke | continued
  deriving DecidableEq, Repr

structure Exit where
  kind : ExitKind
  state : State
  deriving DecidableEq, Repr

def returnAllowed (signature : Signature) (s : State) : Bool :=
  s.cells.isEmpty &&
  if signature.result == .own then s.ownedResult && s.borrowedResult.isNone
  else !s.ownedResult && (match signature.result.permission with
    | some kind => s.borrowedResult == signature.sourceParameter.map (fun root => (root, kind))
    | none => s.borrowedResult.isNone)

def continueExits (run : State → Option (List Exit)) : List Exit → Option (List Exit)
  | [] => some []
  | exit :: rest =>
      (if exit.kind == .normal then run exit.state else some [exit]).bind fun first =>
      (continueExits run rest).bind fun remaining => some (first ++ remaining)

def check (environment : List Signature) (signature : Signature) :
    Plan → State → Option (List Exit)
  | .done, s => some [⟨.normal, s⟩]
  | .step action next, s => do
      let after ← apply environment signature s action
      check environment signature next after
  | .ret, s => do
      require (returnAllowed signature s)
      pure [⟨.returned, s⟩]
  | .breakLoop, s => some [⟨.broke, s⟩]
  | .continueLoop, s => some [⟨.continued, s⟩]
  | .branch yes no next, s => do
      let left ← check environment signature yes s
      let right ← check environment signature no s
      continueExits (check environment signature next) (left ++ right)
  | .loop body next, s => do
      let outcomes ← check environment signature body s
      require (outcomes.all fun exit => exit.kind == .returned || exit.state == s)
      let after ← check environment signature next s
      pure (outcomes.filter (fun exit => exit.kind == .returned) ++ after)

structure Function where
  signature : Signature
  parameters : List (Nat × Slot)
  body : Plan
  deriving DecidableEq, Repr

structure Module where
  foreign : List Signature := []
  functions : List Function
  deriving DecidableEq, Repr

def Module.signatures (m : Module) : List Signature :=
  m.foreign ++ m.functions.map Function.signature

def checkFunction (environment : List Signature) (f : Function) : Bool :=
  signatureValid f.signature && f.signature.obligation.isNone &&
  f.parameters == f.signature.params.zipIdx.map (fun (slot, id) => (id, slot)) &&
  decide (Valid (initial f.signature)) &&
  match check environment f.signature f.body (initial f.signature) with
  | none => false
  | some outcomes => !outcomes.isEmpty && outcomes.all (fun exit => exit.kind == .returned)

def admit (m : Module) : Bool :=
  decide ((m.signatures.map Signature.name).Nodup) &&
  m.foreign.all (fun signature => signatureValid signature && signature.obligation.isSome) &&
  m.functions.all (checkFunction m.signatures)

theorem apply_valid {environment : List Signature} {signature : Signature}
    {first last : State} {action : Action}
    (accepted : apply environment signature first action = some last) : Valid last := by
  simp only [apply, require, bind, Option.bind] at accepted
  split at accepted <;> simp_all
  split at accepted <;> simp_all
  split at accepted <;> simp_all

end Mettapedia.GSLT.LanguageDef.CheckedBytes
