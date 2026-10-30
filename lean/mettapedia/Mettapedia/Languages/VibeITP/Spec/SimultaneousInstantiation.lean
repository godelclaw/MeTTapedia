import Mettapedia.Languages.VibeITP.Spec.Kernel

/-!
# Simultaneous free-variable instantiation

Reference operation for upstream opcode 26 at `f775d856`. Every supplied
replacement is validated, including shadowed entries. Lookup uses the first
entry for a symbol. The traversal substitutes original children but never
recursively substitutes inside an inserted replacement. Word-overflow guards
are retained. This module does not extend the older binary decoder or assert
that sequential instantiation has the same refusal behavior.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec
namespace SimultaneousInstantiation

structure Entry where
  symbol : SymId
  arity : Nat
  value : Term
deriving Repr

def lookup : List Entry → SymId → Option Entry
  | [], _ => none
  | entry :: rest, symbol =>
      if symbol = entry.symbol then some entry else lookup rest symbol

/-- Resolve arities and validate all arguments before visiting the statement. -/
def prepare (sig : Sig) : List (SymId × Term) → Option (List Entry)
  | [] => some []
  | (F, value) :: rest =>
      match sig F with
      | none => none
      | some info =>
          if info.kind = .fvar ∧ depth sig value ≤ info.arity then
            (prepare sig rest).map (⟨F, info.arity, value⟩ :: ·)
          else none

mutual
def go (sig : Sig) (entries : List Entry) : Nat → Term → Option Term
  | _, .bvar index => some (.bvar index)
  | _, .lit bytes => some (.lit bytes)
  | offset, .app symbol arguments =>
      if hasFvar sig (.app symbol arguments) = false then some (.app symbol arguments)
      else
        match args sig entries symbol offset 0 arguments with
        | none => none
        | some arguments' =>
            match lookup entries symbol with
            | none => some (.app symbol arguments')
            | some entry =>
                match shift sig offset entry.arity entry.value with
                | none => none
                | some value => substBVars sig entry.arity arguments' value 0

def args (sig : Sig) (entries : List Entry) (symbol : SymId) (offset : Nat) :
    Nat → List Term → Option (List Term)
  | _, [] => some []
  | index, argument :: rest =>
      if offset + binderAt sig symbol index < wordBound then
        match go sig entries (offset + binderAt sig symbol index) argument,
            args sig entries symbol offset (index + 1) rest with
        | some argument', some rest' => some (argument' :: rest')
        | _, _ => none
      else none

end

/-- Zero entries copy a closed theorem statement without traversing it. -/
def statement (sig : Sig) (replacements : List (SymId × Term)) (source : Term) :
    Option Term :=
  match prepare sig replacements with
  | none => none
  | some entries =>
      let result := if entries.isEmpty then some source else go sig entries 0 source
      match result with
      | none => none
      | some result => if depth sig result = 0 then some result else none

@[simp] theorem lookup_first (entry : Entry) (rest : List Entry) :
    lookup (entry :: rest) entry.symbol = some entry := by simp [lookup]

mutual
theorem go_singleton (sig : Sig) (entry : Entry) (offset : Nat) (source : Term) :
    go sig [entry] offset source =
      instGo sig entry.symbol entry.arity entry.value offset source := by
  cases source with
  | bvar index => rfl
  | lit bytes => rfl
  | app symbol arguments =>
      simp only [go, instGo, args_singleton sig entry symbol offset 0 arguments]
      split
      · rfl
      · cases instArgs sig entry.symbol entry.arity entry.value symbol offset 0 arguments with
        | none => rfl
        | some values =>
            by_cases same : symbol = entry.symbol <;> simp only [lookup, same, if_true, if_false]
            all_goals rfl
termination_by sizeOf source
decreasing_by
  subst_vars
  simp_wf
  exact Nat.lt_add_of_pos_left (Nat.lt_add_right _ Nat.zero_lt_one)

theorem args_singleton (sig : Sig) (entry : Entry) (symbol : SymId) (offset index : Nat)
    (arguments : List Term) :
    args sig [entry] symbol offset index arguments =
      instArgs sig entry.symbol entry.arity entry.value symbol offset index arguments := by
  cases arguments with
  | nil => rfl
  | cons argument rest =>
      rw [args, instArgs,
        go_singleton sig entry (offset + binderAt sig symbol index) argument,
        args_singleton sig entry symbol offset (index + 1) rest]
      rfl
termination_by sizeOf arguments
decreasing_by
  all_goals subst_vars
  · change sizeOf argument < 1 + sizeOf argument + sizeOf rest
    exact Nat.lt_add_right _ (Nat.lt_add_of_pos_left Nat.zero_lt_one)
  · change sizeOf rest < 1 + sizeOf argument + sizeOf rest
    exact Nat.lt_add_of_pos_left (Nat.lt_add_right _ Nat.zero_lt_one)

end

theorem statement_singleton (sig : Sig) (F : SymId) (value source : Term) :
    statement sig [(F, value)] source = instantiateStatement sig F value source := by
  cases found : sig F with
  | none => simp [statement, prepare, instantiateStatement, found]
  | some info =>
      by_cases valid : info.kind = .fvar ∧ depth sig value ≤ info.arity
      · cases result : instGo sig F info.arity value 0 source <;>
          simp [statement, prepare, instantiateStatement, found, valid, go_singleton, result]
      · simp [statement, prepare, instantiateStatement, found, valid]

@[simp] theorem statement_nil (sig : Sig) (source : Term) :
    statement sig [] source = if depth sig source = 0 then some source else none := rfl

mutual
/-- The traversal depends only on the first applicable entry at each head. -/
theorem go_lookup_ext (sig : Sig) (first second : List Entry)
    (agree : ∀ symbol, lookup first symbol = lookup second symbol)
    (offset : Nat) (source : Term) :
    go sig first offset source = go sig second offset source := by
  cases source with
  | bvar index => rfl
  | lit bytes => rfl
  | app symbol children =>
      rw [go, go, args_lookup_ext sig first second agree symbol offset 0 children,
        agree symbol]
termination_by sizeOf source
decreasing_by
  subst_vars
  simp_wf
  exact Nat.lt_add_of_pos_left (Nat.lt_add_right _ Nat.zero_lt_one)

theorem args_lookup_ext (sig : Sig) (first second : List Entry)
    (agree : ∀ symbol, lookup first symbol = lookup second symbol)
    (symbol : SymId) (offset index : Nat) (children : List Term) :
    args sig first symbol offset index children = args sig second symbol offset index children := by
  cases children with
  | nil => rfl
  | cons child rest =>
      rw [args, args, go_lookup_ext sig first second agree
        (offset + binderAt sig symbol index) child,
        args_lookup_ext sig first second agree symbol offset (index + 1) rest]
termination_by sizeOf children
decreasing_by
  all_goals subst_vars
  · change sizeOf child < 1 + sizeOf child + sizeOf rest
    exact Nat.lt_add_right _ (Nat.lt_add_of_pos_left Nat.zero_lt_one)
  · change sizeOf rest < 1 + sizeOf child + sizeOf rest
    exact Nat.lt_add_of_pos_left (Nat.lt_add_right _ Nat.zero_lt_one)
end

theorem lookup_shadow (first shadow : Entry) (same : first.symbol = shadow.symbol)
    (rest : List Entry) (symbol : SymId) :
    lookup (first :: shadow :: rest) symbol = lookup (first :: rest) symbol := by
  by_cases hit : symbol = first.symbol
  · simp [lookup, hit]
  · have miss : symbol ≠ shadow.symbol := by simpa [← same] using hit
    simp [lookup, hit, miss]

/-- A shadowed entry can be removed from an already validated table.
This does not authorize skipping that entry's initial validation. -/
theorem go_shadow (sig : Sig) (first shadow : Entry) (same : first.symbol = shadow.symbol)
    (rest : List Entry) (offset : Nat) (source : Term) :
    go sig (first :: shadow :: rest) offset source = go sig (first :: rest) offset source :=
  go_lookup_ext sig _ _ (lookup_shadow first shadow same rest) offset source

#print axioms statement_singleton
#print axioms go_lookup_ext
#print axioms go_shadow

end SimultaneousInstantiation
end Mettapedia.Languages.VibeITP.Spec
