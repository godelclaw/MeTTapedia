import Mettapedia.Computability.WordTemplateMachine
import Mettapedia.Languages.OpenTheory.SyntaxEncoding
import Mettapedia.Languages.OpenTheory.DerivedRulesEquality
import Mettapedia.Languages.HOLLight.PrimitiveTransport

/-!
# Executed instantiation of fixed scoped HOL templates

Each fixed original de Bruijn term compiles to finite control that emits its
literal syntax and copies independently encoded closed arguments at precisely
their original binder positions. Binder depth is computed from the authored
term. Names, types and constant provenance retain the shared codec's complete
payload. Single discharges and outermost-first sequences use the original
`DBTerm.instantiateAt`; dynamic values live entirely on stacks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.TemplateInstantiationMachine

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine
open Turing StateTransition Polynomial

/-- The existing complete raw-term codec, on a finite five-symbol alphabet. -/
def termWire (value : DBTerm) : List Alphabet := encodeData (putTerm value)

/-- Fixed literal storage remains separate from dynamic substitution holes. -/
def literals (word : List Alphabet) : Template Alphabet := word.map some

/-- Substitution compiles under binders at their physical depth; other bound
indices remain complete unchanged encoded fields. -/
def compile (depth : Nat) : DBTerm → Template Alphabet
  | .const symbol annotation => literals (termWire (.const symbol annotation))
  | .free value => literals (termWire (.free value))
  | .bound index => if index = depth then [none] else literals (termWire (.bound index))
  | .app function argument =>
      literals ([4] ++ encodeData (.atom 3) ++ [4]) ++ compile depth function ++ compile depth argument
  | .abs domain body =>
      literals ([4] ++ encodeData (.atom 4) ++ [4] ++ encodeData (putTy domain)) ++ compile (depth + 1) body
termination_by term => sizeOf term

/-- The emitted word is exactly the independently encoded original substitution,
including repeated occurrences and scope-sensitive negative positions. -/
theorem compile_exact (depth : Nat) (body replacement : DBTerm) :
    instantiate (compile depth body) (termWire replacement) =
      termWire (DBTerm.instantiateAt replacement depth body) := by
  induction body generalizing depth with
  | const symbol annotation => simp [compile, literals, DBTerm.instantiateAt]
  | free value => simp [compile, literals, DBTerm.instantiateAt]
  | bound index =>
      by_cases same : index = depth <;> simp [compile, literals, DBTerm.instantiateAt, same]
  | app function argument firstIH secondIH =>
      simp only [compile, literals, DBTerm.instantiateAt, instantiate_append, instantiate_literals, firstIH, secondIH]
      simp [termWire, putTerm, encodeData_pair, List.append_assoc]
  | abs domain body ih =>
      simp only [compile, literals, DBTerm.instantiateAt, instantiate_append, instantiate_literals, ih]
      simp [termWire, putTerm, encodeData_pair, List.append_assoc]

/-- Actual finite-stack execution computes the original template operation.
The clock is linear in the full encoded argument, for each fixed template. -/
def outputs (depth : Nat) (body replacement : DBTerm) :
    TM2OutputsInTime (machine (compile depth body)) (termWire replacement)
      (some (termWire (DBTerm.instantiateAt replacement depth body)))
      (4 * ((compile depth body).length + 1) * ((termWire replacement).length + 1)) := by
  rw [← compile_exact depth body replacement]
  exact Mettapedia.Computability.WordTemplateMachine.outputs
    (compile depth body) (termWire replacement)

/-- A checked closed argument removes the actual discharged binder while
preserving the original type judgment. -/
theorem typed_result (body : DBTerm) (argument : CanonicalTerm) (codomain : Ty)
    (checkedBody : body.inferType [argument.ty] = some codomain) :
    (DBTerm.instantiateAt argument.term 0 body).inferType [] = some codomain := by
  simpa only [List.nil_append, List.length_nil] using
    DBTerm.inferType_instantiateAt argument.term body argument.ty argument.checked [] checkedBody

/-- Polynomial-time realizability relates the original AST operation to its
actual finite input and output words, rather than an independently chosen clock. -/
noncomputable def realization (depth : Nat) (body : DBTerm) :
    TM2ComputableInPolyTime termWire termWire (fun replacement => DBTerm.instantiateAt replacement depth body) where
  tm := machine (compile depth body)
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C (4 * ((compile depth body).length + 1)) * (X + C 1)
  outputsFun replacement := by
    change TM2OutputsInTime (machine (compile depth body)) ((termWire replacement).map id)
      (some ((termWire (DBTerm.instantiateAt replacement depth body)).map id)) _
    simp only [List.map_id_fun]
    simpa using outputs depth body replacement


namespace Controls

/-- Both occurrences splice the complete argument; they do not coalesce into
one occurrence or inspect only the argument's constructor. -/
theorem repeated_slots (operator : SourceVar) (replacement : DBTerm) :
    instantiate (compile 0 (.app (.app (.free operator) (.bound 0)) (.bound 0))) (termWire replacement) =
      termWire (.app (.app (.free operator) replacement) replacement) := by
  simpa [DBTerm.instantiateAt] using compile_exact 0
    (.app (.app (.free operator) (.bound 0)) (.bound 0)) replacement

/-- The deeper target index changes, while the nearer local binder remains. -/
theorem deeper_scope (domain : Ty) (replacement : DBTerm) :
    instantiate (compile 0 (.abs domain (.app (.bound 1) (.bound 0)))) (termWire replacement) =
      termWire (.abs domain (.app replacement (.bound 0))) := by
  simpa [DBTerm.instantiateAt] using compile_exact 0 (.abs domain (.app (.bound 1) (.bound 0))) replacement

/-- A non-target bound index is not replaced merely because it is a bound node. -/
theorem nearby_binder_unchanged (replacement : DBTerm) :
    instantiate (compile 0 (.bound 1)) (termWire replacement) = termWire (.bound 1) := by
  simpa [DBTerm.instantiateAt] using compile_exact 0 (.bound 1) replacement

/-- An unused argument contributes no field to the resulting original AST. -/
theorem unused_argument (value : SourceVar) (replacement : DBTerm) :
    instantiate (compile 0 (.free value)) (termWire replacement) = termWire (.free value) := by
  simpa [DBTerm.instantiateAt] using compile_exact 0 (.free value) replacement

end Controls

namespace Indexed

open Mettapedia.Computability.WordTemplateMachine.Indexed

/-- Original single-binder operations in outermost-first order. Each argument
is checked closed, so later discharges cannot change an earlier replacement. -/
def sequence : List CanonicalTerm → Nat → DBTerm → DBTerm
  | [], _, body => body
  | argument :: arguments, depth, body =>
      DBTerm.instantiateAt argument.term depth (sequence arguments (depth + 1) body)

theorem sequence_const (arguments : List CanonicalTerm) (depth : Nat) (symbol : Const) (annotation : Ty) :
    sequence arguments depth (.const symbol annotation) = .const symbol annotation := by
  induction arguments generalizing depth with
  | nil => rfl
  | cons argument rest ih => simp [sequence, ih, DBTerm.instantiateAt]

theorem sequence_free (arguments : List CanonicalTerm) (depth : Nat) (value : SourceVar) :
    sequence arguments depth (.free value) = .free value := by
  induction arguments generalizing depth with
  | nil => rfl
  | cons argument rest ih => simp [sequence, ih, DBTerm.instantiateAt]

theorem sequence_app (arguments : List CanonicalTerm) (depth : Nat) (function argument : DBTerm) :
    sequence arguments depth (.app function argument) =
      .app (sequence arguments depth function) (sequence arguments depth argument) := by
  induction arguments generalizing depth with
  | nil => rfl
  | cons replacement rest ih => simp [sequence, ih, DBTerm.instantiateAt]

theorem sequence_abs (arguments : List CanonicalTerm) (depth : Nat) (domain : Ty) (body : DBTerm) :
    sequence arguments depth (.abs domain body) = .abs domain (sequence arguments (depth + 1) body) := by
  induction arguments generalizing depth with
  | nil => rfl
  | cons replacement rest ih => simp [sequence, ih, DBTerm.instantiateAt]

/-- The same ordered sequence removes exactly the admitted original formal
context, preserving any local context and the independently checked result type. -/
theorem sequence_typed (arguments : List CanonicalTerm) (context : List Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType (context ++ arguments.map CanonicalTerm.ty) = some codomain) :
    (sequence arguments context.length body).inferType context = some codomain := by
  induction arguments generalizing context with
  | nil => simpa [sequence] using checkedBody
  | cons argument rest ih =>
      have bodyWithTail : body.inferType ((context ++ [argument.ty]) ++ rest.map CanonicalTerm.ty) = some codomain := by
        simpa [List.append_assoc] using checkedBody
      have tail := ih (context ++ [argument.ty]) bodyWithTail
      have discharged := DBTerm.inferType_instantiateAt argument.term
        (sequence rest (context.length + 1) body) argument.ty argument.checked context
        (by simpa using tail)
      exact discharged

theorem sequence_closed (arguments : List CanonicalTerm) (depth : Nat) (body : CanonicalTerm) :
    sequence arguments depth body.term = body.term := by
  induction arguments generalizing depth with
  | nil => rfl
  | cons argument rest ih =>
      rw [sequence, ih]
      exact DBTerm.instantiateAt_closed body.checked argument.term depth

/-- Closed replacements justify combining separately checked binder discharges
into the original formal interval. Nearby local indices remain untouched. -/
theorem sequence_bound (arguments : List CanonicalTerm) (depth index : Nat) :
    sequence arguments depth (.bound index) =
      if inside : depth ≤ index ∧ index < depth + arguments.length then
        (arguments[index - depth]'(by omega)).term else .bound index := by
  induction arguments generalizing depth with
  | nil => simp [sequence]
  | cons argument rest ih =>
      simp only [sequence, ih]
      by_cases first : index = depth
      · subst index
        simp
      · by_cases later : depth + 1 ≤ index ∧ index < depth + 1 + rest.length
        · rw [dif_pos later, DBTerm.instantiateAt_closed (rest[index - (depth + 1)]'(by omega)).checked argument.term depth]
          have whole : depth ≤ index ∧ index < depth + (argument :: rest).length := by
            simp only [List.length_cons]
            omega
          have offset : index - depth = index - (depth + 1) + 1 := by omega
          rw [dif_pos whole]
          simp only [offset, List.getElem_cons_succ]
        · rw [dif_neg later]
          have outside : ¬(depth ≤ index ∧ index < depth + (argument :: rest).length) := by
            simp only [List.length_cons]
            omega
          rw [dif_neg outside]
          exact DBTerm.instantiateAt_other argument.term depth index first

def argumentWords (arguments : List CanonicalTerm) : Fin arguments.length → List Alphabet :=
  fun index => ((arguments[index.val]?).map fun argument => termWire argument.term).getD []

/-- A single fixed authored body refers to its original finite formal interval.
The argument vector is never baked into the generated control. -/
def compile (arity depth : Nat) : DBTerm → Mettapedia.Computability.WordTemplateMachine.Indexed.Template Alphabet arity
  | .const symbol annotation => (termWire (.const symbol annotation)).map Sum.inl
  | .free value => (termWire (.free value)).map Sum.inl
  | .bound index =>
      if inside : depth ≤ index ∧ index < depth + arity then [.inr ⟨index - depth, by omega⟩]
      else (termWire (.bound index)).map Sum.inl
  | .app function argument =>
      ([4] ++ encodeData (.atom 3) ++ [4]).map Sum.inl ++ compile arity depth function ++ compile arity depth argument
  | .abs domain body =>
      ([4] ++ encodeData (.atom 4) ++ [4] ++ encodeData (putTy domain)).map Sum.inl ++ compile arity (depth + 1) body
termination_by term => sizeOf term

theorem compile_exact (arguments : List CanonicalTerm) (depth : Nat) (body : DBTerm) :
    Mettapedia.Computability.WordTemplateMachine.Indexed.instantiate
      (compile arguments.length depth body) (argumentWords arguments) =
      termWire (sequence arguments depth body) := by
  induction body generalizing depth with
  | const symbol annotation =>
      rw [sequence_const]
      simp [compile]
  | free value =>
      rw [sequence_free]
      simp [compile]
  | bound index =>
      rw [sequence_bound]
      by_cases inside : depth ≤ index ∧ index < depth + arguments.length
      · simp [compile, inside, Mettapedia.Computability.WordTemplateMachine.Indexed.instantiate, argumentWords]
      · simpa only [compile, dif_neg inside] using
          Mettapedia.Computability.WordTemplateMachine.Indexed.instantiate_literals
            (termWire (.bound index)) (argumentWords arguments)
  | app function argument firstIH secondIH =>
      rw [sequence_app]
      simp only [compile, Mettapedia.Computability.WordTemplateMachine.Indexed.instantiate_append,
        Mettapedia.Computability.WordTemplateMachine.Indexed.instantiate_literals, firstIH, secondIH]
      simp [termWire, putTerm, encodeData_pair, List.append_assoc]
  | abs domain body ih =>
      rw [sequence_abs]
      simp only [compile, Mettapedia.Computability.WordTemplateMachine.Indexed.instantiate_append,
        Mettapedia.Computability.WordTemplateMachine.Indexed.instantiate_literals, ih]
      simp [termWire, putTerm, encodeData_pair, List.append_assoc]

/-- The finite tuple representation does not change original argument order. -/
theorem compile_exact_values (arity depth : Nat) (body : DBTerm) (values : Fin arity → CanonicalTerm) :
    Mettapedia.Computability.WordTemplateMachine.Indexed.instantiate
      (compile arity depth body) (fun index => termWire (values index).term) =
      termWire (sequence (List.ofFn values) depth body) := by
  have result := compile_exact (List.ofFn values) depth body
  change Mettapedia.Computability.WordTemplateMachine.Indexed.instantiate
    (compile (List.ofFn values).length depth body)
    (fun index => (((List.ofFn values)[index.val]?).map fun argument => termWire argument.term).getD []) = _ at result
  rw [List.length_ofFn] at result
  simpa using result

def inputWire {arity : Nat} (values : Fin arity → CanonicalTerm) : List (Option Alphabet) :=
  Mettapedia.Computability.WordTemplateMachine.Indexed.argumentWire fun index => termWire (values index).term

/-- The actual finite machine emits the original outermost-first scoped
substitution sequence in one pass over its fixed authored template. -/
def outputs (arity depth : Nat) (body : DBTerm) (values : Fin arity → CanonicalTerm) :
    TM2OutputsInTime (Mettapedia.Computability.WordTemplateMachine.Indexed.machine (compile arity depth body))
      (inputWire values) (some (termWire (sequence (List.ofFn values) depth body)))
      (4 * ((compile arity depth body).length + 1) * ((inputWire values).length + 1)) := by
  rw [← compile_exact_values arity depth body values]
  exact Mettapedia.Computability.WordTemplateMachine.Indexed.outputs
    (compile arity depth body) (fun index => termWire (values index).term)

/-- A fixed authored body admits arbitrary closed typed argument values. The
runtime realization uses their complete independently encoded tuple. -/
noncomputable def realization (arity depth : Nat) (body : DBTerm) : TM2ComputableInPolyTime
    inputWire termWire (fun values : Fin arity → CanonicalTerm => sequence (List.ofFn values) depth body) where
  tm := Mettapedia.Computability.WordTemplateMachine.Indexed.machine (compile arity depth body)
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := C (4 * ((compile arity depth body).length + 1)) * (X + C 1)
  outputsFun values := by
    change TM2OutputsInTime (Mettapedia.Computability.WordTemplateMachine.Indexed.machine (compile arity depth body))
      ((inputWire values).map id) (some ((termWire (sequence (List.ofFn values) depth body)).map id)) _
    simp only [List.map_id_fun]
    simpa using outputs arity depth body values

namespace Controls

theorem nearer_local_binder (arguments : List CanonicalTerm) (depth index : Nat) (nearer : index < depth) :
    sequence arguments depth (.bound index) = .bound index := by
  rw [sequence_bound, dif_neg (by omega)]

theorem outside_formal_interval (arguments : List CanonicalTerm) (depth index : Nat)
    (outside : depth + arguments.length ≤ index) :
    sequence arguments depth (.bound index) = .bound index := by
  rw [sequence_bound, dif_neg (by omega)]

end Controls

end Indexed

namespace Named

open PrimitiveTransport

/-- Closed data substitution cannot change the names consulted by the
original fresh-binder computation. Constant names are retained as syntax,
while only free variables contribute to this computation. -/
theorem freeNames_instantiateAt (replacement : DBTerm) (empty : freeNames replacement = [])
    (depth : Nat) (body : DBTerm) :
    freeNames (DBTerm.instantiateAt replacement depth body) = freeNames body := by
  induction body generalizing depth with
  | const => simp [DBTerm.instantiateAt]
  | free => simp [DBTerm.instantiateAt]
  | bound index =>
      by_cases same : index = depth <;> simp [DBTerm.instantiateAt, freeNames, same, empty]
  | app function argument first second => simp [DBTerm.instantiateAt, freeNames, first, second]
  | abs domain body ih => simpa [DBTerm.instantiateAt, freeNames] using ih (depth + 1)

/-- Fixed authored named syntax compiles around one independently supplied
source word. Escaping fixed indices retain the original refusal. Binder names
are computed by the same original fresh-name function. -/
def compile (depth : Nat) : DBTerm → List SourceVar → Option (Template Alphabet)
  | .const symbol annotation, _ => some (literals (encodeWith sourceTermCodec (.const symbol annotation)))
  | .free value, _ => some (literals (encodeWith sourceTermCodec (.var value.name value.ty)))
  | .bound index, binders =>
      if index = depth then some [none]
      else do
        let binder ← binders[index]?
        pure (literals (encodeWith sourceTermCodec (.var binder.name binder.ty)))
  | .app function argument, binders => do
      let first ← compile depth function binders
      let second ← compile depth argument binders
      pure (literals ([4] ++ encodeData (.atom 2) ++ [4]) ++ first ++ second)
  | .abs domain body, binders => do
      let name := ReverseTranslation.freshName (binders.map Var.name ++ freeNames body)
      let bodyTemplate ← compile (depth + 1) body (⟨name, domain⟩ :: binders)
      pure (literals ([4] ++ encodeData (.atom 3) ++ [4] ++ encodeWith nameCodec name ++
        [4] ++ encodeWith tyCodec domain) ++ bodyTemplate)
termination_by term => sizeOf term

/-- The compiler preserves exactly the original computed representative,
including fresh namespace components, fixed binders and repeated slot uses. -/
theorem compile_exact (replacement : DBTerm) (source : SourceTerm)
    (empty : freeNames replacement = [])
    (contextIndependent : ∀ binders, named? replacement binders = some source)
    (depth : Nat) (body : DBTerm) (binders : List SourceVar) :
    (compile depth body binders).map
      (fun template => instantiate template (encodeWith sourceTermCodec source)) =
    (named? (DBTerm.instantiateAt replacement depth body) binders).map
      (encodeWith sourceTermCodec) := by
  induction body generalizing depth binders with
  | const symbol annotation => simp [compile, named?, DBTerm.instantiateAt, literals]
  | free binder => simp [compile, named?, DBTerm.instantiateAt, literals]
  | bound index =>
      by_cases same : index = depth
      · simp [compile, same, contextIndependent]
      · simp only [compile, if_neg same, named?, DBTerm.instantiateAt]
        cases binders[index]? <;> simp [literals]
  | app function argument first second =>
      have firstExact := first depth binders
      have secondExact := second depth binders
      cases firstCompiled : compile depth function binders <;>
        cases firstNamed : named? (DBTerm.instantiateAt replacement depth function) binders <;>
        cases secondCompiled : compile depth argument binders <;>
        cases secondNamed : named? (DBTerm.instantiateAt replacement depth argument) binders
      all_goals
        simp only [firstCompiled, firstNamed, secondCompiled, secondNamed, Option.map_none,
          Option.map_some, Option.some.injEq] at firstExact secondExact
      all_goals try contradiction
      all_goals try simp only [sourceTermCodec, encodeWith] at firstExact secondExact
      all_goals
        simp [compile, named?, DBTerm.instantiateAt, firstCompiled, firstNamed, secondCompiled, secondNamed,
          literals, firstExact, secondExact, sourceTermCodec, encodeWith, putSourceTerm,
          encodeData_pair, List.append_assoc]
  | abs domain body ih =>
      have names := freeNames_instantiateAt replacement empty (depth + 1) body
      let name := ReverseTranslation.freshName (binders.map Var.name ++ freeNames body)
      have bodyExact := ih (depth + 1) (⟨name, domain⟩ :: binders)
      cases bodyCompiled : compile (depth + 1) body (⟨name, domain⟩ :: binders) <;>
        cases bodyNamed : named? (DBTerm.instantiateAt replacement (depth + 1) body) (⟨name, domain⟩ :: binders)
      all_goals simp only [bodyCompiled, bodyNamed, Option.map_none, Option.map_some,
        Option.some.injEq, sourceTermCodec, encodeWith] at bodyExact
      all_goals dsimp only [name] at bodyCompiled bodyNamed bodyExact
      all_goals try contradiction
      all_goals
        simp [compile, named?, DBTerm.instantiateAt, names, bodyCompiled, bodyNamed,
          literals, bodyExact, sourceTermCodec, encodeWith, putSourceTerm, nameCodec, tyCodec,
          encodeData_pair, List.append_assoc]

/-- The representative used in primitive receipts is the result of the
original Option-valued computation, rather than an existential selection. -/
theorem named_computed (term : DBTerm) (binders : List SourceVar)
    (scope : DBTerm.LooseBelow binders.length term)
    (unique : (binders.map Var.name).Nodup)
    (fresh : ∀ name ∈ freeNames term, name ∉ binders.map Var.name) :
    named? term binders = some (named term binders scope unique fresh) := by
  unfold named
  exact (Option.some_get _).symm

theorem compiled_named_exact (replacement : DBTerm) (source : SourceTerm)
    (empty : freeNames replacement = [])
    (contextIndependent : ∀ binders, named? replacement binders = some source)
    (depth : Nat) (body : DBTerm) (binders : List SourceVar)
    (template : Template Alphabet) (compiled : compile depth body binders = some template)
    (scope : DBTerm.LooseBelow binders.length (DBTerm.instantiateAt replacement depth body))
    (unique : (binders.map Var.name).Nodup)
    (fresh : ∀ name ∈ freeNames (DBTerm.instantiateAt replacement depth body),
      name ∉ binders.map Var.name) :
    instantiate template (encodeWith sourceTermCodec source) =
      encodeWith sourceTermCodec (named (DBTerm.instantiateAt replacement depth body) binders scope unique fresh) := by
  have same := compile_exact replacement source empty contextIndependent depth body binders
  rw [compiled, named_computed _ binders scope unique fresh] at same
  exact Option.some.inj same

/-- Successful compiled source templates run on the existing word copier.
The bound charges the complete independently encoded source operand. -/
def outputs (replacement : DBTerm) (source : SourceTerm)
    (empty : freeNames replacement = [])
    (contextIndependent : ∀ binders, named? replacement binders = some source)
    (depth : Nat) (body : DBTerm) (binders : List SourceVar)
    (template : Template Alphabet) (compiled : compile depth body binders = some template) :
    Σ output : {value : SourceTerm // named? (DBTerm.instantiateAt replacement depth body) binders = some value},
      TM2OutputsInTime (machine template) (encodeWith sourceTermCodec source)
        (some (encodeWith sourceTermCodec output.val))
        (4 * (template.length + 1) * ((encodeWith sourceTermCodec source).length + 1)) := by
  have exactResult := compile_exact replacement source empty contextIndependent depth body binders
  rw [compiled] at exactResult
  cases result : named? (DBTerm.instantiateAt replacement depth body) binders with
  | none => simp [result] at exactResult
  | some output =>
      have wordExact : instantiate template (encodeWith sourceTermCodec source) =
          encodeWith sourceTermCodec output := by simpa [result] using exactResult
      refine ⟨⟨output, rfl⟩, ?_⟩
      rw [← wordExact]
      exact Mettapedia.Computability.WordTemplateMachine.outputs template _

/-- The checked representative retains the result of the original named
scanner; its proof-erased source field is not a second chosen representation. -/
theorem checkedSource_named (term : CanonicalTerm) :
    PrimitiveTransport.named? term.term [] = some (PrimitiveTransport.checkedSource term).source := by
  have computed : PrimitiveTransport.checkedSource? term = some (PrimitiveTransport.checkedSource term) :=
    (Option.some_get _).symm
  cases scanned : PrimitiveTransport.named? term.term [] with
  | none => simp [PrimitiveTransport.checkedSource?, scanned] at computed
  | some source =>
      simp only [PrimitiveTransport.checkedSource?, scanned] at computed
      change (match typed : source.inferType with
        | some type => some (⟨source, type, typed⟩ : CheckedSourceTerm)
        | none => none) = some (PrimitiveTransport.checkedSource term) at computed
      split at computed
      · have same := Option.some.inj computed
        exact congrArg (fun value : CheckedSourceTerm => some value.source) same
      · contradiction

end Named

end Mettapedia.Languages.HOLLight.TemplateInstantiationMachine
