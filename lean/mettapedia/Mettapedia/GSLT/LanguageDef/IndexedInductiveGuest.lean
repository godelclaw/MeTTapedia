import Mettapedia.GSLT.LanguageDef.IndexedInductive
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SchemaTableConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyDeclaration

/-!
# Indexed computation schemas from admitted constructor telescopes

The admitted source supplies every field, recursive index, result index and
constructor occurrence. A scoped interpretation of index expressions supplies
their guest syntax and its substitution law. Compilation produces ordinary
guest terms and the existing finite schema-table format; it introduces no new
term language or computation authority.

Mutual families are represented by one indexed family with tagged indices.
Formation of the family and its dependent eliminator, and whether these raw
equations have judgmental authority, remain obligations of the DTT profile.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

universe u v w
variable {I : Interface.{u}} {Head : Type}

abbrev TermEnv (I : Interface.{u}) (Head : Type) (n : Nat)
    (context : List I.SortCode) := Env (fun _ => Tm Head n) context

def mapEnv {n m : Nat} (mapping : Tm Head n → Tm Head m) :
    {context : List I.SortCode} → TermEnv I Head n context → TermEnv I Head m context
  | [], _ => PUnit.unit
  | _ :: _, environment => (mapping environment.1, mapEnv mapping environment.2)

/-- Syntax for the index-expression language is separate from its semantic
evaluation. The equation is the ordinary scoped substitution obligation. -/
structure IndexSyntax (I : Interface.{u}) (Head : Type) where
  term : {context : List I.SortCode} → {n : Nat} → I.IndexExpr context →
    TermEnv I Head n context → Tm Head n
  substitute : ∀ {context n m} (expression : I.IndexExpr context)
    (environment : TermEnv I Head n context) (substitution : Sub Head n m),
    subst substitution (term expression environment) =
      term expression (mapEnv (subst substitution) environment)

def fieldCount : {context : List I.SortCode} → Code I context → Nat
  | _, .result _ => 0
  | _, .data _ body => fieldCount body + 1
  | _, .recursive _ rest => fieldCount rest + 1

/-- The result index is read after the data binders have been populated. -/
def resultIndex (indexSyntax : IndexSyntax I Head) {n : Nat} :
    {context : List I.SortCode} → (code : Code I context) →
    TermEnv I Head n context → (Fin (fieldCount code) → Tm Head n) → Tm Head n
  | _, .result expression, environment, _ => indexSyntax.term expression environment
  | _, .data _ body, environment, arguments =>
      resultIndex indexSyntax body (arguments ⟨0, by simp [fieldCount]⟩, environment) (fun i => arguments i.succ)
  | _, .recursive _ rest, environment, arguments =>
      resultIndex indexSyntax rest environment (fun i => arguments i.succ)

/-- Every recursive occurrence retains both its own index and its argument.
Original field order is kept, including data fields between recursive fields. -/
def recursiveArguments (indexSyntax : IndexSyntax I Head) {n : Nat} :
    {context : List I.SortCode} → (code : Code I context) →
    TermEnv I Head n context → (Fin (fieldCount code) → Tm Head n) →
      List (Tm Head n × Tm Head n)
  | _, .result _, _, _ => []
  | _, .data _ body, environment, arguments =>
      recursiveArguments indexSyntax body (arguments ⟨0, by simp [fieldCount]⟩, environment) (fun i => arguments i.succ)
  | _, .recursive expression rest, environment, arguments =>
      (indexSyntax.term expression environment, arguments ⟨0, by simp [fieldCount]⟩) ::
        recursiveArguments indexSyntax rest environment (fun i => arguments i.succ)

theorem resultIndex_substitute (indexSyntax : IndexSyntax I Head) {n m : Nat}
    (substitution : Sub Head n m) {context : List I.SortCode} (code : Code I context)
    (environment : TermEnv I Head n context) (arguments : Fin (fieldCount code) → Tm Head n) :
    subst substitution (resultIndex indexSyntax code environment arguments) =
      resultIndex indexSyntax code (mapEnv (subst substitution) environment)
        (fun i => subst substitution (arguments i)) := by
  induction code with
  | result expression => exact indexSyntax.substitute expression environment substitution
  | data sort body ih =>
      exact ih (arguments ⟨0, by simp [fieldCount]⟩, environment) (fun i => arguments i.succ)
  | recursive expression rest ih => exact ih environment (fun i => arguments i.succ)

theorem recursiveArguments_substitute (indexSyntax : IndexSyntax I Head) {n m : Nat}
    (substitution : Sub Head n m) {context : List I.SortCode} (code : Code I context)
    (environment : TermEnv I Head n context) (arguments : Fin (fieldCount code) → Tm Head n) :
    (recursiveArguments indexSyntax code environment arguments).map
        (fun pair => (subst substitution pair.1, subst substitution pair.2)) =
      recursiveArguments indexSyntax code (mapEnv (subst substitution) environment)
        (fun i => subst substitution (arguments i)) := by
  induction code with
  | result => rfl
  | data sort body ih =>
      exact ih (arguments ⟨0, by simp [fieldCount]⟩, environment) (fun i => arguments i.succ)
  | recursive expression rest ih =>
      simp only [recursiveArguments, List.map_cons, indexSyntax.substitute]
      exact congrArg (List.cons _) (ih environment (fun i => arguments i.succ))

def quoteEnv {n : Nat} (quoteData : ∀ sort, I.Value sort → Tm Head n) :
    {context : List I.SortCode} → Env I.Value context → TermEnv I Head n context
  | [], _ => PUnit.unit
  | _ :: _, environment => (quoteData _ environment.1, quoteEnv quoteData environment.2)

/-- Read fields directly from the independent ordered source interpretation.
In particular the terminal result-index equality is not supplied by replay. -/
def sourceArguments {n : Nat} {family : I.Index → Type v}
    (quoteData : ∀ sort, I.Value sort → Tm Head n)
    (quoteChild : ∀ index, family index → Tm Head n) :
    {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    Arguments family code environment index → Fin (fieldCount code) → Tm Head n
  | _, .result _, _, _, _, position => Fin.elim0 position
  | _, .data sort body, _, _, arguments, position =>
      Fin.cases (quoteData sort arguments.1)
        (sourceArguments quoteData quoteChild body arguments.2) position
  | _, .recursive _ rest, _, _, arguments, position =>
      Fin.cases (quoteChild _ arguments.1)
        (sourceArguments quoteData quoteChild rest arguments.2) position

/-- The generated recursor's output index agrees with the source polynomial
fibre whenever index syntax interprets the declared expression language. This
uses the source argument's actual result constraint, including data-dependent
indices, rather than trusting a raw term's claimed index. -/
theorem resultIndex_sourceArguments (indexSyntax : IndexSyntax I Head) {n : Nat}
    {family : I.Index → Type v} (quoteData : ∀ sort, I.Value sort → Tm Head n)
    (quoteChild : ∀ index, family index → Tm Head n) (quoteIndex : I.Index → Tm Head n)
    (compatible : ∀ {context} (expression : I.IndexExpr context) (environment : Env I.Value context),
      indexSyntax.term expression (quoteEnv quoteData environment) = quoteIndex (I.evalIndex expression environment))
    {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : Arguments family code environment index) :
    resultIndex indexSyntax code (quoteEnv quoteData environment)
      (sourceArguments quoteData quoteChild code arguments) = quoteIndex index := by
  induction code with
  | result expression =>
      change indexSyntax.term expression (quoteEnv quoteData environment) = _
      rw [compatible, arguments.down.down]
  | data sort body ih => exact ih arguments.2
  | recursive expression rest ih => exact ih arguments.2

/-- Semantic index agreement permits computed guest expressions whose raw
syntax differs from the canonical quotation of their value. -/
theorem resultIndex_sourceMeaning (indexSyntax : IndexSyntax I Head) {n : Nat}
    {family : I.Index → Type v} (quoteData : ∀ sort, I.Value sort → Tm Head n)
    (quoteChild : ∀ index, family index → Tm Head n) (meaning : Tm Head n → Option I.Index)
    (compatible : ∀ {context} (expression : I.IndexExpr context) (environment : Env I.Value context),
      meaning (indexSyntax.term expression (quoteEnv quoteData environment)) =
        some (I.evalIndex expression environment))
    {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : Arguments family code environment index) :
    meaning (resultIndex indexSyntax code (quoteEnv quoteData environment)
      (sourceArguments quoteData quoteChild code arguments)) = some index := by
  induction code with
  | result expression =>
      change meaning (indexSyntax.term expression (quoteEnv quoteData environment)) = _
      rw [compatible, arguments.down.down]
  | data sort body ih => exact ih arguments.2
  | recursive expression rest ih => exact ih arguments.2

/-- Recursive calls read from the semantic source telescope, indexed by the
actual fibre of each child. Ordinary data arguments remain in the shapes. -/
def sourceRecursiveArguments {n : Nat} {family : I.Index → Type v} {IndexValue : Type w}
    (quoteChild : ∀ index, family index → Tm Head n) (quoteIndex : I.Index → IndexValue) :
    {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    Arguments family code environment index → List (IndexValue × Tm Head n)
  | _, .result _, _, _, _ => []
  | _, .data _ body, _, _, arguments => sourceRecursiveArguments quoteChild quoteIndex body arguments.2
  | _, .recursive expression rest, environment, _, arguments =>
      (quoteIndex (I.evalIndex expression environment), quoteChild _ arguments.1) ::
        sourceRecursiveArguments quoteChild quoteIndex rest arguments.2

theorem recursiveArguments_sourceArguments (indexSyntax : IndexSyntax I Head) {n : Nat}
    {family : I.Index → Type v} (quoteData : ∀ sort, I.Value sort → Tm Head n)
    (quoteChild : ∀ index, family index → Tm Head n) (quoteIndex : I.Index → Tm Head n)
    (compatible : ∀ {context} (expression : I.IndexExpr context) (environment : Env I.Value context),
      indexSyntax.term expression (quoteEnv quoteData environment) = quoteIndex (I.evalIndex expression environment))
    {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : Arguments family code environment index) :
    recursiveArguments indexSyntax code (quoteEnv quoteData environment)
        (sourceArguments quoteData quoteChild code arguments) =
      sourceRecursiveArguments quoteChild quoteIndex code arguments := by
  induction code with
  | result => rfl
  | data sort body ih => exact ih arguments.2
  | recursive expression rest ih =>
      change (indexSyntax.term expression (quoteEnv quoteData environment), quoteChild _ arguments.1) ::
        recursiveArguments indexSyntax rest (quoteEnv quoteData environment)
          (sourceArguments quoteData quoteChild rest arguments.2) =
        (quoteIndex (I.evalIndex expression environment), quoteChild _ arguments.1) ::
          sourceRecursiveArguments quoteChild quoteIndex rest arguments.2
      rw [compatible]
      exact congrArg (List.cons _) (ih arguments.2)

/-- Interpreting the generated recursive indices recovers every actual source
child fibre in order, while preserving the quoted child itself. Computed index
expressions need not be canonical numerals in the raw guest syntax. -/
theorem recursiveArguments_sourceMeaning (indexSyntax : IndexSyntax I Head) {n : Nat}
    {family : I.Index → Type v} (quoteData : ∀ sort, I.Value sort → Tm Head n)
    (quoteChild : ∀ index, family index → Tm Head n) (meaning : Tm Head n → Option I.Index)
    (compatible : ∀ {context} (expression : I.IndexExpr context) (environment : Env I.Value context),
      meaning (indexSyntax.term expression (quoteEnv quoteData environment)) =
        some (I.evalIndex expression environment))
    {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : Arguments family code environment index) :
    (recursiveArguments indexSyntax code (quoteEnv quoteData environment)
      (sourceArguments quoteData quoteChild code arguments)).map
        (fun pair => (meaning pair.1, pair.2)) =
      sourceRecursiveArguments quoteChild some code arguments := by
  induction code with
  | result => rfl
  | data sort body ih => exact ih arguments.2
  | recursive expression rest ih =>
      change (meaning (indexSyntax.term expression (quoteEnv quoteData environment)),
          quoteChild _ arguments.1) ::
        (recursiveArguments indexSyntax rest (quoteEnv quoteData environment)
          (sourceArguments quoteData quoteChild rest arguments.2)).map
            (fun pair => (meaning pair.1, pair.2)) =
        (some (I.evalIndex expression environment), quoteChild _ arguments.1) ::
          sourceRecursiveArguments quoteChild some rest arguments.2
      rw [compatible]
      exact congrArg (List.cons _) (ih arguments.2)

/-- The index is an explicit recursor argument; it cannot be discarded by
the simple-datatype generator's unindexed calling convention. -/
def recursor {n : Nat} (name : DeclName) (motive : Tm Head n)
    (methods : List (Tm Head n)) (index value : Tm Head n) : Tm Head n :=
  Declaration.IndexedFamily.applyArgs (.const name) (motive :: methods ++ [index, value])

theorem recursor_substitute {n m : Nat} (substitution : Sub Head n m)
    (name : DeclName) (motive : Tm Head n) (methods : List (Tm Head n))
    (index value : Tm Head n) :
    subst substitution (recursor name motive methods index value) =
      recursor name (subst substitution motive) (methods.map (subst substitution))
        (subst substitution index) (subst substitution value) := by
  simp [recursor, Declaration.IndexedFamily.subst_applyArgs, subst]

def endpoints (indexSyntax : IndexSyntax I Head) (admitted : Admitted I [])
    (recName : DeclName) (occurrence : Fin admitted.constructors.length) {n : Nat}
    (motive : Tm Head n) (methods : Fin admitted.constructors.length → Tm Head n)
    (arguments : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head n) :
    Tm Head n × Tm Head n :=
  let code := (admitted.constructors.get occurrence).body
  let constructor := Declaration.IndexedFamily.applyArgs
    (.const (.str .anonymous (admitted.constructors.get occurrence).name)) (List.ofFn arguments)
  let left := recursor recName motive (List.ofFn methods)
    (resultIndex indexSyntax code PUnit.unit arguments) constructor
  let recursiveResults := (recursiveArguments indexSyntax code PUnit.unit arguments).map
    (fun pair => recursor recName motive (List.ofFn methods) pair.1 pair.2)
  (left, Declaration.IndexedFamily.applyArgs (methods occurrence)
    (List.ofFn arguments ++ recursiveResults))

theorem endpoints_substitute (indexSyntax : IndexSyntax I Head) (admitted : Admitted I [])
    (recName : DeclName) (occurrence : Fin admitted.constructors.length) {n m : Nat}
    (motive : Tm Head n) (methods : Fin admitted.constructors.length → Tm Head n)
    (arguments : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head n)
    (substitution : Sub Head n m) :
    (subst substitution (endpoints indexSyntax admitted recName occurrence motive methods arguments).1,
      subst substitution (endpoints indexSyntax admitted recName occurrence motive methods arguments).2) =
      endpoints indexSyntax admitted recName occurrence (subst substitution motive)
        (fun i => subst substitution (methods i)) (fun i => subst substitution (arguments i)) := by
  have recursive := recursiveArguments_substitute indexSyntax substitution
    (admitted.constructors.get occurrence).body PUnit.unit arguments
  have result := resultIndex_substitute indexSyntax substitution
    (admitted.constructors.get occurrence).body PUnit.unit arguments
  have mapped := congrArg (List.map (fun pair => recursor recName
    (subst substitution motive) (List.ofFn (fun i => subst substitution (methods i)))
      pair.1 pair.2)) recursive
  dsimp only [mapEnv] at mapped result
  simp only [endpoints]
  apply Prod.ext
  · dsimp only
    erw [recursor_substitute, result]
    simp only [Declaration.IndexedFamily.subst_applyArgs, subst, List.map_ofFn]
    rfl
  · dsimp only
    erw [Declaration.IndexedFamily.subst_applyArgs]
    simp only [List.map_append, List.map_ofFn]
    apply congrArg (Declaration.IndexedFamily.applyArgs (subst substitution (methods occurrence)))
    apply congrArg (List.append (List.ofFn (fun i => subst substitution (arguments i))))
    simpa only [List.map_map, Function.comp_def, recursor_substitute, List.map_ofFn] using mapped

def arity (admitted : Admitted I []) (occurrence : Fin admitted.constructors.length) : Nat :=
  fieldCount (admitted.constructors.get occurrence).body + 1 + admitted.constructors.length

/-- The motive is oldest in the canonical snoc telescope. -/
def motiveSlot (admitted : Admitted I []) (occurrence : Fin admitted.constructors.length) :
    Fin (arity admitted occurrence) :=
  ⟨fieldCount (admitted.constructors.get occurrence).body + admitted.constructors.length, by
    unfold arity
    omega⟩

/-- Methods follow the motive in source order, so their de Bruijn slots reverse
that order and precede all constructor fields. -/
def methodSlot (admitted : Admitted I []) (occurrence : Fin admitted.constructors.length)
    (method : Fin admitted.constructors.length) : Fin (arity admitted occurrence) :=
  ⟨fieldCount (admitted.constructors.get occurrence).body + method.rev.val, by
    have := method.rev.isLt
    unfold arity
    omega⟩

/-- Constructor fields are introduced in source order. The newest field has
slot zero; older dependencies therefore have strictly larger slots. -/
def fieldSlot (admitted : Admitted I []) (occurrence : Fin admitted.constructors.length)
    (field : Fin (fieldCount (admitted.constructors.get occurrence).body)) :
    Fin (arity admitted occurrence) :=
  ⟨field.rev.val, by
    have := field.rev.isLt
    unfold arity
    omega⟩

theorem fieldSlot_order (admitted : Admitted I []) (occurrence : Fin admitted.constructors.length)
    (earlier later : Fin (fieldCount (admitted.constructors.get occurrence).body))
    (ordered : earlier.val < later.val) :
    (fieldSlot admitted occurrence later).val < (fieldSlot admitted occurrence earlier).val := by
  dsimp only [fieldSlot]
  simp only [Fin.val_rev]
  have := earlier.isLt
  have := later.isLt
  omega

theorem fieldSlot_before_method (admitted : Admitted I []) (occurrence : Fin admitted.constructors.length)
    (field : Fin (fieldCount (admitted.constructors.get occurrence).body))
    (method : Fin admitted.constructors.length) :
    (fieldSlot admitted occurrence field).val < (methodSlot admitted occurrence method).val := by
  have := field.rev.isLt
  dsimp only [fieldSlot, methodSlot]
  omega

theorem methodSlot_before_motive (admitted : Admitted I []) (occurrence : Fin admitted.constructors.length)
    (method : Fin admitted.constructors.length) :
    (methodSlot admitted occurrence method).val < (motiveSlot admitted occurrence).val := by
  have := method.rev.isLt
  dsimp only [methodSlot, motiveSlot]
  omega

def schema (indexSyntax : IndexSyntax I Head) (admitted : Admitted I [])
    (recName : DeclName) (occurrence : Fin admitted.constructors.length) :
    (Σ arity : Nat, Tm Head arity × Tm Head arity) :=
  let motive : Tm Head (arity admitted occurrence) := .var (motiveSlot admitted occurrence)
  let methods := fun i => Tm.var (Head := Head) (methodSlot admitted occurrence i)
  let arguments := fun i => Tm.var (Head := Head) (fieldSlot admitted occurrence i)
  let pair := endpoints indexSyntax admitted recName occurrence motive methods arguments
  ⟨arity admitted occurrence, pair⟩

def table (indexSyntax : IndexSyntax I Head) (admitted : Admitted I []) (recName : DeclName) :
    AlgebraicSchema.SchemaTable Head := List.ofFn (schema indexSyntax admitted recName)

@[simp] theorem table_length (indexSyntax : IndexSyntax I Head) (admitted : Admitted I [])
    (recName : DeclName) : (table indexSyntax admitted recName).length = admitted.constructors.length := by
  simp [table]

/-- Every admitted constructor contributes a schema, including constructors
without recursive children. No independently supplied schema list is accepted. -/
theorem schema_mem (indexSyntax : IndexSyntax I Head) (admitted : Admitted I [])
    (recName : DeclName) (occurrence : Fin admitted.constructors.length) :
    schema indexSyntax admitted recName occurrence ∈ table indexSyntax admitted recName := by
  exact List.mem_ofFn.mpr ⟨occurrence, rfl⟩

/-- A schema instance retains every value in canonical de Bruijn slot order:
reversed fields, reversed methods, then the oldest motive. -/
def assignment (admitted : Admitted I []) (occurrence : Fin admitted.constructors.length)
    {n : Nat} (motive : Tm Head n) (methods : Fin admitted.constructors.length → Tm Head n)
    (arguments : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head n) :
    Sub Head (arity admitted occurrence) n := fun position =>
  if field : position.val < fieldCount (admitted.constructors.get occurrence).body then
    arguments (Fin.rev ⟨position.val, field⟩)
  else if last : position.val = fieldCount (admitted.constructors.get occurrence).body +
      admitted.constructors.length then motive
  else methods (Fin.rev ⟨position.val - fieldCount (admitted.constructors.get occurrence).body, by
    have := position.isLt
    simp only [arity] at this
    omega⟩)

theorem schema_instance (indexSyntax : IndexSyntax I Head) (admitted : Admitted I [])
    (recName : DeclName) (occurrence : Fin admitted.constructors.length) {n : Nat}
    (motive : Tm Head n) (methods : Fin admitted.constructors.length → Tm Head n)
    (arguments : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head n) :
    let row := schema indexSyntax admitted recName occurrence
    let substitution := assignment admitted occurrence motive methods arguments
    (subst substitution row.2.1, subst substitution row.2.2) =
      endpoints indexSyntax admitted recName occurrence motive methods arguments := by
  dsimp only [schema]
  rw [endpoints_substitute]
  congr 1
  · simp [subst, assignment, motiveSlot]
  · funext i
    simp only [subst, assignment, methodSlot]
    have bound := i.rev.isLt
    erw [dif_neg (by omega), dif_neg (by omega)]
    have same : (⟨fieldCount (admitted.constructors.get occurrence).body + i.rev.val -
        fieldCount (admitted.constructors.get occurrence).body, by omega⟩ :
        Fin admitted.constructors.length) = i.rev := by
      apply Fin.ext
      simp
    rw [same, Fin.rev_rev]
  · funext i
    simp only [subst, assignment, fieldSlot]
    erw [dif_pos i.rev.isLt]
    exact congrArg arguments (Fin.rev_rev i)

/-- The concrete indexed unfolding relation is stated directly using source
constructor arguments, independently of open schema instantiation. -/
inductive Unfold (indexSyntax : IndexSyntax I Head) (admitted : Admitted I [])
    (recName : DeclName) {n : Nat} : Tm Head n → Tm Head n → Prop where
  | constructor (occurrence : Fin admitted.constructors.length)
      (motive : Tm Head n) (methods : Fin admitted.constructors.length → Tm Head n)
      (arguments : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head n) :
      Unfold indexSyntax admitted recName
        (endpoints indexSyntax admitted recName occurrence motive methods arguments).1
        (endpoints indexSyntax admitted recName occurrence motive methods arguments).2

abbrev computation (indexSyntax : IndexSyntax I Head) (admitted : Admitted I [])
    (recName : DeclName) :=
  SchemaTableConversionCode.root (table indexSyntax admitted recName) (fun _ => true)

theorem Unfold.substitute {indexSyntax : IndexSyntax I Head} {admitted : Admitted I []}
    {recName : DeclName} {n m : Nat} {left right : Tm Head n}
    (unfolding : Unfold indexSyntax admitted recName left right) (substitution : Sub Head n m) :
    Unfold indexSyntax admitted recName (subst substitution left) (subst substitution right) := by
  cases unfolding with
  | constructor occurrence motive methods arguments =>
    have pair := endpoints_substitute indexSyntax admitted recName occurrence motive methods arguments substitution
    have left := congrArg Prod.fst pair
    have right := congrArg Prod.snd pair
    dsimp only at left right
    rw [left, right]
    exact .constructor occurrence _ _ _

/-- Every schema instance is an unfolding with the original source occurrence
and its independently substituted arguments. -/
theorem schema_unfold (indexSyntax : IndexSyntax I Head) (admitted : Admitted I [])
    (recName : DeclName) (occurrence : Fin admitted.constructors.length) {n : Nat}
    (substitution : Sub Head (arity admitted occurrence) n) :
    Unfold indexSyntax admitted recName
      (subst substitution (schema indexSyntax admitted recName occurrence).2.1)
      (subst substitution (schema indexSyntax admitted recName occurrence).2.2) := by
  dsimp only [schema]
  apply Unfold.substitute
  exact .constructor occurrence _ _ _

/-- Raw computation covers exactly indexed source-constructor unfolding.
This does not assert that arbitrary raw field terms have the required types. -/
theorem computation_iff_unfold (indexSyntax : IndexSyntax I Head)
    (admitted : Admitted I []) (recName : DeclName) {n : Nat} (left right : Tm Head n) :
    (computation indexSyntax admitted recName).step left right ↔
      Unfold indexSyntax admitted recName left right := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | instantiate index _ substitution =>
      let occurrence : Fin admitted.constructors.length := ⟨index.val, by
        simpa only [table_length] using index.isLt⟩
      have selected : (table indexSyntax admitted recName).get index =
          schema indexSyntax admitted recName occurrence := by
        change (List.ofFn (schema indexSyntax admitted recName))[index.val] = _
        simp only [List.getElem_ofFn]
        congr 1
      generalize equality : (table indexSyntax admitted recName).get index = row at substitution ⊢
      have same := equality.symm.trans selected
      cases same
      exact schema_unfold indexSyntax admitted recName occurrence substitution
  · intro unfolding
    cases unfolding with
    | constructor occurrence motive methods arguments =>
      let index : Fin (table indexSyntax admitted recName).length := ⟨occurrence.val, by
        simpa only [table_length] using occurrence.isLt⟩
      have selected : (table indexSyntax admitted recName).get index =
          schema indexSyntax admitted recName occurrence := by
        simp [table, index, List.get_eq_getElem]
      have generated := schema_instance indexSyntax admitted recName occurrence motive methods arguments
      have evidence := SchemaTableConversionCode.Evidence.instantiate index (by rfl)
        (Head := Head) (n := n) (table := table indexSyntax admitted recName) (enabled := fun _ => true)
      rw [selected] at evidence
      have instantiated := evidence (assignment admitted occurrence motive methods arguments)
      have hleft := congrArg Prod.fst generated
      have hright := congrArg Prod.snd generated
      dsimp only at hleft hright
      erw [hleft, hright] at instantiated
      exact ⟨instantiated⟩

/-- The existing finite receipt decoder is sound and complete for this source
unfolding relation. Rule occurrence and all assignments are retained by replay. -/
theorem decode_iff_unfold (indexSyntax : IndexSyntax I Head)
    (admitted : Admitted I []) (recName : DeclName) {n : Nat} (left right : Tm Head n) :
    (∃ receipt : SchemaTableConversionCode.Code Head n,
      SchemaTableConversionCode.decode (table indexSyntax admitted recName) (fun _ => true)
        receipt = some (left, right)) ↔ Unfold indexSyntax admitted recName left right := by
  rw [← computation_iff_unfold]
  constructor
  · rintro ⟨receipt, decoded⟩
    exact SchemaTableConversionCode.decode_sound _ _ receipt decoded
  · exact SchemaTableConversionCode.decode_complete _ _

#print axioms schema_instance
#print axioms resultIndex_sourceArguments
#print axioms recursiveArguments_sourceArguments
#print axioms computation_iff_unfold
#print axioms decode_iff_unfold

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest
