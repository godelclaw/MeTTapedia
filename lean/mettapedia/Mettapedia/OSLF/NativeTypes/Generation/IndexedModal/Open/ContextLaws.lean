import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SyntaxSubstitution

/-!
# Open modal applications and operational inclusions

Applying the generated modal primitive commutes with substitution of actual
terms. Formation is preserved by the native substitution and context-lifting
rules. The two operational symbol inclusions and the source-to-code injection
retain their symbols while substitutions pass beneath dependent binders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u

/-- Open a dependent function by applying its weakened term to the newest
variable, keeping both the original domain and the full dependent codomain. -/
def applyVariableTerm {S : Symbols.{u}} {n : Nat}
    (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (function : TermExpr S n) :
    TermExpr S (n + 1) :=
  .app (domain.rename Fin.succ) (body.rename (liftRenaming Fin.succ))
    (function.rename Fin.succ) (.var 0)

theorem applyVariableTerm_substitute {S : Symbols.{u}} {n m : Nat}
    (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) (function : TermExpr S n)
    (mapping : Substitution S n m) :
    (applyVariableTerm domain body function).substitute (liftSubstitution mapping) =
      applyVariableTerm (domain.substitute mapping)
        (body.substitute (liftSubstitution mapping)) (function.substitute mapping) := by
  simp only [applyVariableTerm, TermExpr.substitute, TypeExpr.substitute_weaken,
    TermExpr.substitute_weaken, liftSubstitution_zero]
  congr 1
  rw [TypeExpr.substitute_rename, TypeExpr.rename_substitute]
  congr 1
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ position =>
      simp only [Function.comp_apply, liftRenaming_succ, liftSubstitution_succ,
        TermExpr.rename_comp]
      rfl

theorem newestVariable_cancellation {S : Symbols.{u}} {n : Nat}
    (body : TypeExpr S (n + 1)) :
    (body.rename (liftRenaming (Fin.succ : Renaming n (n + 1)))).substitute
        (instantiate (.var 0)) = body := by
  rw [TypeExpr.substitute_rename]
  have square :
      (instantiate (.var 0 : TermExpr S (n + 1))) ∘ liftRenaming Fin.succ =
        (TermExpr.var : Substitution S (n + 1) (n + 1)) := by
    funext position
    cases position using Fin.cases <;> rfl
  rw [square, TypeExpr.substitute_identity]

def extendContextFormed {S : Symbols.{u}} {theory : Signature S} {n : Nat}
    {context : ContextExpr S n} {domain : TypeExpr S n}
    (formed : Derivation theory (.context context))
    (domainFormed : Derivation theory (.type context domain)) :
    Derivation theory (.context (.snoc context domain)) :=
  deriveList (.contextExtend context domain) (.cons formed (.cons domainFormed .nil))

/-- This is an actual derivation using weakening, lifted substitution and
application. Opening the function returns its original dependent body. -/
def applyVariable {S : Symbols.{u}} {theory : Signature S} {n : Nat}
    {context : ContextExpr S n} {domain : TypeExpr S n}
    {body : TypeExpr S (n + 1)} {function : TermExpr S n}
    (formed : Derivation theory (.context context))
    (domainFormed : Derivation theory (.type context domain))
    (bodyFormed : Derivation theory (.type (.snoc context domain) body))
    (functionTyped : Derivation theory (.term context function (.pi domain body))) :
    Derivation theory (.term (.snoc context domain) (applyVariableTerm domain body function) body) := by
  let extended := extendContextFormed formed domainFormed
  let weakening : Substitution S n (n + 1) := fun position => .var position.succ
  let weakened := deriveList (.substitutionWeaken context domain) (.cons domainFormed .nil)
  have domainThere : Derivation theory
      (.type (.snoc context domain) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, weakening, TypeExpr.substitute_variables] using
      deriveList (.substituteType (.snoc context domain) context weakening domain)
        (.cons weakened (.cons domainFormed .nil))
  have bodyThere : Derivation theory
      (.type (.snoc (.snoc context domain) (domain.rename Fin.succ))
        (body.rename (liftRenaming Fin.succ))) := by
    have tree := deriveList (.substituteType _ _ (liftSubstitution weakening) body)
      (.cons (deriveList (.substitutionLift (.snoc context domain) context domain weakening)
        (.cons weakened (.cons domainFormed .nil))) (.cons bodyFormed .nil))
    simpa only [RuleCode.conclusion, weakening, liftSubstitution_variables,
      TypeExpr.substitute_variables] using tree
  have functionThere : Derivation theory
      (.term (.snoc context domain) (function.rename Fin.succ)
        (.pi (domain.rename Fin.succ) (body.rename (liftRenaming Fin.succ)))) := by
    simpa only [RuleCode.conclusion, weakening, TermExpr.substitute_variables,
      TypeExpr.substitute_variables, TypeExpr.rename] using
      deriveList (.substituteTerm (.snoc context domain) context weakening function (.pi domain body))
        (.cons weakened (.cons functionTyped .nil))
  have variableThere : Derivation theory
      (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using
      deriveList (.variable (.snoc context domain) 0) (.cons extended .nil)
  have tree := deriveList (.application (.snoc context domain) (domain.rename Fin.succ)
    (body.rename (liftRenaming Fin.succ)) (function.rename Fin.succ) (.var 0))
    (.cons domainThere (.cons bodyThere (.cons functionThere (.cons variableThere .nil))))
  simpa only [RuleCode.conclusion, newestVariable_cancellation, applyVariableTerm] using tree

variable (installed : Joined.Installed)

@[simp] theorem modal_primitive_substitute (index : installed.Index) {n m : Nat}
    (arguments : Substitution installed.symbols
      (installed.symbols.termArity (installed.modalSymbol index)) n)
    (mapping : Substitution installed.symbols n m) :
    (TermExpr.primitive (installed.modalSymbol index) arguments).substitute mapping =
      .primitive (installed.modalSymbol index) (composeSubstitution arguments mapping) := rfl

theorem modal_result_substitute (index : installed.Index) {n m : Nat}
    (arguments : Substitution installed.symbols
      (installed.symbols.termArity (installed.modalSymbol index)) n)
    (mapping : Substitution installed.symbols n m) :
    ((installed.modalResult index).substitute arguments).substitute mapping =
      (installed.modalResult index).substitute (composeSubstitution arguments mapping) :=
  TypeExpr.substitute_comp arguments mapping _

theorem modal_primitive_substitute_comp (index : installed.Index) {n m k : Nat}
    (arguments : Substitution installed.symbols
      (installed.symbols.termArity (installed.modalSymbol index)) n)
    (first : Substitution installed.symbols n m)
    (second : Substitution installed.symbols m k) :
    ((TermExpr.primitive (installed.modalSymbol index) arguments).substitute first).substitute second =
      .primitive (installed.modalSymbol index)
        (composeSubstitution arguments (composeSubstitution first second)) := by
  rw [modal_primitive_substitute, modal_primitive_substitute, composeSubstitution_assoc]

/-- Substitution acts on the existing formation derivation, with its complete
computed parameter context and its dependent result type. -/
def modalFormation_substitute (index : installed.Index) {n m : Nat}
    (context : ContextExpr installed.symbols n) (destination : ContextExpr installed.symbols m)
    (arguments : Substitution installed.symbols
      (installed.symbols.termArity (installed.modalSymbol index)) n)
    (mapping : Substitution installed.symbols n m)
    (formed : Derivation installed.signature (.context context))
    (typedArguments : Derivation installed.signature
      (.substitution context (installed.modalParameters index) arguments))
    (typedMapping : Derivation installed.signature (.substitution destination context mapping)) :
    Derivation installed.signature
      (.term destination (.primitive (installed.modalSymbol index) (composeSubstitution arguments mapping))
        ((installed.modalResult index).substitute (composeSubstitution arguments mapping))) := by
  have original := installed.m_form_at index context arguments formed typedArguments
  have tree := deriveList (.substituteTerm destination context mapping
    (.primitive (installed.modalSymbol index) arguments)
    ((installed.modalResult index).substitute arguments))
    (.cons typedMapping (.cons original .nil))
  simpa only [RuleCode.conclusion, modal_primitive_substitute, modal_result_substitute] using tree

/-- A variable introduced after the substitution is preserved, while the old
ambient arguments are weakened. This is the genuine native lifting rule. -/
def modalFormation_lift (index : installed.Index) {n m : Nat}
    (context : ContextExpr installed.symbols n) (destination : ContextExpr installed.symbols m)
    (extra : TypeExpr installed.symbols n)
    (arguments : Substitution installed.symbols
      (installed.symbols.termArity (installed.modalSymbol index)) (n + 1))
    (mapping : Substitution installed.symbols n m)
    (formed : Derivation installed.signature (.context (.snoc context extra)))
    (typedArguments : Derivation installed.signature
      (.substitution (.snoc context extra) (installed.modalParameters index) arguments))
    (typedMapping : Derivation installed.signature (.substitution destination context mapping))
    (extraFormed : Derivation installed.signature (.type context extra)) :
    Derivation installed.signature
      (.term (.snoc destination (extra.substitute mapping))
        (.primitive (installed.modalSymbol index)
          (composeSubstitution arguments (liftSubstitution mapping)))
        ((installed.modalResult index).substitute
          (composeSubstitution arguments (liftSubstitution mapping)))) :=
  modalFormation_substitute installed index (.snoc context extra)
    (.snoc destination (extra.substitute mapping)) arguments (liftSubstitution mapping)
    formed typedArguments
    (deriveList (.substitutionLift destination context extra mapping)
      (.cons typedMapping (.cons extraFormed .nil)))

/-- Operational syntax enters on the left twice, preserving authored symbols. -/
def sourceTerm {n : Nat} (value : TermExpr installed.indexed.operational.symbols n) :
    TermExpr installed.symbols n := SignatureSum.termLeft (SignatureSum.termLeft value)

def sourceType {n : Nat} (type : TypeExpr installed.indexed.operational.symbols n) :
    TypeExpr installed.symbols n := SignatureSum.typeLeft (SignatureSum.typeLeft type)

def sourcePredicate {n : Nat} (predicate : PropExpr installed.indexed.operational.symbols n) :
    PropExpr installed.symbols n := SignatureSum.propLeft (SignatureSum.propLeft predicate)

def sourceContext {n : Nat} (context : ContextExpr installed.indexed.operational.symbols n) :
    ContextExpr installed.symbols n := SignatureSum.contextLeft (SignatureSum.contextLeft context)

@[simp] theorem sourceContext_extend {n : Nat}
    (context : ContextExpr installed.indexed.operational.symbols n)
    (type : TypeExpr installed.indexed.operational.symbols n) :
    sourceContext installed (.snoc context type) =
      .snoc (sourceContext installed context) (sourceType installed type) := rfl

@[simp] theorem sourceContext_assume {n : Nat}
    (context : ContextExpr installed.indexed.operational.symbols n)
    (predicate : PropExpr installed.indexed.operational.symbols n) :
    sourceContext installed (.assume context predicate) =
      .assume (sourceContext installed context) (sourcePredicate installed predicate) := rfl

theorem sourceContext_lookup {n : Nat}
    (context : ContextExpr installed.indexed.operational.symbols n) (position : Fin n) :
    (sourceContext installed context).lookup position = sourceType installed (context.lookup position) := by
  simp only [sourceContext, sourceType, SignatureSum.contextLeft_lookup]

def sourceSubstitution {n m : Nat}
    (mapping : Substitution installed.indexed.operational.symbols n m) :
    Substitution installed.symbols n m := fun position => sourceTerm installed (mapping position)

theorem sourceSubstitution_identity {n : Nat} :
    sourceSubstitution installed (TermExpr.var : Substitution installed.indexed.operational.symbols n n) =
      TermExpr.var := rfl

def sourceTermFormed {n : Nat}
    {context : ContextExpr installed.indexed.operational.symbols n}
    {value : TermExpr installed.indexed.operational.symbols n}
    {type : TypeExpr installed.indexed.operational.symbols n}
    (typed : Derivation installed.indexed.operational.signature (.term context value type)) :
    Derivation installed.signature
      (.term (sourceContext installed context) (sourceTerm installed value) (sourceType installed type)) :=
  SourceInjection.carry installed.indexed (installed.indexed.sourceDerivation typed)

def sourceSubstitutionFormed {n m : Nat}
    {context : ContextExpr installed.indexed.operational.symbols n}
    {destination : ContextExpr installed.indexed.operational.symbols m}
    {mapping : Substitution installed.indexed.operational.symbols n m}
    (typed : Derivation installed.indexed.operational.signature (.substitution destination context mapping)) :
    Derivation installed.signature (.substitution (sourceContext installed destination)
      (sourceContext installed context) (sourceSubstitution installed mapping)) :=
  SourceInjection.carry installed.indexed (installed.indexed.sourceDerivation typed)

theorem sourceTerm_rename {n m : Nat}
    (value : TermExpr installed.indexed.operational.symbols n) (mapping : Renaming n m) :
    sourceTerm installed (value.rename mapping) = (sourceTerm installed value).rename mapping := by
  simp only [sourceTerm, SignatureSum.termLeft_rename]

theorem sourceSubstitution_lift {n m : Nat}
    (mapping : Substitution installed.indexed.operational.symbols n m) :
    sourceSubstitution installed (liftSubstitution mapping) =
      liftSubstitution (sourceSubstitution installed mapping) := by
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ position =>
      exact sourceTerm_rename installed (mapping position) Fin.succ

theorem sourceSubstitution_extend {n m : Nat}
    (mapping : Substitution installed.indexed.operational.symbols n m)
    (value : TermExpr installed.indexed.operational.symbols m) :
    sourceSubstitution installed (extendSubstitution mapping value) =
      extendSubstitution (sourceSubstitution installed mapping) (sourceTerm installed value) := by
  funext position
  cases position using Fin.cases <;> rfl

theorem sourceTerm_substitute {n m : Nat}
    (value : TermExpr installed.indexed.operational.symbols n)
    (mapping : Substitution installed.indexed.operational.symbols n m) :
    sourceTerm installed (value.substitute mapping) =
      (sourceTerm installed value).substitute (sourceSubstitution installed mapping) := by
  simp only [sourceTerm, SignatureSum.termLeft_substitute]
  rfl

theorem sourceType_substitute {n m : Nat}
    (type : TypeExpr installed.indexed.operational.symbols n)
    (mapping : Substitution installed.indexed.operational.symbols n m) :
    sourceType installed (type.substitute mapping) =
      (sourceType installed type).substitute (sourceSubstitution installed mapping) := by
  simp only [sourceType, SignatureSum.typeLeft_substitute]
  rfl

theorem sourcePredicate_substitute {n m : Nat}
    (predicate : PropExpr installed.indexed.operational.symbols n)
    (mapping : Substitution installed.indexed.operational.symbols n m) :
    sourcePredicate installed (predicate.substitute mapping) =
      (sourcePredicate installed predicate).substitute (sourceSubstitution installed mapping) := by
  simp only [sourcePredicate, SignatureSum.propLeft_substitute]
  rfl

theorem sourceSubstitution_compose {n m k : Nat}
    (first : Substitution installed.indexed.operational.symbols n m)
    (second : Substitution installed.indexed.operational.symbols m k) :
    sourceSubstitution installed (composeSubstitution first second) =
      composeSubstitution (sourceSubstitution installed first) (sourceSubstitution installed second) := by
  funext position
  exact sourceTerm_substitute installed (first position) second

@[simp] theorem inject_substitute
    (carrier : (Pipeline.classifierSignature installed.indexed.operational).Carrier)
    {n m : Nat} (value : TermExpr installed.symbols n)
    (mapping : Substitution installed.symbols n m) :
    (SourceInjection.inject installed.indexed carrier value).substitute mapping =
      SourceInjection.inject installed.indexed carrier (value.substitute mapping) := rfl

/-- Injecting an authored open term, then substituting, agrees with first
substituting in the authored syntax. No classifier or source symbol is erased. -/
theorem injectedSource_substitute
    (carrier : (Pipeline.classifierSignature installed.indexed.operational).Carrier)
    {n m : Nat} (value : TermExpr installed.indexed.operational.symbols n)
    (mapping : Substitution installed.indexed.operational.symbols n m) :
    (SourceInjection.inject installed.indexed carrier (sourceTerm installed value)).substitute
        (sourceSubstitution installed mapping) =
      SourceInjection.inject installed.indexed carrier (sourceTerm installed (value.substitute mapping)) := by
  rw [inject_substitute, sourceTerm_substitute]

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open
