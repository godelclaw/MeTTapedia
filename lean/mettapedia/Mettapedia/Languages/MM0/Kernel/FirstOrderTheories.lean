import Mettapedia.Languages.MM0.Kernel.TheoryInvariant
import Mettapedia.Languages.MM0.Kernel.SymbolSupport
import Mettapedia.Languages.MM0.Kernel.DependencyFreeTerms

/-!
# First-order MM0 theories

An MM0 development is first-order when none of its declarations binds a
variable: every formal of a term constructor, of a definition and of an
assertion is a regular variable with no dependency, and no definition has a
dummy variable. This is MM0 without its binder discipline: sorts, term
constructors, definitions by unfolding, and schematic assertions.

`Theory.FirstOrder` is the invariant of such developments. Besides the
shape of each declaration it records the order of the definitions: a body
mentions neither the constant it defines nor a constant defined after it.
The kernel checks each body against the terms declared before it, so the
order of admission is acyclic. That fact is not recoverable from the
finished tables alone, where every body is typed over all terms; it is kept
here as a property of the definition table, whose head is the latest
definition.

`Runs.firstOrder` proves the invariant for every development whose
declarations are first-order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

namespace Preterm

/-- Every variable of the expression is below the bound. -/
def VarsBelow (bound : Nat) : Preterm → Prop
  | .var index => index < bound
  | .term _ => True
  | .app function argument => VarsBelow bound function ∧ VarsBelow bound argument

theorem varsBelow_applyArgs (bound : Nat) (function : Preterm) (arguments : List Preterm) :
    VarsBelow bound (applyArgs function arguments) ↔
      VarsBelow bound function ∧ ∀ argument ∈ arguments, VarsBelow bound argument := by
  induction arguments generalizing function with
  | nil => simp
  | cons argument arguments inductionHypothesis =>
      rw [applyArgs, inductionHypothesis]
      simp only [VarsBelow, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- A typed expression mentions only variables of its context. -/
theorem HasType.varsBelow {signature : TermSignature} {context remaining : Context}
    {expression : Preterm} {sort : Nat}
    (typed : HasType signature context expression remaining sort) :
    VarsBelow context.length expression := by
  induction typed with
  | var known => exact (List.getElem?_eq_some_iff.mp known).1
  | term _ => trivial
  | bound _ known inductionHypothesis =>
      exact ⟨inductionHypothesis, (List.getElem?_eq_some_iff.mp known).1⟩
  | regular _ _ functionHypothesis argumentHypothesis =>
      exact ⟨functionHypothesis, argumentHypothesis⟩

/-- A typed expression mentions only declared term symbols. -/
theorem HasType.symbolsDeclared {signature : TermSignature} {context remaining : Context}
    {expression : Preterm} {sort : Nat}
    (typed : HasType signature context expression remaining sort) :
    SymbolsWithin (fun index => signature index ≠ none) expression := by
  induction typed with
  | var _ => trivial
  | term known =>
      intro absent
      rw [absent] at known
      cases known
  | bound _ _ inductionHypothesis => exact ⟨inductionHypothesis, trivial⟩
  | regular _ _ functionHypothesis argumentHypothesis =>
      exact ⟨functionHypothesis, argumentHypothesis⟩

/-- A typed expression does not mention a symbol the signature lacks. -/
theorem HasType.symbols_ne {signature : TermSignature} {context remaining : Context}
    {expression : Preterm} {sort : Nat}
    (typed : HasType signature context expression remaining sort)
    {symbol : Nat} (absent : signature symbol = none) :
    SymbolsWithin (· ≠ symbol) expression :=
  typed.symbolsDeclared.mono fun index declared same =>
    declared (by rw [same]; exact absent)

end Preterm

namespace Context

/-- Every binder of a well-formed context has a declared sort. -/
theorem Extension.sortDeclared {sorts : SortSignature} {initial context : Context}
    (extension : Extension sorts initial context) :
    ∀ binder ∈ context, sorts binder.sort ≠ none := by
  induction extension with
  | nil => intro binder member; cases member
  | cons admitted _ inductionHypothesis =>
      intro binder member
      rcases List.mem_cons.mp member with rfl | rest
      · cases admitted with
        | bound declared _ => simp [Binder.sort, declared]
        | regular declared _ => simp [Binder.sort, declared]
      · exact inductionHypothesis binder rest

end Context

namespace Admission

/-- The declaration binds no variable: its formals are regular variables
without dependencies, and a definition has no dummy variable. The dummy
variables of a proof are not part of the declared statement. -/
def FirstOrder : Admission → Prop
  | .sort _ _ => True
  | .term _ declaration => declaration.DependencyFree
  | .definition _ declaration body => declaration.DependencyFree ∧ body.dummies = []
  | .axiomDecl _ declaration => Context.DependencyFree declaration.arguments
  | .theoremDecl _ declaration _ _ => Context.DependencyFree declaration.arguments

end Admission

namespace Theory

/-- The tables of a first-order development. The definition table is read
from its head, the latest definition, to its last entry, the first one. -/
structure FirstOrder (theory : Theory) : Prop where
  wellFormed : theory.WellFormed
  terms : ∀ row ∈ theory.terms, row.2.DependencyFree
  theorems : ∀ row ∈ theory.theorems, Context.DependencyFree row.2.arguments
  definitionKeys : (theory.definitions.map Prod.fst).Nodup
  bodies : ∀ row ∈ theory.definitions, row.2.dummies = [] ∧
    ∃ declaration, theory.termSignature row.1 = some declaration ∧
      Definition.AdmissibleBody theory.sortSignature theory.termSignature declaration row.2
  ownSymbol : ∀ row ∈ theory.definitions, row.2.expression.SymbolsWithin (· ≠ row.1)
  laterSymbols : theory.definitions.Pairwise
    (fun later earlier => earlier.2.expression.SymbolsWithin (· ≠ later.1))

theorem empty_firstOrder : FirstOrder ({} : Theory) :=
  { wellFormed := empty_wellFormed
    terms := by intro row member; cases member
    theorems := by intro row member; cases member
    definitionKeys := List.nodup_nil
    bodies := by intro row member; cases member
    ownSymbol := by intro row member; cases member
    laterSymbols := List.Pairwise.nil }

/-- One first-order declaration keeps the invariant. A new definition is
checked before its own constant exists, so its body cannot mention that
constant, and no earlier body can. -/
theorem Step.firstOrder {before after : Theory} {admission : Admission}
    (step : Step before admission after) (shape : admission.FirstOrder)
    (valid : FirstOrder before) : FirstOrder after := by
  have formed := step.wellFormed valid.wellFormed
  have extension := step.extends
  have oldBodies : ∀ row ∈ before.definitions, row.2.dummies = [] ∧
      ∃ declaration, after.termSignature row.1 = some declaration ∧
        Definition.AdmissibleBody after.sortSignature after.termSignature declaration row.2 := by
    intro row member
    obtain ⟨noDummies, declaration, declared, admitted⟩ := valid.bodies row member
    exact ⟨noDummies, declaration, extension.terms _ _ declared,
      admitted.extendSignatures extension.sorts extension.terms⟩
  cases step with
  | intro authorized =>
    cases authorized with
    | sort fresh =>
        exact ⟨formed, valid.terms, valid.theorems, valid.definitionKeys, oldBodies,
          valid.ownSymbol, valid.laterSymbols⟩
    | term fresh admitted =>
        refine ⟨formed, ?_, valid.theorems, valid.definitionKeys, oldBodies,
          valid.ownSymbol, valid.laterSymbols⟩
        intro row member
        rcases List.mem_cons.mp member with rfl | old
        · exact shape
        · exact valid.terms row old
    | @definition index declaration body fresh freshBody admitted bodyAdmitted =>
        have newSymbols : ∀ row ∈ before.definitions,
            row.2.expression.SymbolsWithin (· ≠ index) := by
          intro row member
          obtain ⟨_, _, _, earlier⟩ := valid.bodies row member
          exact earlier.typed.symbols_ne fresh
        refine ⟨formed, ?_, valid.theorems, ?_, ?_, ?_, ?_⟩
        · intro row member
          rcases List.mem_cons.mp member with rfl | old
          · exact shape.1
          · exact valid.terms row old
        · refine List.nodup_cons.mpr ⟨?_, valid.definitionKeys⟩
          intro present
          obtain ⟨row, member, same⟩ := List.mem_map.mp present
          have unequal := List.lookup_eq_none_iff.mp freshBody row member
          simp [same] at unequal
        · intro row member
          rcases List.mem_cons.mp member with rfl | old
          · refine ⟨shape.2, declaration, ?_,
              bodyAdmitted.extendSignatures extension.sorts extension.terms⟩
            simp [termSignature, Admission.insert]
          · exact oldBodies row old
        · intro row member
          rcases List.mem_cons.mp member with rfl | old
          · exact bodyAdmitted.typed.symbols_ne fresh
          · exact valid.ownSymbol row old
        · exact List.pairwise_cons.mpr ⟨newSymbols, valid.laterSymbols⟩
    | axiomDecl fresh admitted =>
        refine ⟨formed, valid.terms, ?_, valid.definitionKeys, oldBodies,
          valid.ownSymbol, valid.laterSymbols⟩
        intro row member
        rcases List.mem_cons.mp member with rfl | old
        · exact shape
        · exact valid.theorems row old
    | theoremDecl fresh admitted dummies proof =>
        refine ⟨formed, valid.terms, ?_, valid.definitionKeys, oldBodies,
          valid.ownSymbol, valid.laterSymbols⟩
        intro row member
        rcases List.mem_cons.mp member with rfl | old
        · exact shape
        · exact valid.theorems row old

/-- Every development of first-order declarations has first-order tables. -/
theorem Runs.firstOrder {before after : Theory} {admissions : List Admission}
    (runs : Runs before admissions after)
    (shape : ∀ admission ∈ admissions, admission.FirstOrder)
    (valid : FirstOrder before) : FirstOrder after := by
  induction runs with
  | nil => exact valid
  | cons step _ inductionHypothesis =>
      exact inductionHypothesis (fun admission member => shape admission (by simp [member]))
        (step.firstOrder (shape _ (by simp)) valid)

end Theory

/-! ## Controls -/

/-- A constructor with a bound formal is not a first-order declaration. -/
example : ¬ (Admission.term 0 ⟨[.bound 0], 0, ∅⟩).FirstOrder := by
  intro shape
  obtain ⟨sort, impossible⟩ := shape.arguments (.bound 0) (by simp)
  cases impossible

/-- A definition with a dummy variable is not one either. -/
example : ¬ (Admission.definition 1 ⟨[], 0, ∅⟩ ⟨[0], .term 0⟩).FirstOrder := by
  intro shape
  cases shape.2

/-- A constructor over regular formals is. -/
example : (Admission.term 0 ⟨[.regular 0 ∅, .regular 0 ∅], 0, ∅⟩).FirstOrder :=
  ⟨by simp [Context.DependencyFree], rfl⟩

end Mettapedia.Languages.MM0.Kernel
