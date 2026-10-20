import Mettapedia.Languages.MM0.Kernel.Typing
import Mettapedia.Languages.MM0.Kernel.DeclarationAdmission
import Mettapedia.Logic.HOL.Syntax.ClosedElaboration

/-!
# Applicative contracts through MM0's native sort checker

Each source simple type is an MM0 sort. An application annotation selects an
ordinary two-argument constructor whose first input has the function sort and
whose second input has the domain sort. MM0 checks both actual arguments.
Annotations are untrusted: choosing a different domain or result does not
authorize that type. Source constants retain their original inventory entries.

This is a direct term-typing realization. It installs no theorem axioms and
does not encode a typing derivation as an equation-rewrite trace.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.ApplicativeTyping

open Kernel
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration

variable {Base : Type} [DecidableEq Base]

def constantDecl (sorts : List (Ty Base)) (type : Ty Base) : TermDecl :=
  ⟨[], sorts.idxOf type, ∅⟩

def applicationDecl (sorts : List (Ty Base)) (domain result : Ty Base) : TermDecl :=
  ⟨[.regular (sorts.idxOf (.arr domain result)) ∅, .regular (sorts.idxOf domain) ∅],
    sorts.idxOf result, ∅⟩

/-- All realized types are ordinary data sorts, with no logical axiom flags. -/
def sortSignature (sorts : List (Ty Base)) : SortSignature := fun index =>
  if index < sorts.length then some {} else none

theorem sort_lookup (sorts : List (Ty Base)) {type : Ty Base} (present : type ∈ sorts) :
    sortSignature sorts (sorts.idxOf type) = some {} := by
  simp [sortSignature, List.idxOf_lt_length_iff.mpr present]

theorem constantDecl_admissible (sorts : List (Ty Base)) {type : Ty Base}
    (present : type ∈ sorts) :
    TermDecl.Admissible (sortSignature sorts) (constantDecl sorts type) := by
  apply (TermDecl.check_iff _ _).mp
  simp [TermDecl.check, constantDecl, Context.check, Context.checkFrom,
    sort_lookup sorts present]

theorem applicationDecl_admissible (sorts : List (Ty Base)) {domain result : Ty Base}
    (functionIn : .arr domain result ∈ sorts) (domainIn : domain ∈ sorts)
    (resultIn : result ∈ sorts) :
    TermDecl.Admissible (sortSignature sorts) (applicationDecl sorts domain result) := by
  apply (TermDecl.check_iff _ _).mp
  simp [TermDecl.check, applicationDecl, Context.check, Context.checkFrom,
    Context.checkBinder, sort_lookup sorts functionIn, sort_lookup sorts domainIn,
    sort_lookup sorts resultIn]

def termSignature (constants sorts : List (Ty Base)) : TermSignature := fun index =>
  if index < constants.length then do
    let type ← constants[index]?
    if type ∈ sorts then some (constantDecl sorts type) else none
  else do
    let .arr domain result ← sorts[index - constants.length]? | none
    if domain ∈ sorts ∧ result ∈ sorts then some (applicationDecl sorts domain result) else none

/-- Every generated constructor passes the native declaration-admission rules. -/
theorem termSignature_admissible (constants sorts : List (Ty Base))
    {index : Nat} {declaration : TermDecl}
    (known : termSignature constants sorts index = some declaration) :
    TermDecl.Admissible (sortSignature sorts) declaration := by
  unfold termSignature at known
  split at known
  · cases found : constants[index]? with
    | none => simp [found] at known
    | some type =>
        by_cases present : type ∈ sorts
        · have same : constantDecl sorts type = declaration := by simpa [found, present] using known
          subst declaration
          exact constantDecl_admissible sorts present
        · simp [found, present] at known
  · cases found : sorts[index - constants.length]? with
    | none => simp [found] at known
    | some type =>
        cases type with
        | prop | base _ => simp [found] at known
        | arr domain result =>
            by_cases present : domain ∈ sorts ∧ result ∈ sorts
            · have same : applicationDecl sorts domain result = declaration := by
                simpa [found, present] using known
              subst declaration
              exact applicationDecl_admissible sorts (List.mem_of_getElem? found)
                present.1 present.2
            · simp [found, present] at known

inductive Certificate (Base : Type) where
  | constant (index : Nat)
  | app (domain result : Ty Base) (function argument : Certificate Base)
  deriving Repr

def Certificate.erase : Certificate Base → NamedTerm Base String Nat
  | .constant index => .constant index
  | .app _ _ function argument => .app function.erase argument.erase

def compile (constants sorts : List (Ty Base)) : Certificate Base → Option Preterm
  | .constant index => if index < constants.length then some (.term index) else none
  | .app domain result function argument => do
      if .arr domain result ∈ sorts ∧ domain ∈ sorts ∧ result ∈ sorts then
        let function ← compile constants sorts function
        let argument ← compile constants sorts argument
        pure (.app (.app (.term (constants.length + sorts.idxOf (.arr domain result)))
          function) argument)
      else none

def infer (constants sorts : List (Ty Base)) (certificate : Certificate Base) :
    Option ExpressionType := do
  let term ← compile constants sorts certificate
  Preterm.infer (termSignature constants sorts) [] term

theorem infer_constant (constants sorts : List (Ty Base)) (index : Nat) :
    infer constants sorts (.constant index) = (do
      let type ← constants[index]?
      if type ∈ sorts then some ([], sorts.idxOf type) else none) := by
  by_cases bound : index < constants.length
  · by_cases present : constants[index] ∈ sorts <;>
      simp [infer, compile, Preterm.infer, termSignature, constantDecl, bound, present]
  · simp [infer, compile, bound]

theorem application_lookup (constants sorts : List (Ty Base)) (domain result : Ty Base)
    (functionIn : .arr domain result ∈ sorts) (domainIn : domain ∈ sorts)
    (resultIn : result ∈ sorts) :
    termSignature constants sorts (constants.length + sorts.idxOf (.arr domain result)) =
      some (applicationDecl sorts domain result) := by
  simp [termSignature, List.getElem?_idxOf functionIn, domainIn, resultIn]

theorem infer_app (constants sorts : List (Ty Base)) (domain result : Ty Base)
    (function argument : Certificate Base) :
    infer constants sorts (.app domain result function argument) =
      if .arr domain result ∈ sorts ∧ domain ∈ sorts ∧ result ∈ sorts ∧
          infer constants sorts function = some ([], sorts.idxOf (.arr domain result)) ∧
          infer constants sorts argument = some ([], sorts.idxOf domain) then
        some ([], sorts.idxOf result)
      else none := by
  by_cases present : .arr domain result ∈ sorts ∧ domain ∈ sorts ∧ result ∈ sorts
  · have lookup := application_lookup constants sorts domain result
      present.1 present.2.1 present.2.2
    cases functionCompiled : compile constants sorts function with
    | none => simp [infer, compile, present, functionCompiled]
    | some compiledFunction =>
        cases argumentCompiled : compile constants sorts argument with
        | none => simp [infer, compile, present, functionCompiled, argumentCompiled]
        | some compiledArgument =>
            by_cases functionTyped : Preterm.infer (termSignature constants sorts) []
                compiledFunction = some ([], sorts.idxOf (.arr domain result)) <;>
              simp [infer, compile, present, functionCompiled, argumentCompiled,
                Preterm.infer, lookup, applicationDecl, functionTyped]
  · simp only [infer, compile, if_neg present, bind, Option.bind_none]
    symm
    apply if_neg
    intro bad
    exact present ⟨bad.1, bad.2.1, bad.2.2.1⟩

/-- The independently stated annotation judgment. -/
inductive Certifies (constants : List (Ty Base)) : Certificate Base → Ty Base → Prop where
  | constant {index : Nat} {type : Ty Base} : constants[index]? = some type →
      Certifies constants (.constant index) type
  | app {domain result : Ty Base} {function argument : Certificate Base} :
      Certifies constants function (.arr domain result) →
      Certifies constants argument domain →
      Certifies constants (.app domain result function argument) result

omit [DecidableEq Base] in
theorem Certifies.typed {constants : List (Ty Base)} {certificate : Certificate Base}
    {type : Ty Base} (certified : Certifies constants certificate type) :
    ApplicativeTyped (fun index => constants[index]?) certificate.erase type := by
  induction certified with
  | constant lookup => exact .constant lookup
  | app _ _ functionIH argumentIH => exact .app functionIH argumentIH

omit [DecidableEq Base] in
theorem exists_certificate {constants : List (Ty Base)} {source : NamedTerm Base String Nat}
    {type : Ty Base} (typed : ApplicativeTyped (fun index => constants[index]?) source type) :
    ∃ certificate, certificate.erase = source ∧ Certifies constants certificate type := by
  induction typed with
  | constant lookup => exact ⟨_, rfl, .constant lookup⟩
  | app _ _ functionIH argumentIH =>
      obtain ⟨function, rfl, functionTyped⟩ := functionIH
      obtain ⟨argument, rfl, argumentTyped⟩ := argumentIH
      exact ⟨_, rfl, .app functionTyped argumentTyped⟩

theorem infer_reflects {constants sorts : List (Ty Base)} {certificate : Certificate Base}
    {remaining : Context} {index : Nat}
    (accepted : infer constants sorts certificate = some (remaining, index)) :
    remaining = [] ∧ ∃ type, type ∈ sorts ∧ index = sorts.idxOf type ∧
      Certifies constants certificate type := by
  induction certificate generalizing remaining index with
  | constant symbol =>
      rw [infer_constant] at accepted
      cases found : constants[symbol]? with
      | none => simp [found] at accepted
      | some type =>
          by_cases present : type ∈ sorts
          · have accepted : [] = remaining ∧ sorts.idxOf type = index := by
              simpa [found, present] using accepted
            exact ⟨accepted.1.symm, type, present, accepted.2.symm, .constant found⟩
          · simp [found, present] at accepted
  | app domain result function argument functionIH argumentIH =>
      rw [infer_app] at accepted
      split at accepted
      · next valid =>
          obtain ⟨functionIn, domainIn, resultIn, functionAccepted, argumentAccepted⟩ := valid
          obtain ⟨_, functionType, functionPresent, functionIndex, functionTyped⟩ :=
            functionIH functionAccepted
          obtain ⟨_, argumentType, argumentPresent, argumentIndex, argumentTyped⟩ :=
            argumentIH argumentAccepted
          have functionSame : .arr domain result = functionType :=
            (List.idxOf_inj functionIn).mp functionIndex
          have argumentSame : domain = argumentType :=
            (List.idxOf_inj domainIn).mp argumentIndex
          subst functionType
          subst argumentType
          have parts := Prod.mk.inj (Option.some.inj accepted)
          exact ⟨parts.1.symm, result, resultIn, parts.2.symm, .app functionTyped argumentTyped⟩
      · contradiction

def subtypes : Ty Base → List (Ty Base)
  | .arr domain result => .arr domain result :: (subtypes domain ++ subtypes result)
  | type => [type]

def typeInventory (constants : List (Ty Base)) : List (Ty Base) := constants.flatMap subtypes

omit [DecidableEq Base] in
theorem self_mem_subtypes (type : Ty Base) : type ∈ subtypes type := by
  cases type <;> simp [subtypes]

omit [DecidableEq Base] in
theorem subtypes_trans {outer inner type : Ty Base}
    (first : inner ∈ subtypes outer) (second : type ∈ subtypes inner) :
    type ∈ subtypes outer := by
  induction outer generalizing inner with
  | prop | base _ =>
      simp only [subtypes, List.mem_singleton] at first
      subst inner
      exact second
  | arr domain result domainIH resultIH =>
      simp only [subtypes, List.mem_cons, List.mem_append] at first ⊢
      rcases first with rfl | first | first
      · simpa only [subtypes, List.mem_cons, List.mem_append] using second
      · exact .inr (.inl (domainIH first second))
      · exact .inr (.inr (resultIH first second))

omit [DecidableEq Base] in
theorem inventory_closed {constants : List (Ty Base)} {outer type : Ty Base}
    (present : outer ∈ typeInventory constants) (child : type ∈ subtypes outer) :
    type ∈ typeInventory constants := by
  obtain ⟨root, member, descendant⟩ := List.mem_flatMap.mp present
  exact List.mem_flatMap.mpr ⟨root, member, subtypes_trans descendant child⟩

omit [DecidableEq Base] in
theorem Certifies.in_inventory {constants : List (Ty Base)} {certificate : Certificate Base}
    {type : Ty Base} (certified : Certifies constants certificate type) :
    type ∈ typeInventory constants := by
  induction certified with
  | constant lookup =>
      exact List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? lookup, self_mem_subtypes _⟩
  | app _ _ functionIH _ =>
      exact inventory_closed functionIH (by simp [subtypes, self_mem_subtypes])

theorem Certifies.checked {constants : List (Ty Base)} {certificate : Certificate Base}
    {type : Ty Base} (certified : Certifies constants certificate type) :
    infer constants (typeInventory constants) certificate =
      some ([], (typeInventory constants).idxOf type) := by
  induction certified with
  | constant lookup =>
      simp [infer_constant, lookup, (Certifies.constant lookup).in_inventory]
  | app functionTyped argumentTyped functionIH argumentIH =>
      have functionIn := functionTyped.in_inventory
      have domainIn := argumentTyped.in_inventory
      have resultIn := (Certifies.app functionTyped argumentTyped).in_inventory
      simp [infer_app, functionIn, domainIn, resultIn, functionIH, argumentIH]

/-- Full preservation and reflection for arbitrary finite applicative signatures. -/
theorem typing_iff (constants : List (Ty Base)) (source : NamedTerm Base String Nat)
    (type : Ty Base) :
    ApplicativeTyped (fun index => constants[index]?) source type ↔
      type ∈ typeInventory constants ∧ ∃ certificate : Certificate Base,
        certificate.erase = source ∧
        infer constants (typeInventory constants) certificate =
          some ([], (typeInventory constants).idxOf type) := by
  constructor
  · intro typed
    obtain ⟨certificate, rfl, certified⟩ := exists_certificate typed
    exact ⟨certified.in_inventory, certificate, rfl, certified.checked⟩
  · rintro ⟨present, certificate, rfl, checked⟩
    obtain ⟨_, found, _, same, certified⟩ := infer_reflects checked
    have equal : type = found := (List.idxOf_inj present).mp same
    simpa [equal] using certified.typed

namespace Controls

def constants : List (Ty Nat) := [.base 0, .arr (.base 0) (.base 1), .base 2]

example : infer constants (typeInventory constants)
    (.app (.base 0) (.base 1) (.constant 1) (.constant 0)) =
      some ([], (typeInventory constants).idxOf (.base 1)) := by decide

example : infer constants (typeInventory constants)
    (.app (.base 2) (.base 1) (.constant 1) (.constant 2)) = none := by decide

example : infer constants (typeInventory constants)
    (.app (.base 0) (.base 2) (.constant 1) (.constant 0)) = none := by decide

example : infer constants (typeInventory constants) (.constant 3) = none := by decide

end Controls

#print axioms typing_iff
#print axioms infer_reflects
#print axioms termSignature_admissible

end Mettapedia.Languages.MM0.Translation.ApplicativeTyping
