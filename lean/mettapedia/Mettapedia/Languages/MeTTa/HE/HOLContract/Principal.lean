import Mettapedia.Languages.MeTTa.HE.HOLContract.Agreement
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# Principal types of the contract, computed by first-order unification

The contract's typing is HE's first-order rule (`typed_iff_firstOrder`).  This module computes it.
`principal space e` enumerates the ways of typing `e`, one per choice of a declaration occurrence
at each declared leaf and of a rule at each expression, solves the type equations of each by the
verified total first-order unifier (`Mettapedia.Logic.LP.unifyTotal`), and answers the principal
type of each solvable choice.  Overloaded heads give several answers, one per choice.

* `principal_sound` and `principal_complete`: when `principal space e` answers, an expression has a
  clean type exactly when that type is an instance of one of the answers.  Clean types are the
  variable-free types whose symbols are not reserved names, arrows and products included.
* `principalChecker`: the checker, with a computable answer.  `PrincipalNative` reads its answers
  as atoms and proves the obligations of `Runtime.NativeChecker`.
* `none` only when the principal type of a head is a bare type variable: the rule at that
  expression then depends on the instance of the variable.
* A solvable way of typing answers only when its solution admits the declarations it uses: the
  instance of each declaration is a contract type.  Unification alone can solve a type variable
  with a reserved name; `AdmissibilityControl.call_untyped` is an expression whose equations are
  solvable and which has no type.

Type variables of the declaration occurrence at a position of the expression become the variables
`(position, name)` of the type terms, so the occurrences are renamed apart.  The variables of
contract types become constants (`Leaf.rigid`): unification never solves them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract.Principal

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

/-! ## Type terms -/

/-- The constants of type terms: symbols, literals, and the variables of contract types. -/
inductive Leaf where
  | symbol (name : String)
  | grounded (value : GroundedValue)
  | rigid (name : String)
  deriving DecidableEq

/-- First-order type terms: a variable is a type variable of the declaration occurrence at a
position, a constant is a leaf, and an expression of `n` elements is the `n`-ary function symbol
`n`. -/
@[reducible] def sig : Mettapedia.Logic.LP.LPSignature where
  constants := Leaf
  vars := List ℕ × String
  relationSymbols := Empty
  relationArity := fun empty => empty.elim
  functionSymbols := ℕ
  functionArity := fun arity => arity

instance : DecidableEq sig.constants := inferInstanceAs (DecidableEq Leaf)
instance : DecidableEq sig.vars := inferInstanceAs (DecidableEq (List ℕ × String))
instance : DecidableEq sig.functionSymbols := inferInstanceAs (DecidableEq ℕ)

/-- Type terms. -/
abbrev TypeTerm := Mettapedia.Logic.LP.Term sig

/-- Substitutions of type terms. -/
abbrev Unifier := Mettapedia.Logic.LP.Subst sig

/-- The expression of a list of type terms. -/
def ofList (terms : List TypeTerm) : TypeTerm :=
  .app terms.length (fun index => terms.get index)

theorem app_congr {n m : ℕ} (lengths : n = m) {left : Fin n → TypeTerm}
    {right : Fin m → TypeTerm} (pointwise : ∀ index : Fin n, left index = right (Fin.cast lengths index)) :
    (Mettapedia.Logic.LP.Term.app n left : TypeTerm) = .app m right := by
  subst lengths
  have : left = right := funext pointwise
  subst this
  rfl

theorem applyTerm_ofList (unifier : Unifier) (terms : List TypeTerm) :
    unifier.applyTerm (ofList terms) = ofList (terms.map unifier.applyTerm) := by
  unfold ofList
  rw [Mettapedia.Logic.LP.Subst.applyTerm_app]
  exact app_congr (List.length_map _).symm (fun index => by simp)

private theorem app_arguments_eq {n m : ℕ} (lengths : n = m) {left : Fin n → TypeTerm}
    {right : Fin m → TypeTerm} (same : HEq left right) (index : ℕ) (bound : index < n) :
    left ⟨index, bound⟩ = right ⟨index, lengths ▸ bound⟩ := by
  subst lengths
  cases same
  rfl

theorem ofList_injective {left right : List TypeTerm} (equal : ofList left = ofList right) :
    left = right := by
  unfold ofList at equal
  injection equal with lengths functions
  apply List.ext_get lengths
  intro index leftBound rightBound
  exact app_arguments_eq lengths functions index leftBound

/-! ## Encodings -/

mutual

/-- A declared type at the position of its occurrence: its type variables are the variables of
that position. -/
def schemeAt (position : List ℕ) : Atom → TypeTerm
  | .symbol name => .const (.symbol name)
  | .grounded value => .const (.grounded value)
  | .var name => .var (position, name)
  | .expression atoms => ofList (schemeList position atoms)

def schemeList (position : List ℕ) : List Atom → List TypeTerm
  | [] => []
  | atom :: atoms => schemeAt position atom :: schemeList position atoms

end

mutual

/-- A contract type, whose type variables are constants. -/
def rigid : Atom → TypeTerm
  | .symbol name => .const (.symbol name)
  | .grounded value => .const (.grounded value)
  | .var name => .const (.rigid name)
  | .expression atoms => ofList (rigidList atoms)

def rigidList : List Atom → List TypeTerm
  | [] => []
  | atom :: atoms => rigid atom :: rigidList atoms

end

theorem schemeList_eq_map (position : List ℕ) :
    ∀ atoms : List Atom, schemeList position atoms = atoms.map (schemeAt position)
  | [] => rfl
  | atom :: atoms => by simp [schemeList, schemeList_eq_map position atoms]

theorem rigidList_eq_map : ∀ atoms : List Atom, rigidList atoms = atoms.map rigid
  | [] => rfl
  | atom :: atoms => by simp [rigidList, rigidList_eq_map atoms]

theorem rigid_expression (atoms : List Atom) :
    rigid (.expression atoms) = ofList (atoms.map rigid) := by
  rw [rigid, rigidList_eq_map]

theorem schemeAt_expression (position : List ℕ) (atoms : List Atom) :
    schemeAt position (.expression atoms) = ofList (atoms.map (schemeAt position)) := by
  rw [schemeAt, schemeList_eq_map]

/-- Back from type terms to atoms; a variable reads as the variable of its name. -/
def decode : TypeTerm → Atom
  | .var (_, name) => .var name
  | .const (.symbol name) => .symbol name
  | .const (.grounded value) => .grounded value
  | .const (.rigid name) => .var name
  | .app _ arguments => .expression (List.ofFn (fun index => decode (arguments index)))

theorem decode_ofList (terms : List TypeTerm) :
    decode (ofList terms) = .expression (terms.map decode) := by
  unfold ofList
  rw [decode]
  congr 1
  apply List.ext_getElem (by simp)
  intro index leftBound rightBound
  simp

mutual

theorem decode_rigid : ∀ atom : Atom, decode (rigid atom) = atom
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .var _ => rfl
  | .expression atoms => by
      rw [rigid, decode_ofList, decode_rigidList atoms]

theorem decode_rigidList : ∀ atoms : List Atom, (rigidList atoms).map decode = atoms
  | [] => rfl
  | atom :: atoms => by
      rw [rigidList, List.map_cons, decode_rigid atom, decode_rigidList atoms]

end

theorem rigid_injective {left right : Atom} (equal : rigid left = rigid right) : left = right := by
  rw [← decode_rigid left, equal, decode_rigid]

/-- A variable-free atom is its own scheme at every position. -/
theorem schemeAt_of_ground (position : List ℕ) :
    ∀ atom : Atom, TypeSubst.typeVars atom = [] → schemeAt position atom = rigid atom := by
  intro atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      TypeSubst.typeVarsList atoms = [] → schemeList position atoms = rigidList atoms) with
  | symbol _ => intro _; rfl
  | grounded _ => intro _; rfl
  | var name => intro ground; simp [TypeSubst.typeVars] at ground
  | expression atoms ih =>
      intro ground
      rw [schemeAt, rigid, ih (by simpa [TypeSubst.typeVars] using ground)]
  | nil => rfl
  | cons head tail headIH tailIH =>
      rename_i ground
      simp only [TypeSubst.typeVarsList, List.append_eq_nil_iff] at ground
      rw [schemeList, rigidList, headIH ground.1, tailIH ground.2]

/-! ## Instances -/

/-- The instance of the declaration occurrence at `position` by a valuation of its type
variables. -/
def instanceAt (position : List ℕ) (valuation : String → Atom) : Unifier :=
  fun key => if key.1 = position then rigid (valuation key.2) else .var key

/-- **A contract instance is a substitution instance of the scheme.** -/
theorem applyTerm_schemeAt (position : List ℕ) (valuation : String → Atom) :
    ∀ scheme : Atom, (instanceAt position valuation).applyTerm (schemeAt position scheme) =
      rigid (applyTypeValuation valuation scheme) := by
  intro scheme
  induction scheme using Atom.rec (motive_2 := fun atoms =>
      (schemeList position atoms).map (instanceAt position valuation).applyTerm =
        rigidList (atoms.map (applyTypeValuation valuation))) with
  | symbol _ => simp [schemeAt, applyTypeValuation, rigid]
  | grounded _ => simp [schemeAt, applyTypeValuation, rigid]
  | var name => simp [schemeAt, instanceAt, applyTypeValuation]
  | expression atoms ih =>
      rw [schemeAt, applyTerm_ofList, ih]
      simp [applyTypeValuation, rigid]
  | nil => rfl
  | cons head tail headIH tailIH =>
      rw [schemeList, List.map_cons, headIH, tailIH]
      simp [rigidList]

/-! ## Deciding contract types -/

/-- A reserved name. -/
def topReservedB : Atom → Bool
  | .symbol name => decide (name ∈ reservedTypeNames)
  | _ => false

theorem topReservedB_iff (atom : Atom) : topReservedB atom = true ↔ TopReserved atom := by
  cases atom with
  | symbol name =>
      simp only [topReservedB, decide_eq_true_eq, TopReserved]
      constructor
      · intro member
        exact ⟨name, member, rfl⟩
      · rintro ⟨other, member, equal⟩
        cases equal
        exact member
  | var name => simp [topReservedB, TopReserved]
  | grounded value => simp [topReservedB, TopReserved]
  | expression atoms => simp [topReservedB, TopReserved]

mutual

/-- `TypeAtom`, decided. -/
def typeAtomB : Atom → Bool
  | .symbol name => decide (name ≠ "->") && decide (name ≠ "%Undefined%")
  | .var _ => true
  | .grounded _ => true
  | .expression [] => true
  | .expression (head :: components) =>
      if head = .symbol "->" then
        !components.isEmpty && allTypeAtomB components &&
          components.all (fun component => !topReservedB component)
      else typeAtomB head && allTypeAtomB components

def allTypeAtomB : List Atom → Bool
  | [] => true
  | atom :: atoms => typeAtomB atom && allTypeAtomB atoms

end

theorem allTypeAtomB_iff : ∀ atoms : List Atom,
    allTypeAtomB atoms = true ↔ ∀ atom ∈ atoms, typeAtomB atom = true
  | [] => by simp [allTypeAtomB]
  | atom :: atoms => by
      simp only [allTypeAtomB, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
      rw [allTypeAtomB_iff atoms]

theorem typeAtomB_arrow (components : List Atom) :
    typeAtomB (.expression (.symbol "->" :: components)) =
      (!components.isEmpty && allTypeAtomB components &&
        components.all (fun component => !topReservedB component)) := by
  simp [typeAtomB]

theorem typeAtomB_nonArrow {atoms : List Atom} (notArrow : ¬ArrowShaped (.expression atoms)) :
    typeAtomB (.expression atoms) = allTypeAtomB atoms := by
  cases atoms with
  | nil => rfl
  | cons head components =>
      have notHead : head ≠ .symbol "->" := by
        rintro rfl
        exact notArrow ⟨components, rfl⟩
      simp [typeAtomB, allTypeAtomB, notHead]

/-- `typeAtomB` decides `TypeAtom`. -/
theorem typeAtomB_iff (atom : Atom) : typeAtomB atom = true ↔ TypeAtom atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      ∀ atom ∈ atoms, (typeAtomB atom = true ↔ TypeAtom atom)) with
  | symbol name =>
      simp only [typeAtomB, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨notArrow, notUndefined⟩
        exact .symbol notArrow notUndefined
      · intro atomic
        cases atomic with
        | symbol notArrow notUndefined => exact ⟨notArrow, notUndefined⟩
  | var name => exact ⟨fun _ => .var name, fun _ => rfl⟩
  | grounded value => exact ⟨fun _ => .grounded value, fun _ => rfl⟩
  | expression atoms ih =>
      by_cases arrow : ArrowShaped (.expression atoms)
      · obtain ⟨components, equal⟩ := arrow
        simp only [Atom.expression.injEq] at equal
        subst equal
        rw [typeAtomB_arrow]
        simp only [Bool.and_eq_true, List.isEmpty_eq_false_iff,
          allTypeAtomB_iff, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        constructor
        · rintro ⟨⟨nonempty, atomic⟩, notReserved⟩
          refine .arrow nonempty (fun component member => ?_) (fun component member => ?_)
          · exact (ih component (List.mem_cons_of_mem _ member)).mp (atomic component member)
          · rw [← topReservedB_iff]
            simp [notReserved component member]
        · intro atomic
          cases atomic with
          | arrow nonempty atomic notReserved =>
              refine ⟨⟨nonempty, fun component member => ?_⟩, fun component member => ?_⟩
              · exact (ih component (List.mem_cons_of_mem _ member)).mpr (atomic component member)
              · have := notReserved component member
                rw [← topReservedB_iff] at this
                simpa using this
          | compound notArrow _ => exact absurd ⟨components, rfl⟩ notArrow
      · rw [typeAtomB_nonArrow arrow, allTypeAtomB_iff]
        constructor
        · intro all
          exact .compound arrow (fun element member => (ih element member).mp (all element member))
        · intro atomic
          cases atomic with
          | arrow _ _ _ => exact absurd ⟨_, rfl⟩ arrow
          | compound _ atomic =>
              exact fun element member => (ih element member).mpr (atomic element member)
  | nil =>
      rename_i atom member
      simp at member
  | cons head tail headIH tailIH =>
      rename_i atom member
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH
      · exact tailIH atom member

/-- `ContractType`, decided. -/
def contractTypeB (atom : Atom) : Bool := typeAtomB atom && !topReservedB atom

theorem contractTypeB_iff (atom : Atom) : contractTypeB atom = true ↔ ContractType atom := by
  simp only [contractTypeB, Bool.and_eq_true, Bool.not_eq_true', ContractType, typeAtomB_iff]
  rw [← topReservedB_iff]
  simp

/-! ## The checker -/

/-- A way of typing an expression: the type it gives, the equations its parts impose, and the
declared types it uses, each at the position of its occurrence. -/
structure Candidate where
  type : TypeTerm
  equations : List (TypeTerm × TypeTerm)
  schemes : List TypeTerm

/-- The most general unifier of a candidate's equations. -/
def solve (candidate : Candidate) : Option Unifier :=
  Mettapedia.Logic.LP.unifyTotal candidate.equations

/-- The arrow symbol as a type term. -/
def arrowSymbol : TypeTerm := .const (.symbol "->")

def isArrowSymbol : TypeTerm → Bool
  | .const (.symbol name) => name == "->"
  | _ => false

theorem isArrowSymbol_iff (term : TypeTerm) : isArrowSymbol term = true ↔ term = arrowSymbol := by
  constructor
  · intro arrow
    match term, arrow with
    | .const (.symbol name), arrow =>
        simp only [isArrowSymbol, beq_iff_eq] at arrow
        subst arrow
        rfl
  · rintro rfl
    rfl

/-- How the principal type of a head types an expression. -/
inductive HeadShape where
  /-- A bare type variable: the rule depends on its instance. -/
  | variable
  /-- An arrow, with its parameters and its result. -/
  | arrow (parameters : List TypeTerm) (result : TypeTerm)
  /-- Another type: the expression is a tuple. -/
  | value
  /-- The arrow symbol alone, `(->)`: no rule applies. -/
  | stuck

def headShapeOfList : List TypeTerm → HeadShape
  | first :: components =>
      if isArrowSymbol first then
        match components.getLast? with
        | some result => .arrow components.dropLast result
        | none => .stuck
      else .value
  | [] => .value

def headShape : TypeTerm → HeadShape
  | .var _ => .variable
  | .const _ => .value
  | .app _ arguments => headShapeOfList (List.ofFn arguments)

/-- Every choice of one candidate from each list, the first list varying slowest. -/
def choices : List (List Candidate) → List (List Candidate)
  | [] => [[]]
  | options :: rest => options.flatMap fun option => (choices rest).map (option :: ·)

theorem mem_choices : ∀ {lists : List (List Candidate)} {choice : List Candidate},
    choice ∈ choices lists ↔ List.Forall₂ (· ∈ ·) choice lists
  | [], choice => by
      cases choice <;> simp [choices]
  | options :: rest, choice => by
      simp only [choices, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨option, member, others, othersMember, rfl⟩
        exact .cons member (mem_choices.mp othersMember)
      · intro all
        cases all with
        | cons member rest' => exact ⟨_, member, _, mem_choices.mpr rest', rfl⟩

/-- The tuple through a head candidate and a choice of argument candidates. -/
def tupleCandidate (head : Candidate) (choice : List Candidate) : Candidate where
  type := ofList (head.type :: choice.map Candidate.type)
  equations := head.equations ++ (choice.map Candidate.equations).flatten
  schemes := head.schemes ++ (choice.map Candidate.schemes).flatten

/-- The application of an arrow with these parameters and result, through a head candidate and a
choice of argument candidates. -/
def applicationCandidate (head : Candidate) (parameters : List TypeTerm) (result : TypeTerm)
    (choice : List Candidate) : Candidate where
  type := result
  equations := head.equations ++ (choice.map Candidate.equations).flatten ++
    parameters.zip (choice.map Candidate.type)
  schemes := head.schemes ++ (choice.map Candidate.schemes).flatten

/-- The candidates of an expression through one candidate of its head, or `none` when the
principal type of the head is a bare type variable. -/
def headCandidates (head : Candidate) (arguments : List (List Candidate)) :
    Option (List Candidate) :=
  match solve head with
  | none => some []
  | some unifier =>
      match headShape (unifier.applyTerm head.type) with
      | .variable => none
      | .stuck => some []
      | .value => some ((choices arguments).map (tupleCandidate head))
      | .arrow parameters result =>
          if parameters.length = arguments.length then
            some ((choices arguments).map (applicationCandidate head parameters result))
          else some []

def combine : List Candidate → List (List Candidate) → Option (List Candidate)
  | [], _ => some []
  | head :: heads, arguments => do
      let mine ← headCandidates head arguments
      let others ← combine heads arguments
      pure (mine ++ others)

/-- The candidates of the declarations of an atom at a position: one per declaration occurrence
whose type is a contract type, the only ones with instances. -/
def declaredCandidates (space : Space) (position : List ℕ) (atom : Atom) : List Candidate :=
  (declarations space atom).filterMap fun scheme =>
    if contractTypeB scheme then
      some ⟨schemeAt position scheme, [], [schemeAt position scheme]⟩
    else none

mutual

/-- The candidates of an atom at a position: its declarations, and, for an expression, the tuples
and applications through the candidates of its head and arguments, at the positions below. -/
def candidates (space : Space) (position : List ℕ) : Atom → Option (List Candidate)
  | .symbol name => some (declaredCandidates space position (.symbol name))
  | .var name => some (declaredCandidates space position (.var name))
  | .grounded value => some (declaredCandidates space position (.grounded value))
  | .expression [] => some (declaredCandidates space position (.expression []))
  | .expression (head :: arguments) => do
      let heads ← candidates space (position ++ [0]) head
      let argumentLists ← candidatesList space position 1 arguments
      let combined ← combine heads argumentLists
      pure (declaredCandidates space position (.expression (head :: arguments)) ++ combined)

def candidatesList (space : Space) (position : List ℕ) :
    ℕ → List Atom → Option (List (List Candidate))
  | _, [] => some []
  | index, atom :: atoms => do
      let first ← candidates space (position ++ [index]) atom
      let rest ← candidatesList space position (index + 1) atoms
      pure (first :: rest)

end

/-- The variables of a type term, in order. -/
def varList : TypeTerm → List sig.vars
  | .var key => [key]
  | .const _ => []
  | .app _ arguments => (List.ofFn fun index => varList (arguments index)).flatten

/-- The unifier admits a declared type: its instance is a contract type, and every type variable
of the declared type takes a type atom.  A way of typing whose principal solution does not admit
one of its declared types has no instance in the contract: an instance of the solution keeps the
reserved names that exclude it. -/
def admitsB (unifier : Unifier) (scheme : TypeTerm) : Bool :=
  contractTypeB (decode (unifier.applyTerm scheme)) &&
    (varList scheme).all fun key => typeAtomB (decode (unifier key))

def admissibleB (unifier : Unifier) (candidate : Candidate) : Bool :=
  candidate.schemes.all (admitsB unifier)

/-- The principal type of a candidate: its type under the most general unifier of its equations,
when the unifier admits its declared types. -/
def principalOf (candidate : Candidate) : Option TypeTerm :=
  match solve candidate with
  | some unifier =>
      if admissibleB unifier candidate then some (unifier.applyTerm candidate.type) else none
  | none => none

/-- **The principal types of an expression**: one for each way of typing it that has an
instance. -/
def principal (space : Space) (expression : Atom) : Option (List TypeTerm) :=
  (candidates space [] expression).map fun found => found.filterMap principalOf

/-! ## Clean types -/

/-- Clean type terms: no variable and no rigid constant, and every symbol a type constant other
than a reserved name, except the arrow symbol at the head of an arrow with at least its result. -/
inductive CleanTerm : TypeTerm → Prop where
  | symbol {name : String} : name ∉ reservedTypeNames → CleanTerm (.const (.symbol name))
  | grounded (value : GroundedValue) : CleanTerm (.const (.grounded value))
  | arrow {components : List TypeTerm} : components ≠ [] →
      (∀ component ∈ components, CleanTerm component) →
      CleanTerm (ofList (arrowSymbol :: components))
  | compound {elements : List TypeTerm} : (∀ element ∈ elements, CleanTerm element) →
      (∀ rest, elements ≠ arrowSymbol :: rest) → CleanTerm (ofList elements)

/-- Clean types: variable-free types built from literals and from type constants that are not
reserved names, by arrows and products. -/
def Clean (type : Atom) : Prop := CleanTerm (rigid type)

theorem CleanTerm.rigid_decode {term : TypeTerm} (clean : CleanTerm term) :
    rigid (decode term) = term := by
  induction clean with
  | symbol _ => rfl
  | grounded _ => rfl
  | arrow _ _ ih =>
      rw [decode_ofList, rigid_expression, List.map_map]
      congr 1
      simp only [List.map_cons, Function.comp_apply]
      congr 1
      exact List.map_congr_left ih |>.trans (List.map_id _)
  | compound _ _ ih =>
      rw [decode_ofList, rigid_expression, List.map_map]
      congr 1
      exact List.map_congr_left ih |>.trans (List.map_id _)

theorem CleanTerm.decode_contract {term : TypeTerm} (clean : CleanTerm term) :
    TypeAtom (decode term) ∧ ¬TopReserved (decode term) := by
  induction clean with
  | symbol notReserved =>
      refine ⟨.symbol ?_ ?_, ?_⟩
      · rintro rfl
        exact notReserved (by simp [reservedTypeNames])
      · rintro rfl
        exact notReserved (by simp [reservedTypeNames])
      · rintro ⟨other, member, equal⟩
        simp only [decode, Atom.symbol.injEq] at equal
        subst equal
        exact notReserved member
  | grounded value =>
      exact ⟨.grounded value, by rintro ⟨_, _, equal⟩; cases equal⟩
  | arrow nonempty _ ih =>
      rw [decode_ofList, List.map_cons]
      refine ⟨.arrow (by simpa using nonempty) ?_ ?_, by rintro ⟨_, _, equal⟩; cases equal⟩
      · intro component member
        obtain ⟨term, termMember, rfl⟩ := List.mem_map.mp member
        exact (ih term termMember).1
      · intro component member
        obtain ⟨term, termMember, rfl⟩ := List.mem_map.mp member
        exact (ih term termMember).2
  | compound allClean notArrow ih =>
      rename_i elements
      rw [decode_ofList]
      refine ⟨.compound ?_ ?_, by rintro ⟨_, _, equal⟩; cases equal⟩
      · rintro ⟨components, equal⟩
        simp only [Atom.expression.injEq] at equal
        cases elements with
        | nil => simp at equal
        | cons first rest =>
            simp only [List.map_cons, List.cons.injEq] at equal
            have reserved : TopReserved (decode first) :=
              ⟨"->", by simp [reservedTypeNames], equal.1⟩
            exact (ih first (by simp)).2 reserved
      · intro element member
        obtain ⟨term, termMember, rfl⟩ := List.mem_map.mp member
        exact (ih term termMember).1

theorem Clean.contractType {type : Atom} (clean : Clean type) : ContractType type := by
  have := CleanTerm.decode_contract clean
  rw [decode_rigid] at this
  exact this

/-! ## Instances of contract types -/

/-- **A contract type stays one under a valuation by type atoms that are not reserved names.** -/
theorem typeAtom_applyTypeValuation {valuation : String → Atom}
    (values : ∀ name, TypeAtom (valuation name) ∧ ¬TopReserved (valuation name))
    {scheme : Atom} (atomic : TypeAtom scheme) :
    TypeAtom (applyTypeValuation valuation scheme) ∧
      (¬TopReserved scheme → ¬TopReserved (applyTypeValuation valuation scheme)) := by
  induction atomic with
  | symbol notArrow notUndefined =>
      simp only [applyTypeValuation]
      exact ⟨.symbol notArrow notUndefined, fun notReserved => notReserved⟩
  | var name =>
      simp only [applyTypeValuation]
      exact ⟨(values name).1, fun _ => (values name).2⟩
  | grounded value =>
      simp only [applyTypeValuation]
      exact ⟨.grounded value, fun notReserved => notReserved⟩
  | arrow nonempty _ notReserved ih =>
      rename_i components
      simp only [applyTypeValuation, List.map_cons]
      refine ⟨.arrow (by simpa using nonempty) ?_ ?_, fun _ => by
        rintro ⟨_, _, equal⟩; cases equal⟩
      · intro component member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact (ih original originalMember).1
      · intro component member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact (ih original originalMember).2 (notReserved original originalMember)
  | compound notArrow allAtomic ih =>
      rename_i elements
      simp only [applyTypeValuation]
      refine ⟨.compound ?_ ?_, fun _ => by rintro ⟨_, _, equal⟩; cases equal⟩
      · rintro ⟨components, equal⟩
        simp only [Atom.expression.injEq] at equal
        cases elements with
        | nil => simp at equal
        | cons first rest =>
            simp only [List.map_cons, List.cons.injEq] at equal
            cases first with
            | symbol name =>
                simp only [applyTypeValuation, Atom.symbol.injEq] at equal
                obtain ⟨nameEq, -⟩ := equal
                subst nameEq
                exact notArrow ⟨rest, rfl⟩
            | var name =>
                simp only [applyTypeValuation] at equal
                exact (values name).2 ⟨"->", by simp [reservedTypeNames], equal.1⟩
            | grounded _ => simp [applyTypeValuation] at equal
            | expression _ => simp [applyTypeValuation] at equal
      · intro element member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact (ih original originalMember).1

theorem contractType_applyTypeValuation {valuation : String → Atom}
    (values : ∀ name, TypeAtom (valuation name) ∧ ¬TopReserved (valuation name))
    {scheme : Atom} (contract : ContractType scheme) :
    ContractType (applyTypeValuation valuation scheme) :=
  let both := typeAtom_applyTypeValuation values contract.1
  ⟨both.1, both.2 contract.2⟩

/-- **A scheme with a contract instance is a contract type.** -/
theorem contractType_of_instance {valuation : String → Atom}
    (values : ∀ name, TypeAtom (valuation name)) (scheme : Atom)
    (contract : ContractType (applyTypeValuation valuation scheme)) : ContractType scheme := by
  have notReserved : ¬TopReserved scheme := by
    rintro ⟨name, member, rfl⟩
    exact contract.2 ⟨name, member, by simp [applyTypeValuation]⟩
  refine ⟨?_, notReserved⟩
  have atomic := contract.1
  clear contract notReserved
  induction scheme using Atom.rec (motive_2 := fun atoms =>
      ∀ atom ∈ atoms, TypeAtom (applyTypeValuation valuation atom) → TypeAtom atom) with
  | symbol name =>
      simp only [applyTypeValuation] at atomic
      exact atomic
  | var name => exact .var name
  | grounded value => exact .grounded value
  | expression atoms ih =>
      simp only [applyTypeValuation] at atomic
      generalize mappedEq : atoms.map (applyTypeValuation valuation) = mapped at atomic
      cases atomic with
      | arrow nonempty atomic notReserved =>
          rename_i components
          cases atoms with
          | nil => simp at mappedEq
          | cons first rest =>
              simp only [List.map_cons, List.cons.injEq] at mappedEq
              obtain ⟨firstEq, restEq⟩ := mappedEq
              have firstSymbol : first = .symbol "->" := by
                cases first with
                | symbol name =>
                    simp only [applyTypeValuation, Atom.symbol.injEq] at firstEq
                    rw [firstEq]
                | var name =>
                    simp only [applyTypeValuation] at firstEq
                    have := values name
                    rw [firstEq] at this
                    cases this with
                    | symbol notArrow _ => exact absurd rfl notArrow
                | grounded _ => simp [applyTypeValuation] at firstEq
                | expression _ => simp [applyTypeValuation] at firstEq
              subst firstSymbol
              subst restEq
              refine .arrow (by simpa using nonempty) (fun component member => ?_)
                (fun component member => ?_)
              · exact ih component (List.mem_cons_of_mem _ member)
                  (atomic _ (List.mem_map.mpr ⟨component, member, rfl⟩))
              · rintro ⟨name, nameMember, rfl⟩
                exact notReserved _ (List.mem_map.mpr ⟨_, member, rfl⟩)
                  ⟨name, nameMember, by simp [applyTypeValuation]⟩
      | compound notArrow atomic =>
          subst mappedEq
          refine .compound ?_ (fun element member =>
            ih element member (atomic _ (List.mem_map.mpr ⟨element, member, rfl⟩)))
          rintro ⟨components, equal⟩
          simp only [Atom.expression.injEq] at equal
          subst equal
          exact notArrow ⟨components.map (applyTypeValuation valuation), by
            simp [applyTypeValuation]⟩
  | nil =>
      rename_i atom member _
      simp at member
  | cons head tail headIH tailIH =>
      rename_i atom member atomic
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH atomic
      · exact tailIH atom member atomic

/-! ## The unifier -/

open Mettapedia.Logic.LP (Unifies)

theorem solve_unifies {candidate : Candidate} {unifier : Unifier}
    (solved : solve candidate = some unifier) : Unifies unifier candidate.equations :=
  Mettapedia.Logic.LP.unifyTotal_sound _ _ solved

theorem solve_complete {candidate : Candidate} {δ : Unifier}
    (unifies : Unifies δ candidate.equations) : ∃ unifier, solve candidate = some unifier :=
  Mettapedia.Logic.LP.unifyTotal_complete ⟨δ, unifies⟩

/-- A solution of a candidate's equations is an instance of their most general unifier, which is
idempotent, so it reads every term through the unifier unchanged. -/
theorem solve_absorbed {candidate : Candidate} {unifier δ : Unifier}
    (solved : solve candidate = some unifier) (unifies : Unifies δ candidate.equations) :
    δ.Absorbs unifier :=
  Mettapedia.Logic.LP.Subst.absorbs_of_moreGeneral
    (Mettapedia.Logic.LP.unifyTotal_relevantIdempotent _ _ solved).absorbs
    (Mettapedia.Logic.LP.unifyTotal_mgu _ _ solved δ unifies)

/-- The most general unifier introduces no variable outside its equations. -/
theorem solve_freeVars {candidate : Candidate} {unifier : Unifier}
    (solved : solve candidate = some unifier) (term : TypeTerm) :
    (unifier.applyTerm term).freeVars ⊆
      term.freeVars ∪ Mettapedia.Logic.LP.eqVars candidate.equations :=
  (Mettapedia.Logic.LP.unifyTotal_relevantIdempotent _ _ solved).freeVars_applyTerm_subset term

/-! ## Shapes of principal types -/

theorem app_eq_ofList (n : ℕ) (arguments : Fin n → TypeTerm) :
    (Mettapedia.Logic.LP.Term.app n arguments : TypeTerm) = ofList (List.ofFn arguments) :=
  app_congr (List.length_ofFn).symm (fun index => by simp)

theorem headShape_ofList (elements : List TypeTerm) :
    headShape (ofList elements) = headShapeOfList elements := by
  show headShapeOfList (List.ofFn fun index => elements.get index) = _
  rw [List.ofFn_get]

theorem applyTerm_ofList_cons (unifier : Unifier) (first : TypeTerm) (rest : List TypeTerm) :
    unifier.applyTerm (ofList (first :: rest)) =
      ofList (unifier.applyTerm first :: rest.map unifier.applyTerm) := by
  rw [applyTerm_ofList, List.map_cons]

theorem mem_freeVars_ofList {elements : List TypeTerm} {key : sig.vars} :
    key ∈ (ofList elements).freeVars ↔ ∃ element ∈ elements, key ∈ element.freeVars := by
  unfold ofList
  rw [Mettapedia.Logic.LP.Term.mem_freeVars_app]
  constructor
  · rintro ⟨index, member⟩
    exact ⟨elements.get index, List.get_mem _ _, member⟩
  · rintro ⟨element, elementMember, member⟩
    obtain ⟨index, rfl⟩ := List.get_of_mem elementMember
    exact ⟨index, member⟩

theorem headShape_arrow {term : TypeTerm} {parameters : List TypeTerm} {result : TypeTerm}
    (shape : headShape term = .arrow parameters result) :
    term = ofList (arrowSymbol :: (parameters ++ [result])) := by
  cases term with
  | var _ => simp [headShape] at shape
  | const _ => simp [headShape] at shape
  | app n arguments =>
      rw [app_eq_ofList]
      rw [app_eq_ofList, headShape_ofList] at shape
      generalize List.ofFn arguments = elements at shape ⊢
      cases elements with
      | nil => simp [headShapeOfList] at shape
      | cons first components =>
          simp only [headShapeOfList] at shape
          split at shape
          · next arrow =>
              rw [(isArrowSymbol_iff first).mp arrow]
              split at shape
              · next last lastEq =>
                  simp only [HeadShape.arrow.injEq] at shape
                  obtain ⟨rfl, rfl⟩ := shape
                  rw [List.dropLast_append_getLast? last lastEq]
              · simp at shape
          · simp at shape

theorem headShape_stuck {term : TypeTerm} (shape : headShape term = .stuck) :
    term = ofList [arrowSymbol] := by
  cases term with
  | var _ => simp [headShape] at shape
  | const _ => simp [headShape] at shape
  | app n arguments =>
      rw [app_eq_ofList]
      rw [app_eq_ofList, headShape_ofList] at shape
      generalize List.ofFn arguments = elements at shape ⊢
      cases elements with
      | nil => simp [headShapeOfList] at shape
      | cons first components =>
          simp only [headShapeOfList] at shape
          split at shape
          · next arrow =>
              rw [(isArrowSymbol_iff first).mp arrow]
              split at shape
              · simp at shape
              · next noLast =>
                  rw [List.getLast?_eq_none_iff.mp noLast]
          · simp at shape

theorem headShape_variable {term : TypeTerm} (shape : headShape term = .variable) :
    ∃ key, term = .var key := by
  cases term with
  | var key => exact ⟨key, rfl⟩
  | const _ => simp [headShape] at shape
  | app n arguments =>
      rw [app_eq_ofList, headShape_ofList] at shape
      generalize List.ofFn arguments = elements at shape
      cases elements with
      | nil => simp [headShapeOfList] at shape
      | cons first components =>
          simp only [headShapeOfList] at shape
          split at shape
          · split at shape <;> simp at shape
          · simp at shape

/-- A clean instance of a value-shaped type is not an arrow. -/
theorem headShape_value_not_arrow {term : TypeTerm} (shape : headShape term = .value)
    {δ : Unifier} (atoms : ∀ key, TypeAtom (decode (δ key))) :
    ¬ArrowShaped (decode (δ.applyTerm term)) := by
  rintro ⟨components, equal⟩
  cases term with
  | var _ => simp [headShape] at shape
  | const leaf => cases leaf <;> simp [decode] at equal
  | app n arguments =>
      rw [app_eq_ofList, headShape_ofList] at shape
      rw [app_eq_ofList, applyTerm_ofList, decode_ofList] at equal
      generalize List.ofFn arguments = elements at shape equal
      cases elements with
      | nil => simp at equal
      | cons first rest =>
          simp only [List.map_cons, Atom.expression.injEq, List.cons.injEq] at equal
          simp only [headShapeOfList] at shape
          split at shape
          · split at shape <;> simp at shape
          · next notArrow =>
              have firstEq := equal.1
              cases first with
              | var key =>
                  have atomic := atoms key
                  rw [show δ.applyTerm (.var key) = δ key from rfl] at firstEq
                  rw [firstEq] at atomic
                  cases atomic with
                  | symbol notArrow _ => exact notArrow rfl
              | const leaf =>
                  cases leaf with
                  | symbol name =>
                      simp only [Mettapedia.Logic.LP.Subst.applyTerm_const, decode,
                        Atom.symbol.injEq] at firstEq
                      subst firstEq
                      exact notArrow rfl
                  | grounded _ => simp [decode] at firstEq
                  | rigid _ => simp [decode] at firstEq
              | app _ _ => simp [decode] at firstEq

/-- An instance of a type whose variables take type atoms is an arrow only when the type is an
arrow or a bare variable. -/
theorem headShape_of_arrow_instance {term : TypeTerm} {δ : Unifier}
    (values : ∀ key, δ key = .var key ∨ ∃ atom, TypeAtom atom ∧ δ key = rigid atom)
    {parameters : List Atom} {result : Atom}
    (instance' : δ.applyTerm term = rigid (arrowAtom parameters result)) :
    headShape term = .variable ∨
      ∃ components last, headShape term = .arrow components last ∧
        components.map δ.applyTerm = parameters.map rigid ∧ δ.applyTerm last = rigid result := by
  cases term with
  | var key => exact .inl rfl
  | const leaf =>
      exfalso
      simp only [Mettapedia.Logic.LP.Subst.applyTerm_const, arrowAtom, rigid_expression] at instance'
      unfold ofList at instance'
      cases instance'
  | app n arguments =>
      right
      rw [app_eq_ofList, headShape_ofList]
      rw [app_eq_ofList, applyTerm_ofList, arrowAtom, rigid_expression] at instance'
      have lists := ofList_injective instance'
      generalize List.ofFn arguments = elements at lists ⊢
      cases elements with
      | nil => simp at lists
      | cons first rest =>
          simp only [List.map_cons, List.cons.injEq] at lists
          obtain ⟨firstEq, restEq⟩ := lists
          have arrow : isArrowSymbol first = true := by
            rw [isArrowSymbol_iff]
            cases first with
            | var key =>
                exfalso
                rw [show δ.applyTerm (.var key) = δ key from rfl] at firstEq
                rcases values key with same | ⟨atom, atomic, valueEq⟩
                · rw [same] at firstEq
                  simp [rigid] at firstEq
                · rw [valueEq] at firstEq
                  have := rigid_injective firstEq
                  subst this
                  cases atomic with
                  | symbol notArrow _ => exact notArrow rfl
            | const leaf =>
                simp only [Mettapedia.Logic.LP.Subst.applyTerm_const, rigid] at firstEq
                rw [firstEq]
                rfl
            | app _ _ =>
                simp [rigid] at firstEq
          simp only [headShapeOfList, arrow, if_true]
          rw [List.map_append] at restEq
          have nonempty : rest ≠ [] := by
            intro empty
            subst empty
            simp at restEq
          have lastSome : rest.getLast? = some (rest.getLast nonempty) :=
            List.getLast?_eq_some_getLast nonempty
          refine ⟨rest.dropLast, rest.getLast nonempty, ?_, ?_, ?_⟩
          · rw [lastSome]
          · have whole := congrArg List.dropLast restEq
            rw [← List.map_dropLast] at whole
            simpa using whole
          · have whole := congrArg List.getLast? restEq
            rw [List.getLast?_map, lastSome] at whole
            simpa using whole

/-- An instance by type atoms of a type that is not a variable is not an arrow when the type is
not. -/
theorem headShape_of_value_instance {term : TypeTerm} {δ : Unifier} {type : Atom}
    (instance' : δ.applyTerm term = rigid type) (notArrow : ¬ArrowShaped type) :
    headShape term = .variable ∨ headShape term = .value := by
  match shape : headShape term with
  | .variable => exact .inl rfl
  | .value => exact .inr rfl
  | .arrow parameters result =>
      exfalso
      rw [headShape_arrow shape, applyTerm_ofList_cons] at instance'
      have := congrArg decode instance'
      rw [decode_rigid, decode_ofList, List.map_cons] at this
      exact notArrow ⟨_, this.symm⟩
  | .stuck =>
      exfalso
      rw [headShape_stuck shape, applyTerm_ofList_cons] at instance'
      have := congrArg decode instance'
      rw [decode_rigid, decode_ofList, List.map_cons] at this
      exact notArrow ⟨_, this.symm⟩

/-! ## Unfolding the checker -/

theorem candidates_expression {space : Space} {position : List ℕ} {head : Atom}
    {arguments : List Atom} {found : List Candidate}
    (computed : candidates space position (.expression (head :: arguments)) = some found) :
    ∃ heads lists combined, candidates space (position ++ [0]) head = some heads ∧
      candidatesList space position 1 arguments = some lists ∧
      combine heads lists = some combined ∧
      found = declaredCandidates space position (.expression (head :: arguments)) ++ combined := by
  simp only [candidates, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at computed
  obtain ⟨heads, headsEq, lists, listsEq, combined, combinedEq, rfl⟩ := computed
  exact ⟨heads, lists, combined, headsEq, listsEq, combinedEq, rfl⟩

theorem candidatesList_cons {space : Space} {position : List ℕ} {index : ℕ} {atom : Atom}
    {atoms : List Atom} {lists : List (List Candidate)}
    (computed : candidatesList space position index (atom :: atoms) = some lists) :
    ∃ first rest, candidates space (position ++ [index]) atom = some first ∧
      candidatesList space position (index + 1) atoms = some rest ∧ lists = first :: rest := by
  simp only [candidatesList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at computed
  obtain ⟨first, firstEq, rest, restEq, rfl⟩ := computed
  exact ⟨first, rest, firstEq, restEq, rfl⟩

theorem candidatesList_nil {space : Space} {position : List ℕ} {index : ℕ}
    {lists : List (List Candidate)}
    (computed : candidatesList space position index [] = some lists) : lists = [] := by
  simp only [candidatesList, Option.some.injEq] at computed
  exact computed.symm

theorem mem_of_combine : ∀ {heads : List Candidate} {arguments : List (List Candidate)}
    {found : List Candidate}, combine heads arguments = some found →
      ∀ {candidate}, candidate ∈ found →
        ∃ head ∈ heads, ∃ mine, headCandidates head arguments = some mine ∧ candidate ∈ mine
  | [], _, found, combined, candidate, member => by
      simp only [combine, Option.some.injEq] at combined
      subst combined
      simp at member
  | head :: heads, arguments, found, combined, candidate, member => by
      simp only [combine, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at combined
      obtain ⟨mine, mineEq, others, othersEq, rfl⟩ := combined
      rcases List.mem_append.mp member with member | member
      · exact ⟨head, List.mem_cons_self .., mine, mineEq, member⟩
      · obtain ⟨other, otherMember, rest⟩ := mem_of_combine othersEq member
        exact ⟨other, List.mem_cons_of_mem _ otherMember, rest⟩

theorem combine_of_mem : ∀ {heads : List Candidate} {arguments : List (List Candidate)}
    {found : List Candidate}, combine heads arguments = some found →
      ∀ {head}, head ∈ heads →
        ∃ mine, headCandidates head arguments = some mine ∧ ∀ candidate ∈ mine, candidate ∈ found
  | [], _, _, _, _, member => by simp at member
  | first :: heads, arguments, found, combined, head, member => by
      simp only [combine, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at combined
      obtain ⟨mine, mineEq, others, othersEq, rfl⟩ := combined
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨mine, mineEq, fun candidate inMine => List.mem_append_left _ inMine⟩
      · obtain ⟨theirs, theirsEq, inside⟩ := combine_of_mem othersEq member
        exact ⟨theirs, theirsEq, fun candidate inTheirs =>
          List.mem_append_right _ (inside candidate inTheirs)⟩

theorem mem_headCandidates {head : Candidate} {arguments : List (List Candidate)}
    {mine : List Candidate} (computed : headCandidates head arguments = some mine)
    {candidate : Candidate} (member : candidate ∈ mine) :
    ∃ unifier, solve head = some unifier ∧
      ((headShape (unifier.applyTerm head.type) = .value ∧
          ∃ choice ∈ choices arguments, candidate = tupleCandidate head choice) ∨
        ∃ parameters result,
          headShape (unifier.applyTerm head.type) = .arrow parameters result ∧
            parameters.length = arguments.length ∧
            ∃ choice ∈ choices arguments,
              candidate = applicationCandidate head parameters result choice) := by
  unfold headCandidates at computed
  split at computed
  · simp only [Option.some.injEq] at computed
    subst computed
    simp at member
  · next unifier solved =>
      refine ⟨unifier, solved, ?_⟩
      split at computed
      · simp at computed
      · simp only [Option.some.injEq] at computed
        subst computed
        simp at member
      · next shape =>
          simp only [Option.some.injEq] at computed
          subst computed
          obtain ⟨choice, choiceMember, rfl⟩ := List.mem_map.mp member
          exact .inl ⟨shape, choice, choiceMember, rfl⟩
      · next parameters result shape =>
          split at computed
          · next lengths =>
              simp only [Option.some.injEq] at computed
              subst computed
              obtain ⟨choice, choiceMember, rfl⟩ := List.mem_map.mp member
              exact .inr ⟨parameters, result, shape, lengths, choice, choiceMember, rfl⟩
          · simp only [Option.some.injEq] at computed
            subst computed
            simp at member

theorem headCandidates_variable {head : Candidate} {arguments : List (List Candidate)}
    {unifier : Unifier} (solved : solve head = some unifier)
    (shape : headShape (unifier.applyTerm head.type) = .variable) :
    headCandidates head arguments = none := by
  unfold headCandidates
  rw [solved]
  simp only [shape]

theorem headCandidates_value {head : Candidate} {arguments : List (List Candidate)}
    {unifier : Unifier} (solved : solve head = some unifier)
    (shape : headShape (unifier.applyTerm head.type) = .value) :
    headCandidates head arguments = some ((choices arguments).map (tupleCandidate head)) := by
  unfold headCandidates
  rw [solved]
  simp only [shape]

theorem headCandidates_arrow {head : Candidate} {arguments : List (List Candidate)}
    {unifier : Unifier} {parameters : List TypeTerm} {result : TypeTerm}
    (solved : solve head = some unifier)
    (shape : headShape (unifier.applyTerm head.type) = .arrow parameters result)
    (lengths : parameters.length = arguments.length) :
    headCandidates head arguments =
      some ((choices arguments).map (applicationCandidate head parameters result)) := by
  unfold headCandidates
  rw [solved]
  simp only [shape, lengths, if_true]

theorem mem_declaredCandidates {space : Space} {position : List ℕ} {atom : Atom}
    {candidate : Candidate} (member : candidate ∈ declaredCandidates space position atom) :
    ∃ (occurrence : ℕ) (scheme : Atom), (declarations space atom)[occurrence]? = some scheme ∧
      ContractType scheme ∧
        candidate = ⟨schemeAt position scheme, [], [schemeAt position scheme]⟩ := by
  unfold declaredCandidates at member
  obtain ⟨scheme, schemeMember, picked⟩ := List.mem_filterMap.mp member
  split at picked
  · next contract =>
      simp only [Option.some.injEq] at picked
      obtain ⟨occurrence, found⟩ := List.mem_iff_getElem?.mp schemeMember
      exact ⟨occurrence, scheme, found, (contractTypeB_iff scheme).mp contract, picked.symm⟩
  · simp at picked

theorem declaredCandidates_mem {space : Space} (position : List ℕ) {atom scheme : Atom}
    {occurrence : ℕ} (found : (declarations space atom)[occurrence]? = some scheme)
    (contract : ContractType scheme) :
    (⟨schemeAt position scheme, [], [schemeAt position scheme]⟩ : Candidate) ∈
      declaredCandidates space position atom := by
  unfold declaredCandidates
  refine List.mem_filterMap.mpr ⟨scheme, List.mem_of_getElem? found, ?_⟩
  rw [if_pos ((contractTypeB_iff scheme).mpr contract)]

/-- The variables of a scheme at a position are the variables of that position. -/
theorem freeVars_schemeAt (position : List ℕ) :
    ∀ (scheme : Atom) (key : sig.vars), key ∈ (schemeAt position scheme).freeVars → key.1 = position := by
  intro scheme
  induction scheme using Atom.rec (motive_2 := fun atoms =>
      ∀ atom ∈ atoms, ∀ key : sig.vars, key ∈ (schemeAt position atom).freeVars → key.1 = position) with
  | symbol _ => intro key member; simp [schemeAt, Mettapedia.Logic.LP.Term.freeVars] at member
  | grounded _ => intro key member; simp [schemeAt, Mettapedia.Logic.LP.Term.freeVars] at member
  | var name =>
      intro key member
      simp only [schemeAt, Mettapedia.Logic.LP.Term.freeVars, Finset.mem_singleton] at member
      subst member
      rfl
  | expression atoms ih =>
      intro key member
      rw [schemeAt_expression, mem_freeVars_ofList] at member
      obtain ⟨element, elementMember, keyMember⟩ := member
      obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp elementMember
      exact ih atom atomMember key keyMember
  | nil =>
      rename_i atom member key keyMember
      simp at member
  | cons head tail headIH tailIH =>
      rename_i atom member key keyMember
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH key keyMember
      · exact tailIH atom member key keyMember

/-! ## Instances of type terms -/

theorem mem_varList (term : TypeTerm) (key : sig.vars) :
    key ∈ varList term ↔ key ∈ term.freeVars := by
  induction term with
  | var other =>
      simp [varList, Mettapedia.Logic.LP.Term.freeVars]
  | const _ => simp [varList, Mettapedia.Logic.LP.Term.freeVars]
  | app n arguments ih =>
      rw [Mettapedia.Logic.LP.Term.mem_freeVars_app]
      simp only [varList, List.mem_flatten, List.mem_ofFn]
      constructor
      · rintro ⟨_, ⟨index, rfl⟩, member⟩
        exact ⟨index, (ih index).mp member⟩
      · rintro ⟨index, member⟩
        exact ⟨_, ⟨index, rfl⟩, (ih index).mpr member⟩

/-- A substitution by variable-free values leaves no variable. -/
theorem rigid_decode_applyTerm {σ : Unifier} :
    ∀ (term : TypeTerm), (∀ key ∈ term.freeVars, CleanTerm (σ key)) →
      rigid (decode (σ.applyTerm term)) = σ.applyTerm term := by
  intro term
  induction term with
  | var key =>
      intro values
      exact (values key (by simp [Mettapedia.Logic.LP.Term.freeVars])).rigid_decode
  | const leaf => intro _; cases leaf <;> rfl
  | app n arguments ih =>
      intro values
      rw [app_eq_ofList, applyTerm_ofList, decode_ofList, rigid_expression, List.map_map,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro element member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact ih index (fun key keyMember =>
        values key (Mettapedia.Logic.LP.Term.mem_freeVars_app.mpr ⟨index, keyMember⟩))

/-- **Substituting clean values keeps type atoms.** -/
theorem typeAtom_decode_applyTerm {σ : Unifier} :
    ∀ (term : TypeTerm), (∀ key ∈ term.freeVars, CleanTerm (σ key)) →
      TypeAtom (decode term) →
        TypeAtom (decode (σ.applyTerm term)) ∧
          (¬TopReserved (decode term) → ¬TopReserved (decode (σ.applyTerm term))) := by
  intro term
  induction term with
  | var key =>
      intro values _
      have clean := values key (by simp [Mettapedia.Logic.LP.Term.freeVars])
      exact ⟨clean.decode_contract.1, fun _ => clean.decode_contract.2⟩
  | const leaf => intro _ atomic; exact ⟨atomic, id⟩
  | app n arguments ih =>
      intro values atomic
      have elementIH : ∀ element ∈ List.ofFn arguments,
          (∀ key ∈ element.freeVars, CleanTerm (σ key)) → TypeAtom (decode element) →
            TypeAtom (decode (σ.applyTerm element)) ∧
              (¬TopReserved (decode element) →
                ¬TopReserved (decode (σ.applyTerm element))) := by
        intro element member
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
        exact ih index
      have elementValues : ∀ element ∈ List.ofFn arguments,
          ∀ key ∈ element.freeVars, CleanTerm (σ key) := by
        intro element member key keyMember
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
        exact values key (Mettapedia.Logic.LP.Term.mem_freeVars_app.mpr ⟨index, keyMember⟩)
      rw [app_eq_ofList] at atomic ⊢
      rw [applyTerm_ofList, decode_ofList, List.map_map]
      rw [decode_ofList] at atomic
      refine ⟨?_, fun _ => by rintro ⟨_, _, equal⟩; cases equal⟩
      generalize List.ofFn arguments = elements at elementIH elementValues atomic
      generalize decodedEq : elements.map decode = decoded at atomic
      cases atomic with
      | arrow nonempty atomicComponents notReserved =>
          rename_i components
          cases elements with
          | nil => simp at decodedEq
          | cons first rest =>
              simp only [List.map_cons, List.cons.injEq] at decodedEq
              obtain ⟨firstEq, restEq⟩ := decodedEq
              have firstConst : first = arrowSymbol := by
                cases first with
                | var _ => simp [decode] at firstEq
                | const leaf =>
                    cases leaf with
                    | symbol name =>
                        simp only [decode, Atom.symbol.injEq] at firstEq
                        rw [firstEq]
                        rfl
                    | grounded _ => simp [decode] at firstEq
                    | rigid _ => simp [decode] at firstEq
                | app _ _ => simp [decode] at firstEq
              subst firstConst
              subst restEq
              simp only [List.map_cons, Function.comp_apply]
              refine .arrow (by simpa using nonempty) (fun component member => ?_)
                (fun component member => ?_)
              · obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
                exact (elementIH element (List.mem_cons_of_mem _ elementMember)
                  (elementValues element (List.mem_cons_of_mem _ elementMember))
                  (atomicComponents _ (List.mem_map.mpr ⟨element, elementMember, rfl⟩))).1
              · obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
                exact (elementIH element (List.mem_cons_of_mem _ elementMember)
                  (elementValues element (List.mem_cons_of_mem _ elementMember))
                  (atomicComponents _ (List.mem_map.mpr ⟨element, elementMember, rfl⟩))).2
                  (notReserved _ (List.mem_map.mpr ⟨element, elementMember, rfl⟩))
      | compound notArrow atomicElements =>
          subst decodedEq
          refine .compound ?_ (fun element member => ?_)
          · rintro ⟨components, equal⟩
            simp only [Atom.expression.injEq] at equal
            cases elements with
            | nil => simp at equal
            | cons first rest =>
                simp only [List.map_cons, List.cons.injEq, Function.comp_apply] at equal
                cases first with
                | var key =>
                    have clean := elementValues _ (List.mem_cons_self ..) key
                      (by simp [Mettapedia.Logic.LP.Term.freeVars])
                    exact clean.decode_contract.2 ⟨"->", by simp [reservedTypeNames], equal.1⟩
                | const leaf =>
                    exact notArrow ⟨rest.map decode, by
                      simp only [Mettapedia.Logic.LP.Subst.applyTerm_const] at equal
                      simp [equal.1]⟩
                | app _ _ => simp [decode] at equal
          · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
            exact (elementIH original originalMember (elementValues original originalMember)
              (atomicElements _ (List.mem_map.mpr ⟨original, originalMember, rfl⟩))).1

theorem contractType_decode_applyTerm {σ : Unifier} {term : TypeTerm}
    (values : ∀ key ∈ term.freeVars, CleanTerm (σ key)) (contract : ContractType (decode term)) :
    ContractType (decode (σ.applyTerm term)) :=
  let both := typeAtom_decode_applyTerm term values contract.1
  ⟨both.1, both.2 contract.2⟩

/-- **A type term whose instance is a type atom is one.** -/
theorem typeAtom_of_decode_applyTerm {σ : Unifier} :
    ∀ (term : TypeTerm), TypeAtom (decode (σ.applyTerm term)) →
      TypeAtom (decode term) ∧
        (¬TopReserved (decode (σ.applyTerm term)) → ¬TopReserved (decode term)) := by
  intro term
  induction term with
  | var key =>
      intro _
      exact ⟨.var _, fun _ => by rintro ⟨_, _, equal⟩; cases equal⟩
  | const leaf => intro atomic; exact ⟨atomic, id⟩
  | app n arguments ih =>
      intro atomic
      have elementIH : ∀ element ∈ List.ofFn arguments,
          TypeAtom (decode (σ.applyTerm element)) →
            TypeAtom (decode element) ∧
              (¬TopReserved (decode (σ.applyTerm element)) →
                ¬TopReserved (decode element)) := by
        intro element member
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
        exact ih index
      rw [app_eq_ofList] at atomic ⊢
      rw [applyTerm_ofList, decode_ofList, List.map_map] at atomic
      rw [decode_ofList]
      refine ⟨?_, fun _ => by rintro ⟨_, _, equal⟩; cases equal⟩
      generalize List.ofFn arguments = elements at elementIH atomic
      generalize decodedEq : elements.map (decode ∘ σ.applyTerm) = decoded at atomic
      cases atomic with
      | arrow nonempty atomicComponents notReserved =>
          cases elements with
          | nil => simp at decodedEq
          | cons first rest =>
              simp only [List.map_cons, List.cons.injEq, Function.comp_apply] at decodedEq
              obtain ⟨firstEq, restEq⟩ := decodedEq
              subst restEq
              have restAtomic : ∀ element ∈ rest, TypeAtom (decode element) ∧
                  (¬TopReserved (decode (σ.applyTerm element)) → ¬TopReserved (decode element)) :=
                fun element member => elementIH element (List.mem_cons_of_mem _ member)
                  (atomicComponents _ (List.mem_map.mpr ⟨element, member, rfl⟩))
              cases first with
              | var key =>
                  refine .compound ?_ (fun element member => ?_)
                  · rintro ⟨_, equal⟩
                    simp [decode] at equal
                  · rcases List.mem_cons.mp member with rfl | member
                    · exact .var _
                    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
                      exact (restAtomic original originalMember).1
              | const leaf =>
                  simp only [Mettapedia.Logic.LP.Subst.applyTerm_const] at firstEq
                  simp only [List.map_cons]
                  rw [firstEq]
                  refine .arrow (by simpa using nonempty) (fun component member => ?_)
                    (fun component member => ?_)
                  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
                    exact (restAtomic original originalMember).1
                  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
                    exact (restAtomic original originalMember).2
                      (notReserved _ (List.mem_map.mpr ⟨original, originalMember, rfl⟩))
              | app _ _ => simp [decode] at firstEq
      | compound notArrow atomicElements =>
          subst decodedEq
          refine .compound ?_ (fun element member => ?_)
          · rintro ⟨components, equal⟩
            simp only [Atom.expression.injEq] at equal
            cases elements with
            | nil => simp at equal
            | cons first rest =>
                simp only [List.map_cons, List.cons.injEq] at equal
                cases first with
                | var _ => simp [decode] at equal
                | const leaf =>
                    exact notArrow ⟨rest.map (decode ∘ σ.applyTerm), by
                      simp only [List.map_cons, Function.comp_apply,
                        Mettapedia.Logic.LP.Subst.applyTerm_const]
                      rw [equal.1]⟩
                | app _ _ => simp [decode] at equal
          · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
            exact (elementIH original originalMember
              (atomicElements _ (List.mem_map.mpr ⟨original, originalMember, rfl⟩))).1

theorem contractType_of_decode_applyTerm {σ : Unifier} {term : TypeTerm}
    (contract : ContractType (decode (σ.applyTerm term))) : ContractType (decode term) :=
  let both := typeAtom_of_decode_applyTerm term contract.1
  ⟨both.1, both.2 contract.2⟩


/-! ## The variables of a candidate -/

/-- Every variable of a candidate's type and equations is a variable of one of its declared
types. -/
def Candidate.SchemeVars (candidate : Candidate) : Prop :=
  ∀ key, (key ∈ candidate.type.freeVars ∨ ∃ equation ∈ candidate.equations,
      key ∈ equation.1.freeVars ∨ key ∈ equation.2.freeVars) →
    ∃ scheme ∈ candidate.schemes, key ∈ scheme.freeVars

theorem freeVars_of_arrow {term : TypeTerm} {parameters : List TypeTerm} {result : TypeTerm}
    (shape : headShape term = .arrow parameters result) {component : TypeTerm}
    (member : component ∈ parameters ∨ component = result) {key : sig.vars}
    (keyMember : key ∈ component.freeVars) : key ∈ term.freeVars := by
  rw [headShape_arrow shape, mem_freeVars_ofList]
  refine ⟨component, ?_, keyMember⟩
  rcases member with member | rfl
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ member)
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem schemeVars_of_head {head : Candidate} {unifier : Unifier}
    (solved : solve head = some unifier) (headVars : head.SchemeVars) {key : sig.vars}
    (member : key ∈ (unifier.applyTerm head.type).freeVars) :
    ∃ scheme ∈ head.schemes, key ∈ scheme.freeVars := by
  have := solve_freeVars solved head.type member
  rcases Finset.mem_union.mp this with typeMember | equationMember
  · exact headVars key (.inl typeMember)
  · exact headVars key (.inr (Mettapedia.Logic.LP.mem_eqVars.mp equationMember))

theorem exists_of_forall₂_mem {choice : List Candidate} {lists : List (List Candidate)}
    (all : List.Forall₂ (· ∈ ·) choice lists) {chosen : Candidate} (member : chosen ∈ choice) :
    ∃ options ∈ lists, chosen ∈ options := by
  induction all with
  | nil => simp at member
  | cons inHead _ ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, List.mem_cons_self .., inHead⟩
      · obtain ⟨options, optionsMember, inOptions⟩ := ih member
        exact ⟨options, List.mem_cons_of_mem _ optionsMember, inOptions⟩

theorem candidates_schemeVars (space : Space) :
    ∀ (atom : Atom) (position : List ℕ) (found : List Candidate),
      candidates space position atom = some found → ∀ candidate ∈ found, candidate.SchemeVars := by
  have declaredVars : ∀ {position : List ℕ} {atom : Atom} {candidate : Candidate},
      candidate ∈ declaredCandidates space position atom → candidate.SchemeVars := by
    intro position atom candidate member key keyMember
    obtain ⟨_, scheme, _, _, rfl⟩ := mem_declaredCandidates member
    rcases keyMember with typeMember | ⟨_, equationMember, _⟩
    · exact ⟨_, List.mem_singleton_self _, typeMember⟩
    · simp at equationMember
  intro atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      ∀ (position : List ℕ) (index : ℕ) (lists : List (List Candidate)),
        candidatesList space position index atoms = some lists →
          ∀ options ∈ lists, ∀ candidate ∈ options, candidate.SchemeVars) with
  | symbol name =>
      intro position found computed candidate member
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact declaredVars member
  | var name =>
      intro position found computed candidate member
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact declaredVars member
  | grounded value =>
      intro position found computed candidate member
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact declaredVars member
  | expression atoms ih =>
      intro position found computed candidate member
      cases atoms with
      | nil =>
          simp only [candidates, Option.some.injEq] at computed
          subst computed
          exact declaredVars member
      | cons head arguments =>
          obtain ⟨heads, lists, combined, headsEq, listsEq, combinedEq, rfl⟩ :=
            candidates_expression computed
          have parts := ih position 0 (heads :: lists) (by
            simp only [candidatesList, Option.bind_eq_bind, headsEq, Option.bind_some,
              Nat.zero_add, listsEq, Option.pure_def])
          have headVars : ∀ candidate ∈ heads, candidate.SchemeVars :=
            parts heads (List.mem_cons_self ..)
          have argumentVars : ∀ options ∈ lists, ∀ candidate ∈ options, candidate.SchemeVars :=
            fun options member => parts options (List.mem_cons_of_mem _ member)
          rcases List.mem_append.mp member with member | member
          · exact declaredVars member
          · obtain ⟨headCandidate, headMember, mine, mineEq, inMine⟩ :=
              mem_of_combine combinedEq member
            obtain ⟨unifier, solved, shapeCase⟩ := mem_headCandidates mineEq inMine
            have headSchemeVars := headVars headCandidate headMember
            have choiceVars : ∀ {choice : List Candidate}, choice ∈ choices lists →
                ∀ chosen ∈ choice, chosen.SchemeVars := by
              intro choice choiceMember chosen chosenMember
              obtain ⟨options, optionsMember, inOptions⟩ :=
                exists_of_forall₂_mem (mem_choices.mp choiceMember) chosenMember
              exact argumentVars options optionsMember chosen inOptions
            have inSchemes : ∀ {choice : List Candidate} {chosen : Candidate}, chosen ∈ choice →
                ∀ scheme ∈ chosen.schemes,
                  scheme ∈ headCandidate.schemes ++ (choice.map Candidate.schemes).flatten :=
              fun chosenMember scheme schemeMember => List.mem_append_right _
                (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, chosenMember, rfl⟩, schemeMember⟩)
            rcases shapeCase with ⟨_, choice, choiceMember, rfl⟩ |
                ⟨parameters, result, shape, _, choice, choiceMember, rfl⟩
            · intro key keyMember
              simp only [tupleCandidate] at keyMember ⊢
              rcases keyMember with typeMember | ⟨equation, equationMember, sides⟩
              · rw [mem_freeVars_ofList] at typeMember
                obtain ⟨element, elementMember, keyInElement⟩ := typeMember
                rcases List.mem_cons.mp elementMember with rfl | elementMember
                · obtain ⟨scheme, schemeMember, inScheme⟩ := headSchemeVars key (.inl keyInElement)
                  exact ⟨scheme, List.mem_append_left _ schemeMember, inScheme⟩
                · obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp elementMember
                  obtain ⟨scheme, schemeMember, inScheme⟩ :=
                    choiceVars choiceMember chosen chosenMember key (.inl keyInElement)
                  exact ⟨scheme, inSchemes chosenMember scheme schemeMember, inScheme⟩
              · rcases List.mem_append.mp equationMember with equationMember | equationMember
                · obtain ⟨scheme, schemeMember, inScheme⟩ :=
                    headSchemeVars key (.inr ⟨equation, equationMember, sides⟩)
                  exact ⟨scheme, List.mem_append_left _ schemeMember, inScheme⟩
                · obtain ⟨equations, equationsMember, inEquations⟩ :=
                    List.mem_flatten.mp equationMember
                  obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp equationsMember
                  obtain ⟨scheme, schemeMember, inScheme⟩ := choiceVars choiceMember chosen
                    chosenMember key (.inr ⟨equation, inEquations, sides⟩)
                  exact ⟨scheme, inSchemes chosenMember scheme schemeMember, inScheme⟩
            · intro key keyMember
              simp only [applicationCandidate] at keyMember ⊢
              have fromHead : key ∈ (unifier.applyTerm headCandidate.type).freeVars →
                  ∃ scheme ∈ headCandidate.schemes ++ (choice.map Candidate.schemes).flatten,
                    key ∈ scheme.freeVars := by
                intro inPrincipal
                obtain ⟨scheme, schemeMember, inScheme⟩ :=
                  schemeVars_of_head solved headSchemeVars inPrincipal
                exact ⟨scheme, List.mem_append_left _ schemeMember, inScheme⟩
              rcases keyMember with typeMember | ⟨equation, equationMember, sides⟩
              · exact fromHead (freeVars_of_arrow shape (.inr rfl) typeMember)
              · rcases List.mem_append.mp equationMember with equationMember | equationMember
                · rcases List.mem_append.mp equationMember with equationMember | equationMember
                  · obtain ⟨scheme, schemeMember, inScheme⟩ :=
                      headSchemeVars key (.inr ⟨equation, equationMember, sides⟩)
                    exact ⟨scheme, List.mem_append_left _ schemeMember, inScheme⟩
                  · obtain ⟨equations, equationsMember, inEquations⟩ :=
                      List.mem_flatten.mp equationMember
                    obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp equationsMember
                    obtain ⟨scheme, schemeMember, inScheme⟩ := choiceVars choiceMember chosen
                      chosenMember key (.inr ⟨equation, inEquations, sides⟩)
                    exact ⟨scheme, inSchemes chosenMember scheme schemeMember, inScheme⟩
                · obtain ⟨inParameters, inTypes⟩ := List.of_mem_zip equationMember
                  rcases sides with side | side
                  · exact fromHead (freeVars_of_arrow shape (.inl inParameters) side)
                  · obtain ⟨chosen, chosenMember, chosenEq⟩ := List.mem_map.mp inTypes
                    rw [← chosenEq] at side
                    obtain ⟨scheme, schemeMember, inScheme⟩ :=
                      choiceVars choiceMember chosen chosenMember key (.inl side)
                    exact ⟨scheme, inSchemes chosenMember scheme schemeMember, inScheme⟩
  | nil =>
      rename_i position index lists computed options member candidate candidateMember
      rw [candidatesList_nil computed] at member
      simp at member
  | cons head tail headIH tailIH =>
      rename_i position index lists computed options member candidate candidateMember
      obtain ⟨first, rest, firstEq, restEq, rfl⟩ := candidatesList_cons computed
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH (position ++ [index]) options firstEq candidate candidateMember
      · exact tailIH position (index + 1) rest restEq options member candidate candidateMember

/-! ## Soundness -/

/-- A safe value of a type variable: variable-free, and a type atom. -/
def Safe (term : TypeTerm) : Prop := rigid (decode term) = term ∧ TypeAtom (decode term)

theorem CleanTerm.safe {term : TypeTerm} (clean : CleanTerm term) : Safe term :=
  ⟨clean.rigid_decode, clean.decode_contract.1⟩

section Soundness

variable (space : Space) {δ : Unifier} (safe : ∀ key, Safe (δ key))
include safe

/-- A safe substitution reads a scheme at a position as the instance by the decoded values. -/
theorem applyTerm_schemeAt_safe (position : List ℕ) (scheme : Atom) :
    δ.applyTerm (schemeAt position scheme) =
      rigid (applyTypeValuation (fun name => decode (δ (position, name))) scheme) := by
  rw [← applyTerm_schemeAt]
  apply Mettapedia.Logic.LP.Subst.applyTerm_congr
  intro key member
  have onPosition := freeVars_schemeAt position scheme key member
  obtain ⟨keyPosition, name⟩ := key
  simp only at onPosition
  subst onPosition
  simp only [instanceAt, if_true]
  exact ((safe _).1).symm

theorem declared_sound {position : List ℕ} {atom : Atom} {candidate : Candidate}
    (member : candidate ∈ declaredCandidates space position atom)
    (instances : ∀ scheme ∈ candidate.schemes, ContractType (decode (δ.applyTerm scheme))) :
    FirstOrderType space atom (decode (δ.applyTerm candidate.type)) := by
  obtain ⟨occurrence, scheme, found, _, rfl⟩ := mem_declaredCandidates member
  have contract := instances _ (List.mem_singleton_self _)
  simp only at contract ⊢
  rw [applyTerm_schemeAt_safe safe, decode_rigid] at contract ⊢
  exact .declared (occurrence := occurrence) ⟨scheme, found, contract, _,
    fun name => (safe (position, name)).2, rfl⟩

omit safe in
theorem unifies_append_left {left right : List (TypeTerm × TypeTerm)}
    (unifies : Unifies δ (left ++ right)) : Unifies δ left :=
  fun equation member => unifies equation (List.mem_append_left _ member)

omit safe in
theorem unifies_append_right {left right : List (TypeTerm × TypeTerm)}
    (unifies : Unifies δ (left ++ right)) : Unifies δ right :=
  fun equation member => unifies equation (List.mem_append_right _ member)

omit safe in
theorem unifies_of_flatten {choice : List Candidate}
    (unifies : Unifies δ (choice.map Candidate.equations).flatten) :
    ∀ candidate ∈ choice, Unifies δ candidate.equations :=
  fun candidate member equation equationMember =>
    unifies equation (List.mem_flatten.mpr
      ⟨candidate.equations, List.mem_map.mpr ⟨candidate, member, rfl⟩, equationMember⟩)

omit safe in
theorem schemes_of_flatten {choice : List Candidate} {property : TypeTerm → Prop}
    (all : ∀ scheme ∈ (choice.map Candidate.schemes).flatten, property scheme) :
    ∀ candidate ∈ choice, ∀ scheme ∈ candidate.schemes, property scheme :=
  fun candidate member scheme schemeMember =>
    all scheme (List.mem_flatten.mpr
      ⟨candidate.schemes, List.mem_map.mpr ⟨candidate, member, rfl⟩, schemeMember⟩)

/-- What soundness proves of the candidates of an atom. -/
def SoundFor (atom : Atom) (candidate : Candidate) : Prop :=
  Unifies δ candidate.equations →
    (∀ scheme ∈ candidate.schemes, ContractType (decode (δ.applyTerm scheme))) →
      FirstOrderType space atom (decode (δ.applyTerm candidate.type))

omit safe in
theorem firstOrderTypes_of_choice :
    ∀ {atoms : List Atom} {lists : List (List Candidate)} {choice : List Candidate},
      List.Forall₂ (fun atom options => ∀ candidate ∈ options, SoundFor space (δ := δ) atom candidate)
        atoms lists →
      List.Forall₂ (· ∈ ·) choice lists →
      (∀ candidate ∈ choice, Unifies δ candidate.equations) →
      (∀ candidate ∈ choice, ∀ scheme ∈ candidate.schemes,
        ContractType (decode (δ.applyTerm scheme))) →
      FirstOrderTypes space atoms
        (choice.map fun candidate => decode (δ.applyTerm candidate.type))
  | [], [], [], .nil, .nil, _, _ => .nil
  | _ :: _, _ :: _, _ :: _, .cons headSound restSound, .cons headMember restMember, unifies,
      instances =>
      .cons (headSound _ headMember (unifies _ (List.mem_cons_self ..))
          (instances _ (List.mem_cons_self ..)))
        (firstOrderTypes_of_choice restSound restMember
          (fun candidate member => unifies candidate (List.mem_cons_of_mem _ member))
          (fun candidate member => instances candidate (List.mem_cons_of_mem _ member)))

omit safe in
theorem map_eq_of_zip {parameters : List TypeTerm} {choice : List Candidate}
    (lengths : parameters.length = choice.length)
    (unifies : Unifies δ (parameters.zip (choice.map Candidate.type))) :
    parameters.map (fun parameter => decode (δ.applyTerm parameter)) =
      choice.map (fun candidate => decode (δ.applyTerm candidate.type)) := by
  induction parameters generalizing choice with
  | nil => cases choice <;> simp_all
  | cons parameter parameters ih =>
      cases choice with
      | nil => simp at lengths
      | cons candidate choice =>
          simp only [List.map_cons, List.cons.injEq]
          refine ⟨?_, ih (by simpa using lengths) (fun equation member =>
            unifies equation (by simp only [List.map_cons, List.zip_cons_cons]; exact
              List.mem_cons_of_mem _ member))⟩
          have := unifies (parameter, candidate.type) (by simp)
          rw [this]

/-- **Soundness.**  Under a safe solution of a candidate's equations whose declared types are
contract types, the candidate's type is a type of the atom. -/
theorem candidates_sound :
    ∀ (atom : Atom) (position : List ℕ) (found : List Candidate),
      candidates space position atom = some found →
        ∀ candidate ∈ found, SoundFor space (δ := δ) atom candidate := by
  intro atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      ∀ (position : List ℕ) (index : ℕ) (lists : List (List Candidate)),
        candidatesList space position index atoms = some lists →
          List.Forall₂ (fun atom options => ∀ candidate ∈ options,
            SoundFor space (δ := δ) atom candidate) atoms lists) with
  | symbol name =>
      intro position found computed candidate member _ instances
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact declared_sound space safe member instances
  | var name =>
      intro position found computed candidate member _ instances
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact declared_sound space safe member instances
  | grounded value =>
      intro position found computed candidate member _ instances
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact declared_sound space safe member instances
  | expression atoms ih =>
      intro position found computed candidate member unifies instances
      cases atoms with
      | nil =>
          simp only [candidates, Option.some.injEq] at computed
          subst computed
          exact declared_sound space safe member instances
      | cons head arguments =>
          obtain ⟨heads, lists, combined, headsEq, listsEq, combinedEq, rfl⟩ :=
            candidates_expression computed
          have parts := ih position 0 (heads :: lists) (by
            simp only [candidatesList, Option.bind_eq_bind, headsEq, Option.bind_some,
              Nat.zero_add, listsEq, Option.pure_def])
          obtain ⟨headSound, argumentsSound⟩ := List.forall₂_cons.mp parts
          rcases List.mem_append.mp member with member | member
          · exact declared_sound space safe member instances
          · obtain ⟨headCandidate, headMember, mine, mineEq, inMine⟩ :=
              mem_of_combine combinedEq member
            obtain ⟨unifier, solved, shapeCase⟩ := mem_headCandidates mineEq inMine
            have atoms : ∀ key, TypeAtom (decode (δ key)) := fun key => (safe key).2
            rcases shapeCase with ⟨shape, choice, choiceMember, rfl⟩ |
                ⟨parameters, result, shape, lengths, choice, choiceMember, rfl⟩
            · have headUnifies := unifies_append_left (δ := δ) unifies
              have choiceUnifies := unifies_of_flatten (unifies_append_right (δ := δ) unifies)
              have headInstances : ∀ scheme ∈ headCandidate.schemes,
                  ContractType (decode (δ.applyTerm scheme)) :=
                fun scheme member => instances scheme (List.mem_append_left _ member)
              have choiceInstances := schemes_of_flatten (fun scheme member =>
                instances scheme (List.mem_append_right _ member))
              have headTyped := headSound headCandidate headMember headUnifies headInstances
              have argumentsTyped := firstOrderTypes_of_choice space argumentsSound
                (mem_choices.mp choiceMember) choiceUnifies choiceInstances
              have notArrow : ¬ArrowShaped (decode (δ.applyTerm headCandidate.type)) := by
                rw [← (solve_absorbed solved headUnifies).applyTerm headCandidate.type]
                exact headShape_value_not_arrow shape atoms
              simp only [tupleCandidate]
              rw [applyTerm_ofList_cons, decode_ofList, List.map_cons, List.map_map,
                List.map_map]
              exact .tuple headTyped notArrow argumentsTyped
            · simp only [applicationCandidate] at unifies instances ⊢
              have headUnifies := unifies_append_left (δ := δ) (unifies_append_left (δ := δ) unifies)
              have choiceUnifies := unifies_of_flatten
                (unifies_append_right (δ := δ) (unifies_append_left (δ := δ) unifies))
              have zipUnifies := unifies_append_right (δ := δ) unifies
              have headInstances : ∀ scheme ∈ headCandidate.schemes,
                  ContractType (decode (δ.applyTerm scheme)) :=
                fun scheme member => instances scheme (List.mem_append_left _ member)
              have choiceInstances := schemes_of_flatten (fun scheme member =>
                instances scheme (List.mem_append_right _ member))
              have headTyped := headSound headCandidate headMember headUnifies headInstances
              have argumentsTyped := firstOrderTypes_of_choice space argumentsSound
                (mem_choices.mp choiceMember) choiceUnifies choiceInstances
              have choiceLengths : choice.length = lists.length :=
                (mem_choices.mp choiceMember).length_eq
              have listsLengths : lists.length = arguments.length :=
                argumentsSound.length_eq.symm
              have parametersEq := map_eq_of_zip (δ := δ)
                (by rw [lengths, choiceLengths, listsLengths]) zipUnifies
              rw [← (solve_absorbed solved headUnifies).applyTerm headCandidate.type,
                headShape_arrow shape, applyTerm_ofList_cons, decode_ofList, List.map_cons,
                List.map_map, List.map_append] at headTyped
              have arrowEq : Atom.expression
                  (decode (δ.applyTerm arrowSymbol) ::
                    (List.map (decode ∘ δ.applyTerm) parameters ++
                      List.map (decode ∘ δ.applyTerm) [result])) =
                  arrowAtom (parameters.map fun parameter => decode (δ.applyTerm parameter))
                    (decode (δ.applyTerm result)) := by
                simp [arrowAtom, arrowSymbol, decode]
              rw [arrowEq, parametersEq] at headTyped
              exact .application headTyped argumentsTyped
  | nil =>
      rename_i position index lists computed
      rw [candidatesList_nil computed]
      exact .nil
  | cons head tail headIH tailIH =>
      rename_i position index lists computed
      obtain ⟨first, rest, firstEq, restEq, rfl⟩ := candidatesList_cons computed
      exact .cons (headIH (position ++ [index]) first firstEq)
        (tailIH position (index + 1) rest restEq)

end Soundness


/-! ## Positions -/

theorem prefix_index_eq {position : List ℕ} {left right : ℕ} {path : List ℕ}
    (leftPrefix : (position ++ [left]) <+: path) (rightPrefix : (position ++ [right]) <+: path) :
    left = right := by
  have lengths : (position ++ [left]).length ≤ (position ++ [right]).length := by simp
  have equal := (List.prefix_of_prefix_length_le leftPrefix rightPrefix lengths).eq_of_length
    (by simp)
  simpa using equal

theorem declared_mem_candidates {space : Space} {position : List ℕ} {atom : Atom}
    {found : List Candidate} (computed : candidates space position atom = some found)
    {candidate : Candidate} (member : candidate ∈ declaredCandidates space position atom) :
    candidate ∈ found := by
  cases atom with
  | symbol _ =>
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact member
  | var _ =>
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact member
  | grounded _ =>
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact member
  | expression atoms =>
      cases atoms with
      | nil =>
          simp only [candidates, Option.some.injEq] at computed
          subst computed
          exact member
      | cons head arguments =>
          obtain ⟨_, _, _, _, _, _, rfl⟩ := candidates_expression computed
          exact List.mem_append_left _ member

/-- The declared types of the candidates of an atom have their variables below its position. -/
theorem candidates_below (space : Space) :
    ∀ (atom : Atom) (position : List ℕ) (found : List Candidate),
      candidates space position atom = some found →
        ∀ candidate ∈ found, ∀ scheme ∈ candidate.schemes, ∀ key ∈ scheme.freeVars,
          position <+: key.1 := by
  have declaredBelow : ∀ {position : List ℕ} {atom : Atom} {candidate : Candidate},
      candidate ∈ declaredCandidates space position atom →
        ∀ scheme ∈ candidate.schemes, ∀ key ∈ scheme.freeVars, position <+: key.1 := by
    intro position atom candidate member scheme schemeMember key keyMember
    obtain ⟨_, declared, _, _, rfl⟩ := mem_declaredCandidates member
    simp only [List.mem_singleton] at schemeMember
    subst schemeMember
    rw [freeVars_schemeAt position declared key keyMember]
  intro atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      ∀ (position : List ℕ) (index : ℕ) (lists : List (List Candidate)),
        candidatesList space position index atoms = some lists →
          ∀ (offset : ℕ) (options : List Candidate), lists[offset]? = some options →
            ∀ candidate ∈ options, ∀ scheme ∈ candidate.schemes, ∀ key ∈ scheme.freeVars,
              (position ++ [index + offset]) <+: key.1) with
  | symbol name =>
      intro position found computed candidate member
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact declaredBelow member
  | var name =>
      intro position found computed candidate member
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact declaredBelow member
  | grounded value =>
      intro position found computed candidate member
      simp only [candidates, Option.some.injEq] at computed
      subst computed
      exact declaredBelow member
  | expression atoms ih =>
      intro position found computed candidate member
      cases atoms with
      | nil =>
          simp only [candidates, Option.some.injEq] at computed
          subst computed
          exact declaredBelow member
      | cons head arguments =>
          obtain ⟨heads, lists, combined, headsEq, listsEq, combinedEq, rfl⟩ :=
            candidates_expression computed
          have parts := ih position 0 (heads :: lists) (by
            simp only [candidatesList, Option.bind_eq_bind, headsEq, Option.bind_some,
              Nat.zero_add, listsEq, Option.pure_def])
          rcases List.mem_append.mp member with member | member
          · exact declaredBelow member
          · obtain ⟨headCandidate, headMember, mine, mineEq, inMine⟩ :=
              mem_of_combine combinedEq member
            obtain ⟨_, _, shapeCase⟩ := mem_headCandidates mineEq inMine
            have headBelow : ∀ scheme ∈ headCandidate.schemes, ∀ key ∈ scheme.freeVars,
                position <+: key.1 := fun scheme schemeMember key keyMember =>
              (List.prefix_append _ _).trans
                (parts 0 heads rfl headCandidate headMember scheme schemeMember key keyMember)
            have choiceBelow : ∀ {choice : List Candidate}, choice ∈ choices lists →
                ∀ scheme ∈ (choice.map Candidate.schemes).flatten, ∀ key ∈ scheme.freeVars,
                  position <+: key.1 := by
              intro choice choiceMember scheme schemeMember key keyMember
              obtain ⟨schemes, schemesMember, inSchemes⟩ := List.mem_flatten.mp schemeMember
              obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp schemesMember
              obtain ⟨options, optionsMember, inOptions⟩ :=
                exists_of_forall₂_mem (mem_choices.mp choiceMember) chosenMember
              obtain ⟨offset, offsetEq⟩ := List.mem_iff_getElem?.mp optionsMember
              exact (List.prefix_append _ _).trans (parts (offset + 1) options
                (by simpa using offsetEq) chosen inOptions scheme inSchemes key keyMember)
            rcases shapeCase with ⟨_, choice, choiceMember, rfl⟩ |
                ⟨_, _, _, _, choice, choiceMember, rfl⟩
            · intro scheme schemeMember key keyMember
              rcases List.mem_append.mp schemeMember with schemeMember | schemeMember
              · exact headBelow scheme schemeMember key keyMember
              · exact choiceBelow choiceMember scheme schemeMember key keyMember
            · intro scheme schemeMember key keyMember
              rcases List.mem_append.mp schemeMember with schemeMember | schemeMember
              · exact headBelow scheme schemeMember key keyMember
              · exact choiceBelow choiceMember scheme schemeMember key keyMember
  | nil =>
      rename_i position index lists computed offset options found candidate candidateMember
        scheme schemeMember key keyMember
      rw [candidatesList_nil computed] at found
      simp at found
  | cons head tail headIH tailIH =>
      rename_i position index lists computed offset options found candidate candidateMember
        scheme schemeMember key keyMember
      obtain ⟨first, rest, firstEq, restEq, rfl⟩ := candidatesList_cons computed
      cases offset with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          have below := headIH (position ++ [index]) first firstEq candidate candidateMember
            scheme schemeMember key keyMember
          simpa using below
      | succ offset =>
          simp only [List.getElem?_cons_succ] at found
          have := tailIH position (index + 1) rest restEq offset options found candidate
            candidateMember scheme schemeMember key keyMember
          simpa [Nat.add_assoc, Nat.add_comm 1 offset] using this

theorem candidatesList_below (space : Space) :
    ∀ (atoms : List Atom) (position : List ℕ) (index : ℕ) (lists : List (List Candidate)),
      candidatesList space position index atoms = some lists →
        ∀ options ∈ lists, ∀ candidate ∈ options, ∀ scheme ∈ candidate.schemes,
          ∀ key ∈ scheme.freeVars, ∃ offset, (position ++ [index + offset]) <+: key.1
  | [], position, index, lists, computed => by
      rw [candidatesList_nil computed]
      intro options member
      simp at member
  | atom :: atoms, position, index, lists, computed => by
      obtain ⟨first, rest, firstEq, restEq, rfl⟩ := candidatesList_cons computed
      intro options member candidate candidateMember scheme schemeMember key keyMember
      rcases List.mem_cons.mp member with rfl | member
      · have below := candidates_below space atom (position ++ [index]) _ firstEq candidate
          candidateMember scheme schemeMember key keyMember
        exact ⟨0, by simpa using below⟩
      · obtain ⟨offset, below⟩ := candidatesList_below space atoms position (index + 1) rest
          restEq options member candidate candidateMember scheme schemeMember key keyMember
        exact ⟨offset + 1, by simpa [Nat.add_assoc, Nat.add_comm 1 offset] using below⟩

/-! ## Completeness -/

theorem candidatesList_length {space : Space} :
    ∀ {atoms : List Atom} {position : List ℕ} {index : ℕ} {lists : List (List Candidate)},
      candidatesList space position index atoms = some lists → lists.length = atoms.length
  | [], _, _, _, computed => by rw [candidatesList_nil computed]; rfl
  | _ :: _, _, _, _, computed => by
      obtain ⟨_, _, _, restEq, rfl⟩ := candidatesList_cons computed
      simp [candidatesList_length restEq]

theorem candidatesList_schemeVars (space : Space) :
    ∀ (atoms : List Atom) (position : List ℕ) (index : ℕ) (lists : List (List Candidate)),
      candidatesList space position index atoms = some lists →
        ∀ options ∈ lists, ∀ candidate ∈ options, candidate.SchemeVars
  | [], _, _, lists, computed => by
      rw [candidatesList_nil computed]
      intro options member
      simp at member
  | atom :: atoms, position, index, lists, computed => by
      obtain ⟨first, rest, firstEq, restEq, rfl⟩ := candidatesList_cons computed
      intro options member
      rcases List.mem_cons.mp member with rfl | member
      · exact candidates_schemeVars space atom (position ++ [index]) _ firstEq
      · exact candidatesList_schemeVars space atoms position (index + 1) rest restEq options member

theorem firstOrderTypes_length {space : Space} :
    ∀ {atoms types : List Atom}, FirstOrderTypes space atoms types → types.length = atoms.length
  | _, _, .nil => rfl
  | _, _, .cons _ rest => by simp [firstOrderTypes_length rest]

theorem forall₂_imp_mem {α β : Type} {left right : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ left as bs →
      (∀ a ∈ as, ∀ b, left a b → right a b) → List.Forall₂ right as bs
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons head rest, imp =>
      .cons (imp _ (List.mem_cons_self ..) _ head)
        (forall₂_imp_mem rest (fun a member b => imp a (List.mem_cons_of_mem _ member) b))

theorem exists_of_forall₂_left {α β : Type} {relation : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ relation as bs → ∀ {a}, a ∈ as →
      ∃ b ∈ bs, relation a b
  | [], [], .nil, _, member => by simp at member
  | _ :: _, _ :: _, .cons head rest, a, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, List.mem_cons_self .., head⟩
      · obtain ⟨b, bMember, related⟩ := exists_of_forall₂_left rest member
        exact ⟨b, List.mem_cons_of_mem _ bMember, related⟩

/-- A solution local to a position: it moves only the variables below the position, each to a
type atom. -/
structure Local (position : List ℕ) (δ : Unifier) : Prop where
  outside : ∀ key : sig.vars, ¬position <+: key.1 → δ key = .var key
  values : ∀ key, δ key = .var key ∨ ∃ atom, TypeAtom atom ∧ δ key = rigid atom

/-- A solution local to the positions from `index` on below a position. -/
structure LocalFrom (position : List ℕ) (index : ℕ) (δ : Unifier) : Prop where
  outside : ∀ key : sig.vars, (∀ offset, ¬(position ++ [index + offset]) <+: key.1) →
    δ key = .var key
  values : ∀ key, δ key = .var key ∨ ∃ atom, TypeAtom atom ∧ δ key = rigid atom

/-- What completeness finds for a candidate at a type: a solution of its equations giving it the
type, under which its declared types are contract types and their variables take type atoms. -/
def Found (δ : Unifier) (candidate : Candidate) (type : Atom) : Prop :=
  Unifies δ candidate.equations ∧ δ.applyTerm candidate.type = rigid type ∧
    ∀ scheme ∈ candidate.schemes, ContractType (decode (δ.applyTerm scheme)) ∧
      ∀ key ∈ scheme.freeVars, TypeAtom (decode (δ key))

theorem found_congr {δ δ' : Unifier} {candidate : Candidate} {type : Atom}
    (vars : candidate.SchemeVars)
    (agree : ∀ scheme ∈ candidate.schemes, ∀ key ∈ scheme.freeVars, δ key = δ' key)
    (found : Found δ candidate type) : Found δ' candidate type := by
  obtain ⟨unifies, typeEq, schemes⟩ := found
  have onTerm : ∀ {term : TypeTerm}, (∀ key ∈ term.freeVars,
      ∃ scheme ∈ candidate.schemes, key ∈ scheme.freeVars) →
        δ'.applyTerm term = δ.applyTerm term := by
    intro term inSchemes
    apply Mettapedia.Logic.LP.Subst.applyTerm_congr
    intro key member
    obtain ⟨scheme, schemeMember, keyMember⟩ := inSchemes key member
    exact (agree scheme schemeMember key keyMember).symm
  refine ⟨fun equation member => ?_, ?_, fun scheme member => ?_⟩
  · rw [onTerm (fun key keyMember => vars key (.inr ⟨equation, member, .inl keyMember⟩)),
      onTerm (fun key keyMember => vars key (.inr ⟨equation, member, .inr keyMember⟩))]
    exact unifies equation member
  · rw [onTerm (fun key keyMember => vars key (.inl keyMember))]
    exact typeEq
  · obtain ⟨contract, atoms⟩ := schemes scheme member
    refine ⟨?_, fun key keyMember => ?_⟩
    · rw [onTerm (fun key keyMember => ⟨scheme, member, keyMember⟩)]
      exact contract
    · rw [← agree scheme member key keyMember]
      exact atoms key keyMember

/-- Two solutions merged at the prefix `position ++ [index]`. -/
def merge (position : List ℕ) (index : ℕ) (left right : Unifier) : Unifier := fun key =>
  if (position ++ [index]) <+: key.1 then left key else right key

theorem merge_values {position : List ℕ} {index : ℕ} {left right : Unifier}
    (leftValues : ∀ key, left key = .var key ∨ ∃ atom, TypeAtom atom ∧ left key = rigid atom)
    (rightValues : ∀ key, right key = .var key ∨ ∃ atom, TypeAtom atom ∧ right key = rigid atom) :
    ∀ key, merge position index left right key = .var key ∨
      ∃ atom, TypeAtom atom ∧ merge position index left right key = rigid atom := by
  intro key
  unfold merge
  split
  · exact leftValues key
  · exact rightValues key

theorem unifies_zip {δ : Unifier} :
    ∀ {terms others : List TypeTerm} {types : List Atom},
      terms.map δ.applyTerm = types.map rigid →
        List.Forall₂ (fun other type => δ.applyTerm other = rigid type) others types →
          Unifies δ (terms.zip others)
  | [], _, _, _, _ => by simp [Unifies]
  | _ :: _, [], _, _, all => by simp [Unifies]
  | term :: terms, other :: others, types, termsEq, all => by
      cases all with
      | cons otherEq rest =>
          simp only [List.map_cons, List.cons.injEq] at termsEq
          intro equation member
          simp only [List.zip_cons_cons, List.mem_cons] at member
          rcases member with rfl | member
          · simp only
            rw [termsEq.1, otherEq]
          · exact unifies_zip termsEq.2 rest equation member

theorem map_type_of_found {δ : Unifier} :
    ∀ {choice : List Candidate} {types : List Atom},
      List.Forall₂ (fun candidate type => Found δ candidate type) choice types →
        choice.map (fun candidate => δ.applyTerm candidate.type) = types.map rigid
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head rest => by
      simp only [List.map_cons, head.2.1, map_type_of_found rest]

/-- A candidate of an argument list is not below the position of the head. -/
theorem chosen_not_below {space : Space} {position : List ℕ} {index : ℕ}
    {atoms : List Atom} {lists : List (List Candidate)}
    (listsEq : candidatesList space position (index + 1) atoms = some lists)
    {choice : List Candidate} (choiceMembers : List.Forall₂ (· ∈ ·) choice lists) :
    ∀ chosen ∈ choice, ∀ scheme ∈ chosen.schemes, ∀ key ∈ scheme.freeVars,
      ¬(position ++ [index]) <+: key.1 := by
  intro chosen chosenMember scheme schemeMember key keyMember below
  obtain ⟨options, optionsMember, inOptions⟩ :=
    exists_of_forall₂_mem choiceMembers chosenMember
  obtain ⟨offset, other⟩ := candidatesList_below space atoms position (index + 1) lists listsEq
    options optionsMember chosen inOptions scheme schemeMember key keyMember
  have := prefix_index_eq below other
  omega

theorem chosen_schemeVars {space : Space} {position : List ℕ} {index : ℕ}
    {atoms : List Atom} {lists : List (List Candidate)}
    (listsEq : candidatesList space position index atoms = some lists)
    {choice : List Candidate} (choiceMembers : List.Forall₂ (· ∈ ·) choice lists) :
    ∀ chosen ∈ choice, chosen.SchemeVars := by
  intro chosen chosenMember
  obtain ⟨options, optionsMember, inOptions⟩ :=
    exists_of_forall₂_mem choiceMembers chosenMember
  exact candidatesList_schemeVars space atoms position index lists listsEq options optionsMember
    chosen inOptions

mutual

/-- **Completeness.**  A type of an atom is found by one of its candidates. -/
theorem candidates_complete (space : Space) :
    ∀ {atom type : Atom}, FirstOrderType space atom type →
      ∀ (position : List ℕ) (found : List Candidate),
        candidates space position atom = some found →
          ∃ candidate ∈ found, ∃ δ : Unifier, Found δ candidate type ∧ Local position δ
  | _, _, @FirstOrderType.declared _ atom type occurrence isInstance, position, found,
      computed => by
      obtain ⟨scheme, schemeFound, contract, valuation, valuesAtomic, instanceEq⟩ := isInstance
      have schemeContract : ContractType scheme :=
        contractType_of_instance valuesAtomic scheme (instanceEq ▸ contract)
      refine ⟨_, declared_mem_candidates computed
        (declaredCandidates_mem position schemeFound schemeContract),
        instanceAt position valuation, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro equation member
        simp at member
      · show (instanceAt position valuation).applyTerm (schemeAt position scheme) = rigid type
        rw [applyTerm_schemeAt, instanceEq]
      · intro other member
        simp only [List.mem_singleton] at member
        subst member
        refine ⟨?_, fun key keyMember => ?_⟩
        · rw [applyTerm_schemeAt, decode_rigid, instanceEq]
          exact contract
        · have onPosition := freeVars_schemeAt position scheme key keyMember
          obtain ⟨keyPosition, name⟩ := key
          simp only at onPosition
          subst onPosition
          simp only [instanceAt, if_true, decode_rigid]
          exact valuesAtomic name
      · intro key notBelow
        simp only [instanceAt]
        rw [if_neg (fun equal => notBelow (by rw [equal]))]
      · intro key
        simp only [instanceAt]
        split
        · exact .inr ⟨_, valuesAtomic _, rfl⟩
        · exact .inl rfl
  | _, _, @FirstOrderType.application _ head result arguments parameters headTyped
      argumentsTyped, position, found, computed => by
      obtain ⟨heads, lists, combined, headsEq, listsEq, combinedEq, rfl⟩ :=
        candidates_expression computed
      obtain ⟨headCandidate, headMember, headSolution, headFoundRaw, headLocal⟩ :=
        candidates_complete space headTyped (position ++ [0]) heads headsEq
      obtain ⟨choice, choiceMembers, argumentSolution, choiceFound, argumentsLocal⟩ :=
        candidatesList_complete space argumentsTyped position 1 lists listsEq
      obtain ⟨unifier, solved⟩ := solve_complete headFoundRaw.1
      have absorbed := solve_absorbed solved headFoundRaw.1
      have principalInstance : headSolution.applyTerm (unifier.applyTerm headCandidate.type) =
          rigid (arrowAtom parameters result) := by
        rw [absorbed.applyTerm, headFoundRaw.2.1]
      obtain ⟨mine, mineEq, mineInside⟩ := combine_of_mem combinedEq headMember
      rcases headShape_of_arrow_instance headLocal.values principalInstance with isVariable |
          ⟨components, last, shape, componentsEq, lastEq⟩
      · rw [headCandidates_variable solved isVariable] at mineEq
        cases mineEq
      · have lengths : components.length = lists.length := by
          have := congrArg List.length componentsEq
          simp only [List.length_map] at this
          rw [this, candidatesList_length listsEq, ← firstOrderTypes_length argumentsTyped]
        rw [headCandidates_arrow solved shape lengths, Option.some.injEq] at mineEq
        subst mineEq
        have candidateMember := mineInside _
          (List.mem_map.mpr ⟨choice, mem_choices.mpr choiceMembers, rfl⟩)
        have headVars := candidates_schemeVars space head (position ++ [0]) heads headsEq
          headCandidate headMember
        have headBelow := candidates_below space head (position ++ [0]) heads headsEq
          headCandidate headMember
        have notBelow := chosen_not_below (index := 0) listsEq choiceMembers
        have chosenVars := chosen_schemeVars listsEq choiceMembers
        let δ := merge position 0 headSolution argumentSolution
        have headAgree : ∀ {term : TypeTerm}, (∀ key ∈ term.freeVars,
            ∃ scheme ∈ headCandidate.schemes, key ∈ scheme.freeVars) →
              δ.applyTerm term = headSolution.applyTerm term := by
          intro term inSchemes
          apply Mettapedia.Logic.LP.Subst.applyTerm_congr
          intro key member
          obtain ⟨scheme, schemeMember, keyMember⟩ := inSchemes key member
          simp only [δ, merge, if_pos (headBelow scheme schemeMember key keyMember)]
        have principalVars : ∀ key ∈ (unifier.applyTerm headCandidate.type).freeVars,
            ∃ scheme ∈ headCandidate.schemes, key ∈ scheme.freeVars :=
          fun key member => schemeVars_of_head solved headVars member
        have headFound : Found δ headCandidate (arrowAtom parameters result) :=
          found_congr headVars (fun scheme schemeMember key keyMember => by
            simp only [δ, merge, if_pos (headBelow scheme schemeMember key keyMember)])
            headFoundRaw
        have chosenFound : List.Forall₂ (fun candidate type => Found δ candidate type)
            choice parameters :=
          forall₂_imp_mem choiceFound (fun chosen chosenMember type found =>
            found_congr (chosenVars chosen chosenMember)
              (fun scheme schemeMember key keyMember => by
                simp only [δ, merge,
                  if_neg (notBelow chosen chosenMember scheme schemeMember key keyMember)])
              found)
        refine ⟨_, List.mem_append_right _ candidateMember, δ, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
        · intro equation member
          simp only [applicationCandidate, List.mem_append] at member
          rcases member with (member | member) | member
          · exact headFound.1 equation member
          · obtain ⟨equations, equationsMember, inEquations⟩ := List.mem_flatten.mp member
            obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp equationsMember
            obtain ⟨_, _, found⟩ := exists_of_forall₂_left chosenFound chosenMember
            exact found.1 equation inEquations
          · refine unifies_zip (types := parameters) ?_ ?_ equation member
            · rw [← componentsEq]
              apply List.map_congr_left
              intro component componentMember
              exact headAgree (fun key keyMember =>
                principalVars key (freeVars_of_arrow shape (.inl componentMember) keyMember))
            · exact List.forall₂_map_left_iff.mpr (chosenFound.imp (fun _ _ found => found.2.1))
        · show δ.applyTerm last = rigid result
          rw [headAgree (fun key keyMember =>
            principalVars key (freeVars_of_arrow shape (.inr rfl) keyMember)), lastEq]
        · intro scheme member
          simp only [applicationCandidate, List.mem_append] at member
          rcases member with member | member
          · exact headFound.2.2 scheme member
          · obtain ⟨schemes, schemesMember, inSchemes⟩ := List.mem_flatten.mp member
            obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp schemesMember
            obtain ⟨_, _, found⟩ := exists_of_forall₂_left chosenFound chosenMember
            exact found.2.2 scheme inSchemes
        · intro key keyNotBelow
          have notHead : ¬(position ++ [0]) <+: key.1 :=
            fun below => keyNotBelow ((List.prefix_append _ _).trans below)
          simp only [δ, merge, if_neg notHead]
          exact argumentsLocal.outside key (fun offset below =>
            keyNotBelow ((List.prefix_append _ _).trans below))
        · exact merge_values headLocal.values argumentsLocal.values
  | _, _, @FirstOrderType.tuple _ head headType arguments argumentTypes headTyped headNotArrow
      argumentsTyped, position, found, computed => by
      obtain ⟨heads, lists, combined, headsEq, listsEq, combinedEq, rfl⟩ :=
        candidates_expression computed
      obtain ⟨headCandidate, headMember, headSolution, headFoundRaw, headLocal⟩ :=
        candidates_complete space headTyped (position ++ [0]) heads headsEq
      obtain ⟨choice, choiceMembers, argumentSolution, choiceFound, argumentsLocal⟩ :=
        candidatesList_complete space argumentsTyped position 1 lists listsEq
      obtain ⟨unifier, solved⟩ := solve_complete headFoundRaw.1
      have absorbed := solve_absorbed solved headFoundRaw.1
      have principalInstance : headSolution.applyTerm (unifier.applyTerm headCandidate.type) =
          rigid headType := by
        rw [absorbed.applyTerm, headFoundRaw.2.1]
      obtain ⟨mine, mineEq, mineInside⟩ := combine_of_mem combinedEq headMember
      rcases headShape_of_value_instance principalInstance headNotArrow with isVariable | isValue
      · rw [headCandidates_variable solved isVariable] at mineEq
        cases mineEq
      · rw [headCandidates_value solved isValue, Option.some.injEq] at mineEq
        subst mineEq
        have candidateMember := mineInside _
          (List.mem_map.mpr ⟨choice, mem_choices.mpr choiceMembers, rfl⟩)
        have headVars := candidates_schemeVars space head (position ++ [0]) heads headsEq
          headCandidate headMember
        have headBelow := candidates_below space head (position ++ [0]) heads headsEq
          headCandidate headMember
        have notBelow := chosen_not_below (index := 0) listsEq choiceMembers
        have chosenVars := chosen_schemeVars listsEq choiceMembers
        let δ := merge position 0 headSolution argumentSolution
        have headFound : Found δ headCandidate headType :=
          found_congr headVars (fun scheme schemeMember key keyMember => by
            simp only [δ, merge, if_pos (headBelow scheme schemeMember key keyMember)])
            headFoundRaw
        have chosenFound : List.Forall₂ (fun candidate type => Found δ candidate type)
            choice argumentTypes :=
          forall₂_imp_mem choiceFound (fun chosen chosenMember type found =>
            found_congr (chosenVars chosen chosenMember)
              (fun scheme schemeMember key keyMember => by
                simp only [δ, merge,
                  if_neg (notBelow chosen chosenMember scheme schemeMember key keyMember)])
              found)
        refine ⟨_, List.mem_append_right _ candidateMember, δ, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
        · intro equation member
          simp only [tupleCandidate, List.mem_append] at member
          rcases member with member | member
          · exact headFound.1 equation member
          · obtain ⟨equations, equationsMember, inEquations⟩ := List.mem_flatten.mp member
            obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp equationsMember
            obtain ⟨_, _, found⟩ := exists_of_forall₂_left chosenFound chosenMember
            exact found.1 equation inEquations
        · show δ.applyTerm (ofList (headCandidate.type :: choice.map Candidate.type)) =
            rigid (.expression (headType :: argumentTypes))
          rw [applyTerm_ofList_cons, headFound.2.1, rigid_expression, List.map_cons, List.map_map]
          congr 2
          exact map_type_of_found chosenFound
        · intro scheme member
          simp only [tupleCandidate, List.mem_append] at member
          rcases member with member | member
          · exact headFound.2.2 scheme member
          · obtain ⟨schemes, schemesMember, inSchemes⟩ := List.mem_flatten.mp member
            obtain ⟨chosen, chosenMember, rfl⟩ := List.mem_map.mp schemesMember
            obtain ⟨_, _, found⟩ := exists_of_forall₂_left chosenFound chosenMember
            exact found.2.2 scheme inSchemes
        · intro key keyNotBelow
          have notHead : ¬(position ++ [0]) <+: key.1 :=
            fun below => keyNotBelow ((List.prefix_append _ _).trans below)
          simp only [δ, merge, if_neg notHead]
          exact argumentsLocal.outside key (fun offset below =>
            keyNotBelow ((List.prefix_append _ _).trans below))
        · exact merge_values headLocal.values argumentsLocal.values

theorem candidatesList_complete (space : Space) :
    ∀ {atoms types : List Atom}, FirstOrderTypes space atoms types →
      ∀ (position : List ℕ) (index : ℕ) (lists : List (List Candidate)),
        candidatesList space position index atoms = some lists →
          ∃ choice, List.Forall₂ (· ∈ ·) choice lists ∧ ∃ δ : Unifier,
            List.Forall₂ (fun candidate type => Found δ candidate type) choice types ∧
              LocalFrom position index δ
  | _, _, .nil, position, index, lists, computed => by
      rw [candidatesList_nil computed]
      exact ⟨[], .nil, Mettapedia.Logic.LP.Subst.id sig, .nil,
        ⟨fun _ _ => rfl, fun _ => .inl rfl⟩⟩
  | _, _, @FirstOrderTypes.cons _ atom type atoms types headTyped tailTyped, position, index,
      lists, computed => by
      obtain ⟨first, rest, firstEq, restEq, rfl⟩ := candidatesList_cons computed
      obtain ⟨chosen, chosenMember, chosenSolution, chosenFound, chosenLocal⟩ :=
        candidates_complete space headTyped (position ++ [index]) first firstEq
      obtain ⟨choice, choiceMembers, restSolution, restFound, restLocal⟩ :=
        candidatesList_complete space tailTyped position (index + 1) rest restEq
      have chosenVars := candidates_schemeVars space atom (position ++ [index]) first firstEq
        chosen chosenMember
      have chosenBelow := candidates_below space atom (position ++ [index]) first firstEq
        chosen chosenMember
      have restNotBelow := chosen_not_below restEq choiceMembers
      have restVars := chosen_schemeVars restEq choiceMembers
      let δ := merge position index chosenSolution restSolution
      refine ⟨chosen :: choice, .cons chosenMember choiceMembers, δ, .cons ?_ ?_, ⟨?_, ?_⟩⟩
      · exact found_congr chosenVars (fun scheme schemeMember key keyMember => by
          simp only [δ, merge, if_pos (chosenBelow scheme schemeMember key keyMember)])
          chosenFound
      · exact forall₂_imp_mem restFound (fun other otherMember type found =>
          found_congr (restVars other otherMember)
            (fun scheme schemeMember key keyMember => by
              simp only [δ, merge,
                if_neg (restNotBelow other otherMember scheme schemeMember key keyMember)])
            found)
      · intro key keyNotBelow
        have notFirst : ¬(position ++ [index]) <+: key.1 := by
          simpa using keyNotBelow 0
        simp only [δ, merge, if_neg notFirst]
        exact restLocal.outside key (fun offset below => keyNotBelow (offset + 1)
          (by simpa [Nat.add_assoc, Nat.add_comm 1 offset] using below))
      · exact merge_values chosenLocal.values restLocal.values

end

/-! ## The principal types decide the contract -/

/-- A clean type term for the type variables a principal type leaves free. -/
def cleanDefault : TypeTerm := .const (.symbol "Type")

theorem cleanDefault_clean : CleanTerm cleanDefault := .symbol (by decide)

theorem admissible_parts {unifier : Unifier} {candidate : Candidate}
    (admissible : admissibleB unifier candidate = true) {scheme : TypeTerm}
    (member : scheme ∈ candidate.schemes) :
    ContractType (decode (unifier.applyTerm scheme)) ∧
      ∀ key ∈ scheme.freeVars, TypeAtom (decode (unifier key)) := by
  unfold admissibleB at admissible
  have admits := List.all_eq_true.mp admissible scheme member
  unfold admitsB at admits
  simp only [Bool.and_eq_true, List.all_eq_true] at admits
  refine ⟨(contractTypeB_iff _).mp admits.1, fun key keyMember => ?_⟩
  exact (typeAtomB_iff _).mp (admits.2 key ((mem_varList scheme key).mpr keyMember))

/-- **Soundness of the principal types.**  If `principal space e` answers `answer`, and `ρ`
instantiates the variables of `answer` by clean types to the type `type`, then `type` is a
contract type of `e`. -/
theorem principal_sound {space : Space} {expression : Atom} {answers : List TypeTerm}
    (computed : principal space expression = some answers) {answer : TypeTerm}
    (member : answer ∈ answers) {type : Atom} {ρ : Unifier}
    (instance' : ρ.applyTerm answer = rigid type)
    (clean : ∀ key ∈ answer.freeVars, CleanTerm (ρ key)) : Typed space expression type := by
  classical
  unfold principal at computed
  simp only [Option.map_eq_some_iff] at computed
  obtain ⟨found, foundEq, rfl⟩ := computed
  obtain ⟨candidate, candidateMember, principalEq⟩ := List.mem_filterMap.mp member
  unfold principalOf at principalEq
  split at principalEq
  · next unifier solved =>
      split at principalEq
      · next admissible =>
          simp only [Option.some.injEq] at principalEq
          subst principalEq
          let cleaned : Unifier := fun key =>
            if key ∈ (unifier.applyTerm candidate.type).freeVars then ρ key else cleanDefault
          have cleanedClean : ∀ key, CleanTerm (cleaned key) := by
            intro key
            simp only [cleaned]
            split
            · next keyMember => exact clean key keyMember
            · exact cleanDefault_clean
          have cleanedType : cleaned.applyTerm (unifier.applyTerm candidate.type) =
              ρ.applyTerm (unifier.applyTerm candidate.type) := by
            apply Mettapedia.Logic.LP.Subst.applyTerm_congr
            intro key keyMember
            simp only [cleaned, if_pos keyMember]
          let δ : Unifier := cleaned ∘ₛ unifier
          have relevant := Mettapedia.Logic.LP.unifyTotal_relevantIdempotent _ _ solved
          have schemeVars := candidates_schemeVars space expression [] found foundEq
            candidate candidateMember
          have safe : ∀ key, Safe (δ key) := by
            intro key
            refine ⟨rigid_decode_applyTerm (unifier key)
              (fun other _ => cleanedClean other), ?_⟩
            by_cases inScheme : ∃ scheme ∈ candidate.schemes, key ∈ scheme.freeVars
            · obtain ⟨scheme, schemeMember, keyMember⟩ := inScheme
              exact (typeAtom_decode_applyTerm (unifier key) (fun other _ => cleanedClean other)
                ((admissible_parts admissible schemeMember).2 key keyMember)).1
            · have notEquation : key ∉ Mettapedia.Logic.LP.eqVars candidate.equations := by
                intro equationMember
                exact inScheme (schemeVars key
                  (.inr (Mettapedia.Logic.LP.mem_eqVars.mp equationMember)))
              have fixed : unifier key = .var key := relevant.fixes key notEquation
              show TypeAtom (decode (cleaned.applyTerm (unifier key)))
              rw [fixed]
              exact (cleanedClean key).decode_contract.1
          have unifies : Unifies δ candidate.equations := by
            intro equation equationMember
            simp only [δ, Mettapedia.Logic.LP.Subst.applyTerm_comp,
              solve_unifies solved equation equationMember]
          have instances : ∀ scheme ∈ candidate.schemes,
              ContractType (decode (δ.applyTerm scheme)) := by
            intro scheme schemeMember
            simp only [δ, Mettapedia.Logic.LP.Subst.applyTerm_comp]
            exact contractType_decode_applyTerm (fun other _ => cleanedClean other)
              (admissible_parts admissible schemeMember).1
          have typed := candidates_sound space safe expression [] found foundEq candidate
            candidateMember unifies instances
          have typeEq : δ.applyTerm candidate.type = rigid type := by
            simp only [δ, Mettapedia.Logic.LP.Subst.applyTerm_comp]
            rw [cleanedType, instance']
          rw [typeEq, decode_rigid] at typed
          exact typed_iff_firstOrder.mpr typed
      · simp at principalEq
  · simp at principalEq

/-- **Completeness of the principal types.**  Every contract type of the expression is an
instance of one of its principal types, by type atoms. -/
theorem principal_complete {space : Space} {expression : Atom} {answers : List TypeTerm}
    (computed : principal space expression = some answers) {type : Atom}
    (typed : Typed space expression type) :
    ∃ answer ∈ answers, ∃ ρ : Unifier, ρ.applyTerm answer = rigid type ∧
      ∀ key ∈ answer.freeVars, TypeAtom (decode (ρ key)) := by
  unfold principal at computed
  simp only [Option.map_eq_some_iff] at computed
  obtain ⟨found, foundEq, rfl⟩ := computed
  obtain ⟨candidate, candidateMember, δ, ⟨unifies, typeEq, schemes⟩, _⟩ :=
    candidates_complete space (typed_iff_firstOrder.mp typed) [] found foundEq
  obtain ⟨unifier, solved⟩ := solve_complete unifies
  obtain ⟨ρ, factor⟩ := Mettapedia.Logic.LP.unifyTotal_mgu _ _ solved δ unifies
  have through : ∀ term : TypeTerm, δ.applyTerm term = ρ.applyTerm (unifier.applyTerm term) := by
    intro term
    rw [← Mettapedia.Logic.LP.Subst.applyTerm_comp]
    congr 1
    funext key
    exact factor key
  have admissible : admissibleB unifier candidate = true := by
    unfold admissibleB
    refine List.all_eq_true.mpr fun scheme member => ?_
    obtain ⟨contract, atoms⟩ := schemes scheme member
    unfold admitsB
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨(contractTypeB_iff _).mpr (contractType_of_decode_applyTerm (σ := ρ) ?_),
      fun key keyMember => (typeAtomB_iff _).mpr ?_⟩
    · rw [← through]
      exact contract
    · have := atoms key ((mem_varList scheme key).mp keyMember)
      rw [factor key] at this
      exact (typeAtom_of_decode_applyTerm _ this).1
  have relevant := Mettapedia.Logic.LP.unifyTotal_relevantIdempotent _ _ solved
  have schemeVars := candidates_schemeVars space expression [] found foundEq candidate
    candidateMember
  refine ⟨unifier.applyTerm candidate.type, List.mem_filterMap.mpr ⟨candidate, candidateMember, ?_⟩,
    ρ, ?_, fun key keyMember => ?_⟩
  · unfold principalOf
    rw [solved]
    simp only [admissible, if_true]
  · rw [← through, typeEq]
  · obtain ⟨original, originalMember, inValue⟩ :=
      Mettapedia.Logic.LP.Subst.mem_freeVars_applyTerm.mp keyMember
    have fixed : unifier key = .var key := relevant.unbound original key inValue
    have value : ρ key = δ key := by rw [factor key, fixed]; rfl
    rw [value]
    have inPrincipal := solve_freeVars solved candidate.type keyMember
    obtain ⟨scheme, schemeMember, inScheme⟩ : ∃ scheme ∈ candidate.schemes, key ∈ scheme.freeVars := by
      rcases Finset.mem_union.mp inPrincipal with typeMember | equationMember
      · exact schemeVars key (.inl typeMember)
      · exact schemeVars key (.inr (Mettapedia.Logic.LP.mem_eqVars.mp equationMember))
    exact (schemes scheme schemeMember).2 key inScheme

/-- A value of a variable inside a clean instance is clean when it is a type atom. -/
theorem clean_of_applyTerm {ρ : Unifier} :
    ∀ (term : TypeTerm), CleanTerm (ρ.applyTerm term) → ∀ key ∈ term.freeVars,
      TypeAtom (decode (ρ key)) → CleanTerm (ρ key) := by
  intro term
  induction term with
  | var key =>
      intro clean other member _
      simp only [Mettapedia.Logic.LP.Term.freeVars, Finset.mem_singleton] at member
      subst member
      exact clean
  | const _ =>
      intro _ key member
      simp [Mettapedia.Logic.LP.Term.freeVars] at member
  | app n arguments ih =>
      intro clean key member atomic
      obtain ⟨index, inArgument⟩ := Mettapedia.Logic.LP.Term.mem_freeVars_app.mp member
      have elementClean : CleanTerm (ρ.applyTerm (arguments index)) → CleanTerm (ρ key) :=
        fun elementClean => ih index elementClean key inArgument atomic
      rw [app_eq_ofList, applyTerm_ofList] at clean
      have element : ρ.applyTerm (arguments index) ∈ (List.ofFn arguments).map ρ.applyTerm :=
        List.mem_map.mpr ⟨arguments index, List.mem_ofFn.mpr ⟨index, rfl⟩, rfl⟩
      generalize listEq : (List.ofFn arguments).map ρ.applyTerm = elements at clean element
      generalize termEq : ofList elements = whole at clean
      cases clean with
      | symbol _ => unfold ofList at termEq; cases termEq
      | grounded _ => unfold ofList at termEq; cases termEq
      | arrow nonempty components =>
          rename_i parts
          have := ofList_injective termEq
          subst this
          rcases List.mem_cons.mp element with first | inParts
          · exfalso
            cases equal : arguments index with
            | var other =>
                rw [equal] at inArgument first
                simp only [Mettapedia.Logic.LP.Term.freeVars, Finset.mem_singleton] at inArgument
                subst inArgument
                rw [show ρ.applyTerm (.var key) = ρ key from rfl] at first
                rw [first] at atomic
                cases atomic with
                | symbol notArrow _ => exact notArrow rfl
            | const _ =>
                rw [equal] at inArgument
                simp [Mettapedia.Logic.LP.Term.freeVars] at inArgument
            | app _ _ =>
                rw [equal] at first
                simp [arrowSymbol] at first
          · exact elementClean (components _ inParts)
      | compound all _ =>
          have := ofList_injective termEq
          subst this
          exact elementClean (all _ element)

/-- **The principal types decide the contract at clean types.** -/
theorem principal_decides {space : Space} {expression : Atom} {answers : List TypeTerm}
    (computed : principal space expression = some answers) {type : Atom} (clean : Clean type) :
    Typed space expression type ↔
      ∃ answer ∈ answers, ∃ ρ : Unifier,
        (∀ key ∈ answer.freeVars, CleanTerm (ρ key)) ∧ ρ.applyTerm answer = rigid type := by
  constructor
  · intro typed
    obtain ⟨answer, member, ρ, instance', atoms⟩ := principal_complete computed typed
    refine ⟨answer, member, ρ, fun key keyMember => ?_, instance'⟩
    have whole : CleanTerm (ρ.applyTerm answer) := by
      rw [instance']
      exact clean
    exact clean_of_applyTerm answer whole key keyMember (atoms key keyMember)
  · rintro ⟨answer, member, ρ, values, instance'⟩
    exact principal_sound computed member instance' values

/-- A checker of the contract with computable answers: whenever it answers an expression, a clean
type is a type of the expression exactly when it is a clean instance of one of the answers. -/
structure PrincipalChecker (space : Space) where
  answers : Atom → Option (List TypeTerm)
  decides : ∀ expression found, answers expression = some found → ∀ type, Clean type →
    (Typed space expression type ↔ ∃ answer ∈ found, ∃ ρ : Unifier,
      (∀ key ∈ answer.freeVars, CleanTerm (ρ key)) ∧ ρ.applyTerm answer = rigid type)

/-- **The principal-type checker**: first-order unification over type terms decides the contract
on every expression whose heads have no bare-variable principal type, overloads included. -/
def principalChecker (space : Space) : PrincipalChecker space where
  answers := principal space
  decides := fun _ _ computed _ clean => principal_decides computed clean

/-! ## Why admissibility is checked -/

namespace AdmissibilityControl

/-- `(: x (List Atom))`, `(: f (-> (List $t) $t Nat))` and `(: z $s)`. -/
def space : Space :=
  Space.ofList
    [SpecBoundary.annotation "x" (.expression [.symbol "List", .symbol "Atom"]),
     SpecBoundary.annotation "f"
       (arrowAtom [.expression [.symbol "List", .var "t"], .var "t"] (.symbol "Nat")),
     SpecBoundary.annotation "z" (.var "s")]

/-- `(f x z)`. -/
abbrev call : Atom := .expression [.symbol "f", .symbol "x", .symbol "z"]

/-- **Negative control: a solvable way of typing without an instance.**  The equations of
`(f x z)` are solvable, with `$t := Atom` and the type `Nat`, but the instance
`(-> (List Atom) Atom Nat)` of `f` has the reserved name `Atom` as a parameter, so it is no
contract type and `(f x z)` has no type: the checker drops a way of typing whose principal
solution does not admit its declared types. -/
theorem call_untyped (type : Atom) : ¬Typed space call type := by
  rw [typed_iff_firstOrder]
  intro typed
  have fDeclarations : declarations space (.symbol "f") =
      [arrowAtom [.expression [.symbol "List", .var "t"], .var "t"] (.symbol "Nat")] := by decide
  have xDeclarations : declarations space (.symbol "x") =
      [.expression [.symbol "List", .symbol "Atom"]] := by decide
  have noAnnotation : declarations space call = [] := by decide
  have fArrow : ∀ {fType : Atom}, FirstOrderType space (.symbol "f") fType →
      ∃ valuation : String → Atom, fType =
        arrowAtom [.expression [.symbol "List", valuation "t"], valuation "t"] (.symbol "Nat") ∧
          ContractType fType := by
    intro fType fTyped
    obtain ⟨occurrence, scheme, found, contract, valuation, _, instanceEq⟩ :=
      firstOrder_symbol fTyped
    rw [fDeclarations] at found
    cases occurrence with
    | succ _ => simp at found
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        refine ⟨valuation, ?_, contract⟩
        rw [← instanceEq]
        simp [applyTypeValuation, arrowAtom]
  cases typed with
  | declared isInstance =>
      obtain ⟨_, found, _⟩ := isInstance
      simp [noAnnotation] at found
  | tuple headTyped headNotArrow _ =>
      obtain ⟨valuation, rfl, _⟩ := fArrow headTyped
      exact headNotArrow (arrowAtom_arrowShaped _ _)
  | application headTyped argumentsTyped =>
      rename_i parameters
      obtain ⟨valuation, headEq, contract⟩ := fArrow headTyped
      obtain ⟨parametersEq, _⟩ := arrowAtom_injective headEq
      subst parametersEq
      cases argumentsTyped with
      | cons xTyped _ =>
          obtain ⟨occurrence, scheme, found, _, xValuation, _, xEq⟩ := firstOrder_symbol xTyped
          rw [xDeclarations] at found
          cases occurrence with
          | succ _ => simp at found
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst found
              simp only [applyTypeValuation, List.map_cons, List.map_nil, Atom.expression.injEq,
                List.cons.injEq, and_true, true_and] at xEq
              have atomComponent : TopReserved (valuation "t") :=
                ⟨"Atom", by simp [reservedTypeNames], xEq.symm⟩
              have components := contract.1.arrowAtom_components (valuation "t") (by simp)
              exact components.2 atomComponent

end AdmissibilityControl

#print axioms principal_sound
#print axioms principal_complete
#print axioms principal_decides
#print axioms principalChecker
#print axioms AdmissibilityControl.call_untyped

end Mettapedia.Languages.MeTTa.HE.HOLContract.Principal
