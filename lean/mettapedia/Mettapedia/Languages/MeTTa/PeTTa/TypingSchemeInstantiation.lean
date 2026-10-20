import Mettapedia.Languages.MeTTa.PeTTa.TypingSourceViews
import Mettapedia.Logic.LP.PrivateVariableRenaming
import Mettapedia.Logic.LP.StructuralTestRenaming

/-!
# Fresh instances of numbered typing declarations

A stored declaration uses local numbered slots, shared between its subject
and type. A use places all those slots in one fresh scope. The allocator
chooses a scope beyond the finite set of live caller roots, including retained
constraints. Repeated indices stay shared; different uses get disjoint slots.

Any two fresh choices have the same public solution family, even after later
caller equations are added. This models the fresh variable table used by
SWI's `varnumbers/2`; it does not verify the Prolog heap allocator, attributed
variables, or the encoding of arbitrary source objects into numbered rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.TypingSchemeInstantiation

open Mettapedia.Logic.LP
open UnificationRenaming IndependentOutputUnification
open JointSchemeContracts

variable {Value : Type}
abbrev signature (Value : Type) := TypingSourceViews.signature Value Coordinate
local notation "τ" => signature Value
local notation "Ty" => Term τ

def InScope (scope : Nat) (term : Ty) : Prop :=
  ∀ slot ∈ term.freeVars, ∃ index, slot = Coordinate.scheme scope index

def place (scope : Nat) : Coordinate → Coordinate
  | .scheme _ index => .scheme scope index
  | slot => slot

def instantiate (scope : Nat) (term : Ty) : Ty := rename (place scope) term

theorem instantiated_variables (scope : Nat) (term : Ty) (localSlots : InScope 0 term)
    (slot : Coordinate) :
    slot ∈ (instantiate scope term).freeVars ↔
      ∃ index, Coordinate.scheme 0 index ∈ term.freeVars ∧ slot = .scheme scope index := by
  rw [instantiate,StructuralTestRenaming.mem_freeVars_rename (σ := τ)]
  constructor
  · rintro ⟨old,present,equal⟩
    obtain ⟨index,rfl⟩ := localSlots old present
    exact ⟨index,present,equal⟩
  · rintro ⟨index,present,equal⟩
    exact ⟨.scheme 0 index,present,equal⟩

theorem recover_numbered_slots (scope : Nat) (term : Ty) (localSlots : InScope 0 term) :
    instantiate 0 (instantiate scope term) = term := by
  unfold instantiate
  rw [rename_comp]
  apply Subst.applyTerm_eq_self
  intro slot present
  obtain ⟨index,rfl⟩ := localSlots slot present
  rfl

theorem instantiation_injective (scope : Nat) (left right : Ty)
    (leftLocal : InScope 0 left) (rightLocal : InScope 0 right)
    (equal : instantiate scope left = instantiate scope right) : left = right := by
  have recovered := congrArg (instantiate 0) equal
  simpa only [recover_numbered_slots scope left leftLocal,
    recover_numbered_slots scope right rightLocal] using recovered

theorem separate_instances (first second : Nat) (different : first ≠ second)
    (left right : Ty) (leftLocal : InScope 0 left) (rightLocal : InScope 0 right) :
    Disjoint (instantiate first left).freeVars (instantiate second right).freeVars := by
  apply Finset.disjoint_left.mpr
  intro slot inLeft inRight
  obtain ⟨i,_,rfl⟩ := (instantiated_variables first left leftLocal slot).mp inLeft
  obtain ⟨j,_,equal⟩ := (instantiated_variables second right rightLocal _).mp inRight
  exact different (Coordinate.scheme.inj equal).1

def liveVariables (terms : List Ty) : Finset Coordinate :=
  terms.foldr (fun term rest => term.freeVars ∪ rest) ∅

theorem mem_liveVariables (terms : List Ty) (slot : Coordinate) :
    slot ∈ liveVariables terms ↔ ∃ term ∈ terms, slot ∈ term.freeVars := by
  induction terms with
  | nil => simp [liveVariables]
  | cons term terms ih =>
      change slot ∈ term.freeVars ∪ liveVariables terms ↔ _
      simp [ih]

def scopeIndex : Coordinate → Nat
  | .scheme scope _ => scope
  | .hole scope _ => scope
  | .observation _ => 0

def freshScope (live : List Ty) : Nat := (liveVariables live).sup scopeIndex + 1

theorem below_freshScope (live : List Ty) (slot : Coordinate)
    (present : slot ∈ liveVariables live) : scopeIndex slot < freshScope live := by
  exact Nat.lt_succ_of_le (Finset.le_sup present)

def FreshFor (scope : Nat) (live : List Ty) : Prop :=
  ∀ term ∈ live, ∀ index, Coordinate.scheme scope index ∉ term.freeVars

theorem freshScope_fresh (live : List Ty) : FreshFor (freshScope live) live := by
  intro term present index occurs
  have bound := below_freshScope live (.scheme (freshScope live) index)
    ((mem_liveVariables live _).mpr ⟨term,present,occurs⟩)
  exact Nat.lt_irrefl _ bound

theorem instantiate_apart (live : List Ty) (term : Ty) (localSlots : InScope 0 term) :
    Disjoint (instantiate (freshScope live) term).freeVars (liveVariables live) := by
  apply Finset.disjoint_left.mpr
  intro slot instantiated existing
  obtain ⟨index,_,rfl⟩ := (instantiated_variables _ term localSlots slot).mp instantiated
  obtain ⟨old,present,occurs⟩ := (mem_liveVariables live _).mp existing
  exact freshScope_fresh live old present index occurs

def swapScopes (first second : Nat) : Coordinate → Coordinate
  | .scheme scope index => .scheme (Equiv.swap first second scope) index
  | slot => slot

theorem swapScopes_inverse (first second : Nat) :
    Function.LeftInverse (swapScopes first second) (swapScopes first second) := by
  intro slot
  cases slot <;> simp [swapScopes]

theorem swap_instantiation (first second : Nat) (term : Ty) (localSlots : InScope 0 term) :
    rename (swapScopes first second) (instantiate first term) = instantiate second term := by
  rw [instantiate,rename_comp]
  apply Subst.applyTerm_congr
  intro slot present
  obtain ⟨index,rfl⟩ := localSlots slot present
  simp [place,swapScopes]

theorem fresh_term_fixed (first second : Nat) (term : Ty)
    (firstFresh : FreshFor first [term]) (secondFresh : FreshFor second [term]) :
    rename (swapScopes first second) term = term := by
  apply Subst.applyTerm_eq_self
  intro slot present
  cases slot with
  | observation _ => rfl
  | hole _ _ => rfl
  | scheme scope index =>
      have notFirst : scope ≠ first := by
        rintro rfl; exact firstFresh term (by simp) index present
      have notSecond : scope ≠ second := by
        rintro rfl; exact secondFresh term (by simp) index present
      simp only [swapScopes,Equiv.swap_apply_of_ne_of_ne notFirst notSecond]

theorem fresh_terms_fixed (first second : Nat) (terms : List Ty)
    (firstFresh : FreshFor first terms) (secondFresh : FreshFor second terms) :
    terms.map (rename (swapScopes first second)) = terms := by
  calc
    _ = terms.map id := by
      apply List.map_congr_left
      intro term present
      apply fresh_term_fixed first second term
      · intro other member index
        have equal : other = term := List.mem_singleton.mp member
        subst other
        exact firstFresh term present index
      · intro other member index
        have equal : other = term := List.mem_singleton.mp member
        subst other
        exact secondFresh term present index
    _ = terms := List.map_id terms

structure NumberedDeclaration (Value : Type) where
  occurrence : Nat
  subject : Term (signature Value)
  type : Term (signature Value)
  subjectLocal : InScope 0 subject
  typeLocal : InScope 0 type

def decode (scope : Nat) (row : NumberedDeclaration Value) :
    DeclarationTypeCandidates.Declaration τ :=
  ⟨row.occurrence,instantiate scope row.subject,instantiate scope row.type⟩

def allocate (live : List Ty) (row : NumberedDeclaration Value) :
    DeclarationTypeCandidates.Declaration τ := decode (freshScope live) row

theorem allocation_apart (live : List Ty) (row : NumberedDeclaration Value) :
    Disjoint (allocate live row).subject.freeVars (liveVariables live) ∧
    Disjoint (allocate live row).type.freeVars (liveVariables live) :=
  ⟨instantiate_apart live row.subject row.subjectLocal,
    instantiate_apart live row.type row.typeLocal⟩

def declarationProblem (scope : Nat) (row : NumberedDeclaration Value)
    (subject expected : Ty) : List (Ty × Ty) :=
  [(subject,(decode scope row).subject),((decode scope row).type,expected)]

def callerRoots (subject expected : Ty) (later : List (Ty × Ty))
    (observations : List Ty) : List Ty :=
  subject :: expected :: later.flatMap (fun pair => [pair.1,pair.2]) ++ observations

theorem fresh_choice_equivalent (row : NumberedDeclaration Value)
    (subject expected : Ty) (later : List (Ty × Ty)) (observations : List Ty)
    (first second : Nat)
    (firstFresh : FreshFor first (callerRoots subject expected later observations))
    (secondFresh : FreshFor second (callerRoots subject expected later observations)) :
    solutions (declarationProblem first row subject expected ++ later) observations =
      solutions (declarationProblem second row subject expected ++ later) observations := by
  have fixed (term : Ty) (present : term ∈ callerRoots subject expected later observations) :
      rename (swapScopes first second) term = term := by
    apply fresh_term_fixed first second term
    · intro other member index
      have equal : other = term := List.mem_singleton.mp member
      subst other
      exact firstFresh term present index
    · intro other member index
      have equal : other = term := List.mem_singleton.mp member
      subst other
      exact secondFresh term present index
  have subjectFixed := fixed subject (by simp [callerRoots])
  have expectedFixed := fixed expected (by simp [callerRoots])
  have contextFixed : equations (swapScopes first second) later = later := by
    calc
      _ = later.map id := by
        apply List.map_congr_left
        intro pair present
        apply Prod.ext
        · apply fixed pair.1
          exact List.mem_append_left observations (List.mem_cons_of_mem subject
            (List.mem_cons_of_mem expected (List.mem_flatMap.mpr ⟨pair,present,by simp⟩)))
        · apply fixed pair.2
          exact List.mem_append_left observations (List.mem_cons_of_mem subject
            (List.mem_cons_of_mem expected (List.mem_flatMap.mpr ⟨pair,present,by simp⟩)))
      _ = later := List.map_id later
  have observationsFixed : observations.map (rename (swapScopes first second)) = observations := by
    calc
      _ = observations.map id := List.map_congr_left fun term present =>
        fixed term (by simp [callerRoots,present])
      _ = observations := List.map_id observations
  have problemRenamed : equations (swapScopes first second)
      (declarationProblem first row subject expected) =
      declarationProblem second row subject expected := by
    simp only [equations,declarationProblem,decode,List.map_cons,List.map_nil,
      subjectFixed,expectedFixed,swap_instantiation _ _ row.subject row.subjectLocal,
      swap_instantiation _ _ row.type row.typeLocal]
  have same := PrivateVariableRenaming.solutions_private_renaming
    (swapScopes first second) (swapScopes first second) (swapScopes_inverse first second)
    (declarationProblem first row subject expected) later observations contextFixed observationsFixed
  rw [problemRenamed] at same
  exact same.symm

theorem fresh_choice_checker [DecidableEq Value] (row : NumberedDeclaration Value)
    (subject expected : Ty) (later : List (Ty × Ty)) (observations : List Ty)
    (first second : Nat)
    (firstFresh : FreshFor first (callerRoots subject expected later observations))
    (secondFresh : FreshFor second (callerRoots subject expected later observations)) :
    publish (unifyTotal (declarationProblem first row subject expected ++ later)) observations =
      publish (unifyTotal (declarationProblem second row subject expected ++ later)) observations :=
  IndependentOutputUnification.total_publication_congr _ _ observations
    (fresh_choice_equivalent row subject expected later observations first second firstFresh secondFresh)

/-- The computed allocation satisfies the source freshness premise. -/
theorem allocated_checker_exact [DecidableEq Value] (row : NumberedDeclaration Value)
    (subject expected : Ty) (later : List (Ty × Ty)) (observations : List Ty)
    (reference : Nat)
    (referenceFresh : FreshFor reference (callerRoots subject expected later observations)) :
    publish (unifyTotal (declarationProblem
      (freshScope (callerRoots subject expected later observations)) row subject expected ++ later)) observations =
      publish (unifyTotal (declarationProblem reference row subject expected ++ later)) observations :=
  fresh_choice_checker row subject expected later observations _ reference
    (freshScope_fresh _) referenceFresh

namespace Controls

abbrev sig := signature String
def symbol (name : String) : Term sig := TypingSourceViews.symbol name
def localSlot : Term sig := .var (.scheme 0 0)
def number : Term sig := symbol "Number"
def string : Term sig := symbol "String"

theorem slot_is_local : InScope 0 localSlot := by
  intro slot present
  have equal : slot = Coordinate.scheme 0 0 :=
    (Term.mem_freeVars_var (σ := sig)).mp present
  subst slot
  exact ⟨0,rfl⟩

def generic : NumberedDeclaration String :=
  ⟨7,symbol "value",localSlot,
    by intro slot present; exact (Term.not_mem_freeVars_const present).elim,
    slot_is_local⟩

theorem subject_and_type_keep_one_slot (scope : Nat) :
    instantiate scope (ListTerms.ofList [localSlot,localSlot]) =
      ListTerms.ofList [.var (.scheme scope 0),.var (.scheme scope 0)] := by
  exact ListTerms.apply_ofList (Constant := TypingSourceViews.Leaf String) (Variable := Coordinate)
    (fun slot => .var (place scope slot)) [localSlot,localSlot]

theorem later_caller_constraints_preserved (later : List (Term sig × Term sig))
    (observations : List (Term sig)) (subject expected : Term sig) (reference : Nat)
    (referenceFresh : FreshFor reference (callerRoots subject expected later observations)) :
    publish (unifyTotal (declarationProblem
      (freshScope (callerRoots subject expected later observations)) generic subject expected ++ later)) observations =
      publish (unifyTotal (declarationProblem reference generic subject expected ++ later)) observations :=
  allocated_checker_exact generic subject expected later observations reference referenceFresh

def required (first second : Nat) : List (Term sig × Term sig) :=
  [(instantiate first localSlot,number),(instantiate second localSlot,string)]

theorem independent_instances_succeed : ∃ witness, unifyTotal (required 1 2) = some witness := by
  apply unifyTotal_complete
  let witness : Subst sig := fun slot =>
    if slot = .scheme 1 0 then number else if slot = .scheme 2 0 then string else .var slot
  refine ⟨witness,?_⟩
  intro pair present
  simp only [required,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl <;>
    simp [instantiate,rename,localSlot,place,Subst.applyTerm,witness,number,string,symbol,TypingSourceViews.symbol]

theorem reused_scope_is_rejected : unifyTotal (required 1 1) = none := by
  rw [unifyTotal_none_iff_not_unifiable (σ := sig)]
  rintro ⟨witness,solves⟩
  have left : witness (.scheme 1 0) = number :=
    solves (instantiate 1 localSlot,number) (by simp [required])
  have right : witness (.scheme 1 0) = string :=
    solves (instantiate 1 localSlot,string) (by simp [required])
  have impossible := left.symm.trans right
  simp [number,string,symbol,TypingSourceViews.symbol] at impossible

end Controls

#print axioms instantiated_variables
#print axioms instantiation_injective
#print axioms separate_instances
#print axioms allocation_apart
#print axioms fresh_choice_equivalent
#print axioms fresh_choice_checker
#print axioms allocated_checker_exact
#print axioms Controls.independent_instances_succeed
#print axioms Controls.reused_scope_is_rejected

end Mettapedia.Languages.MeTTa.PeTTa.TypingSchemeInstantiation
