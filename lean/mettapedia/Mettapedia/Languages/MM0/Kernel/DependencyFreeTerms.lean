import Mettapedia.Languages.MM0.Kernel.FreeVariables

/-!
# Terms without bound-variable dependencies

A context of regular variables that depend on nothing has no bound variable.
A declaration whose formals are such variables, and which returns no
dependency, introduces none. An expression typed over such a context and
such declarations has the empty set of free bound variables. This is the
free-variable premise of definition admission for first-order bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

/-- Every binder is a regular variable with no dependencies. -/
def Context.DependencyFree (context : Context) : Prop :=
  ∀ binder ∈ context, ∃ sort, binder = Binder.regular sort ∅

/-- Regular dependency-free formals, and no returned dependency. -/
structure TermDecl.DependencyFree (declaration : TermDecl) : Prop where
  arguments : Context.DependencyFree declaration.arguments
  dependencies : declaration.dependencies = ∅

namespace Preterm

open FreeVariables

theorem images_empty (target formal : Context) (arguments : List Preterm) :
    Images target formal arguments ∅ ∅ :=
  ⟨by simp, by simp⟩

/-- Dependency-free formals whose arguments have empty free sets contribute
nothing. -/
theorem contributions_empty {target fullFormal : Context} {arguments : List Preterm} :
    ∀ {formal : Context} {freeSets : List (Finset Nat)},
      Context.DependencyFree formal → freeSets.length = formal.length →
      (∀ free ∈ freeSets, free = ∅) →
      Contributions target fullFormal arguments formal freeSets ∅
  | [], [], _, _, _ => .nil
  | binder :: formal, free :: freeSets, regular, length, empty => by
      obtain ⟨sort, rfl⟩ := regular binder (by simp)
      have freeEmpty : free = ∅ := empty free (by simp)
      subst freeEmpty
      have rest : Contributions target fullFormal arguments formal freeSets ∅ :=
        contributions_empty (fun other member => regular other (List.mem_cons_of_mem _ member))
          (by simpa using length)
          (fun other member => empty other (List.mem_cons_of_mem _ member))
      simpa using Contributions.regular (sort := sort) (free := ∅)
        (images_empty target fullFormal arguments) rest
  | [], _ :: _, _, length, _ => by simp at length
  | _ :: _, [], _, length, _ => by simp at length

/-- Over a dependency-free context and dependency-free declarations, a typed
spine whose collected arguments have empty free sets has the empty free set. -/
theorem HasType.freeSpine_empty {signature : TermSignature} {context remaining : Context}
    {source : Preterm} {sort : Nat} (typing : HasType signature context source remaining sort)
    (regularContext : Context.DependencyFree context)
    (regularDeclarations : ∀ symbol declaration, signature symbol = some declaration →
      declaration.DependencyFree)
    {arguments : List Preterm} {freeSets : List (Finset Nat)}
    (fits : List.Forall₂ (FitsBinder signature context) arguments remaining)
    (lengths : freeSets.length = arguments.length)
    (empty : ∀ free ∈ freeSets, free = ∅) :
    FreeSpine signature context source arguments freeSets ∅ := by
  induction typing generalizing arguments freeSets with
  | @var index binder lookup =>
      cases fits
      have noSets : freeSets = [] := List.length_eq_zero_iff.mp (by simpa using lengths)
      subst noSets
      obtain ⟨sort, rfl⟩ := regularContext binder (List.mem_of_getElem? lookup)
      exact .var (.regular lookup)
  | @term symbol declaration lookup =>
      have valid := regularDeclarations symbol declaration lookup
      have contributions := contributions_empty (target := context)
        (fullFormal := declaration.arguments) (arguments := arguments) valid.arguments
        (lengths.trans fits.length_eq) empty
      have images : Images context declaration.arguments arguments declaration.dependencies ∅ := by
        rw [valid.dependencies]
        exact images_empty _ _ _
      simpa using FreeSpine.term lookup fits contributions images
  | bound _ lookup _ =>
      obtain ⟨sort, impossible⟩ := regularContext _ (List.mem_of_getElem? lookup)
      cases impossible
  | regular _ argumentTyping functionHypothesis argumentHypothesis =>
      have child := argumentHypothesis (freeSets := []) .nil rfl (by simp)
      exact .app child
        (functionHypothesis (.cons (.regular argumentTyping) fits) (by simpa using lengths)
          (by
            intro free member
            rcases List.mem_cons.mp member with same | inTail
            · exact same
            · exact empty free inTail))

/-- A typed saturated expression over a dependency-free context and
dependency-free declarations has no free bound variable. -/
theorem HasType.freeVars_empty {signature : TermSignature} {context : Context}
    {source : Preterm} {sort : Nat} (typing : HasType signature context source [] sort)
    (regularContext : Context.DependencyFree context)
    (regularDeclarations : ∀ symbol declaration, signature symbol = some declaration →
      declaration.DependencyFree) :
    FreeVars signature context source ∅ :=
  typing.freeSpine_empty (freeSets := []) regularContext regularDeclarations .nil rfl (by simp)

end Preterm

end Mettapedia.Languages.MM0.Kernel
