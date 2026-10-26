import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.GSLT.LanguageDef.SchemaTyping
import Mettapedia.GSLT.LanguageDef.WellSortedClosing
import Mettapedia.GSLT.LanguageDef.WellSortedOpening
import Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
import Mettapedia.OSLF.MeTTaIL.NameSubstitutionLaws
import Mettapedia.OSLF.MeTTaIL.ScopedSubstitutionAgreement

/-!
# Finite named contexts from used free names

An authored pattern has a finite list of free names, while a sorted binding
signature uses context positions. This module builds a sorted intrinsic
context from exactly those names with assignments in the supplied free-type
context. It introduces no new constructor declarations or typing rules.
-/

namespace Mettapedia.GSLT.LanguageDef.NamedFreeContext

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

/-- The intrinsic context contains the sorts of the recorded named entries
in the same order. No extra sort or name inventory is introduced. -/
def contextSorts (entries : List (String × TypeExpr)) : List TypeExpr :=
  entries.map Prod.snd

/-- Read the name at one intrinsically sorted position of the entry list. -/
def nameAt : (entries : List (String × TypeExpr)) →
    {sort : TypeExpr} → Var (contextSorts entries) sort → String
  | [], _, position => nomatch position
  | (name, _) :: _, _, .zero => name
  | _ :: tail, _, .succ position => nameAt tail position

/-- The same naming as an explicitly sorted context map, for consumers that
use the binding-signature renaming interface. -/
def names (entries : List (String × TypeExpr)) :
    (sort : TypeExpr) → Var (contextSorts entries) sort → String :=
  fun _ position => nameAt entries position

/-- Find an intrinsically sorted position by its authored name and sort.
This computes a position rather than selecting one from an existence proof;
for duplicate entries it chooses the first matching occurrence. -/
def lookupPosition? : (entries : List (String × TypeExpr)) →
    (name : String) → (sort : TypeExpr) →
      Option (Var (contextSorts entries) sort)
  | [], _, _ => none
  | (entryName, entrySort) :: rest, name, sort =>
      if _sameName : entryName = name then
        if sameSort : entrySort = sort then
          some (Eq.mp (congrArg (Var (entrySort :: contextSorts rest)) sameSort)
            Var.zero)
        else
          (lookupPosition? rest name sort).map Var.succ
      else
        (lookupPosition? rest name sort).map Var.succ

/-- Computed lookup succeeds exactly for an entry with the requested name
and sort. Wrong-sort aliases do not count as successful lookup. -/
theorem lookupPosition?_isSome_iff :
    ∀ (entries : List (String × TypeExpr)) (name : String) (sort : TypeExpr),
      (lookupPosition? entries name sort).isSome = true ↔
        (name, sort) ∈ entries := by
  intro entries
  induction entries with
  | nil =>
      intro name sort
      simp [lookupPosition?]
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      intro name sort
      by_cases sameName : headName = name
      · by_cases sameSort : headSort = sort
        · simp [lookupPosition?, sameName, sameSort]
        · simp [lookupPosition?, sameName, sameSort,
            List.mem_cons, Prod.mk.injEq]
          have noHead : sort ≠ headSort := Ne.symm sameSort
          simp only [noHead, false_or]
          cases found : lookupPosition? tail name sort <;>
            simpa [found, Option.map, Option.isSome] using ih name sort
      · simp [lookupPosition?, sameName,
          List.mem_cons, Prod.mk.injEq]
        have noHead : name ≠ headName := Ne.symm sameName
        simp only [noHead, false_and, false_or]
        cases found : lookupPosition? tail name sort <;>
          simpa [found, Option.map, Option.isSome] using ih name sort

/-- A computed position really has the requested authored name. Its sort is
already enforced by the result type of `lookupPosition?`. -/
theorem lookupPosition?_sound :
    ∀ (entries : List (String × TypeExpr)) (name : String) (sort : TypeExpr)
      {position : Var (contextSorts entries) sort},
      lookupPosition? entries name sort = some position →
        nameAt entries position = name := by
  intro entries
  induction entries with
  | nil =>
      intro name sort position accepted
      simp [lookupPosition?] at accepted
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      intro name sort position accepted
      by_cases sameName : headName = name
      · by_cases sameSort : headSort = sort
        · subst sort
          simp [lookupPosition?, sameName] at accepted
          subst position
          exact sameName
        · cases found : lookupPosition? tail name sort with
          | none => simp [lookupPosition?, sameName, sameSort, found,
              Option.map] at accepted
          | some prior =>
              simp [lookupPosition?, sameName, sameSort, found,
                Option.map] at accepted
              cases accepted
              exact ih name sort found
      · cases found : lookupPosition? tail name sort with
        | none => simp [lookupPosition?, sameName, found, Option.map] at accepted
        | some prior =>
            simp [lookupPosition?, sameName, found, Option.map] at accepted
            cases accepted
            exact ih name sort found

/-- A total executable construction from the names actually used by a
pattern. Names lacking a free-type assignment are omitted; a checked typed
pattern supplies assignments for all names that matter. -/
def fromUsed (free : FreeTypeContext) : List String → List (String × TypeExpr)
  | [] => []
  | name :: rest =>
      match free name with
      | none => fromUsed free rest
      | some sort => (name, sort) :: fromUsed free rest

/-- No finite name list acquires an intrinsic position from an empty typing
assignment. -/
theorem fromUsed_empty (used : List String) :
    fromUsed FreeTypeContext.empty used = [] := by
  induction used with
  | nil => rfl
  | cons name rest ih =>
      simpa [fromUsed, FreeTypeContext.empty] using ih

/-- Every assigned input name appears with its assigned sort in the computed
entry list. Duplicate occurrences are retained, so no deduplication policy
is silently imposed. -/
theorem fromUsed_has_assigned_pair (free : FreeTypeContext) :
    ∀ (used : List String) (name : String) (sort : TypeExpr),
      name ∈ used → free name = some sort →
        (name, sort) ∈ fromUsed free used := by
  intro used
  induction used with
  | nil =>
      intro name sort membership _
      cases membership
  | cons head tail ih =>
      intro name sort membership assigned
      rcases List.mem_cons.mp membership with same | later
      · subst name
        simp [fromUsed, assigned]
      · cases found : free head with
        | none => simpa [fromUsed, found] using ih name sort later assigned
        | some headSort =>
            simpa [fromUsed, found] using
              (List.mem_cons_of_mem (head, headSort)
                (ih name sort later assigned))

/-- A pair in the finite entry list has a sorted intrinsic position whose
name is exactly the pair's first coordinate. -/
theorem member_has_position :
    ∀ (entries : List (String × TypeExpr)) {name : String} {sort : TypeExpr},
      (name, sort) ∈ entries →
        ∃ position : Var (contextSorts entries) sort,
          nameAt entries position = name := by
  intro entries
  induction entries with
  | nil =>
      intro name sort membership
      cases membership
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      intro name sort membership
      rcases List.mem_cons.mp membership with same | later
      · cases Prod.mk.inj same with
        | intro nameEq sortEq =>
            subst name
            subst sort
            exact ⟨.zero, rfl⟩
      · obtain ⟨position, named⟩ := ih later
        exact ⟨.succ position, named⟩

/-- Every intrinsic position points to an actual pair in its entry list. -/
theorem position_pair_mem :
    ∀ (entries : List (String × TypeExpr)) (sort : TypeExpr)
      (position : Var (contextSorts entries) sort),
      (nameAt entries position, sort) ∈ entries := by
  intro entries
  induction entries with
  | nil =>
      intro sort position
      nomatch position
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      intro sort position
      cases position with
      | zero => exact List.mem_cons_self
      | succ earlier => exact List.mem_cons_of_mem _ (ih sort earlier)

/-- A generated pair's name really came from the input name list. -/
theorem fromUsed_pair_name_mem (free : FreeTypeContext) :
    ∀ (used : List String) (entry : String × TypeExpr),
      entry ∈ fromUsed free used → entry.1 ∈ used := by
  intro used
  induction used with
  | nil =>
      intro entry membership
      cases membership
  | cons head tail ih =>
      intro entry membership
      cases found : free head with
      | none =>
          exact List.mem_cons_of_mem head
            (ih entry (by simpa [fromUsed, found] using membership))
      | some sort =>
          have member : entry = (head, sort) ∨
              entry ∈ fromUsed free tail := by
            simpa [fromUsed, found] using membership
          rcases member with same | later
          · subst entry
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem head (ih entry later)

/-- A typed used name always resolves in the computed intrinsic context. -/
theorem fromUsed_resolves (free : FreeTypeContext) (used : List String)
    {name : String} {sort : TypeExpr}
    (membership : name ∈ used) (assigned : free name = some sort) :
    ∃ position : Var (contextSorts (fromUsed free used)) sort,
      nameAt (fromUsed free used) position = name :=
  member_has_position _
    (fromUsed_has_assigned_pair free used name sort membership assigned)

/-- The same resolution is executable: a used name with an assignment gives
a computed intrinsic position, not merely an existential one. -/
theorem lookupPosition?_fromUsed_complete (free : FreeTypeContext)
    (used : List String) {name : String} {sort : TypeExpr}
    (membership : name ∈ used) (assigned : free name = some sort) :
    (lookupPosition? (fromUsed free used) name sort).isSome = true :=
  (lookupPosition?_isSome_iff _ _ _).mpr
    (fromUsed_has_assigned_pair free used name sort membership assigned)

/-- No generated context position names something outside the input list. -/
theorem fromUsed_positions_named_in_input (free : FreeTypeContext)
    (used : List String) (sort : TypeExpr)
    (position : Var (contextSorts (fromUsed free used)) sort) :
    nameAt (fromUsed free used) position ∈ used :=
  fromUsed_pair_name_mem free used _
    (position_pair_mem (fromUsed free used) sort position)


/-- Close the recorded names outside an existing de Bruijn prefix. The list
orders the newly appended positions; existing indices and display metadata
stay unchanged. Repeated names retain their own positions. -/
def closeNames (depth : Nat) : List String → Pattern → Pattern
  | [], pattern => pattern
  | name :: rest, pattern =>
      closeNames (depth + 1) rest (Substitution.closeFVar depth name pattern)

/-- Open the same positions in reverse closure order. -/
def openNames (depth : Nat) : List String → Pattern → Pattern
  | [], pattern => pattern
  | name :: rest, pattern =>
      Substitution.openBVar depth (.fvar name) (openNames (depth + 1) rest pattern)

/-- The extra free-name slots are outside the entire existing bound prefix. -/
theorem closeNames_scoped (depth : Nat) (names : List String) (pattern : Pattern)
    (scopeProof : Substitution.lc_at depth pattern = true) :
    Substitution.lc_at (depth + names.length) (closeNames depth names pattern) = true := by
  induction names generalizing depth pattern with
  | nil => simpa only [List.length_nil, Nat.add_zero, closeNames] using scopeProof
  | cons name rest ih =>
      have next := ih (depth + 1) (Substitution.closeFVar depth name pattern)
        (Substitution.lc_at_closeFVar scopeProof)
      simpa only [List.length_cons, closeNames, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using next

/-- Readback reconstructs every source constructor, including explicit
substitution and binder metadata. It needs only the original bound scope. -/
theorem openNames_closeNames (depth : Nat) (names : List String) (pattern : Pattern)
    (scopeProof : Substitution.lc_at depth pattern = true) :
    openNames depth names (closeNames depth names pattern) = pattern := by
  induction names generalizing depth pattern with
  | nil => rfl
  | cons name rest ih =>
      simp only [closeNames, openNames,
        ih (depth + 1) (Substitution.closeFVar depth name pattern)
          (Substitution.lc_at_closeFVar scopeProof)]
      exact Substitution.open_close_id depth name pattern scopeProof

/-- Closing a fixed context cannot identify distinct well-scoped bodies. -/
theorem closeNames_injective (depth : Nat) (names : List String)
    {left right : Pattern} (leftScoped : Substitution.lc_at depth left = true)
    (rightScoped : Substitution.lc_at depth right = true)
    (same : closeNames depth names left = closeNames depth names right) : left = right := by
  rw [← openNames_closeNames depth names left leftScoped,
    ← openNames_closeNames depth names right rightScoped, same]

/-- The shared operation preserves exactly the existing object-pattern flag. -/
theorem closeNames_object (depth : Nat) (names : List String) (pattern : Pattern) :
    isObjectPattern (closeNames depth names pattern) = isObjectPattern pattern := by
  induction names generalizing depth pattern with
  | nil => rfl
  | cons name rest ih =>
      simp only [closeNames, ih, Mettapedia.OSLF.MeTTaIL.ClosingRepresentation.isObjectPattern_closeFVar]

/-- Closing changes incidence without changing the canonical-metadata flag. -/
theorem closeNames_metadata (depth : Nat) (names : List String) (pattern : Pattern) :
    (closeNames depth names pattern).hasCanonicalBinderMetadata =
      pattern.hasCanonicalBinderMetadata := by
  induction names generalizing depth pattern with
  | nil => rfl
  | cons name rest ih =>
      simp only [closeNames, ih,
        Mettapedia.OSLF.MeTTaIL.ClosingRepresentation.hasCanonicalBinderMetadata_closeFVar]

/-- Close exactly the finite authored names, retaining all original type
expressions rather than replacing functional or collection sorts by bases. -/
def closeContext (depth : Nat) (entries : List (String × TypeExpr))
    (pattern : Pattern) : Pattern :=
  closeNames depth (entries.map Prod.fst) pattern

/-- Reconstruct the names from the same finite context. -/
def openContext (depth : Nat) (entries : List (String × TypeExpr))
    (pattern : Pattern) : Pattern :=
  openNames depth (entries.map Prod.fst) pattern

/-- Each closed name consumes its original first-match free lookup. No
object-only restriction is needed: typing is preserved for explicit
substitution, nested binders and every original collection representation. -/
theorem closeContext_typed {language : LanguageDef}
    (entries : List (String × TypeExpr)) {bound : List TypeExpr}
    {pattern : Pattern} {sort : TypeExpr}
    (typed : HasType language (FreeTypeContext.ofList entries) bound pattern sort) :
    HasType language FreeTypeContext.empty (bound ++ contextSorts entries)
      (closeContext bound.length entries pattern) sort := by
  induction entries generalizing bound pattern with
  | nil => simpa only [contextSorts, List.map_nil, List.append_nil,
      closeContext, closeNames, FreeTypeContext.ofList_nil] using typed
  | cons entry rest ih =>
      rcases entry with ⟨name, entrySort⟩
      have closed := typed.closeFVarInto
        (destination := FreeTypeContext.ofList rest) name entrySort
        (by simp [FreeTypeContext.ofList])
        (by
          intro actual actualType distinct present
          simpa only [FreeTypeContext.ofList, if_neg (Ne.symm distinct)] using present)
      simpa only [closeContext, contextSorts, List.map_cons, closeNames,
        List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append] using ih closed

/-- The executable inverse recovers every independently typed source body. -/
theorem openContext_closeContext {language : LanguageDef}
    (entries : List (String × TypeExpr)) {bound : List TypeExpr}
    {pattern : Pattern} {sort : TypeExpr}
    (typed : HasType language (FreeTypeContext.ofList entries) bound pattern sort) :
    openContext bound.length entries (closeContext bound.length entries pattern) = pattern :=
  openNames_closeNames bound.length (entries.map Prod.fst) pattern
    (by rw [← Substitution.isWellScopedAt_eq_lc_at]; exact typed.isWellScopedAt)

/-- Distinct finite names make each recorded row agree with first-match
lookup, including entries with functional or collection types. -/
theorem ofList_lookup_of_mem (entries : List (String × TypeExpr))
    (unique : (entries.map Prod.fst).Nodup) {entry : String × TypeExpr}
    (member : entry ∈ entries) :
    FreeTypeContext.ofList entries entry.1 = some entry.2 := by
  induction entries with
  | nil => cases member
  | cons head rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with first | later
      · subst entry
        simp [FreeTypeContext.ofList]
      · have distinct : head.1 ≠ entry.1 := by
          intro same
          apply absent
          rw [same]
          exact List.mem_map.mpr ⟨entry, later, rfl⟩
        simpa only [FreeTypeContext.ofList, if_neg distinct] using ih tailUnique later

/-- Opening consumes the finite bound suffix using the actual free lookup
at each recorded name. This states the primitive compatibility requirement
without presuming that duplicate names have equal sorts. -/
theorem openContext_typed {language : LanguageDef} {free : FreeTypeContext}
    (entries : List (String × TypeExpr))
    (lookups : ∀ entry ∈ entries, free entry.1 = some entry.2)
    {bound : List TypeExpr} {pattern : Pattern} {sort : TypeExpr}
    (typed : HasType language free (bound ++ contextSorts entries) pattern sort) :
    HasType language free bound (openContext bound.length entries pattern) sort := by
  induction entries generalizing bound pattern with
  | nil => simpa only [openContext, List.map_nil, openNames, contextSorts,
      List.append_nil] using typed
  | cons entry rest ih =>
      rcases entry with ⟨name, entrySort⟩
      have tailTyped : HasType language free
          ((bound ++ [entrySort]) ++ contextSorts rest) pattern sort := by
        simpa only [contextSorts, List.map_cons, List.append_assoc,
          List.singleton_append] using typed
      have tailOpened := ih (fun member present => lookups member (List.mem_cons_of_mem _ present))
        tailTyped
      have opened := tailOpened.openLast name (lookups (name, entrySort) List.mem_cons_self)
      simpa only [openContext, List.map_cons, openNames,
        List.length_append, List.length_singleton] using opened

/-- An arbitrary intrinsically typed closed body becomes an independently
well-sorted open source after the finite context's distinct names are restored. -/
theorem openContext_typed_of_nodup {language : LanguageDef}
    (entries : List (String × TypeExpr)) (unique : (entries.map Prod.fst).Nodup)
    {bound : List TypeExpr} {pattern : Pattern} {sort : TypeExpr}
    (typed : HasType language FreeTypeContext.empty
      (bound ++ contextSorts entries) pattern sort) :
    HasType language (FreeTypeContext.ofList entries) bound
      (openContext bound.length entries pattern) sort := by
  apply openContext_typed entries (fun entry member => ofList_lookup_of_mem entries unique member)
  exact typed.recontextualizeFree (by
    intro name nameType member lookup
    simp only [FreeTypeContext.empty, reduceCtorEq] at lookup)

example : (lookupPosition?
    [("w", .base "State"), ("q", .base "Query")]
    "q" (.base "Query")).isSome = true := by
  decide +kernel

example : lookupPosition?
    [("w", .base "State"), ("q", .base "Query")]
    "q" (.base "State") = none := by
  decide +kernel

example : (lookupPosition?
    [("w", .base "State"), ("w", .base "Query")]
    "w" (.base "Query")).isSome = true := by
  decide +kernel

#print axioms fromUsed_resolves
#print axioms fromUsed_positions_named_in_input
#print axioms lookupPosition?_isSome_iff
#print axioms lookupPosition?_sound
#print axioms lookupPosition?_fromUsed_complete

end Mettapedia.GSLT.LanguageDef.NamedFreeContext

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-- The original bound prefix stays positional; each appended slot reads
its recorded free name. No raw syntax is traversed by this finite assignment. -/
def openingAssignment (depth : Nat) (names : List String) : ContextSubstitution.Assignment :=
  fun index => if index < depth then .bvar index else
    match names[index - depth]? with
    | none => .bvar index
    | some name => .fvar name

theorem openingAssignment_before (depth : Nat) (names : List String) (index : Nat)
    (before : index < depth) : openingAssignment depth names index = .bvar index := by
  simp only [openingAssignment, if_pos before]

theorem openingAssignment_named (depth : Nat) (names : List String) (position : Fin names.length) :
    openingAssignment depth names (depth + position.val) = .fvar (names.get position) := by
  have after : ¬ depth + position.val < depth := by omega
  simp only [openingAssignment, if_neg after, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem position.isLt]
  rfl

theorem openingAssignment_scoped (depth : Nat) (names : List String) :
    WellScopedAssignment (depth + names.length) depth (openingAssignment depth names) := by
  intro index inside
  by_cases before : index < depth
  · rw [openingAssignment_before depth names index before]
    exact decide_eq_true before
  · let position : Fin names.length := ⟨index - depth, by omega⟩
    have indexEq : index = depth + position.val := by dsimp [position]; omega
    rw [indexEq, openingAssignment_named]
    rfl

private theorem open_one_substitute (depth : Nat) (name : String) (pattern : Pattern)
    (scopeProof : pattern.isWellScopedAt (depth + 1) = true) :
    Substitution.openBVar depth (.fvar name) pattern =
      substitute (lift depth (single (.fvar name))) pattern := by
  rw [substitute_lift_single]
  exact (Substitution.instantiateBVarAt_eq_openBVar_of_isWellScoped scopeProof rfl).symm

/-- The existing opening operation is the existing simultaneous context
action under a finite name assignment. The proof reuses source substitution
composition and finite-scope agreement, rather than another syntax fold. -/
theorem openNames_as_substitute (depth : Nat) (names : List String) (pattern : Pattern)
    (scopeProof : pattern.isWellScopedAt (depth + names.length) = true) :
    openNames depth names pattern = substitute (openingAssignment depth names) pattern := by
  induction names generalizing depth pattern with
  | nil =>
      have identity : openingAssignment depth [] = Pattern.bvar := by
        funext index
        simp only [openingAssignment, List.getElem?_nil]
        split <;> rfl
      simp only [openNames, identity, substitute_id]
  | cons name rest ih =>
      have sizes : (depth + 1) + rest.length = depth + (name :: rest).length := by
        simp only [List.length_cons]; omega
      have tailScoped : pattern.isWellScopedAt ((depth + 1) + rest.length) = true := by
        simpa only [sizes] using scopeProof
      have tailAction := ih (depth + 1) pattern tailScoped
      have openedScope := substitute_wellScoped (openingAssignment_scoped (depth + 1) rest) tailScoped
      rw [openNames, tailAction, open_one_substitute depth name _ openedScope, substitute_comp]
      apply substitute_eq_of_agree_on_scope _ _ pattern _ scopeProof
      intro index inside
      by_cases before : index < depth
      · have beforePlus : index < depth + 1 := by omega
        simp only [openingAssignment_before (depth + 1) rest index beforePlus,
          substitute, lift, if_pos before, openingAssignment_before depth (name :: rest) index before]
      · by_cases same : index = depth
        · subst index
          simp [openingAssignment, substitute, lift, single, Substitution.liftBVars]
        · let position : Fin rest.length := ⟨index - (depth + 1), by
            simp only [List.length_cons] at inside
            omega⟩
          have indexEq : index = (depth + 1) + position.val := by dsimp [position]; omega
          rw [indexEq, openingAssignment_named (depth + 1) rest position]
          have after : ¬ (depth + 1) + position.val < depth := by omega
          have difference : (depth + 1 + position.val) - depth = position.val + 1 := by omega
          simp only [substitute, openingAssignment, if_neg after, difference,
            List.getElem?_cons_succ, List.getElem?_eq_getElem position.isLt]
          rfl

/-- A context action on the closed representation preserves the appended
name slots and supplies exactly the original images for the bound prefix.
Opening then commutes with that original source action under all binders. -/
theorem openNames_substitute (sourceDepth targetDepth : Nat) (names : List String)
    (actual original : ContextSubstitution.Assignment) (pattern : Pattern)
    (scopeProof : pattern.isWellScopedAt (sourceDepth + names.length) = true)
    (actualScoped : WellScopedAssignment (sourceDepth + names.length)
      (targetDepth + names.length) actual)
    (images : ∀ index, index < sourceDepth →
      openNames targetDepth names (actual index) = original index)
    (slots : ∀ position : Fin names.length,
      actual (sourceDepth + position.val) = .bvar (targetDepth + position.val)) :
    openNames targetDepth names (substitute actual pattern) =
      substitute original (openNames sourceDepth names pattern) := by
  rw [openNames_as_substitute targetDepth names _ (substitute_wellScoped actualScoped scopeProof),
    openNames_as_substitute sourceDepth names pattern scopeProof, substitute_comp, substitute_comp]
  apply substitute_eq_of_agree_on_scope _ _ pattern _ scopeProof
  intro index inside
  by_cases before : index < sourceDepth
  · rw [openingAssignment_before sourceDepth names index before, substitute]
    exact (openNames_as_substitute targetDepth names (actual index)
      (actualScoped index inside)).symm.trans (images index before)
  · let position : Fin names.length := ⟨index - sourceDepth, by omega⟩
    have indexEq : index = sourceDepth + position.val := by dsimp [position]; omega
    rw [indexEq, slots position, substitute,
      openingAssignment_named targetDepth names position,
      openingAssignment_named sourceDepth names position, substitute]

/-- Closing a scoped source body, executing its actual context action, then
restoring names returns exactly the original source substitution result. -/
theorem closeNames_substitution_readback (sourceDepth targetDepth : Nat) (names : List String)
    (actual original : ContextSubstitution.Assignment) (pattern : Pattern)
    (scopeProof : pattern.isWellScopedAt sourceDepth = true)
    (actualScoped : WellScopedAssignment (sourceDepth + names.length)
      (targetDepth + names.length) actual)
    (images : ∀ index, index < sourceDepth →
      openNames targetDepth names (actual index) = original index)
    (slots : ∀ position : Fin names.length,
      actual (sourceDepth + position.val) = .bvar (targetDepth + position.val)) :
    openNames targetDepth names (substitute actual (closeNames sourceDepth names pattern)) =
      substitute original pattern := by
  have closedScope : (closeNames sourceDepth names pattern).isWellScopedAt
      (sourceDepth + names.length) = true := by
    rw [Substitution.isWellScopedAt_eq_lc_at] at scopeProof ⊢
    exact closeNames_scoped sourceDepth names pattern scopeProof
  rw [openNames_substitute sourceDepth targetDepth names actual original _ closedScope
    actualScoped images slots]
  rw [openNames_closeNames sourceDepth names pattern
    (by rwa [← Substitution.isWellScopedAt_eq_lc_at])]

/-- Restoring outer names does not move an original bound variable. -/
theorem openNames_before (depth : Nat) (names : List String) (index : Nat)
    (before : index < depth) : openNames depth names (.bvar index) = .bvar index := by
  have inside : (Pattern.bvar index).isWellScopedAt (depth + names.length) = true :=
    decide_eq_true (by omega)
  rw [openNames_as_substitute depth names _ inside, substitute,
    openingAssignment_before depth names index before]

/-- Each appended position restores the recorded name at exactly that slot. -/
theorem openNames_named (depth : Nat) (names : List String) (position : Fin names.length) :
    openNames depth names (.bvar (depth + position.val)) = .fvar (names.get position) := by
  have inside : (Pattern.bvar (depth + position.val)).isWellScopedAt
      (depth + names.length) = true := decide_eq_true (by omega)
  rw [openNames_as_substitute depth names _ inside, substitute,
    openingAssignment_named depth names position]

end Mettapedia.GSLT.LanguageDef.NamedFreeContext

namespace Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BindingSyntax
set_option autoImplicit false

/-- Every recorded row agrees with the header's actual first-match lookup.
Repeated names with the same type are permitted. -/
def compatibleHeader (entries : List (String × TypeExpr)) : Bool :=
  entries.all fun entry => FreeTypeContext.ofList entries entry.1 == some entry.2

theorem compatibleHeader_sound (entries : List (String × TypeExpr))
    (accepted : compatibleHeader entries = true) :
    ∀ entry ∈ entries,FreeTypeContext.ofList entries entry.1 = some entry.2 := by
  intro entry member
  exact beq_iff_eq.mp ((List.all_eq_true.mp accepted) entry member)

theorem entriesOn_compatible (free : FreeTypeContext) (used : List String) :
    compatibleHeader (free.entriesOn used) = true := by
  apply List.all_eq_true.mpr
  intro entry member
  obtain ⟨present,lookup⟩ := (FreeTypeContext.entriesOn_mem_iff free used entry.1 entry.2).mp member
  exact beq_iff_eq.mpr (by rw [FreeTypeContext.ofList_entriesOn,if_pos present,lookup])

/-- Receipt data reuses the original sorted binding Term. Its finite header
names exactly the additional bound suffix; the source stays independently
submitted to the readback checker. -/
structure SourceReceiptData (language : LanguageDef) (bound : List TypeExpr) (sort : TypeExpr) where
  entries : List (String × TypeExpr)
  term : Term (signatureOf language) (bound ++ contextSorts entries) sort

/-- Check the finite context, the actual source spine, and exact restoration
of the submitted source. All proofs are reconstructed from these checks. -/
def SourceReceiptData.accepts {language : LanguageDef} {bound : List TypeExpr} {sort : TypeExpr}
    (receipt : SourceReceiptData language bound sort) (source : Pattern) : Bool :=
  compatibleHeader receipt.entries &&
    SourceReadback.check receipt.term (closeContext bound.length receipt.entries source) &&
      (openContext bound.length receipt.entries (closeContext bound.length receipt.entries source) == source)

/-- Readback restores the original raw source judgment, including its
substitution and binder/collection metadata domain. -/
theorem SourceReceiptData.sound {language : LanguageDef} {bound : List TypeExpr} {sort : TypeExpr}
    (receipt : SourceReceiptData language bound sort) (source : Pattern)
    (accepted : receipt.accepts source = true) :
    HasType language (FreeTypeContext.ofList receipt.entries) bound source sort := by
  obtain ⟨initialChecks,reopened⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨header,readback⟩ := Bool.and_eq_true_iff.mp initialChecks
  have closed := SourceReadback.typed receipt.term _ readback
  have lookup := compatibleHeader_sound receipt.entries header
  have closedInHeader := closed.recontextualizeFree (target := FreeTypeContext.ofList receipt.entries)
    (by intro name nameType member impossible; cases impossible)
  have opened := openContext_typed receipt.entries lookup closedInHeader
  have exactSource : openContext bound.length receipt.entries
      (closeContext bound.length receipt.entries source) = source := beq_iff_eq.mp reopened
  rwa [exactSource] at opened

/-- Every independently typed source has finite, checkable receipt data.
The header preserves all free lookups used by that source. -/
theorem SourceReceiptData.exists_of_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (typed : HasType language free bound source sort) :
    ∃ receipt : SourceReceiptData language bound sort,
      receipt.accepts source = true ∧
      ∀ name ∈ source.freeFvarNames,FreeTypeContext.ofList receipt.entries name = free name := by
  let entries := free.entriesOn source.freeFvarNames
  have finiteTyped : HasType language (FreeTypeContext.ofList entries) bound source sort :=
    (HasType.finiteFree_iff language free bound source sort).mpr typed
  have closed := closeContext_typed entries finiteTyped
  obtain ⟨term,readback⟩ := SourceReadback.typed_exists closed
  refine ⟨⟨entries,term⟩,?_,?_⟩
  · have reopened := openContext_closeContext entries finiteTyped
    have header : compatibleHeader entries = true := entriesOn_compatible free _
    simp only [SourceReceiptData.accepts,header,readback,reopened,
      beq_self_eq_true,Bool.and_self]
  · intro name member
    exact (FreeTypeContext.ofList_entriesOn free source.freeFvarNames name).trans (if_pos member)

#print axioms compatibleHeader_sound
#print axioms entriesOn_compatible
#print axioms SourceReceiptData.sound
#print axioms SourceReceiptData.exists_of_typed
end Mettapedia.GSLT.LanguageDef.NamedFreeContext

namespace Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax
set_option autoImplicit false

/-- An existing intrinsic term supplies receipt data without proof search. -/
def SourceReceiptData.ofTerm {language : LanguageDef} {bound : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) bound sort) : SourceReceiptData language bound sort where
  entries := []
  term := (List.append_nil bound).symm ▸ term

theorem SourceReceiptData.ofTerm_accepts {language : LanguageDef} {bound : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) bound sort) :
    (SourceReceiptData.ofTerm term).accepts (erase term) = true := by
  have compare : SourceReadback.check (SourceReceiptData.ofTerm term).term (erase term) =
      SourceReadback.check term (erase term) :=
    SourceReadback.check_transport (List.append_nil bound).symm term (erase term)
  simpa only [SourceReceiptData.accepts,SourceReceiptData.ofTerm,compatibleHeader,
    List.all_nil,closeContext,List.map_nil,closeNames,openContext,openNames,
    beq_self_eq_true,Bool.true_and,Bool.and_true] using compare.trans (SourceReadback.check_erase term)

#print axioms SourceReceiptData.ofTerm_accepts
end Mettapedia.GSLT.LanguageDef.NamedFreeContext
