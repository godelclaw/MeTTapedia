import Mettapedia.GSLT.LanguageDef.TopDownMatchDerivatives
import Mettapedia.GSLT.LanguageDef.TopDownMatchDerivativeNormalization
import Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Binding-exact subterm automata for first-order MeTTaIL subjects

The structural machines feed the same canonical binding matcher. The
complete observation list agrees with independently matching every authored
pattern at every first-order subterm. In particular a structural wildcard
does not bypass the equality check for a repeated metavariable.

First-order subject plans are the existing `PatternPlan` carrier; erasure
gives ordinary MeTTaIL patterns. No new term or binding semantics is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MeTTaILSubtermMatchAutomata

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open MeTTaILFirstOrderRuleCompilation
open SubtermMatching

namespace View
export MeTTaILPatternMatrixCompilation.Matrix (Head lowerPattern lowerSubject)
end View

mutual
  def subterms : PatternPlan → List (Position × PatternPlan)
    | p@(.metavariable _) => [([], p)]
    | p@(.bound _) => [([], p)]
    | p@(.application _ arguments) => ([], p) :: subtermsList 0 arguments

  def subtermsList : Nat → List PatternPlan → List (Position × PatternPlan)
    | _, [] => []
    | next, p :: ps =>
        (subterms p).map (fun entry => (next :: entry.1, entry.2)) ++
          subtermsList (next + 1) ps
end

/-- Resolve a physical child position using the existing structural context.
The siblings remain in authored order on both sides of the distinguished hole. -/
def selectSite? (subject : PatternPlan) : Position →
    Option (Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext × PatternPlan)
  | [] => some (.hole, subject)
  | index :: path =>
      match subject with
      | .application head children => do
          let child ← children[index]?
          let selected ← selectSite? child path
          pure (.apply head (erasePatterns (children.take index)) selected.1
            (erasePatterns (children.drop (index + 1))), selected.2)
      | _ => none
termination_by path => path.length

/-- A selected site reconstructs the exact source, including untouched siblings. -/
theorem selectSite?_fill {subject : PatternPlan} {path : Position}
    {context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext} {focus : PatternPlan}
    (selected : selectSite? subject path = some (context, focus)) :
    context.fill focus.erase = subject.erase := by
  induction path generalizing subject context focus with
  | nil =>
      simp only [selectSite?, Option.some.injEq, Prod.mk.injEq] at selected
      rcases selected with ⟨rfl, rfl⟩
      rfl
  | cons index path ih =>
      cases subject with
      | metavariable name => simp [selectSite?] at selected
      | bound index => simp [selectSite?] at selected
      | application head children =>
          cases childRead : children[index]? with
          | none => simp [selectSite?, childRead] at selected
          | some child =>
              cases innerRead : selectSite? child path with
              | none => simp [selectSite?, childRead, innerRead] at selected
              | some inner =>
                  rw [selectSite?, childRead] at selected
                  dsimp at selected
                  rw [innerRead] at selected
                  simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at selected
                  rcases selected with ⟨rfl, rfl⟩
                  obtain ⟨bound, child_eq⟩ := List.getElem?_eq_some_iff.mp childRead
                  have restored := List.take_append_drop index children
                  rw [List.drop_eq_getElem_cons bound, child_eq] at restored
                  have erased := congrArg (List.map PatternPlan.erase) restored
                  simp only [List.map_append, List.map_cons, ← erasePatterns_eq_map] at erased
                  simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
                    ih innerRead, PatternPlan.erase, erased]

/-- A context whose filled source is first order preserves that syntax when
its hole receives another first-order term. Unsupported frames cannot satisfy
the source premise. -/
theorem firstOrder_fill
    (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext) (source target : Pattern)
    (sourceFirstOrder : isMatchCorrectAux (context.fill source) = true)
    (targetFirstOrder : isMatchCorrectAux target = true) :
    isMatchCorrectAux (context.fill target) = true := by
  induction context generalizing source target with
  | hole => exact targetFirstOrder
  | apply head before inner after ih =>
      simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
        isMatchCorrectAux] at sourceFirstOrder ⊢
      have admitted := (isMatchCorrectListAux_iff_forall _).mp sourceFirstOrder
      apply (isMatchCorrectListAux_iff_forall _).mpr
      intro pattern member
      rcases List.mem_append.mp member with beforeMember | suffix
      · exact admitted pattern (List.mem_append.mpr (Or.inl beforeMember))
      · rcases List.mem_cons.mp suffix with rfl | suffix
        · exact ih source target (admitted (inner.fill source) (by simp)) targetFirstOrder
        · exact admitted pattern (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ suffix)))
  | lambda name inner ih =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, isMatchCorrectAux] at sourceFirstOrder
  | multiLambda arity names inner ih =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, isMatchCorrectAux] at sourceFirstOrder
  | substBody inner replacement ih =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, isMatchCorrectAux] at sourceFirstOrder
  | substReplacement body inner ih =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, isMatchCorrectAux] at sourceFirstOrder
  | collection kind before inner after rest ih =>
      simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, isMatchCorrectAux] at sourceFirstOrder

/-- The traversal retains the physical child ordinal rather than quotienting
equal-looking siblings or their subterm positions. -/
theorem mem_subtermsList_iff (next : Nat) (children : List PatternPlan)
    (position : Position) (focus : PatternPlan) :
    (position, focus) ∈ subtermsList next children ↔
      ∃ index child path, children[index]? = some child ∧
        position = (next + index) :: path ∧ (path, focus) ∈ subterms child := by
  induction children generalizing next with
  | nil => simp [subtermsList]
  | cons child children ih =>
      simp only [subtermsList, List.mem_append]
      constructor
      · rintro (first | rest)
        · obtain ⟨⟨path, found⟩, member, same⟩ := List.mem_map.mp first
          obtain ⟨position_eq, rfl⟩ := Prod.mk.inj same
          exact ⟨0, child, path, rfl, by simpa using position_eq.symm, member⟩
        · obtain ⟨index, found, path, read, same, member⟩ := (ih (next + 1)).mp rest
          exact ⟨index + 1, found, path, read, by simpa [Nat.add_assoc, Nat.add_comm 1] using same, member⟩
      · rintro ⟨index, found, path, read, same, member⟩
        cases index with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at read
            subst found
            left
            exact List.mem_map.mpr ⟨(path, focus), member, by simpa using same.symm⟩
        | succ index =>
            right
            exact (ih (next + 1)).mpr
              ⟨index, found, path, read, by simpa [Nat.add_assoc, Nat.add_comm 1] using same, member⟩

/-- Resolution succeeds exactly at the subterms retained by the ordered
traversal. The context is reconstructed, never supplied as unchecked metadata. -/
theorem selectSite?_exists_iff (subject : PatternPlan) (path : Position) (focus : PatternPlan) :
    (∃ context, selectSite? subject path = some (context, focus)) ↔
      (path, focus) ∈ subterms subject := by
  induction path generalizing subject with
  | nil =>
      cases subject <;> simp [selectSite?, subterms, mem_subtermsList_iff, eq_comm]
  | cons index path ih =>
      cases subject with
      | metavariable name => simp [selectSite?, subterms]
      | bound bound => simp [selectSite?, subterms]
      | application head children =>
          simp only [subterms, List.mem_cons, Prod.mk.injEq]
          simp only [List.cons_ne_nil, false_and, false_or]
          rw [mem_subtermsList_iff]
          simp only [Nat.zero_add, List.cons.injEq]
          constructor
          · rintro ⟨context, selected⟩
            cases childRead : children[index]? with
            | none => simp [selectSite?, childRead] at selected
            | some child =>
                cases innerRead : selectSite? child path with
                | none => simp [selectSite?, childRead, innerRead] at selected
                | some inner =>
                    rw [selectSite?, childRead] at selected
                    dsimp at selected
                    rw [innerRead] at selected
                    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at selected
                    exact ⟨index, child, path, childRead, ⟨rfl, rfl⟩,
                      (ih child).mp ⟨inner.1, by simpa only [← selected.2, Prod.eta] using innerRead⟩⟩
          · rintro ⟨foundIndex, child, innerPath, read, ⟨rfl, rfl⟩, member⟩
            obtain ⟨inner, selected⟩ := (ih child).mpr member
            exact ⟨.apply head (erasePatterns (children.take index)) inner
              (erasePatterns (children.drop (index + 1))), by simp [selectSite?, read, selected]⟩

mutual
  theorem positions_lowerSubject (subject : PatternPlan) :
      positions (View.lowerSubject subject.erase) =
        (subterms subject).map (fun entry => (entry.1, View.lowerSubject entry.2.erase)) := by
    cases subject with
    | metavariable name => simp [PatternPlan.erase, View.lowerSubject, positions, positionsList, subterms]
    | bound index => simp [PatternPlan.erase, View.lowerSubject, positions, positionsList, subterms]
    | application head arguments =>
        simp only [PatternPlan.erase, View.lowerSubject, positions, subterms, List.map_cons]
        congr 1
        exact positions_lowerSubjects 0 arguments

  theorem positions_lowerSubjects (next : Nat) (subjects : List PatternPlan) :
      positionsList next ((erasePatterns subjects).map View.lowerSubject) =
        (subtermsList next subjects).map (fun entry => (entry.1, View.lowerSubject entry.2.erase)) := by
    cases subjects with
    | nil => rfl
    | cons s ss =>
        simp only [erasePatterns, List.map_cons, positionsList, subtermsList,
          List.map_append, List.map_map]
        rw [positions_lowerSubject, positions_lowerSubjects]
        simp only [List.map_map, Function.comp_def]
end

structure BoundMatch where
  location : Location
  bindings : Bindings
deriving DecidableEq, Repr

/-- Independent canonical reference, including the exact binding-list order. -/
def reference (patterns : List Pattern) (subject : PatternPlan) : List BoundMatch :=
  (subterms subject).flatMap fun entry =>
    patterns.zipIdx.flatMap fun row =>
      (matchPattern row.1 entry.2.erase).map (fun bindings => ⟨⟨entry.1, row.2⟩, bindings⟩)

/-- Implementations share the existing occurrence-and-binding observation type.
This interface is restricted to first-order subject plans; it makes no scoped
assignment or declaration-admission claim. -/
abbrev OrderedMatcher := List Pattern → PatternPlan → List BoundMatch

/-- Exact ordered observations, including multiplicity and binding-list order. -/
abbrev MatchingExact (implementation : OrderedMatcher) : Prop :=
  ∀ patterns subject, implementation patterns subject = reference patterns subject

/-- Structural candidates only license the canonical matching attempt. -/
def complete (candidates : List Location) (patterns : List Pattern)
    (subject : PatternPlan) : List BoundMatch :=
  (subterms subject).flatMap fun entry =>
    patterns.zipIdx.flatMap fun row =>
      if (⟨entry.1, row.2⟩ : Location) ∈ candidates then
        (matchPattern row.1 entry.2.erase).map (fun bindings => ⟨⟨entry.1, row.2⟩, bindings⟩)
      else []

theorem candidate_of_binding (patterns : List Pattern) (subject : PatternPlan)
    (entry : Position × PatternPlan) (entryMember : entry ∈ subterms subject)
    (row : Pattern × Nat) (rowMember : row ∈ patterns.zipIdx)
    (bindings : Bindings) (matched : bindings ∈ matchPattern row.1 entry.2.erase) :
    (⟨entry.1, row.2⟩ : Location) ∈ SubtermMatching.reference
      (patterns.map View.lowerPattern) (View.lowerSubject subject.erase) := by
  unfold SubtermMatching.reference
  apply List.mem_flatMap.mpr
  refine ⟨(entry.1, View.lowerSubject entry.2.erase), ?_, ?_⟩
  · rw [positions_lowerSubject]
    exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩
  · apply List.mem_map.mpr
    refine ⟨row.2, ?_, rfl⟩
    rw [select_eq_zipIdx]
    apply List.mem_filterMap.mpr
    refine ⟨(View.lowerPattern row.1, row.2), ?_, ?_⟩
    · rw [List.mk_mem_zipIdx_iff_getElem?]
      simp only [List.getElem?_map, List.mem_zipIdx_iff_getElem?.mp rowMember, Option.map_some]
    · have accepted := MeTTaILPatternMatrixCompilation.Matrix.structuralMatch_of_matchRel
        (matchPattern_sound matched)
      simp [accepted]

theorem complete_reference (patterns : List Pattern) (subject : PatternPlan) :
    complete (SubtermMatching.reference (patterns.map View.lowerPattern)
      (View.lowerSubject subject.erase)) patterns subject = reference patterns subject := by
  unfold complete reference
  apply List.flatMap_congr
  intro entry entryMember
  apply List.flatMap_congr
  intro row rowMember
  split
  · rfl
  · rename_i absent
    have refused : matchPattern row.1 entry.2.erase = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro bindings matched
      exact absent (candidate_of_binding patterns subject entry entryMember row rowMember bindings matched)
    simp [refused]

def bottomUp (patterns : List Pattern) (subject : PatternPlan) : List BoundMatch :=
  complete (BottomUpMatchAutomaton.run (patterns.map View.lowerPattern)
    (View.lowerSubject subject.erase)) patterns subject

def topDown (patterns : List Pattern) (subject : PatternPlan) : List BoundMatch :=
  complete (TopDownMatchDerivatives.run (patterns.map View.lowerPattern)
    (View.lowerSubject subject.erase)) patterns subject

/-- Exact canonical matches: occurrence, position, bindings, order, multiplicity. -/
theorem bottomUp_eq_reference (patterns : List Pattern) (subject : PatternPlan) :
    bottomUp patterns subject = reference patterns subject := by
  rw [bottomUp, BottomUpMatchAutomaton.run_eq_reference, complete_reference]

theorem topDown_eq_reference (patterns : List Pattern) (subject : PatternPlan) :
    topDown patterns subject = reference patterns subject := by
  rw [topDown, TopDownMatchDerivatives.run_eq_reference, complete_reference]

/-- The partitioned relative-control derivative machine still uses canonical
binding completion. Its control pool shares inspection work without merging
physical rule occurrences or subject positions. -/
def normalizedTopDown (patterns : List Pattern) (subject : PatternPlan) : List BoundMatch :=
  complete (TopDownMatchDerivativeNormalization.run (patterns.map View.lowerPattern)
    (View.lowerSubject subject.erase)) patterns subject

theorem normalizedTopDown_eq_reference (patterns : List Pattern) (subject : PatternPlan) :
    normalizedTopDown patterns subject = reference patterns subject := by
  rw [normalizedTopDown, TopDownMatchDerivativeNormalization.run_eq_reference,
    complete_reference]

theorem bottomUp_matching_exact : MatchingExact bottomUp := bottomUp_eq_reference

theorem topDown_matching_exact : MatchingExact topDown := topDown_eq_reference

theorem normalizedTopDown_matching_exact : MatchingExact normalizedTopDown :=
  normalizedTopDown_eq_reference

/-- The matcher face of an authored language uses its exact rewrite list. -/
def languagePatterns (language : LanguageDef) : List Pattern := language.rewrites.map (·.left)

theorem language_matches_exact (language : LanguageDef) (subject : PatternPlan) :
    bottomUp (languagePatterns language) subject = reference (languagePatterns language) subject ∧
      topDown (languagePatterns language) subject = reference (languagePatterns language) subject :=
  ⟨bottomUp_eq_reference _ _, topDown_eq_reference _ _⟩

namespace NormalizedControls

private def unary : PatternPlan := .application "f" [.metavariable "x"]
private def unarySubject : PatternPlan := .application "f" [.application "a" []]
private def observed : List BoundMatch :=
  [⟨⟨[], 0⟩, [("x", .apply "a" [])]⟩, ⟨⟨[], 1⟩, [("x", .apply "a" [])]⟩]

theorem duplicate_order_preserved :
    normalizedTopDown [unary.erase, unary.erase] unarySubject = observed := by
  rw [normalizedTopDown_eq_reference]
  decide +kernel

theorem dropping_duplicate_changes_observations :
    normalizedTopDown [unary.erase, unary.erase] unarySubject ≠ observed.take 1 := by
  rw [duplicate_order_preserved]
  decide +kernel

theorem repeated_variable_conflict_refused :
    normalizedTopDown
      [(.application "pair" [.metavariable "x", .metavariable "x"] : PatternPlan).erase]
      (.application "pair" [.application "a" [], .application "b" []]) = [] := by
  rw [normalizedTopDown_eq_reference]
  decide +kernel

theorem repeated_siblings_keep_positions :
    (normalizedTopDown [(.application "a" [] : PatternPlan).erase]
      (.application "pair" [.application "a" [], .application "a" []])).map (·.location) =
      [⟨[0], 0⟩, ⟨[1], 0⟩] := by
  rw [normalizedTopDown_eq_reference]
  decide +kernel

end NormalizedControls

namespace SiteControls

private def leaf : PatternPlan := .application "a" []
private def siblings : PatternPlan := .application "pair" [leaf, leaf]

theorem repeated_sibling_positions :
    selectSite? siblings [0] = some (.apply "pair" [] .hole [leaf.erase], leaf) ∧
      selectSite? siblings [1] = some (.apply "pair" [leaf.erase] .hole [], leaf) := by
  constructor <;> simp [selectSite?, siblings, leaf, erasePatterns]

theorem distinct_sibling_replacements :
    let replacement := Pattern.apply "b" []
    (Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.apply "pair" [] .hole [leaf.erase]).fill replacement ≠
      (Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.apply "pair" [leaf.erase] .hole []).fill replacement := by
  decide +kernel

theorem missing_position_refused :
    selectSite? siblings [2] = none ∧ selectSite? siblings [1, 0] = none := by
  decide +kernel

end SiteControls

#print axioms selectSite?_fill
#print axioms selectSite?_exists_iff
#print axioms firstOrder_fill
#print axioms mem_subtermsList_iff
#print axioms SiteControls.repeated_sibling_positions
#print axioms SiteControls.distinct_sibling_replacements
#print axioms SiteControls.missing_position_refused
#print axioms bottomUp_eq_reference
#print axioms topDown_eq_reference
#print axioms NormalizedControls.duplicate_order_preserved
#print axioms NormalizedControls.dropping_duplicate_changes_observations
#print axioms NormalizedControls.repeated_variable_conflict_refused
#print axioms NormalizedControls.repeated_siblings_keep_positions
#print axioms normalizedTopDown_eq_reference
#print axioms normalizedTopDown_matching_exact
#print axioms language_matches_exact

end Mettapedia.GSLT.LanguageDef.MeTTaILSubtermMatchAutomata
