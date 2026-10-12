import Mettapedia.GSLT.Parsing.CanonicalGrammar

/-!
# Nonempty separated-list recursion preserves yields and projections

Singleton plus right cons and singleton plus left snoc have the same token
yields at the same ordered element lists. Element yields may be empty or
ambiguous; separator token lists may be empty. No deduplication or reversal
is part of the transformation.

The result is connected to the existing `ListForm.separated`, `PrintsList`,
`Derives`, and `canon` interfaces. Across two classified grammars, the explicit
boundary is equality of the element-printing interfaces. No whole-grammar,
lexer, packed-forest multiplicity, or byte-printer equivalence is assumed.
Nullable separator macros are modeled separately: their epsilon alternative
changes the language when the recursion is redirected.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.NonemptySeparatorRefactoring

open CanonicalGrammar

universe u v

variable {Element : Type u} {Token : Type v}

inductive Right (element : Element → List Token → Prop) (separator : List Token) :
    List Element → List Token → Prop where
  | one {e : Element} {tokens : List Token} (h : element e tokens) : Right element separator [e] tokens
  | cons {e : Element} {es : List Element} {head tail : List Token}
      (he : element e head) (rest : Right element separator es tail) :
      Right element separator (e :: es) (head ++ separator ++ tail)

inductive Left (element : Element → List Token → Prop) (separator : List Token) :
    List Element → List Token → Prop where
  | one {e : Element} {tokens : List Token} (h : element e tokens) : Left element separator [e] tokens
  | snoc {es : List Element} {e : Element} {lead tail : List Token}
      (rest : Left element separator es lead) (he : element e tail) :
      Left element separator (es ++ [e]) (lead ++ separator ++ tail)

variable {element other : Element → List Token → Prop} {separator : List Token}

theorem Right.nonempty {es : List Element} {tokens : List Token}
    (h : Right element separator es tokens) : es ≠ [] := by
  cases h <;> simp

theorem Left.nonempty {es : List Element} {tokens : List Token}
    (h : Left element separator es tokens) : es ≠ [] := by
  cases h <;> simp

theorem Right.append_element {es : List Element} {tokens tail : List Token} {e : Element}
    (h : Right element separator es tokens) (he : element e tail) :
    Right element separator (es ++ [e]) (tokens ++ separator ++ tail) := by
  induction h with
  | one h => exact .cons h (.one he)
  | cons h rest ih => simpa only [List.cons_append, List.append_assoc] using Right.cons h ih

theorem Left.prepend_element {es : List Element} {tokens head : List Token} {e : Element}
    (he : element e head) (h : Left element separator es tokens) :
    Left element separator (e :: es) (head ++ separator ++ tokens) := by
  induction h with
  | one h => simpa only [List.singleton_append] using Left.snoc (Left.one he) h
  | snoc rest h ih => simpa only [List.cons_append, List.append_assoc] using Left.snoc ih h

theorem right_to_left {es : List Element} {tokens : List Token}
    (h : Right element separator es tokens) : Left element separator es tokens := by
  induction h with
  | one h => exact .one h
  | cons h rest ih => exact ih.prepend_element h

theorem left_to_right {es : List Element} {tokens : List Token}
    (h : Left element separator es tokens) : Right element separator es tokens := by
  induction h with
  | one h => exact .one h
  | snoc rest h ih => exact ih.append_element h

theorem orientation_equivalence (es : List Element) (tokens : List Token) :
    Right element separator es tokens ↔ Left element separator es tokens :=
  ⟨right_to_left, left_to_right⟩

theorem Right.map_element (preserve : ∀ e tokens, element e tokens → other e tokens)
    {es : List Element} {tokens : List Token} (h : Right element separator es tokens) :
    Right other separator es tokens := by
  induction h with
  | one h => exact .one (preserve _ _ h)
  | cons h rest ih => exact .cons (preserve _ _ h) ih

theorem Left.map_element (preserve : ∀ e tokens, element e tokens → other e tokens)
    {es : List Element} {tokens : List Token} (h : Left element separator es tokens) :
    Left other separator es tokens := by
  induction h with
  | one h => exact .one (preserve _ _ h)
  | snoc rest h ih => exact .snoc ih (preserve _ _ h)

theorem orientation_equivalence_of_element_iff
    (same : ∀ e tokens, element e tokens ↔ other e tokens)
    (es : List Element) (tokens : List Token) :
    Right element separator es tokens ↔ Left other separator es tokens := by
  constructor
  · intro h
    exact (right_to_left h).map_element (fun e tokens => (same e tokens).mp)
  · intro h
    exact (left_to_right h).map_element (fun e tokens => (same e tokens).mpr)

/-! ## The actual separated-list printer relation -/

variable {G : Grammar} {C : Classification} {L : String → Option (ListForm × String)}

theorem printsList_to_right {item : Sym} {sep : List String} :
    ∀ {es tokens}, PrintsList G C L (.separated item sep true) es tokens →
      Right (Prints G C L item) (fixedToks sep) es tokens
  | _, _, .sepOne _ _ _ _ _ h => .one h
  | _, _, .sepCons _ _ _ _ _ _ h rest => .cons h (printsList_to_right rest)

theorem right_to_printsList {item : Sym} {sep : List String} {es tokens}
    (h : Right (Prints G C L item) (fixedToks sep) es tokens) :
    PrintsList G C L (.separated item sep true) es tokens := by
  induction h with
  | one h => exact .sepOne item sep true _ _ h
  | cons h rest ih => exact .sepCons item sep _ _ _ _ h ih

theorem printsList_to_left {item : Sym} {sep : List String} :
    ∀ {es tokens}, PrintsList G C L (.separated item sep false) es tokens →
      Left (Prints G C L item) (fixedToks sep) es tokens
  | _, _, .sepOne _ _ _ _ _ h => .one h
  | _, _, .sepSnoc _ _ _ _ _ _ rest h => .snoc (printsList_to_left rest) h
termination_by es _ _ => es.length
decreasing_by simp_wf

theorem left_to_printsList {item : Sym} {sep : List String} {es tokens}
    (h : Left (Prints G C L item) (fixedToks sep) es tokens) :
    PrintsList G C L (.separated item sep false) es tokens := by
  induction h with
  | one h => exact .sepOne item sep false _ _ h
  | snoc rest h ih => exact .sepSnoc item sep _ _ _ _ ih h

theorem printsList_orientation_equivalence (item : Sym) (sep : List String)
    (es : List CanonicalTerm) (tokens : List Tok) :
    PrintsList G C L (.separated item sep true) es tokens ↔
      PrintsList G C L (.separated item sep false) es tokens := by
  constructor
  · intro h
    exact left_to_printsList (right_to_left (printsList_to_right h))
  · intro h
    exact right_to_printsList (left_to_right (printsList_to_left h))

theorem printsList_refactoring
    {G' : Grammar} {C' : Classification} {L' : String → Option (ListForm × String)}
    (item : Sym) (sep : List String)
    (sameElements : ∀ e tokens, Prints G C L item e tokens ↔ Prints G' C' L' item e tokens)
    (es : List CanonicalTerm) (tokens : List Tok) :
    PrintsList G C L (.separated item sep true) es tokens ↔
      PrintsList G' C' L' (.separated item sep false) es tokens := by
  constructor
  · intro h
    exact left_to_printsList
      ((right_to_left (printsList_to_right h)).map_element (fun e ts => (sameElements e ts).mp))
  · intro h
    exact right_to_printsList
      ((left_to_right (printsList_to_left h)).map_element (fun e ts => (sameElements e ts).mpr))

/-! ## Token language and canonical projection across classified grammars -/

theorem projected_derivation_iff_printsList (wellFormed : WellFormed G C L)
    {root key : String} {item : Sym} {sep : List String} {right : Bool}
    (form : L root = some (.separated item sep right, key))
    (es : List CanonicalTerm) (tokens : List Tok) :
    (∃ tree, Derives G root tokens tree ∧ canon G C tree = some (.node key [.seq es])) ↔
      PrintsList G C L (.separated item sep right) es tokens := by
  constructor
  · rintro ⟨tree, derived, projected⟩
    obtain ⟨value, k, finished, shape⟩ := finishes wellFormed derived
    simp only [Finished, form] at shape
    obtain ⟨rfl, elems, rfl⟩ := shape
    simp only [canon, finished, Option.map_some, named, Option.some.injEq,
      CanonicalTerm.node.injEq, List.cons.injEq, CanonicalTerm.seq.injEq, and_true, true_and] at projected
    subst elems
    exact (prints_fact wellFormed derived).2 _ _ _ form finished
  · intro printed
    obtain ⟨production, member, lhs, rhs, spec⟩ :=
      list_production wellFormed form (rhs := [item]) (by cases right <;> simp [ListForm.rhss])
    have kind : C.kind production = .list key none := spec.2.2.1
    have form' : L production.lhs = some (.separated item sep right, key) := by rw [lhs]; exact form
    have printedAt : Prints G C L (.rule root) (.node key [.seq es]) tokens := by
      rw [← lhs]
      exact .rule production member _ _ (.list production key none kind _ form' es tokens printed)
    exact derives_of_prints wellFormed printedAt

theorem projected_derivation_refactoring
    {G' : Grammar} {C' : Classification} {L' : String → Option (ListForm × String)}
    (wellFormed : WellFormed G C L) (wellFormed' : WellFormed G' C' L')
    {root root' key : String} (item : Sym) (sep : List String)
    (form : L root = some (.separated item sep true, key))
    (form' : L' root' = some (.separated item sep false, key))
    (sameElements : ∀ e tokens, Prints G C L item e tokens ↔ Prints G' C' L' item e tokens)
    (es : List CanonicalTerm) (tokens : List Tok) :
    (∃ tree, Derives G root tokens tree ∧ canon G C tree = some (.node key [.seq es])) ↔
      (∃ tree, Derives G' root' tokens tree ∧ canon G' C' tree = some (.node key [.seq es])) := by
  rw [projected_derivation_iff_printsList wellFormed form,
    projected_derivation_iff_printsList wellFormed' form']
  exact printsList_refactoring item sep sameElements es tokens

theorem language_refactoring
    {G' : Grammar} {C' : Classification} {L' : String → Option (ListForm × String)}
    (wellFormed : WellFormed G C L) (wellFormed' : WellFormed G' C' L')
    {root root' key : String} (item : Sym) (sep : List String)
    (form : L root = some (.separated item sep true, key))
    (form' : L' root' = some (.separated item sep false, key))
    (sameElements : ∀ e tokens, Prints G C L item e tokens ↔ Prints G' C' L' item e tokens)
    (tokens : List Tok) :
    (∃ tree, Derives G root tokens tree) ↔ (∃ tree, Derives G' root' tokens tree) := by
  have listValue : ∀ {H : Grammar} {D : Classification} {K : String → Option (ListForm × String)}
      {name : String} {direction : Bool}, WellFormed H D K →
      K name = some (.separated item sep direction, key) →
      ∀ {tree}, Derives H name tokens tree →
        ∃ es, canon H D tree = some (.node key [.seq es]) := by
    intro H D K name direction wf listForm tree derived
    obtain ⟨value, k, finished, shape⟩ := finishes wf derived
    simp only [Finished, listForm] at shape
    obtain ⟨rfl, es, rfl⟩ := shape
    exact ⟨es, by simp only [canon, finished, Option.map_some, named]⟩
  constructor
  · rintro ⟨tree, derived⟩
    obtain ⟨es, projected⟩ := listValue wellFormed form derived
    obtain ⟨tree', derived', _⟩ :=
      (projected_derivation_refactoring wellFormed wellFormed' item sep form form' sameElements es tokens).mp
        ⟨tree, derived, projected⟩
    exact ⟨tree', derived'⟩
  · rintro ⟨tree, derived⟩
    obtain ⟨es, projected⟩ := listValue wellFormed' form' derived
    obtain ⟨tree', derived', _⟩ :=
      (projected_derivation_refactoring wellFormed wellFormed' item sep form form' sameElements es tokens).mpr
        ⟨tree, derived, projected⟩
    exact ⟨tree', derived'⟩

/-! ## Nullable separator macros have a different boundary -/

inductive NullableRight (element : Element → List Token → Prop) (separator : List Token) :
    List Element → List Token → Prop where
  | nil : NullableRight element separator [] []
  | one {e : Element} {tokens : List Token} (h : element e tokens) :
      NullableRight element separator [e] tokens
  | cons {e : Element} {es : List Element} {head tail : List Token}
      (he : element e head) (rest : NullableRight element separator es tail) :
      NullableRight element separator (e :: es) (head ++ separator ++ tail)

inductive NullableLeft (element : Element → List Token → Prop) (separator : List Token) :
    List Element → List Token → Prop where
  | nil : NullableLeft element separator [] []
  | one {e : Element} {tokens : List Token} (h : element e tokens) :
      NullableLeft element separator [e] tokens
  | snoc {es : List Element} {e : Element} {lead tail : List Token}
      (rest : NullableLeft element separator es lead) (he : element e tail) :
      NullableLeft element separator (es ++ [e]) (lead ++ separator ++ tail)

theorem NullableRight.first_element_yield {es : List Element} {tokens : List Token}
    (h : NullableRight element separator es tokens) (nonempty : tokens ≠ []) :
    ∃ e head rest, element e head ∧ tokens = head ++ rest := by
  cases h with
  | nil => exact False.elim (nonempty rfl)
  | one h => exact ⟨_, _, [], h, (List.append_nil _).symm⟩
  | cons h rest => exact ⟨_, _, _, h, List.append_assoc _ _ _⟩

theorem NullableLeft.final_element_yield {es : List Element} {tokens : List Token}
    (h : NullableLeft element separator es tokens) (nonempty : tokens ≠ []) :
    ∃ lead e tail, element e tail ∧ tokens = lead ++ tail := by
  cases h with
  | nil => exact False.elim (nonempty rfl)
  | one h => exact ⟨[], _, _, h, rfl⟩
  | snoc rest h => exact ⟨_, _, _, h, rfl⟩

end Mettapedia.GSLT.Parsing.NonemptySeparatorRefactoring
