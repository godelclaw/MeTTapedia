import Mettapedia.GSLT.Parsing.NonemptySeparatorRefactoring

/-!
# Controls for separated-list recursion refactoring

The two grammars below have distinct recursive productions and derivation
trees. Their canonical lists retain the order and the repeated item `x`.
An epsilon alternative is a separate macro: redirecting that recursion can
remove trailing separators and introduce leading separators.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.NonemptySeparatorRefactoring.Controls

open CanonicalGrammar

def singleton : Production := ⟨"H.one", "H", [.token "Item"]⟩

def recursive (right : Bool) (sep : List String) : Production :=
  ⟨"H.more", "H", if right then .token "Item" :: fixedSyms sep ++ [.rule "H"]
    else .rule "H" :: fixedSyms sep ++ [.token "Item"]⟩

def grammar (right : Bool) (sep : List String) : Grammar :=
  ⟨[singleton, recursive right sep],
    fun cls spelling => cls = "Item" ∧ (spelling = "x" ∨ spelling = "y")⟩

def kind (_ : Production) : Kind := .list "items" none

def marks (right : Bool) (p : Production) : List (Nat × Action) :=
  if p.label = "H.more" then [(if right then 1 else 0, .splice)] else []

abbrev classification (right : Bool) : Classification := .ofMarks kind (marks right)

def table (right : Bool) (sep : List String) : List (String × ListForm × String) :=
  [("H", .separated (.token "Item") sep right, "items")]

abbrev lists (right : Bool) (sep : List String) := listRules (table right sep)

theorem comma_wellFormed (right : Bool) :
    WellFormed (grammar right [","]) (classification right) (lists right [","]) := by
  cases right <;> exact wellFormed_of_check (by decide)

theorem empty_separator_wellFormed (right : Bool) :
    WellFormed (grammar right []) (classification right) (lists right []) := by
  cases right <;> exact wellFormed_of_check (by decide)

theorem elements_agree (right right' : Bool) (sep sep' : List String)
    (e : CanonicalTerm) (tokens : List Tok) :
    Prints (grammar right sep) (classification right) (lists right sep) (.token "Item") e tokens ↔
      Prints (grammar right' sep') (classification right') (lists right' sep')
        (.token "Item") e tokens := by
  constructor <;> intro h <;> cases h with
  | token _ spelling valid => exact .token "Item" spelling valid

theorem comma_projection_equivalence (es : List CanonicalTerm) (tokens : List Tok) :
    (∃ tree, Derives (grammar true [","]) "H" tokens tree ∧
      canon (grammar true [","]) (classification true) tree = some (.node "items" [.seq es])) ↔
    (∃ tree, Derives (grammar false [","]) "H" tokens tree ∧
      canon (grammar false [","]) (classification false) tree = some (.node "items" [.seq es])) :=
  projected_derivation_refactoring (comma_wellFormed true) (comma_wellFormed false)
    (.token "Item") [","] rfl rfl (elements_agree true false [","] [","]) es tokens

theorem comma_language_equivalence (tokens : List Tok) :
    (∃ tree, Derives (grammar true [","]) "H" tokens tree) ↔
      (∃ tree, Derives (grammar false [","]) "H" tokens tree) :=
  language_refactoring (comma_wellFormed true) (comma_wellFormed false)
    (.token "Item") [","] rfl rfl (elements_agree true false [","] [","]) tokens

theorem empty_separator_projection_equivalence (es : List CanonicalTerm) (tokens : List Tok) :
    (∃ tree, Derives (grammar true []) "H" tokens tree ∧
      canon (grammar true []) (classification true) tree = some (.node "items" [.seq es])) ↔
    (∃ tree, Derives (grammar false []) "H" tokens tree ∧
      canon (grammar false []) (classification false) tree = some (.node "items" [.seq es])) :=
  projected_derivation_refactoring (empty_separator_wellFormed true) (empty_separator_wellFormed false)
    (.token "Item") [] rfl rfl (elements_agree true false [] []) es tokens

def x : CanonicalTerm := .node "Item" [.text "x"]
def y : CanonicalTerm := .node "Item" [.text "y"]

def repeatedTokens : List Tok :=
  [.lexeme "Item" "x", .fixed ",", .lexeme "Item" "x", .fixed ",", .lexeme "Item" "y"]

def repeatedCanonical : CanonicalTerm := .node "items" [.seq [x, x, y]]

def rightTree : Tree :=
  .node "H.more" [.leaf "Item" "x",
    .node "H.more" [.leaf "Item" "x", .node "H.one" [.leaf "Item" "y"]]]

def leftTree : Tree :=
  .node "H.more" [.node "H.more" [.node "H.one" [.leaf "Item" "x"], .leaf "Item" "x"],
    .leaf "Item" "y"]

theorem spines_are_distinct : rightTree ≠ leftTree := by
  intro h
  cases h

theorem singleton_derivation (right : Bool) {spelling : String}
    (valid : spelling = "x" ∨ spelling = "y") :
    Derives (grammar right [","]) "H" [.lexeme "Item" spelling]
      (.node "H.one" [.leaf "Item" spelling]) := by
  exact Derives.node (G := grammar right [","]) singleton (by simp [grammar]) _ _
    (DerivesItems.token (G := grammar right [","]) "Item" spelling ⟨rfl, valid⟩ [] [] [] .nil)

theorem right_cons {tokens : List Tok} {tree : Tree} {spelling : String}
    (valid : spelling = "x" ∨ spelling = "y")
    (derived : Derives (grammar true [","]) "H" tokens tree) :
    Derives (grammar true [","]) "H" (.lexeme "Item" spelling :: .fixed "," :: tokens)
      (.node "H.more" [.leaf "Item" spelling, tree]) := by
  have tailItems : DerivesItems (grammar true [","]) [.rule "H"] tokens [tree] := by
    simpa only [List.append_nil] using DerivesItems.rule "H" tokens tree derived [] [] [] .nil
  exact Derives.node (G := grammar true [","]) (recursive true [","]) (by simp [grammar]) _ _
    (DerivesItems.token (G := grammar true [","]) "Item" spelling ⟨rfl, valid⟩ _ _ _
      (.fixed "," _ _ _ tailItems))

theorem left_snoc {tokens : List Tok} {tree : Tree} {spelling : String}
    (valid : spelling = "x" ∨ spelling = "y")
    (derived : Derives (grammar false [","]) "H" tokens tree) :
    Derives (grammar false [","]) "H" (tokens ++ [.fixed ",", .lexeme "Item" spelling])
      (.node "H.more" [tree, .leaf "Item" spelling]) := by
  exact Derives.node (G := grammar false [","]) (recursive false [","]) (by simp [grammar]) _ _
    (.rule "H" tokens tree derived _ _ _
      (.fixed "," _ _ _ (DerivesItems.token (G := grammar false [","])
        "Item" spelling ⟨rfl, valid⟩ [] [] [] .nil)))

theorem right_repeated_derivation : Derives (grammar true [","]) "H" repeatedTokens rightTree :=
  right_cons (Or.inl rfl) (right_cons (Or.inl rfl) (singleton_derivation true (Or.inr rfl)))

theorem left_repeated_derivation : Derives (grammar false [","]) "H" repeatedTokens leftTree :=
  left_snoc (Or.inr rfl) (left_snoc (Or.inl rfl) (singleton_derivation false (Or.inl rfl)))

theorem right_repeated_projection :
    canon (grammar true [","]) (classification true) rightTree = some repeatedCanonical := by
  rfl

theorem left_repeated_projection :
    canon (grammar false [","]) (classification false) leftTree = some repeatedCanonical := by
  rfl

theorem repeated_projection_agrees :
    canon (grammar true [","]) (classification true) rightTree =
      canon (grammar false [","]) (classification false) leftTree := by
  rw [right_repeated_projection, left_repeated_projection]

theorem occurrence_order_is_preserved :
    canon (grammar true [","]) (classification true) rightTree ≠
      some (.node "items" [.seq [y, x, x]]) := by
  rw [right_repeated_projection]
  simp [repeatedCanonical, x, y]

theorem repeated_occurrence_is_not_collapsed :
    canon (grammar true [","]) (classification true) rightTree ≠
      some (.node "items" [.seq [x, y]]) := by
  rw [right_repeated_projection]
  simp [repeatedCanonical, x, y]

theorem source_accepts_no_empty_list :
    ¬ ∃ tree, Derives (grammar true [","]) "H" [] tree ∧
      canon (grammar true [","]) (classification true) tree = some (.node "items" [.seq []]) := by
  intro h
  have printed := (projected_derivation_iff_printsList (comma_wellFormed true) rfl [] []).mp h
  exact (printsList_to_right printed).nonempty rfl

theorem target_accepts_no_empty_list :
    ¬ ∃ tree, Derives (grammar false [","]) "H" [] tree ∧
      canon (grammar false [","]) (classification false) tree = some (.node "items" [.seq []]) := by
  intro h
  have printed := (projected_derivation_iff_printsList (comma_wellFormed false) rfl [] []).mp h
  exact (printsList_to_left printed).nonempty rfl

/-! ## Element chunks, empty yields and separator chunks -/

inductive Chunk : String → List Nat → Prop where
  | empty : Chunk "empty" []
  | pair : Chunk "pair" [1, 2]

theorem nullable_elements_with_empty_separator_right :
    Right Chunk [] ["empty", "pair", "empty", "pair"] [1, 2, 1, 2] :=
  .cons Chunk.empty (.cons Chunk.pair (.cons Chunk.empty (.one Chunk.pair)))

theorem nullable_elements_with_empty_separator_left :
    Left Chunk [] ["empty", "pair", "empty", "pair"] [1, 2, 1, 2] :=
  right_to_left nullable_elements_with_empty_separator_right

theorem multi_token_separator_and_elements_right :
    Right Chunk [9, 8] ["pair", "pair"] [1, 2, 9, 8, 1, 2] :=
  .cons Chunk.pair (.one Chunk.pair)

theorem multi_token_separator_and_elements_left :
    Left Chunk [9, 8] ["pair", "pair"] [1, 2, 9, 8, 1, 2] :=
  right_to_left multi_token_separator_and_elements_right

theorem nonempty_elements_can_yield_no_tokens : Right Chunk [] ["empty", "empty"] [] :=
  .cons Chunk.empty (.one Chunk.empty)

/-! A genuine grammar element can derive epsilon even when the list cannot. -/

def nullableSingleton : Production := ⟨"H.one", "H", [.rule "E"]⟩

def nullableRecursive (right : Bool) : Production :=
  ⟨"H.more", "H", if right then [.rule "E", .rule "H"] else [.rule "H", .rule "E"]⟩

def emptyElement : Production := ⟨"E.empty", "E", []⟩

def nullableElementGrammar (right : Bool) : Grammar :=
  ⟨[nullableSingleton, nullableRecursive right, emptyElement],
    fun cls spelling => cls = "Item" ∧ (spelling = "x" ∨ spelling = "y")⟩

def nullableElementKind (p : Production) : Kind :=
  if p.lhs = "H" then .list "items" none else .constructor p.label

abbrev nullableElementClassification (right : Bool) : Classification :=
  .ofMarks nullableElementKind (marks right)

abbrev nullableElementLists (right : Bool) :=
  listRules [("H", .separated (.rule "E") [] right, "items")]

theorem nullable_element_wellFormed (right : Bool) :
    WellFormed (nullableElementGrammar right) (nullableElementClassification right)
      (nullableElementLists right) := by
  cases right <;> exact wellFormed_of_check (by decide)

theorem empty_element_prints (right : Bool) :
    Prints (nullableElementGrammar right) (nullableElementClassification right)
      (nullableElementLists right) (.rule "E") (.node "E.empty" []) [] := by
  exact .rule emptyElement (by simp [nullableElementGrammar]) _ _
    (.constructor emptyElement "E.empty" rfl [] [] (.nil emptyElement 0))

theorem nonempty_list_of_nullable_elements_derives (right : Bool) :
    ∃ tree, Derives (nullableElementGrammar right) "H" [] tree ∧
      canon (nullableElementGrammar right) (nullableElementClassification right) tree =
        some (.node "items" [.seq [.node "E.empty" [], .node "E.empty" []]]) := by
  apply (projected_derivation_iff_printsList (nullable_element_wellFormed right) rfl _ []).mpr
  cases right with
  | false =>
    exact .sepSnoc (.rule "E") [] [.node "E.empty" []] (.node "E.empty" []) [] []
      (.sepOne (.rule "E") [] false _ [] (empty_element_prints false)) (empty_element_prints false)
  | true =>
    exact .sepCons (.rule "E") [] (.node "E.empty" []) [.node "E.empty" []] [] []
      (empty_element_prints true) (.sepOne (.rule "E") [] true _ [] (empty_element_prints true))

/-! ## Redirecting a nullable separator macro changes its language -/

inductive OneToken : String → List Tok → Prop where
  | item (spelling : String) : OneToken spelling [.lexeme "Item" spelling]

theorem nullable_right_accepts_trailing_separator :
    NullableRight OneToken [.fixed ","] ["x"] [.lexeme "Item" "x", .fixed ","] :=
  .cons (OneToken.item "x") .nil

theorem nullable_left_rejects_trailing_separator :
    ¬ ∃ es, NullableLeft OneToken [.fixed ","] es [.lexeme "Item" "x", .fixed ","] := by
  rintro ⟨es, parsed⟩
  obtain ⟨lead, e, tail, element, equality⟩ := parsed.final_element_yield (by simp)
  cases element with
  | item =>
    have last := congrArg List.getLast? equality
    rw [List.getLast?_append_of_ne_nil lead (l₂ := [.lexeme "Item" e]) (by simp)] at last
    simp only [List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at last
    cases last

theorem nullable_left_accepts_leading_separator :
    NullableLeft OneToken [.fixed ","] ["x"] [.fixed ",", .lexeme "Item" "x"] :=
  .snoc .nil (OneToken.item "x")

theorem nullable_right_rejects_leading_separator :
    ¬ ∃ es, NullableRight OneToken [.fixed ","] es [.fixed ",", .lexeme "Item" "x"] := by
  rintro ⟨es, parsed⟩
  obtain ⟨e, head, rest, element, equality⟩ := parsed.first_element_yield (by simp)
  cases element with
  | item =>
    have first := congrArg List.head? equality
    simp at first

theorem nullable_orientations_have_different_languages :
    ¬ (∀ tokens, (∃ es, NullableRight OneToken [.fixed ","] es tokens) ↔
      (∃ es, NullableLeft OneToken [.fixed ","] es tokens)) := by
  intro same
  exact nullable_left_rejects_trailing_separator
    ((same _).mp ⟨["x"], nullable_right_accepts_trailing_separator⟩)

end Mettapedia.GSLT.Parsing.NonemptySeparatorRefactoring.Controls
