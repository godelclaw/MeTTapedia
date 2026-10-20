import Mettapedia.OSLF.MeTTaIL.OrientationSettle
import Mettapedia.OSLF.MeTTaIL.DistributiveLaws

/-!
# The orientation normalizers and the distributive moves

The distributive moves rearrange collections: they permute, flatten, absorb units, collapse wrappers,
remove repeated summands, absorb into chaos and distribute composition over a sum. The orientation
normalizers act at data and at variable occurrences and rebuild every collection element by element, so
they carry a move to a move of the same kind.

This file holds the facts the carrying needs and the first carrying:
- a walk splits along a split argument list (`mapFrameArgs_append`, `mapFrameList_append`);
- a data word holds no collection, so no move happens inside one (`lawStep_not_word`,
  `wrapperStep_not_word`, `step_not_word`), nor inside an occurrence (`LawStep.notOccurrence`);
- `lawStep_mapFrame`: every walk carries a collection law move to one, on a term whose data and
  decorations are words, when a flattening collection's elements have a homogeneous type that is not
  data (`LawsHomogeneous`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax CollectionLaws CanonicalBags

/-! ## Walks along split lists -/

section Split

variable {language : LanguageDef} {decl : OrientationDecl}

/-- **A walk over a split argument list** walks the first part with the leading types and the rest with
the remaining ones. -/
theorem mapFrameArgs_append (f v : Nat → Pattern → Pattern) (depth : Nat) :
    ∀ (types : List TypeExpr) (before rest : List Pattern),
      mapFrameArgs language decl f v depth types (before ++ rest) =
        mapFrameArgs language decl f v depth types before ++
          mapFrameArgs language decl f v depth (types.drop before.length) rest
  | type :: types, argument :: before, rest => by
    rw [List.cons_append, mapFrameArgs, mapFrameArgs, mapFrameArgs_append f v depth types before rest,
      List.length_cons, List.drop_succ_cons, List.cons_append]
  | [], before, rest => by
    cases before <;> cases rest <;> simp [mapFrameArgs]
  | _ :: _, [], rest => by simp [mapFrameArgs]

theorem mapFrameList_append (f v : Nat → Pattern → Pattern) (depth : Nat) (element : TypeExpr) :
    ∀ (before rest : List Pattern),
      mapFrameList language decl f v depth element (before ++ rest) =
        mapFrameList language decl f v depth element before ++ mapFrameList language decl f v depth element rest
  | [], rest => by rw [List.nil_append, mapFrameList, List.nil_append]
  | pattern :: before, rest => by
    rw [List.cons_append, mapFrameList, mapFrameList, mapFrameList_append f v depth element before rest,
      List.cons_append]

theorem mapFrameList_eq_map (f v : Nat → Pattern → Pattern) (depth : Nat) (element : TypeExpr) :
    ∀ (patterns : List Pattern),
      mapFrameList language decl f v depth element patterns =
        patterns.map (mapFrame language decl f v depth element)
  | [] => by rw [mapFrameList, List.map_nil]
  | pattern :: patterns => by rw [mapFrameList, List.map_cons, mapFrameList_eq_map f v depth element patterns]

end Split

/-! ## No move inside a data word -/

section Words

variable {decl : OrientationDecl} {G : Type} [Group G] {constant : String → Option G}

/-- An argument of a data word is a data word. -/
theorem letters_argument {label : String} {before after : List Pattern} {argument : Pattern}
    {found : List (Letter G)} (parsed : letters decl constant (.apply label (before ++ argument :: after)) = some found) :
    ∃ inner, letters decl constant argument = some inner := by
  have member : argument ∈ before ++ argument :: after := List.mem_append_right _ List.mem_cons_self
  generalize before ++ argument :: after = arguments at parsed member
  match arguments, parsed, member with
  | [single], parsed, member =>
    rw [List.mem_singleton] at member
    subst member
    rw [letters] at parsed
    split at parsed
    · obtain ⟨inner, innerParsed, _⟩ := Option.map_eq_some_iff.mp parsed
      exact ⟨inner, innerParsed⟩
    · cases parsed
  | [left, right], parsed, member =>
    rw [letters] at parsed
    split at parsed
    · split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with same | same
        · subst same
          exact ⟨leftLetters, leftParsed⟩
        · subst same
          exact ⟨rightLetters, rightParsed⟩
      · cases parsed
    · cases parsed
  | [], _, member => cases member
  | _ :: _ :: _ :: _, parsed, _ => simp [letters] at parsed

/-- **No collection law moves inside a data word.** -/
theorem lawStep_not_word {laws : List Laws} {word changed : Pattern} (step : LawStep laws word changed) :
    ∀ {found : List (Letter G)}, letters decl constant word = some found → False := by
  induction step with
  | permute => intro _ parsed; simp [letters] at parsed
  | members => intro _ parsed; simp [letters] at parsed
  | flatten => intro _ parsed; simp [letters] at parsed
  | unit => intro _ parsed; simp [letters] at parsed
  | apply _ inner =>
    intro _ parsed
    obtain ⟨_, argumentParsed⟩ := letters_argument parsed
    exact inner argumentParsed
  | lambda => intro _ parsed; simp [letters] at parsed
  | multiLambda => intro _ parsed; simp [letters] at parsed
  | substBody => intro _ parsed; simp [letters] at parsed
  | substReplacement => intro _ parsed; simp [letters] at parsed
  | element => intro _ parsed; simp [letters] at parsed

/-- **No wrapper law moves inside a data word.** -/
theorem wrapperStep_not_word {laws : List Laws} {word changed : Pattern}
    (step : Wrappers.WrapperStep laws word changed) :
    ∀ {found : List (Letter G)}, letters decl constant word = some found → False := by
  induction step with
  | singleton => intro _ parsed; simp [letters] at parsed
  | empty => intro _ parsed; simp [letters] at parsed
  | apply _ inner =>
    intro _ parsed
    obtain ⟨_, argumentParsed⟩ := letters_argument parsed
    exact inner argumentParsed
  | lambda => intro _ parsed; simp [letters] at parsed
  | multiLambda => intro _ parsed; simp [letters] at parsed
  | substBody => intro _ parsed; simp [letters] at parsed
  | substReplacement => intro _ parsed; simp [letters] at parsed
  | element => intro _ parsed; simp [letters] at parsed

/-- **No distributive step moves inside a data word.** -/
theorem step_not_word {distributive : Distributive.Decl} {word changed : Pattern}
    (step : Distributive.Step distributive word changed) :
    ∀ {found : List (Letter G)}, letters decl constant word = some found → False := by
  induction step with
  | repeated => intro _ parsed; simp [letters] at parsed
  | absorbProduct => intro _ parsed; simp [letters] at parsed
  | absorbSum => intro _ parsed; simp [letters] at parsed
  | distribute => intro _ parsed; simp [letters] at parsed
  | apply _ inner =>
    intro _ parsed
    obtain ⟨_, argumentParsed⟩ := letters_argument parsed
    exact inner argumentParsed
  | lambda => intro _ parsed; simp [letters] at parsed
  | multiLambda => intro _ parsed; simp [letters] at parsed
  | substBody => intro _ parsed; simp [letters] at parsed
  | substReplacement => intro _ parsed; simp [letters] at parsed
  | element => intro _ parsed; simp [letters] at parsed

end Words

/-! ## Position predicates at a position of a list -/

section Positions

variable {language : LanguageDef} {decl : OrientationDecl}

theorem frameAllArgs_at {dataOk variableOk : Nat → Pattern → Prop} {depth : Nat} :
    ∀ {types : List TypeExpr} {before after : List Pattern} {argument : Pattern} {type : TypeExpr}
      {types' : List TypeExpr},
      FrameAllArgs language decl dataOk variableOk depth types (before ++ argument :: after) →
        types.drop before.length = type :: types' → FrameAll language decl dataOk variableOk depth type argument
  | _ :: _, [], after, argument, type, types', all, dropped => by
    simp only [List.length_nil, List.drop_zero, List.cons.injEq] at dropped
    obtain ⟨rfl, rfl⟩ := dropped
    rw [List.nil_append, FrameAllArgs] at all
    exact all.1
  | _ :: types, _ :: before, after, argument, type, types', all, dropped => by
    rw [List.cons_append, FrameAllArgs] at all
    simp only [List.length_cons, List.drop_succ_cons] at dropped
    exact frameAllArgs_at all.2 dropped
  | [], _, _, _, _, _, _, dropped => by simp at dropped

theorem frameAllList_at {dataOk variableOk : Nat → Pattern → Prop} {depth : Nat} {element : TypeExpr} :
    ∀ {before after : List Pattern} {item : Pattern},
      FrameAllList language decl dataOk variableOk depth element (before ++ item :: after) →
        FrameAll language decl dataOk variableOk depth element item
  | [], after, item, all => by
    rw [List.nil_append, FrameAllList] at all
    exact all.1
  | _ :: before, after, item, all => by
    rw [List.cons_append, FrameAllList] at all
    exact frameAllList_at all.2

end Positions

/-! ## A walk carries a collection law -/

section CarryLaw

variable {language : LanguageDef} {decl : OrientationDecl}

/-- A collection law move never ends at a bare variable. -/
theorem LawStep.not_bare {laws : List Laws} {a b : Pattern} (step : LawStep laws a b) : isBare b = false := by
  cases step <;> rfl

/-- A collection law move keeps a term that is not an occurrence one. -/
theorem LawStep.decorated?_none {laws : List Laws} {a b : Pattern} (step : LawStep laws a b)
    (structural : decorated? decl a = none) : decorated? decl b = none := by
  cases step with
  | apply inner =>
    rename_i label before after argument changed
    cases found : decorated? decl (.apply label (before ++ changed :: after)) with
    | none => rfl
    | some pair =>
      exfalso
      obtain ⟨coefficient, occurrenceVar⟩ := pair
      obtain ⟨bare, plain, applied⟩ := decorated?_shape found
      cases coefficient with
      | none =>
        have same := plain rfl
        rw [← same] at bare
        simp [isBare] at bare
      | some c =>
        have shape := applied c rfl
        simp only [Pattern.apply.injEq] at shape
        obtain ⟨labelSame, argumentsSame⟩ := shape
        match before, after, argumentsSame with
        | [], [x], argumentsSame =>
          simp only [List.nil_append, List.cons.injEq, and_true] at argumentsSame
          obtain ⟨_, rfl⟩ := argumentsSame
          rw [labelSame, List.nil_append, decorated?_action _ _ bare] at structural
          cases structural
        | [y], [], argumentsSame =>
          simp only [List.singleton_append, List.cons.injEq, and_true] at argumentsSame
          obtain ⟨_, rfl⟩ := argumentsSame
          rw [LawStep.not_bare inner] at bare
          cases bare
        | [], [], argumentsSame => simp at argumentsSame
        | [], _ :: _ :: _, argumentsSame => simp at argumentsSame
        | [_], _ :: _, argumentsSame => simp at argumentsSame
        | _ :: _ :: _, _, argumentsSame => simp at argumentsSame
  | _ => simp [decorated?]

/-- No collection law moves a bare variable. -/
theorem LawStep.not_from_bare {laws : List Laws} {a b : Pattern} (step : LawStep laws a b) : isBare a = false := by
  cases step <;> rfl

variable {G : Type} [Group G] {reading : DataReading decl G}

/-- A word-formed term moved by a collection law sits at no data position. -/
theorem LawStep.notData {laws : List Laws} {a b : Pattern} (step : LawStep laws a b) {depth : Nat}
    {type : TypeExpr} (words : WordsAt (language := language) reading depth type a) :
    type ≠ .base decl.dataSort := by
  intro data
  unfold WordsAt at words
  rw [FrameAll.eq_def, if_pos data] at words
  obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp words
  exact lawStep_not_word step parsed

/-- A word-formed term moved by a collection law is no occurrence: its coefficient is a word and its
variable bare. -/
theorem LawStep.notOccurrence {laws : List Laws} {a b : Pattern} (step : LawStep laws a b) {depth : Nat}
    {type : TypeExpr} (words : WordsAt (language := language) reading depth type a)
    (notData : type ≠ .base decl.dataSort) :
    ¬((decorated? decl a).isSome ∧ actionType language decl = some type) := by
  rintro ⟨occurs, sort⟩
  unfold WordsAt at words
  rw [FrameAll.eq_def, if_neg notData, if_pos ⟨occurs, sort⟩] at words
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  cases coefficient with
  | none =>
    have same := plain rfl
    subst same
    rw [LawStep.not_from_bare step] at bare
    cases bare
  | some c =>
    have same := applied c rfl
    subst same
    obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp (words c occurrenceVar found)
    generalize stepped : Pattern.apply decl.action [c, occurrenceVar] = moved at step
    cases step with
    | apply inner =>
      rename_i label before after argument changed
      simp only [Pattern.apply.injEq] at stepped
      obtain ⟨_, argumentsSame⟩ := stepped
      match before, after, argumentsSame with
      | [], [x], argumentsSame =>
        simp only [List.nil_append, List.cons.injEq, and_true] at argumentsSame
        obtain ⟨rfl, _⟩ := argumentsSame
        exact lawStep_not_word inner cParsed
      | [y], [], argumentsSame =>
        simp only [List.singleton_append, List.cons.injEq, and_true] at argumentsSame
        obtain ⟨_, rfl⟩ := argumentsSame
        rw [LawStep.not_from_bare inner] at bare
        cases bare
      | [], [], argumentsSame => simp at argumentsSame
      | [], _ :: _ :: _, argumentsSame => simp at argumentsSame
      | [_], _ :: _, argumentsSame => simp at argumentsSame
      | _ :: _ :: _, _, argumentsSame => simp at argumentsSame
    | _ => simp at stepped

/-- The structural branch of a moved term is the structural branch of its result. -/
theorem LawStep.structural {laws : List Laws} {a b : Pattern} (step : LawStep laws a b) {type : TypeExpr}
    (structural : ¬((decorated? decl a).isSome ∧ actionType language decl = some type)) :
    ¬((decorated? decl b).isSome ∧ actionType language decl = some type) := by
  rintro ⟨occurs, sort⟩
  have none : decorated? decl a = none := by
    cases found : decorated? decl a with
    | none => rfl
    | some _ => exact absurd ⟨by rw [found]; rfl, sort⟩ structural
  rw [LawStep.decorated?_none step none] at occurs
  cases occurs

/-- What carrying the collection laws asks of the language: a collection of a flattening kind holds
elements of its own type, none of them data. -/
def LawsHomogeneous (language : LanguageDef) (decl : OrientationDecl) (laws : List Laws) : Prop :=
  ∀ law kind, lawFor laws kind = some law → ∀ type element, elementType language type kind = some element →
    elementType language element kind = some element ∧ element ≠ .base decl.dataSort

/-- A walk rebuilds a constant. -/
theorem mapFrame_constant {f v : Nat → Pattern → Pattern} {depth : Nat} {type : TypeExpr}
    (notData : type ≠ .base decl.dataSort) (label : String) :
    mapFrame language decl f v depth type (.apply label []) = .apply label [] := by
  have structural : ¬((decorated? decl (.apply label [])).isSome ∧ actionType language decl = some type) := by
    simp [decorated?]
  cases found : paramTypes language label with
  | none => exact mapFrame_apply_unknown notData structural found
  | some types =>
    rw [mapFrame_apply_structural notData structural found]
    cases types <;> simp [mapFrameArgs]

/-- **A walk carries a collection law move to one**, on a term whose data and decorations are words: the
move happens at no data position and inside no occurrence, so the walk rebuilds it. -/
theorem lawStep_mapFrame {f v : Nat → Pattern → Pattern} {laws : List Laws}
    (homogeneous : LawsHomogeneous language decl laws) {a b : Pattern} (step : LawStep laws a b) :
    ∀ (depth : Nat) (type : TypeExpr), WordsAt (language := language) reading depth type a →
      LawStep laws (mapFrame language decl f v depth type a) (mapFrame language decl f v depth type b) := by
  induction step with
  | @permute kind elements permuted rest unordered permutation =>
    intro depth type words
    have data := LawStep.notData (laws := laws) (.permute unordered permutation) words
    cases found : elementType language type kind with
    | none =>
      rw [mapFrame_collection_unknown data found, mapFrame_collection_unknown data found]
      exact .permute unordered permutation
    | some element =>
      rw [mapFrame_collection data found, mapFrame_collection data found, mapFrameList_eq_map, mapFrameList_eq_map]
      exact .permute unordered (permutation.map _)
  | @members elements others rest same =>
    intro depth type words
    have data := LawStep.notData (laws := laws) (.members same) words
    cases found : elementType language type .hashSet with
    | none =>
      rw [mapFrame_collection_unknown data found, mapFrame_collection_unknown data found]
      exact .members same
    | some element =>
      rw [mapFrame_collection data found, mapFrame_collection data found, mapFrameList_eq_map, mapFrameList_eq_map]
      refine .members fun item => ?_
      simp only [List.mem_map]
      constructor
      · rintro ⟨x, member, rfl⟩
        exact ⟨x, (same x).mp member, rfl⟩
      · rintro ⟨x, member, rfl⟩
        exact ⟨x, (same x).mpr member, rfl⟩
  | @flatten kind law before inner after rest found =>
    intro depth type words
    have data := LawStep.notData (.flatten found) words
    cases elementFound : elementType language type kind with
    | none =>
      rw [mapFrame_collection_unknown data elementFound, mapFrame_collection_unknown data elementFound]
      exact .flatten found
    | some element =>
      obtain ⟨innerFound, elementNotData⟩ := homogeneous law kind found type element elementFound
      rw [mapFrame_collection data elementFound, mapFrame_collection data elementFound, mapFrameList_eq_map,
        mapFrameList_eq_map, List.map_append, List.map_cons, mapFrame_collection elementNotData innerFound,
        mapFrameList_eq_map, List.map_append, List.map_append]
      exact .flatten found
  | @unit kind law label before after rest found unitIs =>
    intro depth type words
    have data := LawStep.notData (.unit found unitIs) words
    cases elementFound : elementType language type kind with
    | none =>
      rw [mapFrame_collection_unknown data elementFound, mapFrame_collection_unknown data elementFound]
      exact .unit found unitIs
    | some element =>
      obtain ⟨_, elementNotData⟩ := homogeneous law kind found type element elementFound
      rw [mapFrame_collection data elementFound, mapFrame_collection data elementFound, mapFrameList_eq_map,
        mapFrameList_eq_map, List.map_append, List.map_cons, mapFrame_constant elementNotData, List.map_append]
      exact .unit found unitIs
  | @apply label before after argument changed inner inductive_ =>
    intro depth type words
    have data := LawStep.notData (.apply inner) words
    have structural := LawStep.notOccurrence (.apply inner) words data
    have structuralAfter := LawStep.structural (.apply inner) structural
    unfold WordsAt at words
    rw [FrameAll.eq_def, if_neg data, if_neg structural] at words
    cases found : paramTypes language label with
    | none =>
      rw [mapFrame_apply_unknown data structural found, mapFrame_apply_unknown data structuralAfter found]
      exact .apply inner
    | some types =>
      dsimp only at words
      rw [found] at words
      dsimp only at words
      rw [mapFrame_apply_structural data structural found, mapFrame_apply_structural data structuralAfter found,
        mapFrameArgs_append, mapFrameArgs_append]
      cases dropped : types.drop before.length with
      | nil =>
        simp only [mapFrameArgs]
        exact .apply inner
      | cons argumentType rest =>
        rw [mapFrameArgs, mapFrameArgs]
        exact .apply (inductive_ depth argumentType (frameAllArgs_at words dropped))
  | @lambda binder body changed inner inductive_ =>
    intro depth type words
    have data := LawStep.notData (.lambda inner) words
    cases type with
    | arrow domain codomain =>
      unfold WordsAt at words
      rw [FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])] at words
      rw [mapFrame_lambda data, mapFrame_lambda data]
      exact .lambda (inductive_ (depth + 1) codomain words)
    | base sort =>
      have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
      rw [mapFrame_lambda_other data notArrow, mapFrame_lambda_other data notArrow]
      exact .lambda inner
    | collection kind element =>
      have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
      rw [mapFrame_lambda_other data notArrow, mapFrame_lambda_other data notArrow]
      exact .lambda inner
    | multiBinder innerType =>
      have notArrow : ∀ domain codomain, TypeExpr.multiBinder innerType ≠ .arrow domain codomain := by simp
      rw [mapFrame_lambda_other data notArrow, mapFrame_lambda_other data notArrow]
      exact .lambda inner
  | @multiLambda arity binders body changed inner inductive_ =>
    intro depth type words
    have data := LawStep.notData (.multiLambda inner) words
    cases type with
    | arrow domain codomain =>
      unfold WordsAt at words
      rw [FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])] at words
      rw [mapFrame_multiLambda data, mapFrame_multiLambda data]
      exact .multiLambda (inductive_ (depth + arity) codomain words)
    | base sort =>
      have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
      rw [mapFrame_multiLambda_other data notArrow, mapFrame_multiLambda_other data notArrow]
      exact .multiLambda inner
    | collection kind element =>
      have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
      rw [mapFrame_multiLambda_other data notArrow, mapFrame_multiLambda_other data notArrow]
      exact .multiLambda inner
    | multiBinder innerType =>
      have notArrow : ∀ domain codomain, TypeExpr.multiBinder innerType ≠ .arrow domain codomain := by simp
      rw [mapFrame_multiLambda_other data notArrow, mapFrame_multiLambda_other data notArrow]
      exact .multiLambda inner
  | @substBody body changed replacement inner _ =>
    intro depth type words
    have data := LawStep.notData (.substBody (replacement := replacement) inner) words
    have leaf : ∀ {x y : Pattern}, mapFrame language decl f v depth type (.subst x y) = .subst x y := fun {x y} =>
      mapFrame_leaf data (by simp [decorated?]) (.inr (.inr ⟨x, y, rfl⟩))
    rw [leaf, leaf]
    exact .substBody inner
  | @substReplacement body replacement changed inner _ =>
    intro depth type words
    have data := LawStep.notData (.substReplacement (body := body) inner) words
    have leaf : ∀ {x y : Pattern}, mapFrame language decl f v depth type (.subst x y) = .subst x y := fun {x y} =>
      mapFrame_leaf data (by simp [decorated?]) (.inr (.inr ⟨x, y, rfl⟩))
    rw [leaf, leaf]
    exact .substReplacement inner
  | @element kind before after element changed rest inner inductive_ =>
    intro depth type words
    have data := LawStep.notData (.element (kind := kind) (before := before) (after := after) (rest := rest) inner)
      words
    unfold WordsAt at words
    rw [FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])] at words
    cases elementFound : elementType language type kind with
    | none =>
      rw [mapFrame_collection_unknown data elementFound, mapFrame_collection_unknown data elementFound]
      exact .element inner
    | some elementType' =>
      dsimp only at words
      rw [elementFound] at words
      dsimp only at words
      rw [mapFrame_collection data elementFound, mapFrame_collection data elementFound, mapFrameList_append,
        mapFrameList_append, mapFrameList, mapFrameList]
      exact .element (inductive_ depth elementType' (frameAllList_at words))

end CarryLaw

end Mettapedia.OSLF.MeTTaIL.Orientation
