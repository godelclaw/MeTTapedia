import Mettapedia.OSLF.MeTTaIL.OrientationAuthored

/-!
# Settling is idempotent

`settle` evaluates the action nodes of a term from the inside out. On a term whose action nodes all sit
where a process of the action's body sort does, with a coefficient and a body (`actionsAtBody`), its
result has no action node but decorations (`actionFree_settle`): an action node becomes a decoration or the
frame-normal action of its coefficient on the settled body, and a walk that keeps occurrences keeps a term
action-free (`actionFree_mapFrame`). Settling keeps data and decorations words (`wordsAt_settle`; the action
of any word, closed or not, keeps a word a word: `letters_actData_some`), and it fixes an action-free term
whose data and decorations are words, so it is idempotent (`settle_settle`), when the action's parameters
are a datum and a process (`dataSorted`) and multiplication is not the action.

Settling sees through the frame normal form (`normalWalk_settle_normal`): normalizing data and decorations
before settling changes nothing after normalizing again, when every action coefficient is a closed word
(`closedActions`). At an action node on an occurrence both sides compose the coefficient with the
decoration, and the values agree in `G ∗ F(V)`; on any other body the action depends on the coefficient's
element alone (`frameAct_congr`) and respects the normal form of the body (`frameAct_normal`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax

/-! ## Where action nodes may sit -/

section Placement

variable (language : LanguageDef) (decl : OrientationDecl)

mutual
  /-- **Every action node sits at the action's body sort, with a coefficient and a body.** -/
  def actionsAtBody (type : TypeExpr) (pattern : Pattern) : Bool :=
    if type = .base decl.dataSort then true
    else if (decorated? decl pattern).isSome ∧ actionType language decl = some type then true
    else
      match pattern with
      | .apply label arguments =>
          (label != decl.action || (decide (actionType language decl = some type) && arguments.length == 2)) &&
            match paramTypes language label with
            | some types => actionsAtBodyArgs types arguments
            | none => true
      | .lambda _ body =>
          match type with
          | .arrow _ codomain => actionsAtBody codomain body
          | _ => true
      | .multiLambda _ _ body =>
          match type with
          | .arrow _ codomain => actionsAtBody codomain body
          | _ => true
      | .collection kind elements _ =>
          match elementType language type kind with
          | some element => actionsAtBodyList element elements
          | none => true
      | _ => true
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def actionsAtBodyArgs : List TypeExpr → List Pattern → Bool
    | type :: types, argument :: arguments => actionsAtBody type argument && actionsAtBodyArgs types arguments
    | [], _ => true
    | _ :: _, [] => true
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def actionsAtBodyList (element : TypeExpr) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => actionsAtBody element pattern && actionsAtBodyList element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end Placement

/-! ## Walks keep a term action-free -/

section KeepFree

variable {language : LanguageDef} {decl : OrientationDecl}

/-- The data and variable branches of an action-freeness step; leaves the structural branch with `free`
unfolded and `structural` for the walk's result. -/
syntax "keep_free_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| keep_free_cases $pattern) => `(tactic| (
      by_cases data : type = .base decl.dataSort
      · rw [actionFree.eq_def, if_pos data]
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [mapFrame_variable data occurs, actionFree.eq_def, if_neg data,
          if_pos ⟨keeps.occurs _ _ occurs.1, occurs.2⟩]
      have structural := decorated?_mapFrame_structural (language := language) (f := f) (v := v)
        (depth := depth) keeps.notBare bodyNotData data occurs
      rw [actionFree.eq_def, if_neg data, if_neg occurs] at free))

mutual
  /-- **A walk that keeps occurrences keeps a term action-free.** -/
  theorem actionFree_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), actionFree language decl type pattern = true →
        actionFree language decl type (mapFrame language decl f v depth type pattern) = true
    | depth, type, .apply label arguments, free => by
      keep_free_cases (.apply label arguments)
      dsimp only at free
      simp only [Bool.and_eq_true] at free
      cases found : paramTypes language label with
      | none =>
        rw [mapFrame_apply_unknown data occurs found, actionFree.eq_def, if_neg data, if_neg occurs]
        dsimp only
        rw [found]
        simp only [Bool.and_true]
        exact free.1
      | some types =>
        rw [found] at free
        rw [mapFrame_apply_structural data occurs found] at structural ⊢
        rw [actionFree.eq_def, if_neg data, if_neg structural]
        dsimp only
        rw [found]
        dsimp only
        simp only [Bool.and_eq_true]
        exact ⟨free.1, actionFreeArgs_mapFrame keeps bodyNotData depth types arguments free.2⟩
    | depth, type, .lambda binder body, free => by
      keep_free_cases (.lambda binder body)
      cases type with
      | arrow domain codomain =>
        dsimp only at free
        rw [mapFrame_lambda data, actionFree.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact actionFree_mapFrame keeps bodyNotData (depth + 1) codomain body free
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, actionFree.eq_def, if_neg data, if_neg occurs]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, actionFree.eq_def, if_neg data, if_neg occurs]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, actionFree.eq_def, if_neg data, if_neg occurs]
    | depth, type, .multiLambda arity binders body, free => by
      keep_free_cases (.multiLambda arity binders body)
      cases type with
      | arrow domain codomain =>
        dsimp only at free
        rw [mapFrame_multiLambda data, actionFree.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact actionFree_mapFrame keeps bodyNotData (depth + arity) codomain body free
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, actionFree.eq_def, if_neg data, if_neg occurs]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, actionFree.eq_def, if_neg data, if_neg occurs]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, actionFree.eq_def, if_neg data, if_neg occurs]
    | depth, type, .collection kind elements rest, free => by
      keep_free_cases (.collection kind elements rest)
      dsimp only at free
      cases found : elementType language type kind with
      | none =>
        rw [mapFrame_collection_unknown data found, actionFree.eq_def, if_neg data, if_neg occurs]
        dsimp only
        rw [found]
      | some element =>
        rw [found] at free
        dsimp only at free
        rw [mapFrame_collection data found, actionFree.eq_def, if_neg data, if_neg (by simp [decorated?])]
        dsimp only
        rw [found]
        exact actionFreeList_mapFrame keeps bodyNotData depth element elements free
    | depth, type, .bvar index, free => by
      keep_free_cases (.bvar index)
      rw [mapFrame_leaf data occurs (.inl ⟨index, rfl⟩), actionFree.eq_def, if_neg data, if_neg occurs]
    | depth, type, .fvar name, free => by
      keep_free_cases (.fvar name)
      rw [mapFrame_leaf data occurs (.inr (.inl ⟨name, rfl⟩)), actionFree.eq_def, if_neg data, if_neg occurs]
    | depth, type, .subst body replacement, free => by
      keep_free_cases (.subst body replacement)
      rw [mapFrame_leaf data occurs (.inr (.inr ⟨body, replacement, rfl⟩)), actionFree.eq_def, if_neg data,
        if_neg occurs]
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionFreeArgs_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        actionFreeArgs language decl types arguments = true →
          actionFreeArgs language decl types (mapFrameArgs language decl f v depth types arguments) = true
    | depth, type :: types, argument :: arguments, free => by
      rw [actionFreeArgs, Bool.and_eq_true] at free
      rw [mapFrameArgs, actionFreeArgs, Bool.and_eq_true]
      exact ⟨actionFree_mapFrame keeps bodyNotData depth type argument free.1,
        actionFreeArgs_mapFrame keeps bodyNotData depth types arguments free.2⟩
    | depth, [], arguments, _ => by simp [mapFrameArgs, actionFreeArgs]
    | depth, _ :: _, [], _ => by simp [mapFrameArgs, actionFreeArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionFreeList_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        actionFreeList language decl element patterns = true →
          actionFreeList language decl element (mapFrameList language decl f v depth element patterns) = true
    | depth, element, [], _ => by rw [mapFrameList, actionFreeList]
    | depth, element, pattern :: patterns, free => by
      rw [actionFreeList, Bool.and_eq_true] at free
      rw [mapFrameList, actionFreeList, Bool.and_eq_true]
      exact ⟨actionFree_mapFrame keeps bodyNotData depth element pattern free.1,
        actionFreeList_mapFrame keeps bodyNotData depth element patterns free.2⟩
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end KeepFree

/-! ## Settling produces action-free terms -/

section SettleFree

variable {language : LanguageDef} {decl : OrientationDecl}

/-- Settling an action node: a decoration on a variable keeps it, two decorations compose, and on any
other body the node is the frame-normal action of the settled coefficient. -/
theorem settle_actionNode {dataType bodyType : TypeExpr}
    (actionTypes : paramTypes language decl.action = some [dataType, bodyType]) (type : TypeExpr)
    (coefficient body : Pattern) :
    settle language decl type (.apply decl.action [coefficient, body]) =
      match decorated? decl (settle language decl bodyType body) with
      | some (none, occurrenceVar) => .apply decl.action [settle language decl dataType coefficient, occurrenceVar]
      | some (some inner, occurrenceVar) =>
          .apply decl.action [mulWord decl (settle language decl dataType coefficient) inner, occurrenceVar]
      | none => frameAct language decl (settle language decl dataType coefficient) bodyType
          (settle language decl bodyType body) := by
  rw [settle.eq_def]
  dsimp only
  rw [actionTypes]
  dsimp only
  rw [if_pos rfl]
  simp only [settleArgs]
  rfl

theorem decorated?_apply_other {label : String} {arguments : List Pattern} (other : label ≠ decl.action) :
    decorated? decl (.apply label arguments) = none := by
  match arguments with
  | [] => simp [decorated?]
  | [_] => simp [decorated?]
  | [_, .bvar _] => simp [decorated?, other]
  | [_, .fvar _] => simp [decorated?, other]
  | [_, .apply _ _] => simp [decorated?]
  | [_, .lambda _ _] => simp [decorated?]
  | [_, .multiLambda _ _ _] => simp [decorated?]
  | [_, .subst _ _] => simp [decorated?]
  | [_, .collection _ _ _] => simp [decorated?]
  | _ :: _ :: _ :: _ => simp [decorated?]

/-- The data and variable branches of the settling step; leaves the structural branch with `placed`
unfolded. -/
syntax "settle_free_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| settle_free_cases $pattern) => `(tactic| (
      by_cases data : type = .base decl.dataSort
      · rw [actionFree.eq_def, if_pos data]
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [actionFree.eq_def, if_neg data, if_pos ⟨settle_occurs bodySort occurs.1, occurs.2⟩]
      rw [actionsAtBody.eq_def, if_neg data, if_neg occurs] at placed))

/-- Settling keeps an occurrence an occurrence. -/
theorem settle_occurs {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {type : TypeExpr}
    {occurrence : Pattern} (occurs : (decorated? decl occurrence).isSome) :
    (decorated? decl (settle language decl type occurrence)).isSome := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  obtain ⟨dataType, actionTypes⟩ := paramTypes_action bodySort
  cases coefficient with
  | none =>
    rw [plain rfl, settle_bare bare, decorated?_of_bare bare]
    rfl
  | some c =>
    rw [applied c rfl, settle_actionNode actionTypes, settle_bare bare, decorated?_of_bare bare]
    dsimp only
    rw [decorated?_action _ _ bare]
    rfl

mutual
  /-- **Settling produces an action-free term**, when every action node sits at the action's body sort with
  a coefficient and a body. -/
  theorem actionFree_settle (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) :
      ∀ (type : TypeExpr) (pattern : Pattern), actionsAtBody language decl type pattern = true →
        actionFree language decl type (settle language decl type pattern) = true
    | type, .apply label arguments, placed => by
      settle_free_cases (.apply label arguments)
      dsimp only at placed
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at placed
      obtain ⟨where_, rest⟩ := placed
      by_cases isAction : label = decl.action
      · subst isAction
        have atBody := where_.resolve_left (fun h => h rfl)
        have sameType : type = bodyType := Option.some.inj (atBody.1.symm.trans bodySort)
        subst sameType
        obtain ⟨dataType, actionTypes⟩ := paramTypes_action bodySort
        rw [actionTypes] at rest
        dsimp only at rest
        obtain ⟨coefficient, body, same⟩ := List.length_eq_two.mp atBody.2
        subst same
        simp only [actionsAtBodyArgs, Bool.and_eq_true] at rest
        have bodyFree := actionFree_settle bodyNotData bodySort type body rest.2.1
        rw [settle_actionNode actionTypes]
        cases settledBody : decorated? decl (settle language decl type body) with
        | none =>
          dsimp only
          exact actionFree_mapFrame (actVariable_keeps _) bodyNotData 0 type _ bodyFree
        | some pair =>
          obtain ⟨inner, occurrenceVar⟩ := pair
          obtain ⟨bare, _, _⟩ := decorated?_shape settledBody
          cases inner with
          | none =>
            dsimp only
            rw [actionFree.eq_def, if_neg data, if_pos ⟨by rw [decorated?_action _ _ bare]; rfl, atBody.1⟩]
          | some c =>
            dsimp only
            rw [actionFree.eq_def, if_neg data, if_pos ⟨by rw [decorated?_action _ _ bare]; rfl, atBody.1⟩]
      · rw [settle_apply_other isAction]
        cases found : paramTypes language label with
        | none =>
          dsimp only
          rw [actionFree.eq_def, if_neg data, if_neg (by rw [decorated?_apply_other isAction]; simp)]
          dsimp only
          rw [found]
          simp [isAction]
        | some types =>
          rw [found] at rest
          dsimp only at rest ⊢
          rw [actionFree.eq_def, if_neg data, if_neg (by rw [decorated?_apply_other isAction]; simp)]
          dsimp only
          rw [found]
          dsimp only
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
          exact ⟨isAction, actionFreeArgs_settleArgs bodyNotData bodySort types arguments rest⟩
    | type, .lambda binder body, placed => by
      settle_free_cases (.lambda binder body)
      rw [settle.eq_def]
      cases type with
      | arrow domain codomain =>
        dsimp only at placed ⊢
        rw [actionFree.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact actionFree_settle bodyNotData bodySort codomain body placed
      | _ =>
        dsimp only
        rw [actionFree.eq_def, if_neg data, if_neg occurs]
    | type, .multiLambda arity binders body, placed => by
      settle_free_cases (.multiLambda arity binders body)
      rw [settle.eq_def]
      cases type with
      | arrow domain codomain =>
        dsimp only at placed ⊢
        rw [actionFree.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact actionFree_settle bodyNotData bodySort codomain body placed
      | _ =>
        dsimp only
        rw [actionFree.eq_def, if_neg data, if_neg occurs]
    | type, .collection kind elements rest, placed => by
      settle_free_cases (.collection kind elements rest)
      rw [settle.eq_def]
      dsimp only at placed ⊢
      cases found : elementType language type kind with
      | none =>
        dsimp only
        rw [actionFree.eq_def, if_neg data, if_neg occurs]
        dsimp only
        rw [found]
      | some element =>
        rw [found] at placed
        dsimp only at placed ⊢
        rw [actionFree.eq_def, if_neg data, if_neg (by simp [decorated?])]
        dsimp only
        rw [found]
        exact actionFreeList_settleList bodyNotData bodySort element elements placed
    | type, .bvar index, placed => by
      settle_free_cases (.bvar index)
      rw [settle_bvar, actionFree.eq_def, if_neg data, if_neg occurs]
    | type, .fvar name, placed => by
      settle_free_cases (.fvar name)
      rw [settle_fvar, actionFree.eq_def, if_neg data, if_neg occurs]
    | type, .subst body replacement, placed => by
      settle_free_cases (.subst body replacement)
      rw [settle.eq_def, actionFree.eq_def, if_neg data, if_neg occurs]
  termination_by _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionFreeArgs_settleArgs (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) :
      ∀ (types : List TypeExpr) (arguments : List Pattern), actionsAtBodyArgs language decl types arguments = true →
        actionFreeArgs language decl types (settleArgs language decl types arguments) = true
    | type :: types, argument :: arguments, placed => by
      rw [actionsAtBodyArgs, Bool.and_eq_true] at placed
      rw [settleArgs, actionFreeArgs, Bool.and_eq_true]
      exact ⟨actionFree_settle bodyNotData bodySort type argument placed.1,
        actionFreeArgs_settleArgs bodyNotData bodySort types arguments placed.2⟩
    | [], arguments, _ => by simp [settleArgs, actionFreeArgs]
    | _ :: _, [], _ => by simp [settleArgs, actionFreeArgs]
  termination_by _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionFreeList_settleList (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) :
      ∀ (element : TypeExpr) (patterns : List Pattern), actionsAtBodyList language decl element patterns = true →
        actionFreeList language decl element (settleList language decl element patterns) = true
    | element, [], _ => by simp [settleList, actionFreeList]
    | element, pattern :: patterns, placed => by
      rw [actionsAtBodyList, Bool.and_eq_true] at placed
      rw [settleList, actionFreeList, Bool.and_eq_true]
      exact ⟨actionFree_settle bodyNotData bodySort element pattern placed.1,
        actionFreeList_settleList bodyNotData bodySort element patterns placed.2⟩
  termination_by _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end SettleFree

/-! ## Words stay words -/

section Words

variable {decl : OrientationDecl} {G : Type} [Group G] {reading : DataReading decl G}

/-- **Lifting keeps a word a word.** -/
theorem letters_liftBVars (cutoff shift : Nat) :
    ∀ (word : Pattern) {found : List (Letter G)}, letters decl reading.constant word = some found →
      ∃ lifted, letters decl reading.constant (Substitution.liftBVars cutoff shift word) = some lifted
  | .bvar index, found, parsed => by
    simp only [Substitution.liftBVars]
    split
    · exact ⟨_, by rw [letters]⟩
    · exact ⟨_, by rw [letters]⟩
  | .fvar name, found, parsed => ⟨found, by simpa [Substitution.liftBVars] using parsed⟩
  | .apply label [], found, parsed =>
    ⟨found, by simpa [Substitution.liftBVars, Substitution.liftBVarsList] using parsed⟩
  | .apply label [argument], found, parsed => by
    rw [letters] at parsed
    split at parsed
    · rename_i isInverse
      obtain ⟨inner, innerParsed, _⟩ := Option.map_eq_some_iff.mp parsed
      obtain ⟨lifted, liftedParsed⟩ := letters_liftBVars cutoff shift argument innerParsed
      refine ⟨invertLetters lifted, ?_⟩
      simp only [Substitution.liftBVars, Substitution.liftBVarsList]
      rw [letters, if_pos isInverse, liftedParsed]
      rfl
    · cases parsed
  | .apply label [left, right], found, parsed => by
    rw [letters] at parsed
    split at parsed
    · rename_i isMultiply
      split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        obtain ⟨leftLifted, leftLiftedParsed⟩ := letters_liftBVars cutoff shift left leftParsed
        obtain ⟨rightLifted, rightLiftedParsed⟩ := letters_liftBVars cutoff shift right rightParsed
        refine ⟨leftLifted ++ rightLifted, ?_⟩
        simp only [Substitution.liftBVars, Substitution.liftBVarsList]
        rw [letters, if_pos isMultiply, leftLiftedParsed, rightLiftedParsed]
      · cases parsed
    · cases parsed
  | .apply label (_ :: _ :: _ :: _), found, parsed => by simp [letters] at parsed
  | .lambda _ _, found, parsed => by simp [letters] at parsed
  | .multiLambda _ _ _, found, parsed => by simp [letters] at parsed
  | .subst _ _, found, parsed => by simp [letters] at parsed
  | .collection _ _ _, found, parsed => by simp [letters] at parsed
termination_by word => sizeOf word
decreasing_by all_goals sizeOf_pattern_dec

/-- **(FRAME) by any word keeps a word a word.** -/
theorem letters_frameWord_some {g : Pattern} {gLetters : List (Letter G)}
    (gParsed : letters decl reading.constant g = some gLetters) (depth : Nat) :
    ∀ (word : Pattern) {found : List (Letter G)}, letters decl reading.constant word = some found →
      ∃ framed, letters decl reading.constant (frameWord decl g depth word) = some framed
  | .bvar index, found, parsed => by
    by_cases inside : index < depth
    · refine ⟨invertLetters gLetters ++ [.power (.bound index) 1], ?_⟩
      simp only [frameWord, if_pos inside]
      exact letters_mulWord (letters_invWord gParsed) (by rw [letters])
    · exact ⟨found, by simp only [frameWord, if_neg inside]; exact parsed⟩
  | .fvar name, found, parsed => ⟨found, by simp only [frameWord]; exact parsed⟩
  | .apply label [], found, parsed => ⟨found, by simp only [frameWord, frameWords]; exact parsed⟩
  | .apply label [argument], found, parsed => by
    rw [letters] at parsed
    split at parsed
    · rename_i isInverse
      obtain ⟨inner, innerParsed, _⟩ := Option.map_eq_some_iff.mp parsed
      obtain ⟨framed, framedParsed⟩ := letters_frameWord_some gParsed depth argument innerParsed
      refine ⟨invertLetters framed, ?_⟩
      simp only [frameWord, frameWords]
      rw [letters, if_pos isInverse, framedParsed]
      rfl
    · cases parsed
  | .apply label [left, right], found, parsed => by
    rw [letters] at parsed
    split at parsed
    · rename_i isMultiply
      split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        obtain ⟨leftFramed, leftFramedParsed⟩ := letters_frameWord_some gParsed depth left leftParsed
        obtain ⟨rightFramed, rightFramedParsed⟩ := letters_frameWord_some gParsed depth right rightParsed
        refine ⟨leftFramed ++ rightFramed, ?_⟩
        simp only [frameWord, frameWords]
        rw [letters, if_pos isMultiply, leftFramedParsed, rightFramedParsed]
      · cases parsed
    · cases parsed
  | .apply label (_ :: _ :: _ :: _), found, parsed => by simp [letters] at parsed
  | .lambda _ _, found, parsed => by simp [letters] at parsed
  | .multiLambda _ _ _, found, parsed => by simp [letters] at parsed
  | .subst _ _, found, parsed => by simp [letters] at parsed
  | .collection _ _ _, found, parsed => by simp [letters] at parsed
termination_by word => sizeOf word
decreasing_by all_goals sizeOf_pattern_dec

/-- **The action of any word keeps a datum a word.** -/
theorem letters_actData_some {g : Pattern} {gLetters : List (Letter G)}
    (gParsed : letters decl reading.constant g = some gLetters) (depth : Nat) {word : Pattern}
    {found : List (Letter G)} (parsed : letters decl reading.constant word = some found) :
    ∃ acted, letters decl reading.constant (actData decl g depth word) = some acted := by
  obtain ⟨lifted, liftedParsed⟩ := letters_liftBVars (reading := reading) 0 depth g gParsed
  obtain ⟨framed, framedParsed⟩ := letters_frameWord_some liftedParsed depth word parsed
  exact ⟨lifted ++ framed, letters_mulWord liftedParsed framedParsed⟩

/-- **The action of any word keeps a decoration's coefficient a word.** -/
theorem actVariable_coefficientParses {g : Pattern} {gLetters : List (Letter G)}
    (gParsed : letters decl reading.constant g = some gLetters) (depth : Nat) {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome) (parses : CoefficientParses reading occurrence) :
    CoefficientParses reading (actVariable decl g depth occurrence) := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  obtain ⟨lifted, liftedParsed⟩ := letters_liftBVars (reading := reading) 0 depth g gParsed
  intro c v acted
  cases coefficient with
  | none =>
    rw [plain rfl] at acted
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_bare_inside g inside, decorated?_of_bare bare] at acted
        cases acted
      · rw [actVariable_bare_outside g inside, decorated?_action _ _ bare] at acted
        cases acted
        rw [liftedParsed]
        rfl
    | .fvar name, bare =>
      rw [actVariable_bare_free, decorated?_action _ _ bare] at acted
      cases acted
      rw [liftedParsed]
      rfl
  | some c₀ =>
    rw [applied c₀ rfl] at acted
    obtain ⟨c₀Letters, c₀Parsed⟩ := Option.isSome_iff_exists.mp (parses c₀ occurrenceVar found)
    obtain ⟨acted', actedParsed⟩ := letters_actData_some gParsed depth c₀Parsed
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_decorated_inside g _ inside, decorated?_action _ _ bare] at acted
        cases acted
        rw [letters_mulWord actedParsed (letters_invWord liftedParsed)]
        rfl
      · rw [actVariable_decorated_outside g _ inside, decorated?_action _ _ bare] at acted
        cases acted
        rw [actedParsed]
        rfl
    | .fvar name, bare =>
      rw [actVariable_decorated_free, decorated?_action _ _ bare] at acted
      cases acted
      rw [actedParsed]
      rfl

end Words

/-! ## Settling is idempotent -/

section Idempotent

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] {reading : DataReading decl G}

omit [Group G] in
theorem bodySort_of_dataSorted {bodyType : TypeExpr}
    (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType]) :
    actionType language decl = some bodyType := by
  unfold actionType
  rw [dataSorted]

/-- Word-formedness does not see its depth. -/
theorem wordsAt_depth (depth : Nat) (type : TypeExpr) (pattern : Pattern) :
    WordsAt (language := language) reading depth type pattern ↔ WordsAt (language := language) reading 0 type pattern := by
  have shifted := frameAll_shift (language := language) (decl := decl)
    (dataOk := fun _ datum => (letters decl reading.constant datum).isSome)
    (variableOk := fun _ occurrence => CoefficientParses reading occurrence) depth 0 type pattern
  rw [Nat.zero_add] at shifted
  exact shifted

/-- **The action of a word keeps data and decorations words.** -/
theorem wordsAt_frameAct (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) {g : Pattern} {gLetters : List (Letter G)}
    (gParsed : letters decl reading.constant g = some gLetters) (type : TypeExpr) {pattern : Pattern}
    (words : WordsAt (language := language) reading 0 type pattern) :
    WordsAt (language := language) reading 0 type (frameAct language decl g type pattern) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  apply frameAll_mapFrame (actVariable_keeps g).notBare bodyNotData bodySort _ _ 0 type pattern words
  · intro k datum parsed
    obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsed
    obtain ⟨acted, actedParsed⟩ := letters_actData_some gParsed k parsed
    show (letters decl reading.constant _).isSome = true
    rw [actedParsed]
    rfl
  · intro k occurrence occurs parses
    rw [frameAll_occurrence bodySort notData ((actVariable_keeps g).occurs k occurrence occurs)]
    exact actVariable_coefficientParses gParsed k occurs parses

/-- The data and variable branches of the word-formedness step; leaves the structural branch with
`placed` and `words` unfolded. -/
syntax "words_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| words_cases $pattern) => `(tactic| (
      unfold WordsAt at words ⊢
      by_cases data : type = .base decl.dataSort
      · have parsedWord := words
        rw [FrameAll.eq_def, if_pos data] at parsedWord
        obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsedWord
        rw [settle_word multiplyNe reading.constant _ parsed type]
        exact words
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · have parses := words
        rw [FrameAll.eq_def, if_neg data, if_pos occurs] at parses
        rw [settle_occurrence multiplyNe bodySort reading occurs.1 parses type]
        exact words
      rw [actionsAtBody.eq_def, if_neg data, if_neg occurs] at placed
      rw [FrameAll.eq_def, if_neg data, if_neg occurs] at words))

mutual
  /-- **Settling keeps data and decorations words.** -/
  theorem wordsAt_settle (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), actionsAtBody language decl type pattern = true →
        WordsAt (language := language) reading depth type pattern →
          WordsAt (language := language) reading depth type (settle language decl type pattern)
    | depth, type, .apply label arguments, placed, words => by
      words_cases (.apply label arguments)
      dsimp only at placed words
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at placed
      obtain ⟨where_, rest⟩ := placed
      by_cases isAction : label = decl.action
      · subst isAction
        have atBody := where_.resolve_left (fun h => h rfl)
        have sameType : type = bodyType := Option.some.inj (atBody.1.symm.trans bodySort)
        subst sameType
        rw [dataSorted] at rest words
        dsimp only at rest words
        obtain ⟨coefficient, body, same⟩ := List.length_eq_two.mp atBody.2
        subst same
        simp only [actionsAtBodyArgs, Bool.and_eq_true] at rest
        simp only [FrameAllArgs] at words
        obtain ⟨coefficientWord, bodyWords, _⟩ := words
        rw [FrameAll.eq_def, if_pos rfl] at coefficientWord
        obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp coefficientWord
        have bodySettled := wordsAt_settle multiplyNe bodyNotData dataSorted bodySort depth type body rest.2.1 bodyWords
        rw [settle_actionNode dataSorted, settle_word multiplyNe reading.constant coefficient cParsed]
        cases settledBody : decorated? decl (settle language decl type body) with
        | none =>
          dsimp only
          exact (wordsAt_depth depth type _).mpr
            (wordsAt_frameAct bodyNotData bodySort cParsed type ((wordsAt_depth depth type _).mp bodySettled))
        | some pair =>
          obtain ⟨inner, occurrenceVar⟩ := pair
          obtain ⟨bare, _, applied⟩ := decorated?_shape settledBody
          cases inner with
          | none =>
            dsimp only
            rw [FrameAll.eq_def, if_neg data, if_pos ⟨by rw [decorated?_action _ _ bare]; rfl, atBody.1⟩]
            intro c v found
            rw [decorated?_action _ _ bare] at found
            cases found
            rw [cParsed]
            rfl
          | some c =>
            dsimp only
            have innerParses := bodySettled
            unfold WordsAt at innerParses
            rw [FrameAll.eq_def, if_neg data,
              if_pos ⟨by rw [settledBody]; rfl, atBody.1⟩] at innerParses
            obtain ⟨innerLetters, innerParsed⟩ := Option.isSome_iff_exists.mp (innerParses c occurrenceVar settledBody)
            rw [FrameAll.eq_def, if_neg data, if_pos ⟨by rw [decorated?_action _ _ bare]; rfl, atBody.1⟩]
            intro c' v found
            rw [decorated?_action _ _ bare] at found
            cases found
            rw [letters_mulWord cParsed innerParsed]
            rfl
      · rw [settle_apply_other isAction]
        cases found : paramTypes language label with
        | none =>
          dsimp only
          rw [FrameAll.eq_def, if_neg data, if_neg occurs]
          dsimp only
          rw [found]
          trivial
        | some types =>
          rw [found] at rest words
          dsimp only at rest words ⊢
          rw [FrameAll.eq_def, if_neg data, if_neg (by rw [decorated?_apply_other isAction]; simp)]
          dsimp only
          rw [found]
          dsimp only
          exact wordsAtArgs_settleArgs multiplyNe bodyNotData dataSorted bodySort depth types arguments rest words
    | depth, type, .lambda binder body, placed, words => by
      words_cases (.lambda binder body)
      rw [settle.eq_def]
      cases type with
      | arrow domain codomain =>
        dsimp only at placed words ⊢
        rw [FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact wordsAt_settle multiplyNe bodyNotData dataSorted bodySort (depth + 1) codomain body placed words
      | _ =>
        dsimp only
        rw [FrameAll.eq_def, if_neg data, if_neg occurs]
        trivial
    | depth, type, .multiLambda arity binders body, placed, words => by
      words_cases (.multiLambda arity binders body)
      rw [settle.eq_def]
      cases type with
      | arrow domain codomain =>
        dsimp only at placed words ⊢
        rw [FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact wordsAt_settle multiplyNe bodyNotData dataSorted bodySort (depth + arity) codomain body placed words
      | _ =>
        dsimp only
        rw [FrameAll.eq_def, if_neg data, if_neg occurs]
        trivial
    | depth, type, .collection kind elements rest, placed, words => by
      words_cases (.collection kind elements rest)
      rw [settle.eq_def]
      dsimp only at placed words ⊢
      cases found : elementType language type kind with
      | none =>
        dsimp only
        rw [FrameAll.eq_def, if_neg data, if_neg occurs]
        dsimp only
        rw [found]
        trivial
      | some element =>
        rw [found] at placed words
        dsimp only at placed words ⊢
        rw [FrameAll.eq_def, if_neg data, if_neg (by simp [decorated?])]
        dsimp only
        rw [found]
        exact wordsAtList_settleList multiplyNe bodyNotData dataSorted bodySort depth element elements placed words
    | depth, type, .bvar index, placed, words => by
      words_cases (.bvar index)
      rw [settle_bvar, FrameAll.eq_def, if_neg data, if_neg occurs]
      trivial
    | depth, type, .fvar name, placed, words => by
      words_cases (.fvar name)
      rw [settle_fvar, FrameAll.eq_def, if_neg data, if_neg occurs]
      trivial
    | depth, type, .subst body replacement, placed, words => by
      words_cases (.subst body replacement)
      rw [settle.eq_def, FrameAll.eq_def, if_neg data, if_neg occurs]
      trivial
  termination_by _ _ pattern _ _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem wordsAtArgs_settleArgs (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        actionsAtBodyArgs language decl types arguments = true →
          FrameAllArgs language decl (fun _ datum => (letters decl reading.constant datum).isSome)
              (fun _ occurrence => CoefficientParses reading occurrence) depth types arguments →
            FrameAllArgs language decl (fun _ datum => (letters decl reading.constant datum).isSome)
              (fun _ occurrence => CoefficientParses reading occurrence) depth types
              (settleArgs language decl types arguments)
    | depth, type :: types, argument :: arguments, placed, words => by
      rw [actionsAtBodyArgs, Bool.and_eq_true] at placed
      rw [FrameAllArgs] at words
      rw [settleArgs, FrameAllArgs]
      exact ⟨wordsAt_settle multiplyNe bodyNotData dataSorted bodySort depth type argument placed.1 words.1,
        wordsAtArgs_settleArgs multiplyNe bodyNotData dataSorted bodySort depth types arguments placed.2 words.2⟩
    | depth, [], arguments, _, _ => by simp [settleArgs, FrameAllArgs]
    | depth, _ :: _, [], _, _ => by simp [settleArgs, FrameAllArgs]
  termination_by _ _ arguments _ _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem wordsAtList_settleList (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        actionsAtBodyList language decl element patterns = true →
          FrameAllList language decl (fun _ datum => (letters decl reading.constant datum).isSome)
              (fun _ occurrence => CoefficientParses reading occurrence) depth element patterns →
            FrameAllList language decl (fun _ datum => (letters decl reading.constant datum).isSome)
              (fun _ occurrence => CoefficientParses reading occurrence) depth element
              (settleList language decl element patterns)
    | depth, element, [], _, _ => by simp [settleList, FrameAllList]
    | depth, element, pattern :: patterns, placed, words => by
      rw [actionsAtBodyList, Bool.and_eq_true] at placed
      rw [FrameAllList] at words
      rw [settleList, FrameAllList]
      exact ⟨wordsAt_settle multiplyNe bodyNotData dataSorted bodySort depth element pattern placed.1 words.1,
        wordsAtList_settleList multiplyNe bodyNotData dataSorted bodySort depth element patterns placed.2 words.2⟩
  termination_by _ _ patterns _ _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- **Settling is idempotent** on terms whose action nodes sit at the body sort and whose data and
decorations are words. -/
theorem settle_settle (multiplyNe : decl.multiply ≠ decl.action)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType]) (depth : Nat)
    (type : TypeExpr) (pattern : Pattern) (placed : actionsAtBody language decl type pattern = true)
    (words : WordsAt (language := language) reading depth type pattern) :
    settle language decl type (settle language decl type pattern) = settle language decl type pattern := by
  have bodySort := bodySort_of_dataSorted dataSorted
  exact settle_of_actionFree multiplyNe bodySort reading depth type _
    (actionFree_settle bodyNotData bodySort type pattern placed)
    (wordsAt_settle multiplyNe bodyNotData dataSorted bodySort depth type pattern placed words)

end Idempotent


/-! ## Closed action coefficients -/

section ClosedActions

variable (language : LanguageDef) (decl : OrientationDecl)
variable {G : Type} [Group G]

mutual
  /-- **Every action coefficient is a closed word**: at an action node and at a decoration. -/
  def closedActions (reading : DataReading decl G) (type : TypeExpr) (pattern : Pattern) : Bool :=
    if type = .base decl.dataSort then true
    else if (decorated? decl pattern).isSome ∧ actionType language decl = some type then
      match decorated? decl pattern with
      | some (some coefficient, _) => (read decl reading.constant coefficient).isSome
      | _ => true
    else
      match pattern with
      | .apply label arguments =>
          (label != decl.action ||
              match arguments with
              | [coefficient, _] => (read decl reading.constant coefficient).isSome
              | _ => true) &&
            match paramTypes language label with
            | some types => closedActionsArgs reading types arguments
            | none => true
      | .lambda _ body =>
          match type with
          | .arrow _ codomain => closedActions reading codomain body
          | _ => true
      | .multiLambda _ _ body =>
          match type with
          | .arrow _ codomain => closedActions reading codomain body
          | _ => true
      | .collection kind elements _ =>
          match elementType language type kind with
          | some element => closedActionsList reading element elements
          | none => true
      | _ => true
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def closedActionsArgs (reading : DataReading decl G) : List TypeExpr → List Pattern → Bool
    | type :: types, argument :: arguments =>
        closedActions reading type argument && closedActionsArgs reading types arguments
    | [], _ => true
    | _ :: _, [] => true
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def closedActionsList (reading : DataReading decl G) (element : TypeExpr) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => closedActions reading element pattern && closedActionsList reading element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end ClosedActions

/-! ## The frame normal form keeps the shape -/

section NormalShape

variable {language : LanguageDef} {decl : OrientationDecl}

theorem length_mapFrameArgs (f v : Nat → Pattern → Pattern) (depth : Nat) :
    ∀ (types : List TypeExpr) (arguments : List Pattern),
      (mapFrameArgs language decl f v depth types arguments).length = arguments.length
  | type :: types, argument :: arguments => by
    rw [mapFrameArgs, List.length_cons, List.length_cons, length_mapFrameArgs f v depth types arguments]
  | [], arguments => by simp [mapFrameArgs]
  | _ :: _, [] => by simp [mapFrameArgs]

variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- **The frame normal form keeps data and decorations words.** -/
theorem wordsAt_normalWalk (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) (depth : Nat) (type : TypeExpr) {pattern : Pattern}
    (words : WordsAt (language := language) reading depth type pattern) :
    WordsAt (language := language) reading depth type (normalWalkAt (language := language) reading depth type pattern) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  apply frameAll_mapFrame normalVariable_keeps.notBare bodyNotData bodySort _ _ depth type pattern words
  · intro k datum parsed
    obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsed
    obtain ⟨normal, normalParsed, _⟩ := letters_wordNormal (reading := reading) parsed
    show (letters decl reading.constant _).isSome = true
    rw [normalParsed]
    rfl
  · intro k occurrence occurs parses
    rw [frameAll_occurrence bodySort notData (normalVariable_keeps.occurs k occurrence occurs)]
    obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
    obtain ⟨bare, plain, applied⟩ := decorated?_shape found
    intro c v normal
    cases coefficient with
    | none =>
      rw [plain rfl, normalVariable_bare bare, decorated?_action _ _ bare] at normal
      cases normal
      obtain ⟨one, oneParsed, _⟩ := letters_of_read reading.constant _ (reading.read_write 1)
      rw [oneParsed]
      rfl
    | some c₀ =>
      rw [applied c₀ rfl, normalVariable_decorated bare, decorated?_action _ _ bare] at normal
      cases normal
      obtain ⟨c₀Letters, c₀Parsed⟩ := Option.isSome_iff_exists.mp (parses c₀ occurrenceVar found)
      obtain ⟨normal, normalParsed, _⟩ := letters_wordNormal (reading := reading) c₀Parsed
      rw [normalParsed]
      rfl

/-- At the body sort the frame normal form keeps an occurrence an occurrence, and anything else no
occurrence. -/
theorem decorated?_normalWalk (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) (depth : Nat) (pattern : Pattern) :
    (decorated? decl (normalWalkAt (language := language) reading depth bodyType pattern)).isSome =
      (decorated? decl pattern).isSome := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  unfold normalWalkAt
  by_cases occurs : (decorated? decl pattern).isSome
  · rw [mapFrame_variable notData ⟨occurs, bodySort⟩, occurs]
    exact normalVariable_keeps.occurs depth pattern occurs
  · have structural := decorated?_mapFrame_structural (language := language)
      (f := fun _ datum => wordNormal decl reading datum) (v := normalVariable decl reading) (depth := depth)
      normalVariable_keeps.notBare bodyNotData notData (fun both => occurs both.1)
    rw [Bool.eq_false_iff.mpr occurs]
    exact Bool.eq_false_iff.mpr (fun found => structural ⟨found, bodySort⟩)

end NormalShape

section KeepPlaced

variable {language : LanguageDef} {decl : OrientationDecl}

/-- The data and variable branches of an action-placement step; leaves the structural branch with `free`
unfolded and `structural` for the walk's result. -/
syntax "keep_placed_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| keep_placed_cases $pattern) => `(tactic| (
      by_cases data : type = .base decl.dataSort
      · rw [actionsAtBody.eq_def, if_pos data]
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [mapFrame_variable data occurs, actionsAtBody.eq_def, if_neg data,
          if_pos ⟨keeps.occurs _ _ occurs.1, occurs.2⟩]
      have structural := decorated?_mapFrame_structural (language := language) (f := f) (v := v)
        (depth := depth) keeps.notBare bodyNotData data occurs
      rw [actionsAtBody.eq_def, if_neg data, if_neg occurs] at free))

mutual
  /-- **A walk that keeps occurrences keeps every action node at the body sort.** -/
  theorem actionsAtBody_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), actionsAtBody language decl type pattern = true →
        actionsAtBody language decl type (mapFrame language decl f v depth type pattern) = true
    | depth, type, .apply label arguments, free => by
      keep_placed_cases (.apply label arguments)
      dsimp only at free
      simp only [Bool.and_eq_true] at free
      cases found : paramTypes language label with
      | none =>
        rw [mapFrame_apply_unknown data occurs found, actionsAtBody.eq_def, if_neg data, if_neg occurs]
        dsimp only
        rw [found]
        simp only [Bool.and_true]
        exact free.1
      | some types =>
        rw [found] at free
        rw [mapFrame_apply_structural data occurs found] at structural ⊢
        rw [actionsAtBody.eq_def, if_neg data, if_neg structural]
        dsimp only
        rw [found]
        dsimp only
        simp only [Bool.and_eq_true]
        refine ⟨?_, actionsAtBodyArgs_mapFrame keeps bodyNotData depth types arguments free.2⟩
        rw [length_mapFrameArgs]
        exact free.1
    | depth, type, .lambda binder body, free => by
      keep_placed_cases (.lambda binder body)
      cases type with
      | arrow domain codomain =>
        dsimp only at free
        rw [mapFrame_lambda data, actionsAtBody.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact actionsAtBody_mapFrame keeps bodyNotData (depth + 1) codomain body free
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, actionsAtBody.eq_def, if_neg data, if_neg occurs]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, actionsAtBody.eq_def, if_neg data, if_neg occurs]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, actionsAtBody.eq_def, if_neg data, if_neg occurs]
    | depth, type, .multiLambda arity binders body, free => by
      keep_placed_cases (.multiLambda arity binders body)
      cases type with
      | arrow domain codomain =>
        dsimp only at free
        rw [mapFrame_multiLambda data, actionsAtBody.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact actionsAtBody_mapFrame keeps bodyNotData (depth + arity) codomain body free
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, actionsAtBody.eq_def, if_neg data, if_neg occurs]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, actionsAtBody.eq_def, if_neg data, if_neg occurs]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, actionsAtBody.eq_def, if_neg data, if_neg occurs]
    | depth, type, .collection kind elements rest, free => by
      keep_placed_cases (.collection kind elements rest)
      dsimp only at free
      cases found : elementType language type kind with
      | none =>
        rw [mapFrame_collection_unknown data found, actionsAtBody.eq_def, if_neg data, if_neg occurs]
        dsimp only
        rw [found]
      | some element =>
        rw [found] at free
        dsimp only at free
        rw [mapFrame_collection data found, actionsAtBody.eq_def, if_neg data, if_neg (by simp [decorated?])]
        dsimp only
        rw [found]
        exact actionsAtBodyList_mapFrame keeps bodyNotData depth element elements free
    | depth, type, .bvar index, free => by
      keep_placed_cases (.bvar index)
      rw [mapFrame_leaf data occurs (.inl ⟨index, rfl⟩), actionsAtBody.eq_def, if_neg data, if_neg occurs]
    | depth, type, .fvar name, free => by
      keep_placed_cases (.fvar name)
      rw [mapFrame_leaf data occurs (.inr (.inl ⟨name, rfl⟩)), actionsAtBody.eq_def, if_neg data, if_neg occurs]
    | depth, type, .subst body replacement, free => by
      keep_placed_cases (.subst body replacement)
      rw [mapFrame_leaf data occurs (.inr (.inr ⟨body, replacement, rfl⟩)), actionsAtBody.eq_def, if_neg data,
        if_neg occurs]
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionsAtBodyArgs_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        actionsAtBodyArgs language decl types arguments = true →
          actionsAtBodyArgs language decl types (mapFrameArgs language decl f v depth types arguments) = true
    | depth, type :: types, argument :: arguments, free => by
      rw [actionsAtBodyArgs, Bool.and_eq_true] at free
      rw [mapFrameArgs, actionsAtBodyArgs, Bool.and_eq_true]
      exact ⟨actionsAtBody_mapFrame keeps bodyNotData depth type argument free.1,
        actionsAtBodyArgs_mapFrame keeps bodyNotData depth types arguments free.2⟩
    | depth, [], arguments, _ => by simp [mapFrameArgs, actionsAtBodyArgs]
    | depth, _ :: _, [], _ => by simp [mapFrameArgs, actionsAtBodyArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionsAtBodyList_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        actionsAtBodyList language decl element patterns = true →
          actionsAtBodyList language decl element (mapFrameList language decl f v depth element patterns) = true
    | depth, element, [], _ => by rw [mapFrameList, actionsAtBodyList]
    | depth, element, pattern :: patterns, free => by
      rw [actionsAtBodyList, Bool.and_eq_true] at free
      rw [mapFrameList, actionsAtBodyList, Bool.and_eq_true]
      exact ⟨actionsAtBody_mapFrame keeps bodyNotData depth element pattern free.1,
        actionsAtBodyList_mapFrame keeps bodyNotData depth element patterns free.2⟩
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end KeepPlaced

section KeepClosed

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] {reading : DataReading decl G}

/-- An occurrence's coefficient, if it has one, is a closed word. -/
def coefficientClosed (reading : DataReading decl G) (occurrence : Pattern) : Bool :=
  match decorated? decl occurrence with
  | some (some coefficient, _) => (read decl reading.constant coefficient).isSome
  | _ => true

/-- The data and variable branches of a closed-coefficient step; leaves the structural branch with `free`
unfolded and `structural` for the walk's result. -/
syntax "keep_closed_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| keep_closed_cases $pattern) => `(tactic| (
      by_cases data : type = .base decl.dataSort
      · rw [closedActions.eq_def, if_pos data]
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [closedActions.eq_def, if_neg data, if_pos occurs] at free
        rw [mapFrame_variable data occurs, closedActions.eq_def, if_neg data,
          if_pos ⟨keeps.occurs _ _ occurs.1, occurs.2⟩]
        exact variableClosed _ _ occurs.1 free
      have structural := decorated?_mapFrame_structural (language := language) (f := f) (v := v)
        (depth := depth) keeps.notBare bodyNotData data occurs
      rw [closedActions.eq_def, if_neg data, if_neg occurs] at free))

mutual
  /-- **A walk that keeps closed words closed keeps every action coefficient closed.** -/
  theorem closedActions_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (dataClosed : ∀ depth word, (read decl reading.constant word).isSome →
        (read decl reading.constant (f depth word)).isSome)
      (variableClosed : ∀ depth occurrence, (decorated? decl occurrence).isSome →
        coefficientClosed reading occurrence = true → coefficientClosed reading (v depth occurrence) = true) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), closedActions language decl reading type pattern = true →
        closedActions language decl reading type (mapFrame language decl f v depth type pattern) = true
    | depth, type, .apply label arguments, free => by
      keep_closed_cases (.apply label arguments)
      dsimp only at free
      simp only [Bool.and_eq_true] at free
      cases found : paramTypes language label with
      | none =>
        rw [mapFrame_apply_unknown data occurs found, closedActions.eq_def, if_neg data, if_neg occurs]
        dsimp only
        rw [found]
        simp only [Bool.and_true]
        exact free.1
      | some types =>
        rw [found] at free
        rw [mapFrame_apply_structural data occurs found] at structural ⊢
        rw [closedActions.eq_def, if_neg data, if_neg structural]
        dsimp only
        rw [found]
        dsimp only
        simp only [Bool.and_eq_true]
        refine ⟨?_, closedActionsArgs_mapFrame keeps bodyNotData dataSorted dataClosed variableClosed depth types
          arguments free.2⟩
        by_cases isAction : label = decl.action
        · subst isAction
          rw [dataSorted] at found
          cases found
          have coefficient := free.1
          simp only [bne_self_eq_false, Bool.false_or] at coefficient ⊢
          match arguments, coefficient with
          | [c, body], coefficient =>
            simp only [mapFrameArgs, mapFrame_data (rfl : TypeExpr.base decl.dataSort = TypeExpr.base decl.dataSort)]
            exact dataClosed depth c coefficient
          | [], _ => simp [mapFrameArgs]
          | [c], _ => simp [mapFrameArgs]
          | _ :: _ :: _ :: _, _ => simp [mapFrameArgs]
        · simp [isAction]
    | depth, type, .lambda binder body, free => by
      keep_closed_cases (.lambda binder body)
      cases type with
      | arrow domain codomain =>
        dsimp only at free
        rw [mapFrame_lambda data, closedActions.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact closedActions_mapFrame keeps bodyNotData dataSorted dataClosed variableClosed (depth + 1) codomain body free
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, closedActions.eq_def, if_neg data, if_neg occurs]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, closedActions.eq_def, if_neg data, if_neg occurs]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, closedActions.eq_def, if_neg data, if_neg occurs]
    | depth, type, .multiLambda arity binders body, free => by
      keep_closed_cases (.multiLambda arity binders body)
      cases type with
      | arrow domain codomain =>
        dsimp only at free
        rw [mapFrame_multiLambda data, closedActions.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact closedActions_mapFrame keeps bodyNotData dataSorted dataClosed variableClosed (depth + arity) codomain body free
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, closedActions.eq_def, if_neg data, if_neg occurs]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, closedActions.eq_def, if_neg data, if_neg occurs]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, closedActions.eq_def, if_neg data, if_neg occurs]
    | depth, type, .collection kind elements rest, free => by
      keep_closed_cases (.collection kind elements rest)
      dsimp only at free
      cases found : elementType language type kind with
      | none =>
        rw [mapFrame_collection_unknown data found, closedActions.eq_def, if_neg data, if_neg occurs]
        dsimp only
        rw [found]
      | some element =>
        rw [found] at free
        dsimp only at free
        rw [mapFrame_collection data found, closedActions.eq_def, if_neg data, if_neg (by simp [decorated?])]
        dsimp only
        rw [found]
        exact closedActionsList_mapFrame keeps bodyNotData dataSorted dataClosed variableClosed depth element elements free
    | depth, type, .bvar index, free => by
      keep_closed_cases (.bvar index)
      rw [mapFrame_leaf data occurs (.inl ⟨index, rfl⟩), closedActions.eq_def, if_neg data, if_neg occurs]
    | depth, type, .fvar name, free => by
      keep_closed_cases (.fvar name)
      rw [mapFrame_leaf data occurs (.inr (.inl ⟨name, rfl⟩)), closedActions.eq_def, if_neg data, if_neg occurs]
    | depth, type, .subst body replacement, free => by
      keep_closed_cases (.subst body replacement)
      rw [mapFrame_leaf data occurs (.inr (.inr ⟨body, replacement, rfl⟩)), closedActions.eq_def, if_neg data,
        if_neg occurs]
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem closedActionsArgs_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (dataClosed : ∀ depth word, (read decl reading.constant word).isSome →
        (read decl reading.constant (f depth word)).isSome)
      (variableClosed : ∀ depth occurrence, (decorated? decl occurrence).isSome →
        coefficientClosed reading occurrence = true → coefficientClosed reading (v depth occurrence) = true) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        closedActionsArgs language decl reading types arguments = true →
          closedActionsArgs language decl reading types (mapFrameArgs language decl f v depth types arguments) = true
    | depth, type :: types, argument :: arguments, free => by
      rw [closedActionsArgs, Bool.and_eq_true] at free
      rw [mapFrameArgs, closedActionsArgs, Bool.and_eq_true]
      exact ⟨closedActions_mapFrame keeps bodyNotData dataSorted dataClosed variableClosed depth type argument free.1,
        closedActionsArgs_mapFrame keeps bodyNotData dataSorted dataClosed variableClosed depth types arguments free.2⟩
    | depth, [], arguments, _ => by simp [mapFrameArgs, closedActionsArgs]
    | depth, _ :: _, [], _ => by simp [mapFrameArgs, closedActionsArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem closedActionsList_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (dataClosed : ∀ depth word, (read decl reading.constant word).isSome →
        (read decl reading.constant (f depth word)).isSome)
      (variableClosed : ∀ depth occurrence, (decorated? decl occurrence).isSome →
        coefficientClosed reading occurrence = true → coefficientClosed reading (v depth occurrence) = true) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        closedActionsList language decl reading element patterns = true →
          closedActionsList language decl reading element (mapFrameList language decl f v depth element patterns) = true
    | depth, element, [], _ => by rw [mapFrameList, closedActionsList]
    | depth, element, pattern :: patterns, free => by
      rw [closedActionsList, Bool.and_eq_true] at free
      rw [mapFrameList, closedActionsList, Bool.and_eq_true]
      exact ⟨closedActions_mapFrame keeps bodyNotData dataSorted dataClosed variableClosed depth element pattern free.1,
        closedActionsList_mapFrame keeps bodyNotData dataSorted dataClosed variableClosed depth element patterns free.2⟩
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end KeepClosed

/-! ## Settling sees through the frame normal form -/

section SeesThrough

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- The normal form of an occurrence has a word for coefficient. -/
theorem normalVariable_coefficientParses (depth : Nat) {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome) (parses : CoefficientParses reading occurrence) :
    CoefficientParses reading (normalVariable decl reading depth occurrence) := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  intro c v normal
  cases coefficient with
  | none =>
    rw [plain rfl, normalVariable_bare bare, decorated?_action _ _ bare] at normal
    cases normal
    obtain ⟨one, oneParsed, _⟩ := letters_of_read reading.constant _ (reading.read_write 1)
    rw [oneParsed]
    rfl
  | some c₀ =>
    rw [applied c₀ rfl, normalVariable_decorated bare, decorated?_action _ _ bare] at normal
    cases normal
    obtain ⟨c₀Letters, c₀Parsed⟩ := Option.isSome_iff_exists.mp (parses c₀ occurrenceVar found)
    obtain ⟨normal, normalParsed, _⟩ := letters_wordNormal (reading := reading) c₀Parsed
    rw [normalParsed]
    rfl

omit [DecidableEq G] in
/-- Word-formedness gives the parse of the group-action laws. -/
theorem wordsParse_of_wordsAt (depth : Nat) (type : TypeExpr) {pattern : Pattern}
    (words : WordsAt (language := language) reading depth type pattern) : WordsParse language reading type pattern :=
  frameAll_mono (fun _ _ h => h.2) (fun _ _ h => h) 0 type pattern
    (frameAll_and 0 type pattern (frameAll_occurs 0 type pattern) ((wordsAt_depth depth type pattern).mp words))

/-- The value of an occurrence's coefficient: its decoration's, or the unit's. -/
theorem occurrence_value {occurrence : Pattern} (occurs : (decorated? decl occurrence).isSome)
    (parses : CoefficientParses reading occurrence) (depth : Nat) :
    ∃ coefficient found occurrenceVar, normalVariable decl reading depth occurrence =
        .apply decl.action [wordNormal decl reading coefficient, occurrenceVar] ∧
      letters decl reading.constant coefficient = some found ∧ isBare occurrenceVar = true ∧
      (decorated? decl occurrence = some (some coefficient, occurrenceVar) ∨
        (decorated? decl occurrence = some (none, occurrenceVar) ∧ coefficient = reading.write 1)) := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  cases coefficient with
  | none =>
    obtain ⟨one, oneParsed, _⟩ := letters_of_read reading.constant _ (reading.read_write 1)
    refine ⟨reading.write 1, one, occurrenceVar, ?_, oneParsed, bare, .inr ⟨found, rfl⟩⟩
    rw [plain rfl, normalVariable_bare bare, wordNormal_write]
  | some c =>
    obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp (parses c occurrenceVar found)
    exact ⟨c, cLetters, occurrenceVar, by rw [applied c rfl, normalVariable_decorated bare], cParsed, bare,
      .inl found⟩

/-- Two coefficients composed with a closed word, in normal form, when the decorations agree. -/
theorem wordNormal_compose {c c' k k' : Pattern} {cLetters c'Letters kLetters k'Letters : List (Letter G)}
    (cParsed : letters decl reading.constant c = some cLetters) (c'Parsed : letters decl reading.constant c' = some c'Letters)
    (kParsed : letters decl reading.constant k = some kLetters) (k'Parsed : letters decl reading.constant k' = some k'Letters)
    (sameC : evalLetters cLetters = evalLetters c'Letters) (sameK : evalLetters kLetters = evalLetters k'Letters) :
    wordNormal decl reading (mulWord decl c k) = wordNormal decl reading (mulWord decl c' k') :=
  (wordNormal_eq_iff (letters_mulWord cParsed kParsed) (letters_mulWord c'Parsed k'Parsed)).mpr
    (by rw [evalLetters_append, evalLetters_append, sameC, sameK])

omit [DecidableEq G] in
/-- The unit's word evaluates to the unit. -/
theorem write_one_value : ∃ found, letters decl reading.constant (reading.write 1) = some found ∧ evalLetters found = 1 := by
  obtain ⟨found, parsed, value⟩ := letters_of_read reading.constant _ (reading.read_write 1)
  exact ⟨found, parsed, value.trans constEval_one⟩

/-- The settled action node on an occurrence, as a decoration with a word for coefficient whose value is
the coefficient's times the occurrence's. -/
theorem settled_onOccurrence {coefficient : Pattern} {cLetters : List (Letter G)}
    (cParsed : letters decl reading.constant coefficient = some cLetters) {body : Pattern}
    (occurs : (decorated? decl body).isSome) (parses : CoefficientParses reading body) (depth : Nat)
    (bodyType : TypeExpr) :
    ∃ composed composedLetters inner innerLetters occurrenceVar,
      (match decorated? decl body with
        | some (none, occurrenceVar) => Pattern.apply decl.action [coefficient, occurrenceVar]
        | some (some inner, occurrenceVar) => Pattern.apply decl.action [mulWord decl coefficient inner, occurrenceVar]
        | none => frameAct language decl coefficient bodyType body) =
        .apply decl.action [composed, occurrenceVar] ∧
      normalVariable decl reading depth body = .apply decl.action [wordNormal decl reading inner, occurrenceVar] ∧
      letters decl reading.constant composed = some composedLetters ∧
      letters decl reading.constant inner = some innerLetters ∧
      evalLetters composedLetters = evalLetters cLetters * evalLetters innerLetters ∧ isBare occurrenceVar = true := by
  obtain ⟨inner, innerLetters, occurrenceVar, normal, innerParsed, bare, shape⟩ :=
    occurrence_value (reading := reading) occurs parses depth
  rcases shape with decoratedBody | ⟨bareBody, isOne⟩
  · refine ⟨mulWord decl coefficient inner, cLetters ++ innerLetters, inner, innerLetters, occurrenceVar, ?_, normal,
      letters_mulWord cParsed innerParsed, innerParsed, evalLetters_append _ _, bare⟩
    rw [decoratedBody]
  · subst isOne
    obtain ⟨one, oneParsed, oneValue⟩ := write_one_value (reading := reading)
    rw [innerParsed] at oneParsed
    cases oneParsed
    refine ⟨coefficient, cLetters, reading.write 1, innerLetters, occurrenceVar, ?_, normal, cParsed, innerParsed,
      by rw [oneValue, mul_one], bare⟩
    rw [bareBody]

/-- The data and variable branches of the sees-through step; leaves the structural branch with `placed`,
`closed` and `wordsHere` unfolded. -/
syntax "sees_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sees_cases $pattern) => `(tactic| (
      have wordsHere := words
      unfold WordsAt at wordsHere
      unfold normalWalkAt
      by_cases data : type = .base decl.dataSort
      · rw [FrameAll.eq_def, if_pos data] at wordsHere
        obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp wordsHere
        obtain ⟨normal, normalParsed, _⟩ := letters_wordNormal (reading := reading) parsed
        simp only [mapFrame_data data]
        rw [settle_word multiplyNe reading.constant _ normalParsed type,
          settle_word multiplyNe reading.constant _ parsed type, wordNormal_normal]
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [FrameAll.eq_def, if_neg data, if_pos occurs] at wordsHere
        rw [settle_occurrence multiplyNe bodySort reading occurs.1 wordsHere type]
        simp only [mapFrame_variable data occurs]
        rw [settle_occurrence multiplyNe bodySort reading (normalVariable_keeps.occurs depth _ occurs.1)
            (normalVariable_coefficientParses depth occurs.1 wordsHere) type,
          mapFrame_variable data ⟨normalVariable_keeps.occurs depth _ occurs.1, occurs.2⟩,
          normalVariable_idem depth occurs.1]
      rw [FrameAll.eq_def, if_neg data, if_neg occurs] at wordsHere
      rw [actionsAtBody.eq_def, if_neg data, if_neg occurs] at placed
      rw [closedActions.eq_def, if_neg data, if_neg occurs] at closed))

mutual
  /-- **Settling sees through the frame normal form**: normalizing data and decorations before settling
  changes nothing after normalizing again. -/
  theorem normalWalk_settle_normal (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), actionsAtBody language decl type pattern = true →
        closedActions language decl reading type pattern = true →
        WordsAt (language := language) reading depth type pattern →
          normalWalkAt (language := language) reading depth type
              (settle language decl type (normalWalkAt (language := language) reading depth type pattern)) =
            normalWalkAt (language := language) reading depth type (settle language decl type pattern)
    | depth, type, .apply label arguments, placed, closed, words => by
      sees_cases (.apply label arguments)
      have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
      dsimp only at placed closed wordsHere
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at placed
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at closed
      obtain ⟨where_, rest⟩ := placed
      obtain ⟨coefficientClosed, closedRest⟩ := closed
      by_cases isAction : label = decl.action
      · subst isAction
        have atBody := where_.resolve_left (fun h => h rfl)
        have sameType : type = bodyType := Option.some.inj (atBody.1.symm.trans bodySort)
        subst sameType
        obtain ⟨coefficient, body, same⟩ := List.length_eq_two.mp atBody.2
        subst same
        rw [dataSorted] at rest wordsHere closedRest
        dsimp only at rest wordsHere closedRest
        simp only [actionsAtBodyArgs, Bool.and_eq_true, closedActionsArgs] at rest closedRest
        simp only [FrameAllArgs] at wordsHere
        obtain ⟨coefficientWord, bodyWords, _⟩ := wordsHere
        rw [FrameAll.eq_def, if_pos rfl] at coefficientWord
        obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp coefficientWord
        obtain ⟨x, cRead⟩ := Option.isSome_iff_exists.mp
          (coefficientClosed.resolve_left (fun h => h rfl))
        obtain ⟨normalC, normalCParsed, normalCValue⟩ := letters_wordNormal (reading := reading) cParsed
        have normalCRead : read decl reading.constant (wordNormal decl reading coefficient) = some x := by
          rw [wordNormal_closed cRead]
          exact reading.read_write x
        have inductive_ := normalWalk_settle_normal multiplyNe bodyNotData dataSorted bodySort depth type body rest.2.1
          closedRest.2.1 bodyWords
        have wordsSettled := wordsAt_settle multiplyNe bodyNotData dataSorted bodySort depth type body rest.2.1 bodyWords
        have wordsNormalSettled := wordsAt_settle multiplyNe bodyNotData dataSorted bodySort depth type
          (normalWalkAt (language := language) reading depth type body)
          (actionsAtBody_mapFrame normalVariable_keeps bodyNotData depth type body rest.2.1)
          (wordsAt_normalWalk bodyNotData bodySort depth type bodyWords)
        rw [mapFrame_apply_structural data occurs dataSorted]
        simp only [mapFrameArgs, mapFrame_data (rfl : TypeExpr.base decl.dataSort = TypeExpr.base decl.dataSort)]
        rw [settle_actionNode dataSorted, settle_actionNode dataSorted,
          settle_word multiplyNe reading.constant _ normalCParsed, settle_word multiplyNe reading.constant _ cParsed]
        unfold normalWalkAt at inductive_ wordsNormalSettled
        generalize settle language decl type (mapFrame language decl (fun _ datum => wordNormal decl reading datum)
          (normalVariable decl reading) depth type body) = settledNormal at inductive_ wordsNormalSettled ⊢
        generalize settle language decl type body = settled at inductive_ wordsSettled ⊢
        have sameOccurs : (decorated? decl settledNormal).isSome = (decorated? decl settled).isSome := by
          rw [← decorated?_normalWalk (reading := reading) bodyNotData bodySort depth settledNormal,
            ← decorated?_normalWalk (reading := reading) bodyNotData bodySort depth settled]
          unfold normalWalkAt
          rw [inductive_]
        by_cases occurs₀ : (decorated? decl settled).isSome
        · have occurs₁ : (decorated? decl settledNormal).isSome := by rw [sameOccurs]; exact occurs₀
          have parses₀ := wordsSettled
          unfold WordsAt at parses₀
          rw [FrameAll.eq_def, if_neg notData, if_pos ⟨occurs₀, bodySort⟩] at parses₀
          have parses₁ := wordsNormalSettled
          unfold WordsAt at parses₁
          rw [FrameAll.eq_def, if_neg notData, if_pos ⟨occurs₁, bodySort⟩] at parses₁
          obtain ⟨composed₀, composed₀Letters, inner₀, inner₀Letters, var₀, result₀, normal₀, composed₀Parsed,
            inner₀Parsed, composed₀Value, bare₀⟩ := settled_onOccurrence cParsed occurs₀ parses₀ depth type
          obtain ⟨composed₁, composed₁Letters, inner₁, inner₁Letters, var₁, result₁, normal₁, composed₁Parsed,
            inner₁Parsed, composed₁Value, bare₁⟩ :=
            settled_onOccurrence normalCParsed occurs₁ parses₁ depth type
          rw [result₀, result₁]
          rw [mapFrame_variable data ⟨occurs₁, bodySort⟩, mapFrame_variable data ⟨occurs₀, bodySort⟩, normal₀,
            normal₁] at inductive_
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at inductive_
          obtain ⟨sameInner, sameVar⟩ := inductive_
          subst sameVar
          rw [mapFrame_variable data ⟨decorated?_some_of_action _ bare₁, bodySort⟩,
            mapFrame_variable data ⟨decorated?_some_of_action _ bare₁, bodySort⟩, normalVariable_decorated bare₁,
            normalVariable_decorated bare₁]
          have innerValues := (wordNormal_eq_iff inner₁Parsed inner₀Parsed).mp sameInner
          have composedSame : wordNormal decl reading composed₁ = wordNormal decl reading composed₀ :=
            (wordNormal_eq_iff composed₁Parsed composed₀Parsed).mpr
              (by rw [composed₁Value, composed₀Value, normalCValue, innerValues])
          rw [composedSame]
        · have notOccurs₁ : ¬(decorated? decl settledNormal).isSome := by rw [sameOccurs]; exact occurs₀
          rw [Option.not_isSome_iff_eq_none.mp occurs₀, Option.not_isSome_iff_eq_none.mp notOccurs₁]
          dsimp only
          have inductiveNormal : frameNormal language decl reading type settledNormal =
              frameNormal language decl reading type settled := by
            have := inductive_
            rw [← normalWalk_depth (language := language) depth type settledNormal,
              ← normalWalk_depth (language := language) depth type settled]
            exact this
          show normalWalkAt (language := language) reading depth type _ = normalWalkAt (language := language) reading depth type _
          rw [normalWalk_depth, normalWalk_depth,
            ← frameAct_normal bodyNotData normalCRead type settledNormal, inductiveNormal,
            frameAct_normal bodyNotData normalCRead type settled,
            frameAct_congr bodyNotData normalCRead cRead type settled (wordsParse_of_wordsAt depth type wordsSettled)]
      · rw [settle_apply_other isAction]
        cases found : paramTypes language label with
        | none =>
          dsimp only
          rw [mapFrame_apply_unknown data occurs found, settle_apply_other isAction, found]
          dsimp only
          rw [mapFrame_apply_unknown data occurs found]
        | some types =>
          rw [found] at rest closedRest wordsHere
          dsimp only at rest closedRest wordsHere ⊢
          rw [mapFrame_apply_structural data occurs found, settle_apply_other isAction, found]
          dsimp only
          rw [mapFrame_apply_structural data (by rw [decorated?_apply_other isAction]; simp) found,
            mapFrame_apply_structural data (by rw [decorated?_apply_other isAction]; simp) found,
            normalArgs_settle_normal multiplyNe bodyNotData dataSorted bodySort depth types arguments rest closedRest
              wordsHere]
    | depth, type, .lambda binder body, placed, closed, words => by
      sees_cases (.lambda binder body)
      cases type with
      | arrow domain codomain =>
        dsimp only at placed closed wordsHere
        rw [mapFrame_lambda data, settle.eq_def, settle.eq_def]
        dsimp only
        rw [mapFrame_lambda data, mapFrame_lambda data]
        have inner := normalWalk_settle_normal multiplyNe bodyNotData dataSorted bodySort (depth + 1) codomain body placed
          closed wordsHere
        unfold normalWalkAt at inner
        rw [inner]
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, settle.eq_def]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, settle.eq_def]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, settle.eq_def]
    | depth, type, .multiLambda arity binders body, placed, closed, words => by
      sees_cases (.multiLambda arity binders body)
      cases type with
      | arrow domain codomain =>
        dsimp only at placed closed wordsHere
        rw [mapFrame_multiLambda data, settle.eq_def, settle.eq_def]
        dsimp only
        rw [mapFrame_multiLambda data, mapFrame_multiLambda data]
        have inner := normalWalk_settle_normal multiplyNe bodyNotData dataSorted bodySort (depth + arity) codomain body
          placed closed wordsHere
        unfold normalWalkAt at inner
        rw [inner]
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, settle.eq_def]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, settle.eq_def]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, settle.eq_def]
    | depth, type, .collection kind elements rest, placed, closed, words => by
      sees_cases (.collection kind elements rest)
      dsimp only at placed closed wordsHere
      cases found : elementType language type kind with
      | none =>
        rw [mapFrame_collection_unknown data found, settle.eq_def]
      | some element =>
        rw [found] at placed closed wordsHere
        dsimp only at placed closed wordsHere
        rw [mapFrame_collection data found, settle.eq_def, settle.eq_def]
        dsimp only
        rw [found]
        dsimp only
        rw [mapFrame_collection data found, mapFrame_collection data found,
          normalList_settle_normal multiplyNe bodyNotData dataSorted bodySort depth element elements placed closed
            wordsHere]
    | depth, type, .bvar index, placed, closed, words => by
      sees_cases (.bvar index)
      rw [mapFrame_leaf data occurs (.inl ⟨index, rfl⟩), settle_bvar]
    | depth, type, .fvar name, placed, closed, words => by
      sees_cases (.fvar name)
      rw [mapFrame_leaf data occurs (.inr (.inl ⟨name, rfl⟩)), settle_fvar]
    | depth, type, .subst body replacement, placed, closed, words => by
      sees_cases (.subst body replacement)
      rw [mapFrame_leaf data occurs (.inr (.inr ⟨body, replacement, rfl⟩)), settle.eq_def]
  termination_by _ _ pattern _ _ _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem normalArgs_settle_normal (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        actionsAtBodyArgs language decl types arguments = true →
        closedActionsArgs language decl reading types arguments = true →
        FrameAllArgs language decl (fun _ datum => (letters decl reading.constant datum).isSome)
            (fun _ occurrence => CoefficientParses reading occurrence) depth types arguments →
          mapFrameArgs language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth
              types (settleArgs language decl types (mapFrameArgs language decl
                (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth types arguments)) =
            mapFrameArgs language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth
              types (settleArgs language decl types arguments)
    | depth, type :: types, argument :: arguments, placed, closed, words => by
      rw [actionsAtBodyArgs, Bool.and_eq_true] at placed
      rw [closedActionsArgs, Bool.and_eq_true] at closed
      rw [FrameAllArgs] at words
      have head := normalWalk_settle_normal multiplyNe bodyNotData dataSorted bodySort depth type argument placed.1
        closed.1 words.1
      unfold normalWalkAt at head
      rw [mapFrameArgs, settleArgs, mapFrameArgs, settleArgs, mapFrameArgs, head,
        normalArgs_settle_normal multiplyNe bodyNotData dataSorted bodySort depth types arguments placed.2 closed.2 words.2]
    | depth, [], arguments, _, _, _ => by simp [mapFrameArgs, settleArgs]
    | depth, _ :: _, [], _, _, _ => by simp [mapFrameArgs, settleArgs]
  termination_by _ _ arguments _ _ _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem normalList_settle_normal (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        actionsAtBodyList language decl element patterns = true →
        closedActionsList language decl reading element patterns = true →
        FrameAllList language decl (fun _ datum => (letters decl reading.constant datum).isSome)
            (fun _ occurrence => CoefficientParses reading occurrence) depth element patterns →
          mapFrameList language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth
              element (settleList language decl element (mapFrameList language decl
                (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth element patterns)) =
            mapFrameList language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth
              element (settleList language decl element patterns)
    | depth, element, [], _, _, _ => by simp [mapFrameList, settleList]
    | depth, element, pattern :: patterns, placed, closed, words => by
      rw [actionsAtBodyList, Bool.and_eq_true] at placed
      rw [closedActionsList, Bool.and_eq_true] at closed
      rw [FrameAllList] at words
      have head := normalWalk_settle_normal multiplyNe bodyNotData dataSorted bodySort depth element pattern placed.1
        closed.1 words.1
      unfold normalWalkAt at head
      rw [mapFrameList, settleList, mapFrameList, settleList, mapFrameList, head,
        normalList_settle_normal multiplyNe bodyNotData dataSorted bodySort depth element patterns placed.2 closed.2
          words.2]
  termination_by _ _ patterns _ _ _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end SeesThrough

/-! ## Well-formedness through settling and the frame normal form -/

section KeepWell

variable {language : LanguageDef} {decl : OrientationDecl}

/-- The data and variable branches of the step from action-free to placed. -/
syntax "placed_cases" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| placed_cases) => `(tactic| (
      rw [actionFree.eq_def] at free
      rw [actionsAtBody.eq_def]
      split_ifs at free ⊢
      · rfl
      · rfl))

mutual
  /-- An action-free term has every action node at the body sort: it has none. -/
  theorem actionsAtBody_of_actionFree :
      ∀ (type : TypeExpr) (pattern : Pattern), actionFree language decl type pattern = true →
        actionsAtBody language decl type pattern = true
    | type, .apply label arguments, free => by
      placed_cases
      dsimp only at free ⊢
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at free ⊢
      refine ⟨by simp [free.1], ?_⟩
      cases found : paramTypes language label with
      | none => rfl
      | some types =>
        rw [found] at free
        exact actionsAtBodyArgs_of_actionFree types arguments free.2
    | type, .lambda binder body, free => by
      placed_cases
      dsimp only at free ⊢
      cases type with
      | arrow domain codomain => exact actionsAtBody_of_actionFree codomain body free
      | _ => rfl
    | type, .multiLambda arity binders body, free => by
      placed_cases
      dsimp only at free ⊢
      cases type with
      | arrow domain codomain => exact actionsAtBody_of_actionFree codomain body free
      | _ => rfl
    | type, .collection kind elements rest, free => by
      placed_cases
      dsimp only at free ⊢
      cases found : elementType language type kind with
      | none => rfl
      | some element =>
        rw [found] at free
        exact actionsAtBodyList_of_actionFree element elements free
    | type, .bvar index, free => by placed_cases; rfl
    | type, .fvar name, free => by placed_cases; rfl
    | type, .subst body replacement, free => by placed_cases; rfl
  termination_by _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionsAtBodyArgs_of_actionFree :
      ∀ (types : List TypeExpr) (arguments : List Pattern), actionFreeArgs language decl types arguments = true →
        actionsAtBodyArgs language decl types arguments = true
    | type :: types, argument :: arguments, free => by
      rw [actionFreeArgs, Bool.and_eq_true] at free
      rw [actionsAtBodyArgs, Bool.and_eq_true]
      exact ⟨actionsAtBody_of_actionFree type argument free.1, actionsAtBodyArgs_of_actionFree types arguments free.2⟩
    | [], arguments, _ => by rw [actionsAtBodyArgs]
    | _ :: _, [], _ => by rw [actionsAtBodyArgs]
  termination_by _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionsAtBodyList_of_actionFree :
      ∀ (element : TypeExpr) (patterns : List Pattern), actionFreeList language decl element patterns = true →
        actionsAtBodyList language decl element patterns = true
    | element, [], _ => by rw [actionsAtBodyList]
    | element, pattern :: patterns, free => by
      rw [actionFreeList, Bool.and_eq_true] at free
      rw [actionsAtBodyList, Bool.and_eq_true]
      exact ⟨actionsAtBody_of_actionFree element pattern free.1,
        actionsAtBodyList_of_actionFree element patterns free.2⟩
  termination_by _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- **The frame normal form keeps every action coefficient closed.** -/
theorem closedActions_normalWalk (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
    (depth : Nat) (type : TypeExpr) {pattern : Pattern}
    (closed : closedActions language decl reading type pattern = true) :
    closedActions language decl reading type (normalWalkAt (language := language) reading depth type pattern) = true := by
  apply closedActions_mapFrame normalVariable_keeps bodyNotData dataSorted _ _ depth type pattern closed
  · intro _ word readable
    obtain ⟨x, wordRead⟩ := Option.isSome_iff_exists.mp readable
    show (read decl reading.constant (wordNormal decl reading word)).isSome = true
    rw [wordNormal_closed wordRead, reading.read_write]
    rfl
  · intro k occurrence occurs coefficient
    obtain ⟨⟨c, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
    obtain ⟨bare, plain, applied⟩ := decorated?_shape found
    unfold coefficientClosed
    cases c with
    | none =>
      rw [plain rfl, normalVariable_bare bare, decorated?_action _ _ bare]
      dsimp only
      rw [reading.read_write]
      rfl
    | some c =>
      unfold coefficientClosed at coefficient
      rw [found] at coefficient
      dsimp only at coefficient
      obtain ⟨x, cRead⟩ := Option.isSome_iff_exists.mp coefficient
      rw [applied c rfl, normalVariable_decorated bare, decorated?_action _ _ bare]
      dsimp only
      rw [wordNormal_closed cRead, reading.read_write]
      rfl

omit [DecidableEq G] in
theorem coefficientClosed_iff {occurrence : Pattern} :
    coefficientClosed reading occurrence = true ↔ ClosedCoefficients reading occurrence := by
  constructor
  · intro closed c v found
    unfold coefficientClosed at closed
    rw [found] at closed
    exact Option.isSome_iff_exists.mp closed
  · intro closed
    unfold coefficientClosed
    cases found : decorated? decl occurrence with
    | none => rfl
    | some pair =>
      obtain ⟨inner, occurrenceVar⟩ := pair
      cases inner with
      | none => rfl
      | some c =>
        dsimp only
        obtain ⟨y, cRead⟩ := closed c occurrenceVar found
        rw [cRead]
        rfl

omit [DecidableEq G] in
/-- **The action of a closed word keeps every action coefficient closed.** -/
theorem closedActions_frameAct (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
    {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x) (type : TypeExpr) {pattern : Pattern}
    (closed : closedActions language decl reading type pattern = true) :
    closedActions language decl reading type (frameAct language decl g type pattern) = true := by
  apply closedActions_mapFrame (actVariable_keeps g) bodyNotData dataSorted _ _ 0 type pattern closed
  · intro k word readable
    obtain ⟨y, wordRead⟩ := Option.isSome_iff_exists.mp readable
    rw [actData_closed_word gRead wordRead k, read_mulWord gRead wordRead]
    rfl
  · intro k occurrence occurs coefficient
    exact coefficientClosed_iff.mpr
      (actVariable_closedCoefficients gRead k occurs (coefficientClosed_iff.mp coefficient))

/-- The data and variable branches of the closedness-through-settling step; leaves the structural branch
with `placed`, `closed` and `words` unfolded. -/
syntax "closed_settle_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| closed_settle_cases $pattern) => `(tactic| (
      unfold WordsAt at words
      by_cases data : type = .base decl.dataSort
      · rw [closedActions.eq_def, if_pos data]
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · have parses := words
        rw [FrameAll.eq_def, if_neg data, if_pos occurs] at parses
        rw [settle_occurrence multiplyNe bodySort reading occurs.1 parses type]
        exact closed
      rw [actionsAtBody.eq_def, if_neg data, if_neg occurs] at placed
      rw [closedActions.eq_def, if_neg data, if_neg occurs] at closed
      rw [FrameAll.eq_def, if_neg data, if_neg occurs] at words))

omit [DecidableEq G] in
mutual
  /-- **Settling keeps every action coefficient closed.** -/
  theorem closedActions_settle (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), actionsAtBody language decl type pattern = true →
        closedActions language decl reading type pattern = true →
        WordsAt (language := language) reading depth type pattern →
          closedActions language decl reading type (settle language decl type pattern) = true
    | depth, type, .apply label arguments, placed, closed, words => by
      closed_settle_cases (.apply label arguments)
      have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
      dsimp only at placed closed words
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at placed
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at closed
      obtain ⟨where_, rest⟩ := placed
      obtain ⟨coefficientClosed', closedRest⟩ := closed
      by_cases isAction : label = decl.action
      · subst isAction
        have atBody := where_.resolve_left (fun h => h rfl)
        have sameType : type = bodyType := Option.some.inj (atBody.1.symm.trans bodySort)
        subst sameType
        obtain ⟨coefficient, body, same⟩ := List.length_eq_two.mp atBody.2
        subst same
        rw [dataSorted] at rest closedRest words
        dsimp only at rest closedRest words
        simp only [actionsAtBodyArgs, Bool.and_eq_true, closedActionsArgs] at rest closedRest
        simp only [FrameAllArgs] at words
        obtain ⟨coefficientWord, bodyWords, _⟩ := words
        rw [FrameAll.eq_def, if_pos rfl] at coefficientWord
        obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp coefficientWord
        obtain ⟨x, cRead⟩ := Option.isSome_iff_exists.mp (coefficientClosed'.resolve_left (fun h => h rfl))
        have bodyClosed := closedActions_settle multiplyNe bodyNotData dataSorted bodySort depth type body rest.2.1
          closedRest.2.1 bodyWords
        rw [settle_actionNode dataSorted, settle_word multiplyNe reading.constant coefficient cParsed]
        cases settledBody : decorated? decl (settle language decl type body) with
        | none =>
          dsimp only
          exact closedActions_frameAct bodyNotData dataSorted cRead type bodyClosed
        | some pair =>
          obtain ⟨inner, occurrenceVar⟩ := pair
          obtain ⟨bare, _, _⟩ := decorated?_shape settledBody
          have settledOccurs : (decorated? decl (settle language decl type body)).isSome := by rw [settledBody]; rfl
          rw [closedActions.eq_def, if_neg data, if_pos ⟨settledOccurs, atBody.1⟩, settledBody] at bodyClosed
          cases inner with
          | none =>
            dsimp only
            rw [closedActions.eq_def, if_neg data, if_pos ⟨decorated?_some_of_action _ bare, atBody.1⟩,
              decorated?_action _ _ bare]
            dsimp only
            rw [cRead]
            rfl
          | some c =>
            dsimp only at bodyClosed ⊢
            obtain ⟨z, innerRead⟩ := Option.isSome_iff_exists.mp bodyClosed
            rw [closedActions.eq_def, if_neg data, if_pos ⟨decorated?_some_of_action _ bare, atBody.1⟩,
              decorated?_action _ _ bare]
            dsimp only
            rw [read_mulWord cRead innerRead]
            rfl
      · rw [settle_apply_other isAction]
        cases found : paramTypes language label with
        | none =>
          dsimp only
          rw [closedActions.eq_def, if_neg data, if_neg occurs]
          dsimp only
          rw [found]
          simp [isAction]
        | some types =>
          rw [found] at rest closedRest words
          dsimp only at rest closedRest words ⊢
          rw [closedActions.eq_def, if_neg data, if_neg (by rw [decorated?_apply_other isAction]; simp)]
          dsimp only
          rw [found]
          dsimp only
          simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
          exact ⟨.inl isAction, closedActionsArgs_settleArgs multiplyNe bodyNotData dataSorted bodySort depth types
            arguments rest closedRest words⟩
    | depth, type, .lambda binder body, placed, closed, words => by
      closed_settle_cases (.lambda binder body)
      rw [settle.eq_def]
      cases type with
      | arrow domain codomain =>
        dsimp only at placed closed words ⊢
        rw [closedActions.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact closedActions_settle multiplyNe bodyNotData dataSorted bodySort (depth + 1) codomain body placed closed
          words
      | _ =>
        dsimp only
        rw [closedActions.eq_def, if_neg data, if_neg occurs]
    | depth, type, .multiLambda arity binders body, placed, closed, words => by
      closed_settle_cases (.multiLambda arity binders body)
      rw [settle.eq_def]
      cases type with
      | arrow domain codomain =>
        dsimp only at placed closed words ⊢
        rw [closedActions.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact closedActions_settle multiplyNe bodyNotData dataSorted bodySort (depth + arity) codomain body placed
          closed words
      | _ =>
        dsimp only
        rw [closedActions.eq_def, if_neg data, if_neg occurs]
    | depth, type, .collection kind elements rest, placed, closed, words => by
      closed_settle_cases (.collection kind elements rest)
      rw [settle.eq_def]
      dsimp only at placed closed words ⊢
      cases found : elementType language type kind with
      | none =>
        dsimp only
        rw [closedActions.eq_def, if_neg data, if_neg occurs]
        dsimp only
        rw [found]
      | some element =>
        rw [found] at placed closed words
        dsimp only at placed closed words ⊢
        rw [closedActions.eq_def, if_neg data, if_neg (by simp [decorated?])]
        dsimp only
        rw [found]
        exact closedActionsList_settleList multiplyNe bodyNotData dataSorted bodySort depth element elements placed
          closed words
    | depth, type, .bvar index, placed, closed, words => by
      closed_settle_cases (.bvar index)
      rw [settle_bvar, closedActions.eq_def, if_neg data, if_neg occurs]
    | depth, type, .fvar name, placed, closed, words => by
      closed_settle_cases (.fvar name)
      rw [settle_fvar, closedActions.eq_def, if_neg data, if_neg occurs]
    | depth, type, .subst body replacement, placed, closed, words => by
      closed_settle_cases (.subst body replacement)
      rw [settle.eq_def, closedActions.eq_def, if_neg data, if_neg occurs]
  termination_by _ _ pattern _ _ _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem closedActionsArgs_settleArgs (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        actionsAtBodyArgs language decl types arguments = true →
        closedActionsArgs language decl reading types arguments = true →
        FrameAllArgs language decl (fun _ datum => (letters decl reading.constant datum).isSome)
            (fun _ occurrence => CoefficientParses reading occurrence) depth types arguments →
          closedActionsArgs language decl reading types (settleArgs language decl types arguments) = true
    | depth, type :: types, argument :: arguments, placed, closed, words => by
      rw [actionsAtBodyArgs, Bool.and_eq_true] at placed
      rw [closedActionsArgs, Bool.and_eq_true] at closed
      rw [FrameAllArgs] at words
      rw [settleArgs, closedActionsArgs, Bool.and_eq_true]
      exact ⟨closedActions_settle multiplyNe bodyNotData dataSorted bodySort depth type argument placed.1 closed.1
          words.1,
        closedActionsArgs_settleArgs multiplyNe bodyNotData dataSorted bodySort depth types arguments placed.2
          closed.2 words.2⟩
    | depth, [], arguments, _, _, _ => by simp [settleArgs, closedActionsArgs]
    | depth, _ :: _, [], _, _, _ => by simp [settleArgs, closedActionsArgs]
  termination_by _ _ arguments _ _ _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem closedActionsList_settleList (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType])
      (bodySort : actionType language decl = some bodyType) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        actionsAtBodyList language decl element patterns = true →
        closedActionsList language decl reading element patterns = true →
        FrameAllList language decl (fun _ datum => (letters decl reading.constant datum).isSome)
            (fun _ occurrence => CoefficientParses reading occurrence) depth element patterns →
          closedActionsList language decl reading element (settleList language decl element patterns) = true
    | depth, element, [], _, _, _ => by simp [settleList, closedActionsList]
    | depth, element, pattern :: patterns, placed, closed, words => by
      rw [actionsAtBodyList, Bool.and_eq_true] at placed
      rw [closedActionsList, Bool.and_eq_true] at closed
      rw [FrameAllList] at words
      rw [settleList, closedActionsList, Bool.and_eq_true]
      exact ⟨closedActions_settle multiplyNe bodyNotData dataSorted bodySort depth element pattern placed.1 closed.1
          words.1,
        closedActionsList_settleList multiplyNe bodyNotData dataSorted bodySort depth element patterns placed.2
          closed.2 words.2⟩
  termination_by _ _ patterns _ _ _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end KeepWell

end Mettapedia.OSLF.MeTTaIL.Orientation
