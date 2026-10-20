import Mettapedia.OSLF.MeTTaIL.OrientationComm
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# The authored communication

The module writes the reduct of communication with explicit substitutions,
`(a b⁻¹) . (subst (subst ^X.^d.P Q) D)`. Executing them instantiates the body's process variable and
its datum by plain de Bruijn instantiation (`plainContinuation`), which leaves `w . Q` wherever the body
has the decoration `w . X`; settling evaluates these actions. On a settled body and payload this is the
discharging continuation of `OrientationComm` (`settle_plainContinuation`), so the equivariance of
communication holds of the authored reduct.

`settledAt depth type pattern` says what this needs: no action node remains but decorations, and the
walks skip only subterms scoped at their depth (a constructor of unknown parameters, an abstraction at
a type that is not an arrow, an explicit substitution, a variable that is neither a datum nor an
occurrence of the body sort), so that instantiating a variable bound at or outside the depth changes
nothing there. Settling fixes a settled term (`settle_of_settled`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax

/-! ## Settled terms -/

section Settled

variable (language : LanguageDef) (decl : OrientationDecl)

mutual
  /-- **A settled term the walks see whole**, from `depth` binders: no action node but decorations, and
  every subterm the walks skip is scoped at its depth. -/
  def settledAt (depth : Nat) (type : TypeExpr) (pattern : Pattern) : Bool :=
    if type = .base decl.dataSort then true
    else if (decorated? decl pattern).isSome ∧ actionType language decl = some type then true
    else
      match pattern with
      | .apply label arguments =>
          label != decl.action &&
            match paramTypes language label with
            | some types => settledArgsAt depth types arguments
            | none => Pattern.isWellScopedListAt depth arguments
      | .lambda binder body =>
          match type with
          | .arrow _ codomain => settledAt (depth + 1) codomain body
          | _ => (Pattern.lambda binder body).isWellScopedAt depth
      | .multiLambda arity binders body =>
          match type with
          | .arrow _ codomain => settledAt (depth + arity) codomain body
          | _ => (Pattern.multiLambda arity binders body).isWellScopedAt depth
      | .collection kind elements _ =>
          match elementType language type kind with
          | some element => settledListAt depth element elements
          | none => Pattern.isWellScopedListAt depth elements
      | .bvar index => decide (index < depth)
      | .fvar _ => true
      | .subst body replacement => (Pattern.subst body replacement).isWellScopedAt depth
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def settledArgsAt (depth : Nat) : List TypeExpr → List Pattern → Bool
    | type :: types, argument :: arguments =>
        settledAt depth type argument && settledArgsAt depth types arguments
    | [], arguments => Pattern.isWellScopedListAt depth arguments
    | _ :: _, [] => true
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def settledListAt (depth : Nat) (element : TypeExpr) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => settledAt depth element pattern && settledListAt depth element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- **No action node but decorations**: every action node is a decoration on a variable. -/
  def actionFree (type : TypeExpr) (pattern : Pattern) : Bool :=
    if type = .base decl.dataSort then true
    else if (decorated? decl pattern).isSome ∧ actionType language decl = some type then true
    else
      match pattern with
      | .apply label arguments =>
          label != decl.action &&
            match paramTypes language label with
            | some types => actionFreeArgs types arguments
            | none => true
      | .lambda _ body =>
          match type with
          | .arrow _ codomain => actionFree codomain body
          | _ => true
      | .multiLambda _ _ body =>
          match type with
          | .arrow _ codomain => actionFree codomain body
          | _ => true
      | .collection kind elements _ =>
          match elementType language type kind with
          | some element => actionFreeList element elements
          | none => true
      | _ => true
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def actionFreeArgs : List TypeExpr → List Pattern → Bool
    | type :: types, argument :: arguments => actionFree type argument && actionFreeArgs types arguments
    | [], _ => true
    | _ :: _, [] => true
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def actionFreeList (element : TypeExpr) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => actionFree element pattern && actionFreeList element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end Settled

/-! ## Walks that change nothing -/

section Identity

variable {language : LanguageDef} {decl : OrientationDecl}

mutual
  /-- **The walk of identities is the identity.** -/
  theorem mapFrame_identity :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        mapFrame language decl (fun _ x => x) (fun _ x => x) depth type pattern = pattern
    | depth, type, .apply label arguments => by
      rw [mapFrame.eq_def]
      split_ifs
      · rfl
      · rfl
      · dsimp only
        split
        · rw [mapFrameArgs_identity]
        · rfl
    | depth, type, .lambda binder body => by
      rw [mapFrame.eq_def]
      split_ifs
      · rfl
      · rfl
      · dsimp only
        split
        · rw [mapFrame_identity]
        · rfl
    | depth, type, .multiLambda arity binders body => by
      rw [mapFrame.eq_def]
      split_ifs
      · rfl
      · rfl
      · dsimp only
        split
        · rw [mapFrame_identity]
        · rfl
    | depth, type, .collection kind elements rest => by
      rw [mapFrame.eq_def]
      split_ifs
      · rfl
      · rfl
      · dsimp only
        split
        · rw [mapFrameList_identity]
        · rfl
    | depth, type, .bvar index => by
      rw [mapFrame.eq_def]
      split_ifs <;> rfl
    | depth, type, .fvar name => by
      rw [mapFrame.eq_def]
      split_ifs <;> rfl
    | depth, type, .subst body replacement => by
      rw [mapFrame.eq_def]
      split_ifs <;> rfl
  termination_by _ _ pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameArgs_identity :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        mapFrameArgs language decl (fun _ x => x) (fun _ x => x) depth types arguments = arguments
    | depth, type :: types, argument :: arguments => by
      rw [mapFrameArgs, mapFrame_identity, mapFrameArgs_identity]
    | depth, [], arguments => by simp [mapFrameArgs]
    | depth, _ :: _, [] => by simp [mapFrameArgs]
  termination_by _ _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameList_identity :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        mapFrameList language decl (fun _ x => x) (fun _ x => x) depth element patterns = patterns
    | depth, element, [] => by rw [mapFrameList]
    | depth, element, pattern :: patterns => by
      rw [mapFrameList, mapFrame_identity, mapFrameList_identity]
  termination_by _ _ patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- **A walk whose functions fix what they visit fixes the term.** -/
theorem mapFrame_fixed {f v : Nat → Pattern → Pattern} {depth : Nat} {type : TypeExpr} {pattern : Pattern}
    (fixes : FrameAll language decl (fun k x => f k x = x) (fun k x => v k x = x) depth type pattern) :
    mapFrame language decl f v depth type pattern = pattern := by
  rw [mapFrame_congr (f' := fun _ x => x) (v' := fun _ x => x) (fun _ _ same => same) (fun _ _ same => same) depth
    type pattern fixes, mapFrame_identity]

/-- **Instantiating a variable bound at or outside the depth changes nothing in a closed term.** -/
theorem instantiateWalk_closed (replacement : Pattern) (depth : Nat) (type : TypeExpr) {pattern : Pattern}
    (closed : Closed pattern) :
    mapFrame language decl (fun k word => Substitution.instantiateBVarAt k replacement word)
      (fun k occurrence => Substitution.instantiateBVarAt k replacement occurrence) depth type pattern = pattern := by
  apply mapFrame_fixed
  have atDepth := (frameAll_shift (language := language) (decl := decl)
    (dataOk := fun k word => Substitution.instantiateBVarAt k replacement word = word)
    (variableOk := fun k occurrence => Substitution.instantiateBVarAt k replacement occurrence = occurrence)
    depth 0 type pattern).mpr
    (frameAll_mono
      (fun j _ inScope => Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt
        (ScopedPattern.isWellScopedAt_mono inScope (by omega)))
      (fun j _ inScope => Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt
        (ScopedPattern.isWellScopedAt_mono inScope (by omega)))
      0 type pattern (scopedAll_of_scoped (language := language) (decl := decl) 0 type pattern closed))
  rwa [Nat.zero_add] at atDepth

end Identity

/-! ## Settling fixes settled terms -/

section Settle

variable {language : LanguageDef} {decl : OrientationDecl}

theorem settle_bvar (type : TypeExpr) (index : Nat) :
    settle language decl type (.bvar index) = .bvar index := by
  rw [settle.eq_def]

theorem settle_fvar (type : TypeExpr) (name : String) :
    settle language decl type (.fvar name) = .fvar name := by
  rw [settle.eq_def]

theorem settle_bare {occurrenceVar : Pattern} (bare : isBare occurrenceVar = true) (type : TypeExpr) :
    settle language decl type occurrenceVar = occurrenceVar := by
  match occurrenceVar, bare with
  | .bvar index, _ => exact settle_bvar type index
  | .fvar name, _ => exact settle_fvar type name

/-- Settling the arguments fixes arguments that settling fixes at every type. -/
theorem settleArgs_fixed :
    ∀ (types : List TypeExpr) (arguments : List Pattern),
      (∀ argument ∈ arguments, ∀ type, settle language decl type argument = argument) →
        settleArgs language decl types arguments = arguments
  | type :: types, argument :: arguments, fixes => by
    rw [settleArgs, fixes argument (List.mem_cons_self ..) type,
      settleArgs_fixed types arguments (fun other member => fixes other (List.mem_cons_of_mem _ member))]
  | [], arguments, _ => by simp [settleArgs]
  | _ :: _, [], _ => by simp [settleArgs]

/-- A constructor node whose arguments settling fixes, and which is not an action node of two
arguments, is fixed by settling. -/
theorem settle_apply_fixed {type : TypeExpr} {label : String} {arguments : List Pattern}
    (fixes : ∀ argument ∈ arguments, ∀ type, settle language decl type argument = argument)
    (notPair : label = decl.action → arguments.length ≠ 2) :
    settle language decl type (.apply label arguments) = .apply label arguments := by
  rw [settle.eq_def]
  dsimp only
  split
  · rename_i types _
    rw [settleArgs_fixed types arguments fixes]
    split_ifs with isAction
    · have lengthNe := notPair isAction
      match arguments, lengthNe with
      | [], _ => rfl
      | [_], _ => rfl
      | _ :: _ :: _ :: _, _ => rfl
      | [_, _], lengthNe => exact absurd rfl lengthNe
    · rfl
  · rfl

variable {G : Type} [Group G]

/-- **Settling fixes a data word**, when multiplication is not the action. -/
theorem settle_word (multiplyNe : decl.multiply ≠ decl.action) (constant : String → Option G) :
    ∀ (word : Pattern) {found : List (Letter G)}, letters decl constant word = some found →
      ∀ type, settle language decl type word = word
  | .bvar index, _, _, type => settle_bvar type index
  | .fvar name, _, _, type => settle_fvar type name
  | .apply label [], _, _, type =>
    settle_apply_fixed (fun _ member => by cases member) (fun _ => by simp)
  | .apply label [argument], found, parsed, type => by
    rw [letters] at parsed
    split at parsed
    · obtain ⟨inner, innerParsed, _⟩ := Option.map_eq_some_iff.mp parsed
      have fixed := settle_word multiplyNe constant argument innerParsed
      exact settle_apply_fixed (fun other member => by
        rw [List.mem_singleton] at member
        subst member
        exact fixed) (fun _ => by simp)
    · cases parsed
  | .apply label [left, right], found, parsed, type => by
    rw [letters] at parsed
    split at parsed
    · rename_i isMultiply
      split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        have leftFixed := settle_word multiplyNe constant left leftParsed
        have rightFixed := settle_word multiplyNe constant right rightParsed
        exact settle_apply_fixed (fun other member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact leftFixed
          · exact rightFixed) (fun isAction => absurd (isMultiply.symm.trans isAction) multiplyNe)
      · cases parsed
    · cases parsed
  | .apply label (_ :: _ :: _ :: _), found, parsed, type => by simp [letters] at parsed
  | .lambda _ _, found, parsed, type => by simp [letters] at parsed
  | .multiLambda _ _ _, found, parsed, type => by simp [letters] at parsed
  | .subst _ _, found, parsed, type => by simp [letters] at parsed
  | .collection _ _ _, found, parsed, type => by simp [letters] at parsed
termination_by word => sizeOf word
decreasing_by all_goals sizeOf_pattern_dec

omit [Group G] in
/-- The action's declared parameters: a datum and the body sort. -/
theorem paramTypes_action {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) :
    ∃ dataType, paramTypes language decl.action = some [dataType, bodyType] := by
  unfold actionType at bodySort
  split at bodySort
  · rename_i dataType body found
    cases bodySort
    exact ⟨dataType, found⟩
  · cases bodySort

/-- **Settling fixes a decoration** whose coefficient is a data word. -/
theorem settle_decoration (multiplyNe : decl.multiply ≠ decl.action) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) (reading : DataReading decl G) {coefficient occurrenceVar : Pattern}
    {found : List (Letter G)} (parsed : letters decl reading.constant coefficient = some found)
    (bare : isBare occurrenceVar = true) (type : TypeExpr) :
    settle language decl type (.apply decl.action [coefficient, occurrenceVar]) =
      .apply decl.action [coefficient, occurrenceVar] := by
  obtain ⟨dataType, found⟩ := paramTypes_action bodySort
  rw [settle.eq_def]
  dsimp only
  rw [found]
  dsimp only
  rw [if_pos rfl]
  simp only [settleArgs, settle_word multiplyNe reading.constant coefficient parsed, settle_bare bare]
  rw [decorated?_of_bare bare]

/-- **Settling fixes an occurrence** whose coefficient is a data word. -/
theorem settle_occurrence (multiplyNe : decl.multiply ≠ decl.action) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) (reading : DataReading decl G) {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome) (parses : CoefficientParses reading occurrence) (type : TypeExpr) :
    settle language decl type occurrence = occurrence := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  cases coefficient with
  | none =>
    rw [plain rfl]
    exact settle_bare bare type
  | some c =>
    obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp (parses c occurrenceVar found)
    rw [applied c rfl]
    exact settle_decoration multiplyNe bodySort reading cParsed bare type

/-- What settling a settled term asks of its data and decorations: they are data words. -/
abbrev WordsAt (reading : DataReading decl G) (depth : Nat) (type : TypeExpr) (pattern : Pattern) : Prop :=
  FrameAll language decl (fun _ datum => (letters decl reading.constant datum).isSome)
    (fun _ occurrence => CoefficientParses reading occurrence) depth type pattern

/-- The data and variable branches of a settling step; leaves the structural branch with `settled` and
`words` unfolded. -/
syntax "settled_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| settled_cases $pattern) => `(tactic| (
      unfold WordsAt at words
      by_cases data : type = .base decl.dataSort
      · rw [FrameAll.eq_def, if_pos data] at words
        obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp words
        exact settle_word multiplyNe reading.constant _ parsed type
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [FrameAll.eq_def, if_neg data, if_pos occurs] at words
        exact settle_occurrence multiplyNe bodySort reading occurs.1 words type
      rw [actionFree.eq_def, if_neg data, if_neg occurs] at settled
      rw [FrameAll.eq_def, if_neg data, if_neg occurs] at words))

mutual
  /-- **Settling fixes an action-free term** whose data and decorations are words. -/
  theorem settle_of_actionFree (multiplyNe : decl.multiply ≠ decl.action) {bodyType : TypeExpr}
      (bodySort : actionType language decl = some bodyType) (reading : DataReading decl G) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), actionFree language decl type pattern = true →
        WordsAt (language := language) reading depth type pattern → settle language decl type pattern = pattern
    | depth, type, .apply label arguments, settled, words => by
      settled_cases (.apply label arguments)
      dsimp only at settled words
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at settled
      obtain ⟨notAction, rest⟩ := settled
      rw [settle.eq_def]
      dsimp only
      cases found : paramTypes language label with
      | none => rfl
      | some types =>
        rw [found] at rest words
        dsimp only at rest words ⊢
        rw [if_neg notAction, settleArgs_of_actionFree multiplyNe bodySort reading depth types arguments rest words]
    | depth, type, .lambda binder body, settled, words => by
      settled_cases (.lambda binder body)
      rw [settle.eq_def]
      cases type with
      | arrow domain codomain =>
        dsimp only at settled words ⊢
        rw [settle_of_actionFree multiplyNe bodySort reading (depth + 1) codomain body settled words]
      | _ => rfl
    | depth, type, .multiLambda arity binders body, settled, words => by
      settled_cases (.multiLambda arity binders body)
      rw [settle.eq_def]
      cases type with
      | arrow domain codomain =>
        dsimp only at settled words ⊢
        rw [settle_of_actionFree multiplyNe bodySort reading (depth + arity) codomain body settled words]
      | _ => rfl
    | depth, type, .collection kind elements rest, settled, words => by
      settled_cases (.collection kind elements rest)
      rw [settle.eq_def]
      dsimp only at settled words ⊢
      cases found : elementType language type kind with
      | none => rfl
      | some element =>
        rw [found] at settled words
        dsimp only at settled words ⊢
        rw [settleList_of_actionFree multiplyNe bodySort reading depth element elements settled words]
    | depth, type, .bvar index, settled, words => settle_bvar type index
    | depth, type, .fvar name, settled, words => settle_fvar type name
    | depth, type, .subst body replacement, settled, words => by rw [settle.eq_def]
  termination_by _ _ pattern _ _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem settleArgs_of_actionFree (multiplyNe : decl.multiply ≠ decl.action) {bodyType : TypeExpr}
      (bodySort : actionType language decl = some bodyType) (reading : DataReading decl G) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        actionFreeArgs language decl types arguments = true →
          FrameAllArgs language decl (fun _ datum => (letters decl reading.constant datum).isSome)
            (fun _ occurrence => CoefficientParses reading occurrence) depth types arguments →
            settleArgs language decl types arguments = arguments
    | depth, type :: types, argument :: arguments, settled, words => by
      rw [actionFreeArgs, Bool.and_eq_true] at settled
      rw [FrameAllArgs] at words
      rw [settleArgs, settle_of_actionFree multiplyNe bodySort reading depth type argument settled.1 words.1,
        settleArgs_of_actionFree multiplyNe bodySort reading depth types arguments settled.2 words.2]
    | depth, [], arguments, _, _ => by simp [settleArgs]
    | depth, _ :: _, [], _, _ => by simp [settleArgs]
  termination_by _ _ arguments _ _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem settleList_of_actionFree (multiplyNe : decl.multiply ≠ decl.action) {bodyType : TypeExpr}
      (bodySort : actionType language decl = some bodyType) (reading : DataReading decl G) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        actionFreeList language decl element patterns = true →
          FrameAllList language decl (fun _ datum => (letters decl reading.constant datum).isSome)
            (fun _ occurrence => CoefficientParses reading occurrence) depth element patterns →
            settleList language decl element patterns = patterns
    | depth, element, [], _, _ => by rw [settleList]
    | depth, element, pattern :: patterns, settled, words => by
      rw [actionFreeList, Bool.and_eq_true] at settled
      rw [FrameAllList] at words
      rw [settleList, settle_of_actionFree multiplyNe bodySort reading depth element pattern settled.1 words.1,
        settleList_of_actionFree multiplyNe bodySort reading depth element patterns settled.2 words.2]
  termination_by _ _ patterns _ _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end


/-- The data and variable branches of a step from settled to action-free. -/
syntax "free_cases" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| free_cases) => `(tactic| (
      rw [settledAt.eq_def] at settled
      rw [actionFree.eq_def]
      split_ifs at settled ⊢
      · rfl
      · rfl))

mutual
  /-- A settled term is action-free. -/
  theorem actionFree_of_settled :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), settledAt language decl depth type pattern = true →
        actionFree language decl type pattern = true
    | depth, type, .apply label arguments, settled => by
      free_cases
      dsimp only at settled ⊢
      simp only [Bool.and_eq_true] at settled ⊢
      refine ⟨settled.1, ?_⟩
      cases found : paramTypes language label with
      | none => rfl
      | some types =>
        rw [found] at settled
        exact actionFreeArgs_of_settled depth types arguments settled.2
    | depth, type, .lambda binder body, settled => by
      free_cases
      dsimp only at settled ⊢
      cases type with
      | arrow domain codomain => exact actionFree_of_settled (depth + 1) codomain body settled
      | _ => rfl
    | depth, type, .multiLambda arity binders body, settled => by
      free_cases
      dsimp only at settled ⊢
      cases type with
      | arrow domain codomain => exact actionFree_of_settled (depth + arity) codomain body settled
      | _ => rfl
    | depth, type, .collection kind elements rest, settled => by
      free_cases
      dsimp only at settled ⊢
      cases found : elementType language type kind with
      | none => rfl
      | some element =>
        rw [found] at settled
        exact actionFreeList_of_settled depth element elements settled
    | depth, type, .bvar index, settled => by free_cases; rfl
    | depth, type, .fvar name, settled => by free_cases; rfl
    | depth, type, .subst body replacement, settled => by free_cases; rfl
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionFreeArgs_of_settled :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        settledArgsAt language decl depth types arguments = true → actionFreeArgs language decl types arguments = true
    | depth, type :: types, argument :: arguments, settled => by
      rw [settledArgsAt, Bool.and_eq_true] at settled
      rw [actionFreeArgs, Bool.and_eq_true]
      exact ⟨actionFree_of_settled depth type argument settled.1,
        actionFreeArgs_of_settled depth types arguments settled.2⟩
    | depth, [], arguments, _ => by rw [actionFreeArgs]
    | depth, _ :: _, [], _ => by rw [actionFreeArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem actionFreeList_of_settled :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        settledListAt language decl depth element patterns = true →
          actionFreeList language decl element patterns = true
    | depth, element, [], _ => by rw [actionFreeList]
    | depth, element, pattern :: patterns, settled => by
      rw [settledListAt, Bool.and_eq_true] at settled
      rw [actionFreeList, Bool.and_eq_true]
      exact ⟨actionFree_of_settled depth element pattern settled.1,
        actionFreeList_of_settled depth element patterns settled.2⟩
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- **Settling fixes a settled term.** -/
theorem settle_of_settled (multiplyNe : decl.multiply ≠ decl.action) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) (reading : DataReading decl G) (depth : Nat)
    (type : TypeExpr) (pattern : Pattern) (settled : settledAt language decl depth type pattern = true)
    (words : WordsAt (language := language) reading depth type pattern) : settle language decl type pattern = pattern :=
  settle_of_actionFree multiplyNe bodySort reading depth type pattern (actionFree_of_settled depth type pattern settled)
    words
end Settle

/-! ## The authored continuation, settled -/

section Authored

variable {language : LanguageDef} {decl : OrientationDecl}

/-- Instantiating the variable one level out by the payload, then the variable of the level by the
datum: the module's two explicit substitutions, `depth` binders inside the body. -/
def instantiateTwice (payload datum : Pattern) (depth : Nat) (pattern : Pattern) : Pattern :=
  Substitution.instantiateBVarAt depth datum (Substitution.instantiateBVarAt (depth + 1) payload pattern)

/-- **The authored continuation**: the receive's body with its process variable and its datum
instantiated as the module's explicit substitutions execute. -/
def plainContinuation (body payload datum : Pattern) : Pattern :=
  instantiateTwice payload datum 0 body

theorem instantiateTwice_apply (payload datum : Pattern) (depth : Nat) (label : String) (arguments : List Pattern) :
    instantiateTwice payload datum depth (.apply label arguments) =
      .apply label (arguments.map (instantiateTwice payload datum depth)) := by
  simp only [instantiateTwice, Substitution.instantiateBVarAt, List.map_map]
  rfl

theorem instantiateTwice_lambda (payload datum : Pattern) (depth : Nat) (binder : Option String) (body : Pattern) :
    instantiateTwice payload datum depth (.lambda binder body) =
      .lambda binder (instantiateTwice payload datum (depth + 1) body) := by
  simp only [instantiateTwice, Substitution.instantiateBVarAt]

theorem instantiateTwice_multiLambda (payload datum : Pattern) (depth arity : Nat) (binders : List String)
    (body : Pattern) :
    instantiateTwice payload datum depth (.multiLambda arity binders body) =
      .multiLambda arity binders (instantiateTwice payload datum (depth + arity) body) := by
  simp only [instantiateTwice, Substitution.instantiateBVarAt, show depth + 1 + arity = depth + arity + 1 by omega]

theorem instantiateTwice_collection (payload datum : Pattern) (depth : Nat) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    instantiateTwice payload datum depth (.collection kind elements rest) =
      .collection kind (elements.map (instantiateTwice payload datum depth)) rest := by
  simp only [instantiateTwice, Substitution.instantiateBVarAt, List.map_map]
  rfl

theorem instantiateTwice_scoped (payload datum : Pattern) {depth : Nat} {pattern : Pattern}
    (inScope : pattern.isWellScopedAt depth = true) : instantiateTwice payload datum depth pattern = pattern := by
  unfold instantiateTwice
  rw [Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt
      (ScopedPattern.isWellScopedAt_mono inScope (Nat.le_succ depth)),
    Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt inScope]

theorem instantiateTwice_scopedList (payload datum : Pattern) {depth : Nat} :
    ∀ {patterns : List Pattern}, Pattern.isWellScopedListAt depth patterns = true →
      patterns.map (instantiateTwice payload datum depth) = patterns
  | [], _ => rfl
  | pattern :: patterns, inScope => by
    simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
    rw [List.map_cons, instantiateTwice_scoped payload datum inScope.1,
      instantiateTwice_scopedList payload datum inScope.2]

theorem settle_apply_other {type : TypeExpr} {label : String} {arguments : List Pattern}
    (other : label ≠ decl.action) :
    settle language decl type (.apply label arguments) =
      match paramTypes language label with
      | some types => .apply label (settleArgs language decl types arguments)
      | none => .apply label arguments := by
  rw [settle.eq_def]
  dsimp only
  cases found : paramTypes language label with
  | none => rfl
  | some types =>
    dsimp only
    rw [if_neg other]

variable {G : Type} [Group G] {reading : DataReading decl G}

mutual
  /-- (FRAME) from no binder renames nothing. -/
  theorem frameWord_zero (g : Pattern) : ∀ word : Pattern, frameWord decl g 0 word = word
    | .bvar index => by simp [frameWord]
    | .fvar name => by simp [frameWord]
    | .apply label arguments => by rw [frameWord, frameWords_zero g arguments]
    | .lambda binder body => by simp [frameWord]
    | .multiLambda arity binders body => by simp [frameWord]
    | .subst body replacement => by simp [frameWord]
    | .collection kind elements rest => by simp [frameWord]

  theorem frameWords_zero (g : Pattern) : ∀ words : List Pattern, frameWords decl g 0 words = words
    | [] => by rw [frameWords]
    | word :: words => by rw [frameWords, frameWord_zero g word, frameWords_zero g words]
end

/-- **Settling an action node is the frame-normal action of its coefficient on the settled body**: on a
variable both are a decoration, and on a decoration both compose. -/
theorem settle_action (multiplyNe : decl.multiply ≠ decl.action)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) {coefficient : Pattern} {found : List (Letter G)}
    (coefficientParsed : letters decl reading.constant coefficient = some found) (body : Pattern) (type : TypeExpr) :
    settle language decl type (.apply decl.action [coefficient, body]) =
      frameAct language decl coefficient bodyType (settle language decl bodyType body) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  obtain ⟨dataType, actionTypes⟩ := paramTypes_action bodySort
  have coefficientLift : Substitution.liftBVars 0 0 coefficient = coefficient :=
    Substitution.liftBVars_zero coefficient 0
  rw [settle.eq_def]
  dsimp only
  rw [actionTypes]
  dsimp only
  rw [if_pos rfl]
  simp only [settleArgs, settle_word multiplyNe reading.constant coefficient coefficientParsed]
  generalize settle language decl bodyType body = settled
  cases decoratedSettled : decorated? decl settled with
  | none => rfl
  | some pair =>
    obtain ⟨inner, occurrenceVar⟩ := pair
    obtain ⟨bare, plain, applied⟩ := decorated?_shape decoratedSettled
    have occurs : (decorated? decl settled).isSome := by rw [decoratedSettled]; rfl
    unfold frameAct
    rw [mapFrame_variable notData ⟨occurs, bodySort⟩]
    cases inner with
    | none =>
      have same := plain rfl
      subst same
      match settled, bare with
      | .fvar name, _ =>
        dsimp only
        rw [actVariable_bare_free, coefficientLift]
      | .bvar index, _ =>
        dsimp only
        rw [actVariable_bare_outside _ (Nat.not_lt_zero index), coefficientLift]
    | some c =>
      have same := applied c rfl
      subst same
      match occurrenceVar, bare with
      | .fvar name, _ =>
        dsimp only
        rw [actVariable_decorated_free]
        unfold actData
        rw [coefficientLift]
        dsimp only
        rw [frameWord_zero]
      | .bvar index, _ =>
        dsimp only
        rw [actVariable_decorated_outside _ _ (Nat.not_lt_zero index)]
        unfold actData
        rw [coefficientLift]
        dsimp only
        rw [frameWord_zero]

/-- At a data position the instantiated word is a word, which settling fixes. -/
theorem settle_twice_data (multiplyNe : decl.multiply ≠ decl.action) (payload : Pattern) {datum : Pattern} {y : G}
    (datumRead : read decl reading.constant datum = some y) {depth : Nat} {word : Pattern}
    (ready : ∃ found, letters decl reading.constant word = some found ∧ LevelFree (depth + 1) found)
    (type : TypeExpr) :
    settle language decl type (instantiateTwice payload datum depth word) = instantiateTwice payload datum depth word := by
  obtain ⟨found, parsed, free⟩ := ready
  obtain ⟨once, onceParsed, _⟩ := letters_instantiate (read_unitWord (reading := reading)) (depth + 1) word parsed
  obtain ⟨twice, twiceParsed, _⟩ := letters_instantiate datumRead depth _ onceParsed
  unfold instantiateTwice
  rw [instantiate_levelFree (depth + 1) payload (unitWord (decl := decl)) word parsed free]
  exact settle_word multiplyNe reading.constant _ twiceParsed type

/-- **At an occurrence, the settled plain instantiation is the discharging one, followed by the
datum's.** -/
theorem settle_twice_occurrence (multiplyNe : decl.multiply ≠ decl.action)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) {payload datum : Pattern}
    (payloadReady : PayloadReady (language := language) reading bodyType payload)
    (payloadFixed : settle language decl bodyType payload = payload) {depth : Nat} {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome) (closed : ClosedCoefficients reading occurrence)
    (notDatum : NotVariable decl depth occurrence) :
    settle language decl bodyType (instantiateTwice payload datum depth occurrence) =
      mapFrame language decl (fun k word => Substitution.instantiateBVarAt k datum word)
        (fun k other => Substitution.instantiateBVarAt k datum other) depth bodyType
        (instVariable language decl bodyType payload (depth + 1) occurrence) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  have payloadLift : Substitution.liftBVars 0 (depth + 1) payload = payload :=
    Substitution.liftBVars_eq_self_of_isWellScopedAt payloadReady.1
  have payloadInst : Substitution.instantiateBVarAt depth datum payload = payload :=
    Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt
      (ScopedPattern.isWellScopedAt_mono payloadReady.1 (Nat.zero_le depth))
  have atBVar : ∀ index, mapFrame language decl (fun k word => Substitution.instantiateBVarAt k datum word)
      (fun k other => Substitution.instantiateBVarAt k datum other) depth bodyType (.bvar index) =
        Substitution.instantiateBVarAt depth datum (.bvar index) := fun index =>
    mapFrame_variable notData ⟨rfl, bodySort⟩
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have variableNe := notDatum _ _ found
  cases coefficient with
  | none =>
    rw [plain rfl]
    match occurrenceVar, bare, variableNe with
    | .bvar index, _, notSame =>
      have indexNe : index ≠ depth := fun same => notSame (by rw [same])
      rw [instVariable_bare]
      by_cases level : index = depth + 1
      · subst level
        rw [if_pos rfl, payloadLift, instantiateWalk_closed datum depth bodyType payloadReady.1]
        simp only [instantiateTwice, Substitution.instantiateBVarAt, Nat.lt_irrefl, if_false, if_true, payloadLift,
          payloadInst]
        exact payloadFixed
      · rw [if_neg level]
        by_cases above : depth + 1 < index
        · rw [if_pos above, atBVar]
          have notBelow : ¬index < depth + 1 := by omega
          have notBelow' : ¬index - 1 < depth := by omega
          have notSame' : index - 1 ≠ depth := by omega
          simp only [instantiateTwice, Substitution.instantiateBVarAt, notBelow, level, notBelow', notSame',
            if_false]
          exact settle_bvar _ _
        · rw [if_neg above, atBVar]
          have below : index < depth := by omega
          have below' : index < depth + 1 := by omega
          simp only [instantiateTwice, Substitution.instantiateBVarAt, below, below', if_true]
          exact settle_bvar _ _
    | .fvar name, _, _ =>
      rw [instVariable_free, mapFrame_variable notData ⟨rfl, bodySort⟩]
      simp only [instantiateTwice, Substitution.instantiateBVarAt]
      exact settle_fvar _ _
  | some c =>
    rw [applied c rfl]
    obtain ⟨z, cRead⟩ := closed c occurrenceVar found
    obtain ⟨cLetters, cParsed, _⟩ := letters_of_read reading.constant c cRead
    have cTwice : instantiateTwice payload datum depth c = c := instantiateTwice_scoped payload datum (read_scoped cRead depth)
    have cInst : ∀ k (replacement : Pattern), Substitution.instantiateBVarAt k replacement c = c := fun k _ =>
      Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped cRead k)
    rw [instantiateTwice_apply]
    simp only [List.map_cons, List.map_nil, cTwice]
    match occurrenceVar, bare, variableNe with
    | .bvar index, _, notSame =>
      have indexNe : index ≠ depth := fun same => notSame (by rw [same])
      rw [instVariable_decorated, cInst]
      by_cases level : index = depth + 1
      · subst level
        rw [if_pos rfl, payloadLift,
          instantiateWalk_closed datum depth bodyType (frameAct_closed cRead bodyType payloadReady.1)]
        simp only [instantiateTwice, Substitution.instantiateBVarAt, Nat.lt_irrefl, if_false, if_true, payloadLift,
          payloadInst]
        rw [settle_action multiplyNe bodyNotData bodySort cParsed payload bodyType, payloadFixed]
      · rw [if_neg level]
        by_cases above : depth + 1 < index
        · rw [if_pos above, mapFrame_variable notData ⟨decorated?_some_of_action c rfl, bodySort⟩]
          have notBelow : ¬index < depth + 1 := by omega
          have notBelow' : ¬index - 1 < depth := by omega
          have notSame' : index - 1 ≠ depth := by omega
          simp only [instantiateTwice, Substitution.instantiateBVarAt, notBelow, level, notBelow', notSame',
            if_false, List.map_cons, List.map_nil, cInst]
          exact settle_decoration multiplyNe bodySort reading cParsed rfl _
        · rw [if_neg above, mapFrame_variable notData ⟨decorated?_some_of_action c rfl, bodySort⟩]
          have below : index < depth := by omega
          have below' : index < depth + 1 := by omega
          simp only [instantiateTwice, Substitution.instantiateBVarAt, below, below', if_true, List.map_cons,
            List.map_nil, cInst]
          exact settle_decoration multiplyNe bodySort reading cParsed rfl _
    | .fvar name, _, _ =>
      rw [instVariable_decorated_free, cInst, mapFrame_variable notData ⟨decorated?_some_of_action c rfl, bodySort⟩]
      simp only [instantiateTwice, Substitution.instantiateBVarAt, List.map_cons, List.map_nil, cInst]
      exact settle_decoration multiplyNe bodySort reading cParsed rfl _

/-- What the authored continuation asks of the body, at the binder depth of its datum: data are words
without the process variable, decorations have closed coefficients, and no occurrence is the datum. -/
abbrev BodyAt (reading : DataReading decl G) (depth : Nat) (type : TypeExpr) (body : Pattern) : Prop :=
  FrameAll language decl
    (fun j datum => ∃ found, letters decl reading.constant datum = some found ∧ LevelFree (j + 1) found)
    (fun j occurrence => (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence ∧
      NotVariable decl j occurrence)
    depth type body

/-- The fused walk of the discharging continuation: at data both instantiations, at an occurrence the
process variable's and then the datum's walk. -/
abbrev twiceVariable (bodyType : TypeExpr) (payload datum : Pattern) (depth : Nat) (occurrence : Pattern) : Pattern :=
  mapFrame language decl (fun k word => Substitution.instantiateBVarAt k datum word)
    (fun k other => Substitution.instantiateBVarAt k datum other) depth bodyType
    (instVariable language decl bodyType payload (depth + 1) occurrence)

/-- The data and variable branches of the authored-continuation induction; leaves the structural branch
with `settled` and `ready` unfolded. -/
syntax "twice_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| twice_cases $pattern) => `(tactic| (
      unfold BodyAt at ready
      by_cases data : type = .base decl.dataSort
      · rw [mapFrame_data data]
        rw [FrameAll.eq_def, if_pos data] at ready
        exact settle_twice_data multiplyNe payload datumRead ready type
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · have sameType : type = bodyType := Option.some.inj (occurs.2.symm.trans bodySort)
        rw [mapFrame_variable data occurs]
        rw [FrameAll.eq_def, if_neg data, if_pos occurs] at ready
        rw [sameType]
        exact settle_twice_occurrence multiplyNe bodyNotData bodySort payloadReady payloadFixed occurs.1 ready.2.1
          ready.2.2
      rw [settledAt.eq_def, if_neg data, if_neg occurs] at settled
      rw [FrameAll.eq_def, if_neg data, if_neg occurs] at ready))

mutual
  /-- **Settling the plain instantiation is the fused discharging walk**, on a settled body. -/
  theorem settle_twice (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (bodySort : actionType language decl = some bodyType) {payload datum : Pattern} {y : G}
      (datumRead : read decl reading.constant datum = some y)
      (payloadReady : PayloadReady (language := language) reading bodyType payload)
      (payloadFixed : settle language decl bodyType payload = payload) :
      ∀ (depth : Nat) (type : TypeExpr) (body : Pattern), settledAt language decl depth type body = true →
        BodyAt (language := language) reading depth type body →
          settle language decl type (instantiateTwice payload datum depth body) =
            mapFrame language decl (fun k word => instantiateTwice payload datum k word)
              (twiceVariable (language := language) (decl := decl) bodyType payload datum) depth type body
    | depth, type, .apply label arguments, settled, ready => by
      twice_cases (.apply label arguments)
      dsimp only at settled ready
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at settled
      obtain ⟨notAction, rest⟩ := settled
      rw [instantiateTwice_apply, settle_apply_other notAction]
      cases found : paramTypes language label with
      | none =>
        rw [found] at rest
        dsimp only at rest ⊢
        rw [mapFrame_apply_unknown data occurs found, instantiateTwice_scopedList payload datum rest]
      | some types =>
        rw [found] at rest ready
        dsimp only at rest ready ⊢
        rw [mapFrame_apply_structural data occurs found,
          settleArgs_twice multiplyNe bodyNotData bodySort datumRead payloadReady payloadFixed depth types arguments
            rest ready]
    | depth, type, .lambda binder body, settled, ready => by
      twice_cases (.lambda binder body)
      rw [instantiateTwice_lambda]
      cases type with
      | arrow domain codomain =>
        dsimp only at settled ready
        rw [mapFrame_lambda data, settle.eq_def]
        dsimp only
        rw [settle_twice multiplyNe bodyNotData bodySort datumRead payloadReady payloadFixed (depth + 1) codomain body
          settled ready]
      | base sort =>
        have bodyScoped : body.isWellScopedAt (depth + 1) = true := by
          simpa [Pattern.isWellScopedAt] using settled
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [instantiateTwice_scoped payload datum bodyScoped, mapFrame_lambda_other data notArrow, settle.eq_def]
      | collection kind element =>
        have bodyScoped : body.isWellScopedAt (depth + 1) = true := by
          simpa [Pattern.isWellScopedAt] using settled
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [instantiateTwice_scoped payload datum bodyScoped, mapFrame_lambda_other data notArrow, settle.eq_def]
      | multiBinder inner =>
        have bodyScoped : body.isWellScopedAt (depth + 1) = true := by
          simpa [Pattern.isWellScopedAt] using settled
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [instantiateTwice_scoped payload datum bodyScoped, mapFrame_lambda_other data notArrow, settle.eq_def]
    | depth, type, .multiLambda arity binders body, settled, ready => by
      twice_cases (.multiLambda arity binders body)
      rw [instantiateTwice_multiLambda]
      cases type with
      | arrow domain codomain =>
        dsimp only at settled ready
        rw [mapFrame_multiLambda data, settle.eq_def]
        dsimp only
        rw [settle_twice multiplyNe bodyNotData bodySort datumRead payloadReady payloadFixed (depth + arity) codomain
          body settled ready]
      | base sort =>
        have bodyScoped : body.isWellScopedAt (depth + arity) = true := by
          simpa [Pattern.isWellScopedAt] using settled
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [instantiateTwice_scoped payload datum bodyScoped, mapFrame_multiLambda_other data notArrow, settle.eq_def]
      | collection kind element =>
        have bodyScoped : body.isWellScopedAt (depth + arity) = true := by
          simpa [Pattern.isWellScopedAt] using settled
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [instantiateTwice_scoped payload datum bodyScoped, mapFrame_multiLambda_other data notArrow, settle.eq_def]
      | multiBinder inner =>
        have bodyScoped : body.isWellScopedAt (depth + arity) = true := by
          simpa [Pattern.isWellScopedAt] using settled
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [instantiateTwice_scoped payload datum bodyScoped, mapFrame_multiLambda_other data notArrow, settle.eq_def]
    | depth, type, .collection kind elements rest, settled, ready => by
      twice_cases (.collection kind elements rest)
      rw [instantiateTwice_collection, settle.eq_def]
      dsimp only at settled ready ⊢
      cases found : elementType language type kind with
      | none =>
        rw [found] at settled
        dsimp only at settled ⊢
        rw [instantiateTwice_scopedList payload datum settled, mapFrame_collection_unknown data found]
      | some element =>
        rw [found] at settled ready
        dsimp only at settled ready ⊢
        rw [mapFrame_collection data found,
          settleList_twice multiplyNe bodyNotData bodySort datumRead payloadReady payloadFixed depth element elements
            settled ready]
    | depth, type, .bvar index, settled, ready => by
      twice_cases (.bvar index)
      rw [instantiateTwice_scoped payload datum (by simpa [Pattern.isWellScopedAt] using settled),
        mapFrame_leaf data occurs (.inl ⟨index, rfl⟩)]
      exact settle_bvar type index
    | depth, type, .fvar name, settled, ready => by
      twice_cases (.fvar name)
      rw [instantiateTwice_scoped payload datum (by simp [Pattern.isWellScopedAt]),
        mapFrame_leaf data occurs (.inr (.inl ⟨name, rfl⟩))]
      exact settle_fvar type name
    | depth, type, .subst body replacement, settled, ready => by
      twice_cases (.subst body replacement)
      rw [instantiateTwice_scoped payload datum settled,
        mapFrame_leaf data occurs (.inr (.inr ⟨body, replacement, rfl⟩)), settle.eq_def]
  termination_by _ _ body _ _ => sizeOf body
  decreasing_by all_goals sizeOf_pattern_dec

  theorem settleArgs_twice (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (bodySort : actionType language decl = some bodyType) {payload datum : Pattern} {y : G}
      (datumRead : read decl reading.constant datum = some y)
      (payloadReady : PayloadReady (language := language) reading bodyType payload)
      (payloadFixed : settle language decl bodyType payload = payload) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        settledArgsAt language decl depth types arguments = true →
          FrameAllArgs language decl
            (fun j datum => ∃ found, letters decl reading.constant datum = some found ∧ LevelFree (j + 1) found)
            (fun j occurrence => (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence ∧
              NotVariable decl j occurrence) depth types arguments →
            settleArgs language decl types (arguments.map (instantiateTwice payload datum depth)) =
              mapFrameArgs language decl (fun k word => instantiateTwice payload datum k word)
                (twiceVariable (language := language) (decl := decl) bodyType payload datum) depth types arguments
    | depth, type :: types, argument :: arguments, settled, ready => by
      rw [settledArgsAt, Bool.and_eq_true] at settled
      rw [FrameAllArgs] at ready
      rw [List.map_cons, settleArgs, mapFrameArgs,
        settle_twice multiplyNe bodyNotData bodySort datumRead payloadReady payloadFixed depth type argument settled.1
          ready.1,
        settleArgs_twice multiplyNe bodyNotData bodySort datumRead payloadReady payloadFixed depth types arguments
          settled.2 ready.2]
    | depth, [], arguments, settled, _ => by
      rw [settledArgsAt] at settled
      simp only [settleArgs, mapFrameArgs]
      exact instantiateTwice_scopedList payload datum settled
    | depth, _ :: _, [], _, _ => by simp [settleArgs, mapFrameArgs]
  termination_by _ _ arguments _ _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem settleList_twice (multiplyNe : decl.multiply ≠ decl.action)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
      (bodySort : actionType language decl = some bodyType) {payload datum : Pattern} {y : G}
      (datumRead : read decl reading.constant datum = some y)
      (payloadReady : PayloadReady (language := language) reading bodyType payload)
      (payloadFixed : settle language decl bodyType payload = payload) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        settledListAt language decl depth element patterns = true →
          FrameAllList language decl
            (fun j datum => ∃ found, letters decl reading.constant datum = some found ∧ LevelFree (j + 1) found)
            (fun j occurrence => (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence ∧
              NotVariable decl j occurrence) depth element patterns →
            settleList language decl element (patterns.map (instantiateTwice payload datum depth)) =
              mapFrameList language decl (fun k word => instantiateTwice payload datum k word)
                (twiceVariable (language := language) (decl := decl) bodyType payload datum) depth element patterns
    | depth, element, [], _, _ => by simp [settleList, mapFrameList]
    | depth, element, pattern :: patterns, settled, ready => by
      rw [settledListAt, Bool.and_eq_true] at settled
      rw [FrameAllList] at ready
      rw [List.map_cons, settleList, mapFrameList,
        settle_twice multiplyNe bodyNotData bodySort datumRead payloadReady payloadFixed depth element pattern
          settled.1 ready.1,
        settleList_twice multiplyNe bodyNotData bodySort datumRead payloadReady payloadFixed depth element patterns
          settled.2 ready.2]
  termination_by _ _ patterns _ _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- A ready payload's data and coefficients are words. -/
theorem payload_words {bodyType : TypeExpr} {payload : Pattern}
    (ready : PayloadReady (language := language) reading bodyType payload) :
    WordsAt (language := language) reading 0 bodyType payload :=
  frameAll_mono (fun _ _ h => h)
    (fun _ _ h c v found => by
      obtain ⟨z, cRead⟩ := h.2 c v found
      obtain ⟨cLetters, cParsed, _⟩ := letters_of_read reading.constant c cRead
      rw [cParsed]
      rfl) 0 bodyType payload ready.2

/-- **Settling the authored continuation is the discharging continuation**, for a settled body and
payload. -/
theorem settle_plainContinuation (multiplyNe : decl.multiply ≠ decl.action)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) {payload datum : Pattern} {y : G}
    (datumRead : read decl reading.constant datum = some y)
    (payloadReady : PayloadReady (language := language) reading bodyType payload)
    (payloadSettled : settledAt language decl 0 bodyType payload = true) (type : TypeExpr) {body : Pattern}
    (ready : BodyReady (language := language) reading type body)
    (bodySettled : settledAt language decl 0 type body = true) :
    settle language decl type (plainContinuation body payload datum) =
      commContinuation (language := language) (decl := decl) bodyType type body payload datum := by
  have payloadFixed : settle language decl bodyType payload = payload :=
    settle_of_settled multiplyNe bodySort reading 0 bodyType payload payloadSettled (payload_words payloadReady)
  rw [plainContinuation,
    settle_twice multiplyNe bodyNotData bodySort datumRead payloadReady payloadFixed 0 type body bodySettled ready]
  unfold commContinuation instDatumWalk instWalkAt
  have shifted := mapFrame_shift (language := language) (decl := decl)
    (f := fun k word => Substitution.instantiateBVarAt k payload word) (v := instVariable language decl bodyType payload)
    1 0 type body
  rw [Nat.zero_add] at shifted
  rw [shifted, mapFrame_fuse (fun k pattern occurs notBare =>
      instVariable_keepsNotBare bodySort bodyNotData payload (k + 1) pattern occurs notBare) bodyNotData bodySort]
  rfl

/-- **The authored reduct**: the module's right-hand side, its explicit substitutions executed, the
continuation acted on by the relative orientation and by its inverse. -/
def plainReduct (sum : CollType) (a b body payload datum : Pattern) : Pattern :=
  .collection sum
    [.apply decl.action [mulWord decl a (invWord decl b), plainContinuation body payload datum],
      .apply decl.action [mulWord decl b (invWord decl a), plainContinuation body payload datum]] none

/-- **Settling the authored reduct is the reduct of communication.** -/
theorem settle_plainReduct (multiplyNe : decl.multiply ≠ decl.action)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) {sum : CollType}
    (summands : elementType language bodyType sum = some bodyType) {a b payload datum : Pattern} {xa xb y : G}
    (aRead : read decl reading.constant a = some xa) (bRead : read decl reading.constant b = some xb)
    (datumRead : read decl reading.constant datum = some y)
    (payloadReady : PayloadReady (language := language) reading bodyType payload)
    (payloadSettled : settledAt language decl 0 bodyType payload = true) {body : Pattern}
    (ready : BodyReady (language := language) reading bodyType body)
    (bodySettled : settledAt language decl 0 bodyType body = true) :
    settle language decl bodyType (plainReduct (decl := decl) sum a b body payload datum) =
      commReduct (language := language) (decl := decl) sum bodyType bodyType a b body payload datum := by
  obtain ⟨abLetters, abParsed, _⟩ := letters_of_read reading.constant _ (read_mulWord aRead (read_invWord bRead))
  obtain ⟨baLetters, baParsed, _⟩ := letters_of_read reading.constant _ (read_mulWord bRead (read_invWord aRead))
  unfold plainReduct commReduct
  rw [settle.eq_def]
  dsimp only
  rw [summands]
  dsimp only
  simp only [settleList]
  rw [settle_action multiplyNe bodyNotData bodySort abParsed, settle_action multiplyNe bodyNotData bodySort baParsed,
    settle_plainContinuation multiplyNe bodyNotData bodySort datumRead payloadReady payloadSettled bodyType ready
      bodySettled]

end Authored

/-! ## Walks keep a term settled -/

section KeepSettled

variable {language : LanguageDef} {decl : OrientationDecl}

/-- The data and variable branches of a settledness step; leaves the structural branch with `settled`
unfolded and `structural` for the walk's result. -/
syntax "keep_settled_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| keep_settled_cases $pattern) => `(tactic| (
      by_cases data : type = .base decl.dataSort
      · rw [settledAt.eq_def, if_pos data]
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [mapFrame_variable data occurs, settledAt.eq_def, if_neg data,
          if_pos ⟨keeps.occurs _ _ occurs.1, occurs.2⟩]
      have structural := decorated?_mapFrame_structural (language := language) (f := f) (v := v)
        (depth := walkDepth) keeps.notBare bodyNotData data occurs
      rw [settledAt.eq_def, if_neg data, if_neg occurs] at settled))

mutual
  /-- **A walk that keeps occurrences keeps a term settled**: it changes no subterm it skips, and
  rebuilds every other constructor as it was. -/
  theorem settledAt_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth walkDepth : Nat) (type : TypeExpr) (pattern : Pattern), settledAt language decl depth type pattern = true →
        settledAt language decl depth type (mapFrame language decl f v walkDepth type pattern) = true
    | depth, walkDepth, type, .apply label arguments, settled => by
      keep_settled_cases (.apply label arguments)
      dsimp only at settled
      cases found : paramTypes language label with
      | none =>
        rw [mapFrame_apply_unknown data occurs found, settledAt.eq_def, if_neg data, if_neg occurs]
        exact settled
      | some types =>
        rw [found] at settled
        rw [mapFrame_apply_structural data occurs found] at structural ⊢
        rw [settledAt.eq_def, if_neg data, if_neg structural]
        dsimp only
        rw [found]
        dsimp only
        simp only [Bool.and_eq_true] at settled ⊢
        exact ⟨settled.1, settledArgsAt_mapFrame keeps bodyNotData depth walkDepth types arguments settled.2⟩
    | depth, walkDepth, type, .lambda binder body, settled => by
      keep_settled_cases (.lambda binder body)
      cases type with
      | arrow domain codomain =>
        dsimp only at settled
        rw [mapFrame_lambda data, settledAt.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact settledAt_mapFrame keeps bodyNotData (depth + 1) (walkDepth + 1) codomain body settled
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, settledAt.eq_def, if_neg data, if_neg occurs]
        exact settled
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, settledAt.eq_def, if_neg data, if_neg occurs]
        exact settled
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_lambda_other data notArrow, settledAt.eq_def, if_neg data, if_neg occurs]
        exact settled
    | depth, walkDepth, type, .multiLambda arity binders body, settled => by
      keep_settled_cases (.multiLambda arity binders body)
      cases type with
      | arrow domain codomain =>
        dsimp only at settled
        rw [mapFrame_multiLambda data, settledAt.eq_def, if_neg data, if_neg (by simp [decorated?])]
        exact settledAt_mapFrame keeps bodyNotData (depth + arity) (walkDepth + arity) codomain body settled
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, settledAt.eq_def, if_neg data, if_neg occurs]
        exact settled
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, settledAt.eq_def, if_neg data, if_neg occurs]
        exact settled
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        rw [mapFrame_multiLambda_other data notArrow, settledAt.eq_def, if_neg data, if_neg occurs]
        exact settled
    | depth, walkDepth, type, .collection kind elements rest, settled => by
      keep_settled_cases (.collection kind elements rest)
      dsimp only at settled
      cases found : elementType language type kind with
      | none =>
        rw [mapFrame_collection_unknown data found, settledAt.eq_def, if_neg data, if_neg occurs]
        exact settled
      | some element =>
        rw [found] at settled
        dsimp only at settled
        rw [mapFrame_collection data found, settledAt.eq_def, if_neg data, if_neg (by simp [decorated?])]
        dsimp only
        rw [found]
        exact settledListAt_mapFrame keeps bodyNotData depth walkDepth element elements settled
    | depth, walkDepth, type, .bvar index, settled => by
      keep_settled_cases (.bvar index)
      rw [mapFrame_leaf data occurs (.inl ⟨index, rfl⟩), settledAt.eq_def, if_neg data, if_neg occurs]
      exact settled
    | depth, walkDepth, type, .fvar name, settled => by
      keep_settled_cases (.fvar name)
      rw [mapFrame_leaf data occurs (.inr (.inl ⟨name, rfl⟩)), settledAt.eq_def, if_neg data, if_neg occurs]
    | depth, walkDepth, type, .subst body replacement, settled => by
      keep_settled_cases (.subst body replacement)
      rw [mapFrame_leaf data occurs (.inr (.inr ⟨body, replacement, rfl⟩)), settledAt.eq_def, if_neg data,
        if_neg occurs]
      exact settled
  termination_by _ _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem settledArgsAt_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth walkDepth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        settledArgsAt language decl depth types arguments = true →
          settledArgsAt language decl depth types (mapFrameArgs language decl f v walkDepth types arguments) = true
    | depth, walkDepth, type :: types, argument :: arguments, settled => by
      rw [settledArgsAt, Bool.and_eq_true] at settled
      rw [mapFrameArgs, settledArgsAt, Bool.and_eq_true]
      exact ⟨settledAt_mapFrame keeps bodyNotData depth walkDepth type argument settled.1,
        settledArgsAt_mapFrame keeps bodyNotData depth walkDepth types arguments settled.2⟩
    | depth, walkDepth, [], arguments, settled => by simpa [mapFrameArgs] using settled
    | depth, walkDepth, _ :: _, [], settled => by simpa [mapFrameArgs] using settled
  termination_by _ _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem settledListAt_mapFrame {f v : Nat → Pattern → Pattern} (keeps : KeepsOccurrences decl v)
      (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) :
      ∀ (depth walkDepth : Nat) (element : TypeExpr) (patterns : List Pattern),
        settledListAt language decl depth element patterns = true →
          settledListAt language decl depth element (mapFrameList language decl f v walkDepth element patterns) = true
    | depth, walkDepth, element, [], _ => by rw [mapFrameList, settledListAt]
    | depth, walkDepth, element, pattern :: patterns, settled => by
      rw [settledListAt, Bool.and_eq_true] at settled
      rw [mapFrameList, settledListAt, Bool.and_eq_true]
      exact ⟨settledAt_mapFrame keeps bodyNotData depth walkDepth element pattern settled.1,
        settledListAt_mapFrame keeps bodyNotData depth walkDepth element patterns settled.2⟩
  termination_by _ _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end KeepSettled

/-! ## The authored communication is equivariant -/

section AuthoredEquivariance

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] {reading : DataReading decl G}

/-- **A readable word has no variable letter.** -/
theorem levelFree_of_read :
    ∀ {g : Pattern} {x : G}, read decl reading.constant g = some x → ∀ {found : List (Letter G)},
      letters decl reading.constant g = some found → ∀ level, LevelFree level found
  | .bvar index, x, readOk, found, _, level => by simp [read] at readOk
  | .fvar name, x, readOk, found, _, level => by simp [read] at readOk
  | .apply label [], x, readOk, found, parsed, level => by
    rw [letters] at parsed
    split at parsed
    · cases parsed
      intro letter member
      cases member
    · obtain ⟨c, _, same⟩ := Option.map_eq_some_iff.mp parsed
      subst same
      intro letter member
      rw [List.mem_singleton] at member
      subst member
      simp [Letter.index]
  | .apply label [argument], x, readOk, found, parsed, level => by
    rw [read] at readOk
    rw [letters] at parsed
    split at parsed
    · rename_i isInverse
      rw [if_pos isInverse] at readOk
      obtain ⟨inner, innerRead, _⟩ := Option.map_eq_some_iff.mp readOk
      obtain ⟨innerLetters, innerParsed, same⟩ := Option.map_eq_some_iff.mp parsed
      subst same
      exact levelFree_invert.mpr (levelFree_of_read innerRead innerParsed level)
    · cases parsed
  | .apply label [left, right], x, readOk, found, parsed, level => by
    rw [read] at readOk
    rw [letters] at parsed
    split at parsed
    · rename_i isMultiply
      rw [if_pos isMultiply] at readOk
      split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        cases parsed
        split at readOk
        · rename_i leftValue rightValue leftRead rightRead
          exact levelFree_append.mpr ⟨levelFree_of_read leftRead leftParsed level,
            levelFree_of_read rightRead rightParsed level⟩
        · cases readOk
      · cases parsed
    · cases parsed
  | .apply label (_ :: _ :: _ :: _), x, readOk, found, _, level => by simp [read] at readOk
  | .lambda _ _, x, readOk, found, _, level => by simp [read] at readOk
  | .multiLambda _ _ _, x, readOk, found, _, level => by simp [read] at readOk
  | .subst _ _, x, readOk, found, _, level => by simp [read] at readOk
  | .collection _ _ _, x, readOk, found, _, level => by simp [read] at readOk
termination_by g => sizeOf g
decreasing_by all_goals sizeOf_pattern_dec

/-- **(FRAME) by a readable word keeps a variable out of a word**: it renames a bound variable `δ` to
`g⁻¹ δ` and adds no variable. -/
theorem letters_frameWord_levelFree {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x)
    (depth level : Nat) :
    ∀ (word : Pattern) {found : List (Letter G)}, letters decl reading.constant word = some found →
      LevelFree level found →
        ∃ framed, letters decl reading.constant (frameWord decl g depth word) = some framed ∧ LevelFree level framed
  | .bvar index, found, parsed, free => by
    by_cases inside : index < depth
    · obtain ⟨gLetters, gParsed, _⟩ := letters_of_read reading.constant g gRead
      rw [letters] at parsed
      cases parsed
      refine ⟨invertLetters gLetters ++ [.power (.bound index) 1], ?_, ?_⟩
      · simp only [frameWord, if_pos inside]
        exact letters_mulWord (letters_invWord gParsed) (by rw [letters])
      · exact levelFree_append.mpr ⟨levelFree_invert.mpr (levelFree_of_read gRead gParsed level), free⟩
    · exact ⟨found, by simp only [frameWord, if_neg inside]; exact parsed, free⟩
  | .fvar name, found, parsed, free => ⟨found, by simp only [frameWord]; exact parsed, free⟩
  | .apply label [], found, parsed, free => ⟨found, by simp only [frameWord, frameWords]; exact parsed, free⟩
  | .apply label [argument], found, parsed, free => by
    rw [letters] at parsed
    split at parsed
    · rename_i isInverse
      obtain ⟨inner, innerParsed, same⟩ := Option.map_eq_some_iff.mp parsed
      subst same
      obtain ⟨framed, framedParsed, framedFree⟩ :=
        letters_frameWord_levelFree gRead depth level argument innerParsed (levelFree_invert.mp free)
      refine ⟨invertLetters framed, ?_, levelFree_invert.mpr framedFree⟩
      simp only [frameWord, frameWords]
      rw [letters, if_pos isInverse, framedParsed]
      rfl
    · cases parsed
  | .apply label [left, right], found, parsed, free => by
    rw [letters] at parsed
    split at parsed
    · rename_i isMultiply
      split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        cases parsed
        obtain ⟨leftFree, rightFree⟩ := levelFree_append.mp free
        obtain ⟨leftFramed, leftFramedParsed, leftFramedFree⟩ :=
          letters_frameWord_levelFree gRead depth level left leftParsed leftFree
        obtain ⟨rightFramed, rightFramedParsed, rightFramedFree⟩ :=
          letters_frameWord_levelFree gRead depth level right rightParsed rightFree
        refine ⟨leftFramed ++ rightFramed, ?_, levelFree_append.mpr ⟨leftFramedFree, rightFramedFree⟩⟩
        simp only [frameWord, frameWords]
        rw [letters, if_pos isMultiply, leftFramedParsed, rightFramedParsed]
      · cases parsed
    · cases parsed
  | .apply label (_ :: _ :: _ :: _), found, parsed, _ => by simp [letters] at parsed
  | .lambda _ _, found, parsed, _ => by simp [letters] at parsed
  | .multiLambda _ _ _, found, parsed, _ => by simp [letters] at parsed
  | .subst _ _, found, parsed, _ => by simp [letters] at parsed
  | .collection _ _ _, found, parsed, _ => by simp [letters] at parsed
termination_by word => sizeOf word
decreasing_by all_goals sizeOf_pattern_dec

/-- The action of a readable word keeps a variable out of a datum. -/
theorem letters_actData_levelFree {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x)
    (depth level : Nat) {word : Pattern} {found : List (Letter G)}
    (parsed : letters decl reading.constant word = some found) (free : LevelFree level found) :
    ∃ acted, letters decl reading.constant (actData decl g depth word) = some acted ∧ LevelFree level acted := by
  obtain ⟨framed, framedParsed, framedFree⟩ := letters_frameWord_levelFree gRead depth level word parsed free
  obtain ⟨gLetters, gParsed, _⟩ := letters_of_read reading.constant g gRead
  refine ⟨gLetters ++ framed, ?_, levelFree_append.mpr ⟨levelFree_of_read gRead gParsed level, framedFree⟩⟩
  unfold actData
  rw [liftBVars_closed gRead]
  exact letters_mulWord gParsed framedParsed

/-- **The action from under the two binders keeps a body ready.** -/
theorem bodyReady_act (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) {g : Pattern} {x : G}
    (gRead : read decl reading.constant g = some x) {type : TypeExpr} {body : Pattern}
    (ready : BodyReady (language := language) reading type body) :
    BodyReady (language := language) reading type (actWalkAt (language := language) (decl := decl) g 2 type body) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  have atTwo : FrameAll language decl
      (fun k word => ∃ found, letters decl reading.constant word = some found ∧ LevelFree (k - 1) found)
      (fun k occurrence => (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence ∧
        NotVariable decl (k - 2) occurrence) 2 type body := by
    have shifted := (frameAll_shift (language := language) (decl := decl)
      (dataOk := fun k word => ∃ found, letters decl reading.constant word = some found ∧ LevelFree (k - 1) found)
      (variableOk := fun k occurrence => (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence ∧
        NotVariable decl (k - 2) occurrence) 2 0 type body).mpr
      (frameAll_mono (fun j _ h => by rw [show j + 2 - 1 = j + 1 by omega]; exact h)
        (fun j _ h => ⟨h.1, h.2.1, by rw [show j + 2 - 2 = j by omega]; exact h.2.2⟩) 0 type body ready)
    rwa [Nat.zero_add] at shifted
  have acted : FrameAll language decl
      (fun k word => ∃ found, letters decl reading.constant word = some found ∧ LevelFree (k - 1) found)
      (fun k occurrence => (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence ∧
        NotVariable decl (k - 2) occurrence) 2 type (actWalkAt (language := language) (decl := decl) g 2 type body) :=
    frameAll_mapFrame (f := actData decl g) (v := actVariable decl g) (actVariable_keeps g).notBare bodyNotData bodySort
    (fun k _ ⟨_, parsed, free⟩ => letters_actData_levelFree gRead k (k - 1) parsed free)
    (fun k occurrence occurs ⟨_, closed, notDatum⟩ => by
      rw [frameAll_occurrence bodySort notData ((actVariable_keeps g).occurs k occurrence occurs)]
      exact ⟨(actVariable_keeps g).occurs k occurrence occurs, actVariable_closedCoefficients gRead k occurs closed,
        actVariable_notVariable g k occurs notDatum⟩) 2 type body atTwo
  have back := (frameAll_shift (language := language) (decl := decl) 2 0 type _).mp acted
  exact frameAll_mono (fun j _ h => by rw [show j + 2 - 1 = j + 1 by omega] at h; exact h)
    (fun j _ h => ⟨h.1, h.2.1, by rw [show j + 2 - 2 = j by omega] at h; exact h.2.2⟩) 0 type _ back

variable [DecidableEq G]

/-- **The authored communication is equivariant**: the module's reduct of the acted receive and
message, settled, is the action on the settled reduct of the receive and message, in normal form. -/
theorem plainReduct_equivariant (multiplyNe : decl.multiply ≠ decl.action)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) {sum : CollType}
    (summands : elementType language bodyType sum = some bodyType) {g a b datum : Pattern} {x xa xb y : G}
    (gRead : read decl reading.constant g = some x) (aRead : read decl reading.constant a = some xa)
    (bRead : read decl reading.constant b = some xb) (datumRead : read decl reading.constant datum = some y)
    {payload : Pattern} (payloadReady : PayloadReady (language := language) reading bodyType payload)
    (payloadSettled : settledAt language decl 0 bodyType payload = true) {body : Pattern}
    (ready : BodyReady (language := language) reading bodyType body)
    (bodySettled : settledAt language decl 0 bodyType body = true) :
    frameNormal language decl reading bodyType
        (settle language decl bodyType
          (plainReduct (decl := decl) sum (mulWord decl g a) (mulWord decl g b)
            (actWalkAt (language := language) (decl := decl) g 2 bodyType body)
            (frameAct language decl g bodyType payload) (mulWord decl g datum))) =
      frameNormal language decl reading bodyType
        (frameAct language decl g bodyType
          (settle language decl bodyType (plainReduct (decl := decl) sum a b body payload datum))) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  rw [settle_plainReduct multiplyNe bodyNotData bodySort summands (read_mulWord gRead aRead) (read_mulWord gRead bRead)
      (read_mulWord gRead datumRead) (payloadReady_frameAct bodyNotData bodySort gRead payloadReady)
      (settledAt_mapFrame (actVariable_keeps g) bodyNotData 0 0 bodyType payload payloadSettled)
      (bodyReady_act bodyNotData bodySort gRead ready)
      (settledAt_mapFrame (actVariable_keeps g) bodyNotData 0 2 bodyType body bodySettled),
    settle_plainReduct multiplyNe bodyNotData bodySort summands aRead bRead datumRead payloadReady payloadSettled ready
      bodySettled]
  exact commReduct_equivariant bodyNotData bodySort summands notData gRead aRead bRead datumRead payloadReady ready

end AuthoredEquivariance

end Mettapedia.OSLF.MeTTaIL.Orientation
