import Mettapedia.OSLF.MeTTaIL.OrientationFrame

/-!
# The action commutes with substitution

In Meredith's calculus a substitution discharges a decoration: `(^w X)σ = w · σ(X)`. Instantiating a
receive's process variable is therefore a walk (`instWalk`): a bare occurrence of the variable becomes
the replacement, a decorated one becomes the action of its coefficient on the replacement, the other
variables lose the binder level, and data words lose it too.

The action commutes with it (`instWalk_frameAct`, from `body_equivariant` at every depth): instantiating
the acted body with the acted replacement is the action on the instantiated body, in normal form, when the
replacement and the acting word are closed, the body's data are words without the instantiated variable,
and its decorations have closed coefficients (`SubstitutionReady`).

Instantiating a receive's datum is a walk too (`instDatumWalk`), and the action commutes with it
(`instDatum_frameAct`): with the acted datum `g · d`, (FRAME)'s renaming `δ ↦ g⁻¹ δ` meets `g · d` and
leaves `d`. In `G ∗ F(V)` this is `σ_{x y} ∘ φ_{x, k+1} = φ_{x, k} ∘ σ_y` (`instHom_frameHom`).

Both are instances of one theorem about walks (`walk_equivariant`): a walk commutes with the action, in
normal form, when it does at data and at occurrences. A bound occurrence keeps
its frame under the action, so it receives the acted replacement unchanged; a decorated one is
conjugated, `^(g w g⁻¹)`, and `(g w g⁻¹) · (g · R) = (g w) · R = g · (w · R)`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax

variable (language : LanguageDef) (decl : OrientationDecl)

/-- A pattern with no bound variable at all. -/
abbrev Closed (pattern : Pattern) : Prop := pattern.isWellScopedAt 0 = true

/-- Instantiation at a variable occurrence of the body sort: the occurrence of the instantiated level
receives the replacement, acted on by its decoration's coefficient; any other bound variable loses the
level. -/
def instVariable (bodyType : TypeExpr) (replacement : Pattern) (depth : Nat) (occurrence : Pattern) : Pattern :=
  match decorated? decl occurrence with
  | some (none, .bvar index) =>
      if index = depth then Substitution.liftBVars 0 depth replacement
      else if depth < index then .bvar (index - 1) else .bvar index
  | some (some coefficient, .bvar index) =>
      if index = depth then
        frameAct language decl (Substitution.instantiateBVarAt depth replacement coefficient) bodyType
          (Substitution.liftBVars 0 depth replacement)
      else
        .apply decl.action [Substitution.instantiateBVarAt depth replacement coefficient,
          if depth < index then .bvar (index - 1) else .bvar index]
  | some (some coefficient, occurrenceVar) =>
      .apply decl.action [Substitution.instantiateBVarAt depth replacement coefficient, occurrenceVar]
  | _ => occurrence

/-- **Discharging instantiation of a process variable**, as a walk from the binder it is bound by. -/
def instWalk (bodyType : TypeExpr) (replacement : Pattern) (type : TypeExpr) (pattern : Pattern) : Pattern :=
  mapFrame language decl (fun depth datum => Substitution.instantiateBVarAt depth replacement datum)
    (instVariable language decl bodyType replacement) 0 type pattern

/-! ## Walks at shifted depths -/

section Shift

variable {language decl}

/-- The structural branch of a shifted walk step. -/
syntax "shift_cases" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| shift_cases) => `(tactic| (
      rw [mapFrame.eq_def language decl f v, mapFrame.eq_def language decl (fun k => f (k + shift))
        (fun k => v (k + shift))]
      all_goals (try split_ifs)
      all_goals (try rfl)))

mutual
  /-- **A walk started deeper is a walk whose functions see the extra depth.** -/
  theorem mapFrame_shift {f v : Nat → Pattern → Pattern} (shift : Nat) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern),
        mapFrame language decl f v (depth + shift) type pattern =
          mapFrame language decl (fun k => f (k + shift)) (fun k => v (k + shift)) depth type pattern
    | depth, type, .apply label arguments => by
      shift_cases
      dsimp only
      cases paramTypes language label with
      | none => rfl
      | some types =>
        dsimp only
        rw [mapFrameArgs_shift shift depth types arguments]
    | depth, type, .lambda binder body => by
      shift_cases
      dsimp only
      cases type with
      | arrow domain codomain =>
        dsimp only
        rw [show depth + shift + 1 = depth + 1 + shift by omega, mapFrame_shift shift (depth + 1) codomain body]
      | _ => rfl
    | depth, type, .multiLambda arity binders body => by
      shift_cases
      dsimp only
      cases type with
      | arrow domain codomain =>
        dsimp only
        rw [show depth + shift + arity = depth + arity + shift by omega,
          mapFrame_shift shift (depth + arity) codomain body]
      | _ => rfl
    | depth, type, .collection kind elements rest => by
      shift_cases
      dsimp only
      cases elementType language type kind with
      | none => rfl
      | some element =>
        dsimp only
        rw [mapFrameList_shift shift depth element elements]
    | depth, type, .bvar index => by shift_cases
    | depth, type, .fvar name => by shift_cases
    | depth, type, .subst body replacement => by shift_cases
  termination_by _ _ pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameArgs_shift {f v : Nat → Pattern → Pattern} (shift : Nat) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        mapFrameArgs language decl f v (depth + shift) types arguments =
          mapFrameArgs language decl (fun k => f (k + shift)) (fun k => v (k + shift)) depth types arguments
    | depth, type :: types, argument :: arguments => by
      rw [mapFrameArgs, mapFrameArgs, mapFrame_shift shift depth type argument,
        mapFrameArgs_shift shift depth types arguments]
    | depth, [], arguments => by simp [mapFrameArgs]
    | depth, _ :: _, [] => by simp [mapFrameArgs]
  termination_by _ _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameList_shift {f v : Nat → Pattern → Pattern} (shift : Nat) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        mapFrameList language decl f v (depth + shift) element patterns =
          mapFrameList language decl (fun k => f (k + shift)) (fun k => v (k + shift)) depth element patterns
    | depth, element, [] => by simp [mapFrameList]
    | depth, element, pattern :: patterns => by
      rw [mapFrameList, mapFrameList, mapFrame_shift shift depth element pattern,
        mapFrameList_shift shift depth element patterns]
  termination_by _ _ patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end Shift

/-! ## Scoped terms -/

section Scoped

variable {language decl}

/-- What a inScope term gives the walk: every datum and occurrence inScope at the walk's depth. -/
abbrev ScopedAll (depth : Nat) (type : TypeExpr) (pattern : Pattern) : Prop :=
  FrameAll language decl (fun k datum => datum.isWellScopedAt k = true)
    (fun k occurrence => occurrence.isWellScopedAt k = true) depth type pattern

mutual
  theorem scopedAll_of_scoped :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), pattern.isWellScopedAt depth = true →
        ScopedAll (language := language) (decl := decl) depth type pattern
    | depth, type, pattern, inScope => by
      unfold ScopedAll
      rw [FrameAll.eq_def]
      split_ifs
      · exact inScope
      · exact inScope
      · match pattern, inScope with
        | .apply label arguments, inScope =>
          dsimp only
          split
          · rename_i types _
            exact scopedArgs_of_scoped depth types arguments (by simpa [Pattern.isWellScopedAt] using inScope)
          · trivial
        | .lambda binder body, inScope =>
          dsimp only
          split
          · exact scopedAll_of_scoped (depth + 1) _ body (by simpa [Pattern.isWellScopedAt] using inScope)
          · trivial
        | .multiLambda arity binders body, inScope =>
          dsimp only
          split
          · exact scopedAll_of_scoped (depth + arity) _ body (by simpa [Pattern.isWellScopedAt] using inScope)
          · trivial
        | .collection kind elements rest, inScope =>
          dsimp only
          split
          · rename_i element _
            exact scopedList_of_scoped depth element elements (by simpa [Pattern.isWellScopedAt] using inScope)
          · trivial
        | .bvar _, _ => trivial
        | .fvar _, _ => trivial
        | .subst _ _, _ => trivial
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem scopedArgs_of_scoped :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        Pattern.isWellScopedListAt depth arguments = true →
          FrameAllArgs language decl (fun k datum => datum.isWellScopedAt k = true)
            (fun k occurrence => occurrence.isWellScopedAt k = true) depth types arguments
    | depth, type :: types, argument :: arguments, inScope => by
      rw [FrameAllArgs]
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
      exact ⟨scopedAll_of_scoped depth type argument inScope.1, scopedArgs_of_scoped depth types arguments inScope.2⟩
    | depth, [], arguments, _ => by simp [FrameAllArgs]
    | depth, _ :: _, [], _ => by simp [FrameAllArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem scopedList_of_scoped :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        Pattern.isWellScopedListAt depth patterns = true →
          FrameAllList language decl (fun k datum => datum.isWellScopedAt k = true)
            (fun k occurrence => occurrence.isWellScopedAt k = true) depth element patterns
    | depth, element, [], _ => by rw [FrameAllList]; trivial
    | depth, element, pattern :: patterns, inScope => by
      rw [FrameAllList]
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
      exact ⟨scopedAll_of_scoped depth element pattern inScope.1, scopedList_of_scoped depth element patterns inScope.2⟩
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end Scoped

/-! ## A closed term is acted on alike at every depth -/

section ClosedAction

variable {language decl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

mutual
  theorem frameWord_scoped (g : Pattern) (shift : Nat) : ∀ {depth : Nat} (word : Pattern),
      word.isWellScopedAt depth = true → frameWord decl g (depth + shift) word = frameWord decl g depth word
    | depth, .bvar index, inScope => by
      have below : index < depth := by simpa [Pattern.isWellScopedAt] using inScope
      simp [frameWord, below, Nat.lt_of_lt_of_le below (Nat.le_add_right depth shift)]
    | depth, .apply label arguments, inScope => by
      simp only [frameWord]
      rw [frameWords_scoped g shift arguments (by simpa [Pattern.isWellScopedAt] using inScope)]
    | depth, .fvar _, _ => by simp [frameWord]
    | depth, .lambda _ _, _ => by simp [frameWord]
    | depth, .multiLambda _ _ _, _ => by simp [frameWord]
    | depth, .subst _ _, _ => by simp [frameWord]
    | depth, .collection _ _ _, _ => by simp [frameWord]

  theorem frameWords_scoped (g : Pattern) (shift : Nat) : ∀ {depth : Nat} (words : List Pattern),
      Pattern.isWellScopedListAt depth words = true →
        frameWords decl g (depth + shift) words = frameWords decl g depth words
    | depth, [], _ => by simp [frameWords]
    | depth, word :: words, inScope => by
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
      simp only [frameWords]
      rw [frameWord_scoped g shift word inScope.1, frameWords_scoped g shift words inScope.2]
end

omit [DecidableEq G] in
theorem actData_scoped {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (shift : Nat)
    {depth : Nat} {word : Pattern} (inScope : word.isWellScopedAt depth = true) :
    actData decl g (depth + shift) word = actData decl g depth word := by
  unfold actData
  simp only [liftBVars_closed closed]
  rw [frameWord_scoped g shift word inScope]

omit [Group G] [DecidableEq G] in
theorem decorated?_scoped {occurrence : Pattern} {coefficient occurrenceVar : Pattern} {depth : Nat}
    (found : decorated? decl occurrence = some (some coefficient, occurrenceVar))
    (inScope : occurrence.isWellScopedAt depth = true) :
    coefficient.isWellScopedAt depth = true ∧ occurrenceVar.isWellScopedAt depth = true := by
  obtain ⟨_, _, applied⟩ := decorated?_shape found
  rw [applied coefficient rfl] at inScope
  simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using inScope

omit [DecidableEq G] in
theorem actVariable_scoped {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (shift : Nat)
    {depth : Nat} {occurrence : Pattern} (inScope : occurrence.isWellScopedAt depth = true) :
    actVariable decl g (depth + shift) occurrence = actVariable decl g depth occurrence := by
  cases found : decorated? decl occurrence with
  | none => simp [actVariable, found]
  | some pair =>
    obtain ⟨coefficient, occurrenceVar⟩ := pair
    obtain ⟨bare, plain, applied⟩ := decorated?_shape found
    cases coefficient with
    | none =>
      rw [plain rfl] at inScope
      match occurrenceVar, bare, inScope with
      | .bvar index, _, inScope =>
        have below : index < depth := by simpa [Pattern.isWellScopedAt] using inScope
        simp [actVariable, found, below, Nat.lt_of_lt_of_le below (Nat.le_add_right depth shift)]
      | .fvar name, _, _ => simp [actVariable, found, liftBVars_closed closed]
    | some c =>
      obtain ⟨coefficientScoped, variableScoped⟩ := decorated?_scoped found inScope
      match occurrenceVar, bare, variableScoped with
      | .bvar index, _, variableScoped =>
        have below : index < depth := by simpa [Pattern.isWellScopedAt] using variableScoped
        simp [actVariable, found, below, Nat.lt_of_lt_of_le below (Nat.le_add_right depth shift),
          liftBVars_closed closed, frameWord_scoped g shift c coefficientScoped]
      | .fvar name, _, _ =>
        simp [actVariable, found, liftBVars_closed closed, frameWord_scoped g shift c coefficientScoped]

omit [DecidableEq G] in
/-- **A closed term is acted on alike at every depth.** -/
theorem frameAct_closed_depth {g : Pattern} {x : G} (closedWord : read decl reading.constant g = some x)
    (depth : Nat) (type : TypeExpr) {pattern : Pattern} (closed : Closed pattern) :
    mapFrame language decl (actData decl g) (actVariable decl g) depth type pattern =
      frameAct language decl g type pattern := by
  unfold frameAct
  rw [show depth = 0 + depth from (Nat.zero_add depth).symm, mapFrame_shift]
  apply mapFrame_congr _ _ 0 type pattern (scopedAll_of_scoped 0 type pattern closed)
  · intro k word inScope
    exact actData_scoped closedWord depth inScope
  · intro k occurrence inScope
    exact actVariable_scoped closedWord depth inScope

end ClosedAction

/-! ## Walks keep scoping -/

section KeepScope

variable {language decl}

/-- The structural branch of a scoping step. -/
syntax "scope_cases" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| scope_cases) => `(tactic| (
      rw [mapFrame.eq_def]
      split_ifs with data occurs
      · exact keepsData _ _ inScope
      · exact keepsVariable _ _ inScope))

mutual
  /-- **A walk keeps a term scoped** when its functions keep the positions scoped. -/
  theorem mapFrame_scoped {f v : Nat → Pattern → Pattern}
      (keepsData : ∀ depth datum, datum.isWellScopedAt depth = true → (f depth datum).isWellScopedAt depth = true)
      (keepsVariable : ∀ depth occurrence, occurrence.isWellScopedAt depth = true →
        (v depth occurrence).isWellScopedAt depth = true) :
      ∀ (depth : Nat) (type : TypeExpr) (pattern : Pattern), pattern.isWellScopedAt depth = true →
        (mapFrame language decl f v depth type pattern).isWellScopedAt depth = true
    | depth, type, .apply label arguments, inScope => by
      scope_cases
      dsimp only
      split
      · rename_i types _
        simp only [Pattern.isWellScopedAt] at inScope ⊢
        exact mapFrameArgs_scoped keepsData keepsVariable depth types arguments inScope
      · exact inScope
    | depth, type, .lambda binder body, inScope => by
      scope_cases
      dsimp only
      split
      · simp only [Pattern.isWellScopedAt] at inScope ⊢
        exact mapFrame_scoped keepsData keepsVariable (depth + 1) _ body inScope
      · exact inScope
    | depth, type, .multiLambda arity binders body, inScope => by
      scope_cases
      dsimp only
      split
      · simp only [Pattern.isWellScopedAt] at inScope ⊢
        exact mapFrame_scoped keepsData keepsVariable (depth + arity) _ body inScope
      · exact inScope
    | depth, type, .collection kind elements rest, inScope => by
      scope_cases
      dsimp only
      split
      · rename_i element _
        simp only [Pattern.isWellScopedAt] at inScope ⊢
        exact mapFrameList_scoped keepsData keepsVariable depth element elements inScope
      · exact inScope
    | depth, type, .bvar index, inScope => by scope_cases; exact inScope
    | depth, type, .fvar name, inScope => by scope_cases; exact inScope
    | depth, type, .subst body replacement, inScope => by scope_cases; exact inScope
  termination_by _ _ pattern _ => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameArgs_scoped {f v : Nat → Pattern → Pattern}
      (keepsData : ∀ depth datum, datum.isWellScopedAt depth = true → (f depth datum).isWellScopedAt depth = true)
      (keepsVariable : ∀ depth occurrence, occurrence.isWellScopedAt depth = true →
        (v depth occurrence).isWellScopedAt depth = true) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        Pattern.isWellScopedListAt depth arguments = true →
          Pattern.isWellScopedListAt depth (mapFrameArgs language decl f v depth types arguments) = true
    | depth, type :: types, argument :: arguments, inScope => by
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
      rw [mapFrameArgs]
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true]
      exact ⟨mapFrame_scoped keepsData keepsVariable depth type argument inScope.1,
        mapFrameArgs_scoped keepsData keepsVariable depth types arguments inScope.2⟩
    | depth, [], arguments, inScope => by simpa [mapFrameArgs] using inScope
    | depth, _ :: _, [], inScope => by simpa [mapFrameArgs] using inScope
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapFrameList_scoped {f v : Nat → Pattern → Pattern}
      (keepsData : ∀ depth datum, datum.isWellScopedAt depth = true → (f depth datum).isWellScopedAt depth = true)
      (keepsVariable : ∀ depth occurrence, occurrence.isWellScopedAt depth = true →
        (v depth occurrence).isWellScopedAt depth = true) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        Pattern.isWellScopedListAt depth patterns = true →
          Pattern.isWellScopedListAt depth (mapFrameList language decl f v depth element patterns) = true
    | depth, element, [], inScope => by simpa [mapFrameList] using inScope
    | depth, element, pattern :: patterns, inScope => by
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
      rw [mapFrameList]
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true]
      exact ⟨mapFrame_scoped keepsData keepsVariable depth element pattern inScope.1,
        mapFrameList_scoped keepsData keepsVariable depth element patterns inScope.2⟩
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end KeepScope


/-! ## The action of a closed word keeps a term closed -/

section ActScope

variable {language decl}
variable {G : Type} [Group G] {reading : DataReading decl G}

/-- A word the reading reads holds no bound variable. -/
theorem read_scoped {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (depth : Nat) :
    g.isWellScopedAt depth = true := by
  match g, closed with
  | .apply label [], _ => simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | .apply label [argument], closed =>
    rw [read] at closed
    split at closed
    · obtain ⟨y, inner, _⟩ := Option.map_eq_some_iff.mp closed
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, read_scoped inner depth]
    · cases closed
  | .apply label [left, right], closed =>
    rw [read] at closed
    split at closed
    · split at closed
      · rename_i y z leftRead rightRead
        simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, read_scoped leftRead depth,
          read_scoped rightRead depth]
      · cases closed
    · cases closed
  | .apply label (_ :: _ :: _ :: _), closed => simp [read] at closed
  | .bvar _, closed => simp [read] at closed
  | .fvar _, closed => simp [read] at closed
  | .lambda _ _, closed => simp [read] at closed
  | .multiLambda _ _ _, closed => simp [read] at closed
  | .subst _ _, closed => simp [read] at closed
  | .collection _ _ _, closed => simp [read] at closed
termination_by sizeOf g
decreasing_by all_goals sizeOf_pattern_dec

mutual
  theorem frameWord_keeps_scope {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) :
      ∀ {depth : Nat} (word : Pattern), word.isWellScopedAt depth = true →
        (frameWord decl g depth word).isWellScopedAt depth = true
    | depth, .bvar index, inScope => by
      have below : index < depth := by simpa [Pattern.isWellScopedAt] using inScope
      simp [frameWord, below, mulWord, invWord, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
        read_scoped closed depth]
    | depth, .apply label arguments, inScope => by
      simp only [frameWord, Pattern.isWellScopedAt] at inScope ⊢
      exact frameWords_keeps_scope closed arguments inScope
    | depth, .fvar _, inScope => by simpa [frameWord] using inScope
    | depth, .lambda _ _, inScope => by simpa [frameWord] using inScope
    | depth, .multiLambda _ _ _, inScope => by simpa [frameWord] using inScope
    | depth, .subst _ _, inScope => by simpa [frameWord] using inScope
    | depth, .collection _ _ _, inScope => by simpa [frameWord] using inScope

  theorem frameWords_keeps_scope {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) :
      ∀ {depth : Nat} (words : List Pattern), Pattern.isWellScopedListAt depth words = true →
        Pattern.isWellScopedListAt depth (frameWords decl g depth words) = true
    | depth, [], _ => by simp [frameWords, Pattern.isWellScopedListAt]
    | depth, word :: words, inScope => by
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
      simp only [frameWords, Pattern.isWellScopedListAt, Bool.and_eq_true]
      exact ⟨frameWord_keeps_scope closed word inScope.1, frameWords_keeps_scope closed words inScope.2⟩
end

theorem actData_keeps_scope {g : Pattern} {x : G} (closed : read decl reading.constant g = some x)
    {depth : Nat} {word : Pattern} (inScope : word.isWellScopedAt depth = true) :
    (actData decl g depth word).isWellScopedAt depth = true := by
  unfold actData
  simp only [liftBVars_closed closed, mulWord, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    read_scoped closed depth, frameWord_keeps_scope closed word inScope, Bool.and_self]

theorem actVariable_keeps_scope {g : Pattern} {x : G} (closed : read decl reading.constant g = some x)
    {depth : Nat} {occurrence : Pattern} (inScope : occurrence.isWellScopedAt depth = true) :
    (actVariable decl g depth occurrence).isWellScopedAt depth = true := by
  cases found : decorated? decl occurrence with
  | none => simpa [actVariable, found] using inScope
  | some pair =>
    obtain ⟨coefficient, occurrenceVar⟩ := pair
    obtain ⟨bare, plain, applied⟩ := decorated?_shape found
    cases coefficient with
    | none =>
      rw [plain rfl] at inScope
      match occurrenceVar, bare, inScope with
      | .bvar index, _, inScope =>
        have below : index < depth := by simpa [Pattern.isWellScopedAt] using inScope
        simp [actVariable, found, below, Pattern.isWellScopedAt]
      | .fvar name, _, _ =>
        simp [actVariable, found, liftBVars_closed closed, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
          read_scoped closed depth]
    | some c =>
      obtain ⟨coefficientScoped, variableScoped⟩ := decorated?_scoped found inScope
      match occurrenceVar, bare, variableScoped with
      | .bvar index, _, variableScoped =>
        have below : index < depth := by simpa [Pattern.isWellScopedAt] using variableScoped
        simp [actVariable, found, below, liftBVars_closed closed, mulWord, invWord, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, read_scoped closed depth, frameWord_keeps_scope closed c coefficientScoped]
      | .fvar name, _, _ =>
        simp [actVariable, found, liftBVars_closed closed, mulWord, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, read_scoped closed depth, frameWord_keeps_scope closed c coefficientScoped]

/-- **The action of a closed word keeps a term closed.** -/
theorem frameAct_closed {g : Pattern} {x : G} (closedWord : read decl reading.constant g = some x) (type : TypeExpr)
    {pattern : Pattern} (closed : Closed pattern) : Closed (frameAct language decl g type pattern) :=
  mapFrame_scoped (fun _ _ inScope => actData_keeps_scope closedWord inScope)
    (fun _ _ inScope => actVariable_keeps_scope closedWord inScope) 0 type pattern closed

end ActScope

/-! ## The action depends on the element a word reads -/

section ElementOnly

variable {language decl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- The normal form ignores the depth of the walk. -/
theorem frameNormal_depth (depth : Nat) (type : TypeExpr) (pattern : Pattern) :
    mapFrame language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth type pattern =
      frameNormal language decl reading type pattern := by
  unfold frameNormal
  rw [show depth = 0 + depth from (Nat.zero_add depth).symm, mapFrame_shift]
  rfl

theorem actData_element {u u' : Pattern} {x : G} (uRead : read decl reading.constant u = some x)
    (uRead' : read decl reading.constant u' = some x) (depth : Nat) {word : Pattern} {found : List (Letter G)}
    (parsed : letters decl reading.constant word = some found) :
    wordNormal decl reading (actData decl u depth word) = wordNormal decl reading (actData decl u' depth word) := by
  obtain ⟨first, firstParsed, firstValue⟩ := letters_actData uRead depth parsed
  obtain ⟨second, secondParsed, secondValue⟩ := letters_actData uRead' depth parsed
  exact (wordNormal_eq_iff firstParsed secondParsed).mpr (firstValue.trans secondValue.symm)

theorem actVariable_element {u u' : Pattern} {x : G} (uRead : read decl reading.constant u = some x)
    (uRead' : read decl reading.constant u' = some x) (depth : Nat) {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome) (parses : CoefficientParses reading occurrence) :
    normalVariable decl reading depth (actVariable decl u depth occurrence) =
      normalVariable decl reading depth (actVariable decl u' depth occurrence) := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have sameNormal : wordNormal decl reading u = wordNormal decl reading u' :=
    (wordNormal_closed uRead).trans (wordNormal_closed uRead').symm
  cases coefficient with
  | none =>
    have same := (plain rfl).symm
    subst same
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_bare_inside u inside, actVariable_bare_inside u' inside]
      · rw [actVariable_bare_outside u inside, actVariable_bare_outside u' inside, liftBVars_closed uRead,
          liftBVars_closed uRead']
        exact normalVariable_congr depth bare sameNormal
    | .fvar name, bare =>
      rw [actVariable_bare_free u depth name, actVariable_bare_free u' depth name, liftBVars_closed uRead,
        liftBVars_closed uRead']
      exact normalVariable_congr depth bare sameNormal
  | some c =>
    have same := (applied c rfl).symm
    subst same
    obtain ⟨cLetters, cParsed⟩ := Option.isSome_iff_exists.mp (parses c occurrenceVar found)
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_decorated_inside u c inside, actVariable_decorated_inside u' c inside]
        apply normalVariable_congr depth bare
        obtain ⟨first, firstParsed, firstValue⟩ := letters_conjugate uRead depth cParsed
        obtain ⟨second, secondParsed, secondValue⟩ := letters_conjugate uRead' depth cParsed
        exact (wordNormal_eq_iff firstParsed secondParsed).mpr (firstValue.trans secondValue.symm)
      · rw [actVariable_decorated_outside u c inside, actVariable_decorated_outside u' c inside]
        exact normalVariable_congr depth bare (actData_element uRead uRead' depth cParsed)
    | .fvar name, bare =>
      rw [actVariable_decorated_free u c depth name, actVariable_decorated_free u' c depth name]
      exact normalVariable_congr depth bare (actData_element uRead uRead' depth cParsed)

/-- **The action depends only on the element a closed word reads**, in normal form. -/
theorem frameAct_element (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {u u' : Pattern}
    {x : G} (uRead : read decl reading.constant u = some x) (uRead' : read decl reading.constant u' = some x)
    (type : TypeExpr) (pattern : Pattern) (parse : WordsParse language reading type pattern) :
    frameNormal language decl reading type (frameAct language decl u type pattern) =
      frameNormal language decl reading type (frameAct language decl u' type pattern) := by
  unfold frameNormal frameAct
  rw [mapFrame_comp (actVariable_keeps u) bodyNotData, mapFrame_comp (actVariable_keeps u') bodyNotData]
  apply mapFrame_congr _ _ 0 type pattern parse
  · intro depth datum parsed
    obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsed
    exact actData_element uRead uRead' depth parsed
  · intro depth occurrence ⟨occurs, coefficients⟩
    exact actVariable_element uRead uRead' depth occurs coefficients

end ElementOnly

/-! ## Instantiation inside a datum -/

section WordInstantiation

variable {decl}
variable {G : Type} [Group G] {reading : DataReading decl G}

/-- The letters of a word without the level `depth` as a variable. -/
def LevelFree (depth : Nat) (found : List (Letter G)) : Prop := ∀ letter ∈ found, letter.index ≠ some (.bound depth)

omit [Group G] in
theorem levelFree_append {depth : Nat} {left right : List (Letter G)} :
    LevelFree depth (left ++ right) ↔ LevelFree depth left ∧ LevelFree depth right := by
  simp only [LevelFree, List.mem_append]
  constructor
  · intro free
    exact ⟨fun letter member => free letter (.inl member), fun letter member => free letter (.inr member)⟩
  · rintro ⟨first, second⟩ letter (member | member)
    · exact first letter member
    · exact second letter member

theorem levelFree_invert {depth : Nat} {found : List (Letter G)} :
    LevelFree depth (invertLetters found) ↔ LevelFree depth found := by
  simp only [LevelFree, invertLetters, List.mem_reverse, List.mem_map]
  constructor
  · intro free letter member
    have := free letter.inv ⟨letter, member, rfl⟩
    cases letter <;> simp_all [Letter.inv, Letter.index]
  · rintro free _ ⟨letter, member, rfl⟩
    have := free letter member
    cases letter <;> simp_all [Letter.inv, Letter.index]

/-- **(FRAME) inside a datum commutes with instantiating a level the datum does not hold.** -/
theorem frameWord_instantiate {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (depth : Nat)
    (replacement : Pattern) :
    ∀ (word : Pattern) {found : List (Letter G)}, letters decl reading.constant word = some found →
      LevelFree depth found →
        Substitution.instantiateBVarAt depth replacement (frameWord decl g (depth + 1) word) =
          frameWord decl g depth (Substitution.instantiateBVarAt depth replacement word)
  | .bvar index, found, parsed, free => by
    rw [letters] at parsed
    cases parsed
    have notLevel : index ≠ depth := by
      intro same
      exact free _ (List.mem_singleton_self _) (by simp [Letter.index, same])
    have gInScope := Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (replacement := replacement)
      (read_scoped closed depth)
    by_cases below : index < depth
    · simp [frameWord, Nat.lt_succ_of_lt below, below, mulWord, invWord, Substitution.instantiateBVarAt, gInScope]
    · have above : depth < index := by omega
      have notBelow : ¬index < depth + 1 := by omega
      have shiftedNotBelow : ¬index - 1 < depth := by omega
      simp [frameWord, notBelow, Substitution.instantiateBVarAt, below, notLevel, shiftedNotBelow]
  | .fvar name, found, parsed, free => by
    simp [frameWord, Substitution.instantiateBVarAt]
  | .apply label [], found, parsed, free => by
    simp [frameWord, frameWords, Substitution.instantiateBVarAt]
  | .apply label [argument], found, parsed, free => by
    rw [letters] at parsed
    split at parsed
    · obtain ⟨inner, innerParsed, rfl⟩ := Option.map_eq_some_iff.mp parsed
      have inside := frameWord_instantiate closed depth replacement argument innerParsed
        (levelFree_invert.mp free)
      simp [frameWord, frameWords, Substitution.instantiateBVarAt, inside]
    · cases parsed
  | .apply label [left, right], found, parsed, free => by
    rw [letters] at parsed
    split at parsed
    · split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        cases parsed
        obtain ⟨leftFree, rightFree⟩ := levelFree_append.mp free
        have first := frameWord_instantiate closed depth replacement left leftParsed leftFree
        have second := frameWord_instantiate closed depth replacement right rightParsed rightFree
        simp [frameWord, frameWords, Substitution.instantiateBVarAt, first, second]
      · cases parsed
    · cases parsed
  | .apply label (_ :: _ :: _ :: _), found, parsed, _ => by simp [letters] at parsed
  | .lambda _ _, found, parsed, _ => by simp [letters] at parsed
  | .multiLambda _ _ _, found, parsed, _ => by simp [letters] at parsed
  | .subst _ _, found, parsed, _ => by simp [letters] at parsed
  | .collection _ _ _, found, parsed, _ => by simp [letters] at parsed
termination_by word => sizeOf word
decreasing_by all_goals sizeOf_pattern_dec

/-- Instantiating a level a word does not hold does not look at the replacement. -/
theorem instantiate_levelFree (depth : Nat) (replacement other : Pattern) :
    ∀ (word : Pattern) {found : List (Letter G)}, letters decl reading.constant word = some found →
      LevelFree depth found →
        Substitution.instantiateBVarAt depth replacement word = Substitution.instantiateBVarAt depth other word
  | .bvar index, found, parsed, free => by
    rw [letters] at parsed
    cases parsed
    have notLevel : index ≠ depth := by
      intro same
      exact free _ (List.mem_singleton_self _) (by simp [Letter.index, same])
    simp [Substitution.instantiateBVarAt, notLevel]
  | .fvar name, found, parsed, free => by simp [Substitution.instantiateBVarAt]
  | .apply label [], found, parsed, free => by simp [Substitution.instantiateBVarAt]
  | .apply label [argument], found, parsed, free => by
    rw [letters] at parsed
    split at parsed
    · obtain ⟨inner, innerParsed, rfl⟩ := Option.map_eq_some_iff.mp parsed
      have inside := instantiate_levelFree depth replacement other argument innerParsed (levelFree_invert.mp free)
      simp [Substitution.instantiateBVarAt, inside]
    · cases parsed
  | .apply label [left, right], found, parsed, free => by
    rw [letters] at parsed
    split at parsed
    · split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        cases parsed
        obtain ⟨leftFree, rightFree⟩ := levelFree_append.mp free
        have first := instantiate_levelFree depth replacement other left leftParsed leftFree
        have second := instantiate_levelFree depth replacement other right rightParsed rightFree
        simp [Substitution.instantiateBVarAt, first, second]
      · cases parsed
    · cases parsed
  | .apply label (_ :: _ :: _ :: _), found, parsed, _ => by simp [letters] at parsed
  | .lambda _ _, found, parsed, _ => by simp [letters] at parsed
  | .multiLambda _ _ _, found, parsed, _ => by simp [letters] at parsed
  | .subst _ _, found, parsed, _ => by simp [letters] at parsed
  | .collection _ _ _, found, parsed, _ => by simp [letters] at parsed
termination_by word => sizeOf word
decreasing_by all_goals sizeOf_pattern_dec

/-- **At a datum, instantiation commutes with the action**, when the datum does not hold the level. -/
theorem actData_instantiate {g : Pattern} {x : G} (closed : read decl reading.constant g = some x) (depth : Nat)
    (replacement other : Pattern) {word : Pattern} {found : List (Letter G)}
    (parsed : letters decl reading.constant word = some found) (free : LevelFree depth found) :
    Substitution.instantiateBVarAt depth replacement (actData decl g (depth + 1) word) =
      actData decl g depth (Substitution.instantiateBVarAt depth other word) := by
  have gInScope := Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (replacement := replacement)
    (read_scoped closed depth)
  unfold actData
  simp only [liftBVars_closed closed]
  rw [instantiate_levelFree depth other replacement word parsed free]
  simp only [mulWord, Substitution.instantiateBVarAt, List.map_cons, List.map_nil, gInScope]
  rw [frameWord_instantiate closed depth replacement word parsed free]

end WordInstantiation

/-! ## One step of a walk -/

section Steps

variable {language decl}
variable {f v : Nat → Pattern → Pattern} {depth : Nat} {type : TypeExpr}

theorem mapFrame_data {pattern : Pattern} (data : type = .base decl.dataSort) :
    mapFrame language decl f v depth type pattern = f depth pattern := by
  rw [mapFrame.eq_def, if_pos data]

theorem mapFrame_variable {pattern : Pattern} (notData : type ≠ .base decl.dataSort)
    (occurs : (decorated? decl pattern).isSome ∧ actionType language decl = some type) :
    mapFrame language decl f v depth type pattern = v depth pattern := by
  rw [mapFrame.eq_def, if_neg notData, if_pos occurs]

theorem mapFrame_apply_structural {label : String} {arguments : List Pattern} {types : List TypeExpr}
    (notData : type ≠ .base decl.dataSort)
    (structural : ¬((decorated? decl (.apply label arguments)).isSome ∧ actionType language decl = some type))
    (found : paramTypes language label = some types) :
    mapFrame language decl f v depth type (.apply label arguments) =
      .apply label (mapFrameArgs language decl f v depth types arguments) := by
  rw [mapFrame.eq_def, if_neg notData, if_neg structural]
  simp only [found]

theorem mapFrame_apply_unknown {label : String} {arguments : List Pattern}
    (notData : type ≠ .base decl.dataSort)
    (structural : ¬((decorated? decl (.apply label arguments)).isSome ∧ actionType language decl = some type))
    (found : paramTypes language label = none) :
    mapFrame language decl f v depth type (.apply label arguments) = .apply label arguments := by
  rw [mapFrame.eq_def, if_neg notData, if_neg structural]
  simp only [found]

theorem mapFrame_lambda {binder : Option String} {body : Pattern} {domain codomain : TypeExpr}
    (notData : TypeExpr.arrow domain codomain ≠ .base decl.dataSort) :
    mapFrame language decl f v depth (.arrow domain codomain) (.lambda binder body) =
      .lambda binder (mapFrame language decl f v (depth + 1) codomain body) := by
  rw [mapFrame.eq_def, if_neg notData, if_neg (by simp [decorated?])]

theorem mapFrame_multiLambda {arity : Nat} {binders : List String} {body : Pattern} {domain codomain : TypeExpr}
    (notData : TypeExpr.arrow domain codomain ≠ .base decl.dataSort) :
    mapFrame language decl f v depth (.arrow domain codomain) (.multiLambda arity binders body) =
      .multiLambda arity binders (mapFrame language decl f v (depth + arity) codomain body) := by
  rw [mapFrame.eq_def, if_neg notData, if_neg (by simp [decorated?])]

theorem mapFrame_collection {kind : CollType} {elements : List Pattern} {rest : Option String}
    {element : TypeExpr} (notData : type ≠ .base decl.dataSort) (found : elementType language type kind = some element) :
    mapFrame language decl f v depth type (.collection kind elements rest) =
      .collection kind (mapFrameList language decl f v depth element elements) rest := by
  rw [mapFrame.eq_def, if_neg notData, if_neg (by simp [decorated?])]
  simp only [found]

theorem mapFrame_lambda_other {binder : Option String} {body : Pattern}
    (notData : type ≠ .base decl.dataSort) (notArrow : ∀ domain codomain, type ≠ .arrow domain codomain) :
    mapFrame language decl f v depth type (.lambda binder body) = .lambda binder body := by
  rw [mapFrame.eq_def, if_neg notData, if_neg (by simp [decorated?])]
  cases type with
  | arrow domain codomain => exact absurd rfl (notArrow domain codomain)
  | _ => rfl

theorem mapFrame_multiLambda_other {arity : Nat} {binders : List String} {body : Pattern}
    (notData : type ≠ .base decl.dataSort) (notArrow : ∀ domain codomain, type ≠ .arrow domain codomain) :
    mapFrame language decl f v depth type (.multiLambda arity binders body) = .multiLambda arity binders body := by
  rw [mapFrame.eq_def, if_neg notData, if_neg (by simp [decorated?])]
  cases type with
  | arrow domain codomain => exact absurd rfl (notArrow domain codomain)
  | _ => rfl

theorem mapFrame_collection_unknown {kind : CollType} {elements : List Pattern} {rest : Option String}
    (notData : type ≠ .base decl.dataSort) (found : elementType language type kind = none) :
    mapFrame language decl f v depth type (.collection kind elements rest) = .collection kind elements rest := by
  rw [mapFrame.eq_def, if_neg notData, if_neg (by simp [decorated?])]
  simp only [found]

theorem mapFrame_leaf {pattern : Pattern} (notData : type ≠ .base decl.dataSort)
    (structural : ¬((decorated? decl pattern).isSome ∧ actionType language decl = some type))
    (leaf : (∃ index, pattern = .bvar index) ∨ (∃ name, pattern = .fvar name) ∨
      ∃ body replacement, pattern = .subst body replacement) :
    mapFrame language decl f v depth type pattern = pattern := by
  rw [mapFrame.eq_def, if_neg notData, if_neg structural]
  rcases leaf with ⟨index, rfl⟩ | ⟨name, rfl⟩ | ⟨body, replacement, rfl⟩ <;> rfl

end Steps

/-! ## Instantiation at occurrences -/

section InstOccurrences

variable {language decl}

theorem instVariable_bare (bodyType : TypeExpr) (replacement : Pattern) (depth index : Nat) :
    instVariable language decl bodyType replacement depth (.bvar index) =
      if index = depth then Substitution.liftBVars 0 depth replacement
      else if depth < index then .bvar (index - 1) else .bvar index := by
  simp [instVariable, decorated?]

theorem instVariable_free (bodyType : TypeExpr) (replacement : Pattern) (depth : Nat) (name : String) :
    instVariable language decl bodyType replacement depth (.fvar name) = .fvar name := by
  simp [instVariable, decorated?]

theorem instVariable_decorated (bodyType : TypeExpr) (replacement coefficient : Pattern) (depth index : Nat) :
    instVariable language decl bodyType replacement depth (.apply decl.action [coefficient, .bvar index]) =
      if index = depth then
        frameAct language decl (Substitution.instantiateBVarAt depth replacement coefficient) bodyType
          (Substitution.liftBVars 0 depth replacement)
      else
        .apply decl.action [Substitution.instantiateBVarAt depth replacement coefficient,
          if depth < index then .bvar (index - 1) else .bvar index] := by
  simp [instVariable, decorated?]

theorem instVariable_decorated_free (bodyType : TypeExpr) (replacement coefficient : Pattern) (depth : Nat)
    (name : String) :
    instVariable language decl bodyType replacement depth (.apply decl.action [coefficient, .fvar name]) =
      .apply decl.action [Substitution.instantiateBVarAt depth replacement coefficient, .fvar name] := by
  simp [instVariable, decorated?]

/-- **Instantiation keeps a coefficient**: a decorated occurrence becomes a decorated occurrence or the
action of its coefficient on the replacement, never a bare variable. -/
theorem instVariable_keepsNotBare {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) (replacement : Pattern) :
    KeepsNotBare decl (instVariable language decl bodyType replacement) := by
  intro depth pattern occurs notBare
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  cases coefficient with
  | none => rw [plain rfl] at notBare; rw [notBare] at bare; cases bare
  | some c =>
    have same := (applied c rfl).symm
    subst same
    have bodyTypeNotData : bodyType ≠ .base decl.dataSort := fun equal => bodyNotData (equal ▸ bodySort)
    match occurrenceVar, bare with
    | .bvar index, _ =>
      rw [instVariable_decorated]
      split
      · unfold frameAct
        generalize Substitution.liftBVars 0 depth replacement = lifted
        cases lifted with
        | bvar other =>
          rw [mapFrame_variable bodyTypeNotData ⟨by simp [decorated?], bodySort⟩]
          simp [actVariable, decorated?, isBare]
        | fvar other =>
          rw [mapFrame_variable bodyTypeNotData ⟨by simp [decorated?], bodySort⟩]
          simp [actVariable, decorated?, isBare]
        | apply label arguments =>
          exact mapFrame_notBare (actVariable_keeps _).notBare bodyTypeNotData rfl
        | lambda binder body => exact mapFrame_notBare (actVariable_keeps _).notBare bodyTypeNotData rfl
        | multiLambda arity binders body => exact mapFrame_notBare (actVariable_keeps _).notBare bodyTypeNotData rfl
        | subst body other => exact mapFrame_notBare (actVariable_keeps _).notBare bodyTypeNotData rfl
        | collection kind elements rest => exact mapFrame_notBare (actVariable_keeps _).notBare bodyTypeNotData rfl
      · rfl
    | .fvar name, _ => rw [instVariable_decorated_free]; rfl

end InstOccurrences

/-! ## The occurrences -/

section Occurrence

variable {language decl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- The action walk from a depth. -/
abbrev actWalkAt (g : Pattern) (depth : Nat) (type : TypeExpr) (pattern : Pattern) : Pattern :=
  mapFrame language decl (actData decl g) (actVariable decl g) depth type pattern

/-- The instantiation walk from a depth. -/
abbrev instWalkAt (bodyType : TypeExpr) (replacement : Pattern) (depth : Nat) (type : TypeExpr) (pattern : Pattern) :
    Pattern :=
  mapFrame language decl (fun k datum => Substitution.instantiateBVarAt k replacement datum)
    (instVariable language decl bodyType replacement) depth type pattern

/-- The normal-form walk from a depth. -/
abbrev normalWalkAt (reading : DataReading decl G) (depth : Nat) (type : TypeExpr) (pattern : Pattern) : Pattern :=
  mapFrame language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth type pattern

omit [DecidableEq G] in
theorem actData_closed_word {g c : Pattern} {x y : G} (gRead : read decl reading.constant g = some x)
    (cRead : read decl reading.constant c = some y) (depth : Nat) :
    actData decl g depth c = mulWord decl g c := by
  unfold actData
  simp only [liftBVars_closed gRead, frameWord_closed cRead]

/-- **At an occurrence of the body sort, instantiating the acted body with the acted replacement is acting
on the instantiated body**, in normal form. -/
theorem occurrence_equivariant (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType)
    {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x)
    {replacement : Pattern} (replacementClosed : Closed replacement)
    (replacementParses : WordsParse language reading bodyType replacement)
    (depth : Nat) {occurrence : Pattern} (occurs : (decorated? decl occurrence).isSome)
    (coefficients : ∀ c v, decorated? decl occurrence = some (some c, v) → ∃ y, read decl reading.constant c = some y) :
    normalWalkAt (language := language) reading depth bodyType
        (instVariable language decl bodyType (frameAct language decl g bodyType replacement) depth
          (actVariable decl g (depth + 1) occurrence)) =
      normalWalkAt (language := language) reading depth bodyType
        (actWalkAt (language := language) (decl := decl) g depth bodyType
          (instVariable language decl bodyType replacement depth occurrence)) := by
  have bodyTypeNotData : bodyType ≠ .base decl.dataSort := fun equal => bodyNotData (equal ▸ bodySort)
  have acted := frameAct_closed (language := language) gRead bodyType replacementClosed
  have actedLift : Substitution.liftBVars 0 depth (frameAct language decl g bodyType replacement) =
      frameAct language decl g bodyType replacement := Substitution.liftBVars_eq_self_of_isWellScopedAt acted
  have replacementLift : Substitution.liftBVars 0 depth replacement = replacement :=
    Substitution.liftBVars_eq_self_of_isWellScopedAt replacementClosed
  have gInst : ∀ Q, Substitution.instantiateBVarAt depth Q g = g := fun Q =>
    Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped gRead depth)
  have gLift := liftBVars_closed gRead 0 (depth + 1)
  have gLift' := liftBVars_closed gRead 0 depth
  have variableStep : ∀ occ, (decorated? decl occ).isSome →
      actWalkAt (language := language) (decl := decl) g depth bodyType occ = actVariable decl g depth occ :=
    fun occ isOcc => mapFrame_variable bodyTypeNotData ⟨isOcc, bodySort⟩
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  cases coefficient with
  | none =>
    have same := (plain rfl).symm
    subst same
    match occurrenceVar, bare with
    | .bvar index, _ =>
      rcases Nat.lt_trichotomy index depth with below | rfl | above
      · rw [actVariable_bare_inside g (Nat.lt_succ_of_lt below), instVariable_bare, instVariable_bare]
        simp only [if_neg (Nat.ne_of_lt below), if_neg (show ¬depth < index by omega)]
        rw [variableStep _ (by simp [decorated?]), actVariable_bare_inside g below]
      · rw [actVariable_bare_inside g (Nat.lt_succ_self index), instVariable_bare, instVariable_bare, if_pos rfl,
          if_pos rfl, actedLift, replacementLift]
        unfold actWalkAt
        rw [frameAct_closed_depth gRead index bodyType replacementClosed]
      · rw [actVariable_bare_outside g (by omega), gLift, instVariable_decorated, instVariable_bare]
        simp only [if_neg (Nat.ne_of_gt above), if_pos above, gInst]
        rw [variableStep _ (by simp [decorated?]), actVariable_bare_outside g (by omega), gLift']
    | .fvar name, _ =>
      rw [actVariable_bare_free g (depth + 1) name, gLift, instVariable_decorated_free, gInst, instVariable_free,
        variableStep _ (by simp [decorated?]), actVariable_bare_free g depth name, gLift']
  | some c =>
    have same := (applied c rfl).symm
    subst same
    obtain ⟨y, cRead⟩ := coefficients c occurrenceVar found
    have cInst : ∀ Q, Substitution.instantiateBVarAt depth Q c = c := fun Q =>
      Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped cRead depth)
    have dataDeep := actData_closed_word gRead cRead (depth + 1)
    have dataShallow := actData_closed_word gRead cRead depth
    have conjugateRead : read decl reading.constant (mulWord decl (mulWord decl g c) (invWord decl g)) =
        some (x * y * x⁻¹) := by
      rw [mulWord, read_multiply, read_mulWord gRead cRead, invWord, read, if_pos rfl, gRead]
      rfl
    have conjugateInst : ∀ Q, Substitution.instantiateBVarAt depth Q (mulWord decl (mulWord decl g c) (invWord decl g)) =
        mulWord decl (mulWord decl g c) (invWord decl g) := fun Q =>
      Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped conjugateRead depth)
    have productInst : ∀ Q, Substitution.instantiateBVarAt depth Q (mulWord decl g c) = mulWord decl g c := fun Q =>
      Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped (read_mulWord gRead cRead) depth)
    match occurrenceVar, bare with
    | .bvar index, _ =>
      rcases Nat.lt_trichotomy index depth with below | rfl | above
      · rw [actVariable_decorated_inside g c (Nat.lt_succ_of_lt below), dataDeep, gLift, instVariable_decorated,
          instVariable_decorated]
        simp only [if_neg (Nat.ne_of_lt below), if_neg (show ¬depth < index by omega), conjugateInst, cInst]
        rw [variableStep _ (by simp [decorated?]), actVariable_decorated_inside g c below, dataShallow, gLift']
      · rw [actVariable_decorated_inside g c (Nat.lt_succ_self index), dataDeep, gLift, instVariable_decorated,
          if_pos rfl, conjugateInst, actedLift, instVariable_decorated, if_pos rfl, cInst, replacementLift]
        have innerClosed := frameAct_closed (language := language) cRead bodyType replacementClosed
        unfold actWalkAt
        rw [frameAct_closed_depth gRead index bodyType innerClosed]
        unfold normalWalkAt
        rw [frameNormal_depth, frameNormal_depth,
          frameAct_mul bodyNotData conjugateRead gRead bodyType replacement replacementParses,
          frameAct_mul bodyNotData gRead cRead bodyType replacement replacementParses]
        apply frameAct_element (x := x * y) bodyNotData _ _ bodyType replacement replacementParses
        · rw [read_mulWord conjugateRead gRead]
          simp [mul_assoc]
        · exact read_mulWord gRead cRead
      · rw [actVariable_decorated_outside g c (by omega), dataDeep, instVariable_decorated, instVariable_decorated]
        simp only [if_neg (Nat.ne_of_gt above), if_pos above, productInst, cInst]
        rw [variableStep _ (by simp [decorated?]), actVariable_decorated_outside g c (by omega), dataShallow]
    | .fvar name, _ =>
      rw [actVariable_decorated_free g c (depth + 1) name, dataDeep, instVariable_decorated_free, productInst,
        instVariable_decorated_free, cInst, variableStep _ (by simp [decorated?]),
        actVariable_decorated_free g c depth name, dataShallow]

end Occurrence

/-! ## The action commutes with substitution -/

section Equivariance

variable {language decl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- The data and variable branches of an equivariance step; leaves the structural branch with `data`,
`occurs`, and `ready` at the structural match. -/
syntax "equi_cases" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| equi_cases $pattern) => `(tactic| (
      rw [FrameAll.eq_def] at ready
      unfold normalWalkAt actWalkAt
      by_cases data : type = .base decl.dataSort
      · rw [if_pos data] at ready
        simp only [mapFrame_data data]
        exact dataCase depth _ ready
      rw [if_neg data] at ready
      by_cases occurs : (decorated? decl $pattern).isSome ∧ actionType language decl = some type
      · rw [if_pos occurs] at ready
        rw [mapFrame_variable (f := actData decl g) (v := actVariable decl g) data occurs,
          mapFrame_variable (v := outerVariable) data ⟨(actVariable_keeps g).occurs _ _ occurs.1, occurs.2⟩,
          mapFrame_variable (v := innerVariable) data occurs]
        exact occurrenceCase depth type _ occurs.2 data occurs.1 ready
      rw [if_neg occurs] at ready))

mutual
  /-- **A walk commutes with the action**, in normal form, when it does at data and at occurrences: the
  walk on the acted term at one depth deeper (`outerData`, `outerVariable`) against the action on the
  walked term (`innerData`, `innerVariable`). -/
  theorem walk_equivariant (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {g : Pattern} {innerData innerVariable outerData outerVariable : Nat → Pattern → Pattern}
      {dataOk variableOk : Nat → Pattern → Prop}
      (keepsInner : KeepsNotBare decl innerVariable) (keepsOuter : KeepsNotBare decl outerVariable)
      (dataCase : ∀ depth datum, dataOk depth datum →
        wordNormal decl reading (outerData depth (actData decl g (depth + 1) datum)) =
          wordNormal decl reading (actData decl g depth (innerData depth datum)))
      (occurrenceCase : ∀ depth type occurrence, actionType language decl = some type → type ≠ .base decl.dataSort →
        (decorated? decl occurrence).isSome → variableOk depth occurrence →
          normalWalkAt (language := language) reading depth type
              (outerVariable depth (actVariable decl g (depth + 1) occurrence)) =
            normalWalkAt (language := language) reading depth type
              (actWalkAt (language := language) (decl := decl) g depth type (innerVariable depth occurrence))) :
      ∀ (depth : Nat) (type : TypeExpr) (body : Pattern), FrameAll language decl dataOk variableOk depth type body →
        normalWalkAt (language := language) reading depth type
            (mapFrame language decl outerData outerVariable depth type
              (actWalkAt (language := language) (decl := decl) g (depth + 1) type body)) =
          normalWalkAt (language := language) reading depth type
            (actWalkAt (language := language) (decl := decl) g depth type
              (mapFrame language decl innerData innerVariable depth type body))
    | depth, type, .apply label arguments, ready => by
      equi_cases (.apply label arguments)
      have structuralA := decorated?_mapFrame_structural (language := language) (f := actData decl g)
        (depth := depth + 1) (actVariable_keeps g).notBare bodyNotData data occurs
      have structuralI := decorated?_mapFrame_structural (language := language) (f := innerData) (depth := depth)
        keepsInner bodyNotData data occurs
      cases found : paramTypes language label with
      | none => simp only [mapFrame_apply_unknown data occurs found]
      | some types =>
        dsimp only at ready
        rw [found] at ready
        dsimp only at ready
        rw [mapFrame_apply_structural data occurs found] at structuralA structuralI
        rw [mapFrame_apply_structural data occurs found, mapFrame_apply_structural data occurs found]
        have structuralIA := decorated?_mapFrame_structural (language := language) (f := outerData) (depth := depth)
          keepsOuter bodyNotData data structuralA
        have structuralAI := decorated?_mapFrame_structural (language := language) (f := actData decl g)
          (depth := depth) (actVariable_keeps g).notBare bodyNotData data structuralI
        rw [mapFrame_apply_structural data structuralA found] at structuralIA
        rw [mapFrame_apply_structural data structuralI found] at structuralAI
        rw [mapFrame_apply_structural data structuralA found, mapFrame_apply_structural data structuralI found,
          mapFrame_apply_structural data structuralIA found, mapFrame_apply_structural data structuralAI found]
        rw [walkArgs_equivariant bodyNotData keepsInner keepsOuter dataCase occurrenceCase depth types arguments ready]
    | depth, type, .lambda binder body, ready => by
      equi_cases (.lambda binder body)
      dsimp only at ready
      cases type with
      | arrow domain codomain =>
        rw [mapFrame_lambda data, mapFrame_lambda data, mapFrame_lambda data, mapFrame_lambda data,
          mapFrame_lambda data, mapFrame_lambda data]
        have inner := walk_equivariant bodyNotData keepsInner keepsOuter dataCase occurrenceCase (depth + 1) codomain
          body ready
        unfold normalWalkAt actWalkAt at inner
        rw [inner]
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        simp only [mapFrame_lambda_other data notArrow]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        simp only [mapFrame_lambda_other data notArrow]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        simp only [mapFrame_lambda_other data notArrow]
    | depth, type, .multiLambda arity binders body, ready => by
      equi_cases (.multiLambda arity binders body)
      dsimp only at ready
      cases type with
      | arrow domain codomain =>
        rw [mapFrame_multiLambda data, mapFrame_multiLambda data, mapFrame_multiLambda data,
          mapFrame_multiLambda data, mapFrame_multiLambda data, mapFrame_multiLambda data,
          show depth + 1 + arity = depth + arity + 1 by omega]
        have inner := walk_equivariant bodyNotData keepsInner keepsOuter dataCase occurrenceCase (depth + arity)
          codomain body ready
        unfold normalWalkAt actWalkAt at inner
        rw [inner]
      | base sort =>
        have notArrow : ∀ domain codomain, TypeExpr.base sort ≠ .arrow domain codomain := by simp
        simp only [mapFrame_multiLambda_other data notArrow]
      | collection kind element =>
        have notArrow : ∀ domain codomain, TypeExpr.collection kind element ≠ .arrow domain codomain := by simp
        simp only [mapFrame_multiLambda_other data notArrow]
      | multiBinder inner =>
        have notArrow : ∀ domain codomain, TypeExpr.multiBinder inner ≠ .arrow domain codomain := by simp
        simp only [mapFrame_multiLambda_other data notArrow]
    | depth, type, .collection kind elements rest, ready => by
      equi_cases (.collection kind elements rest)
      dsimp only at ready
      cases found : elementType language type kind with
      | none => simp only [mapFrame_collection_unknown data found]
      | some element =>
        rw [found] at ready
        dsimp only at ready
        simp only [mapFrame_collection data found]
        rw [walkList_equivariant bodyNotData keepsInner keepsOuter dataCase occurrenceCase depth element elements ready]
    | depth, type, .bvar index, ready => by
      equi_cases (.bvar index)
      simp only [mapFrame_leaf data occurs (.inl ⟨index, rfl⟩)]
    | depth, type, .fvar name, ready => by
      equi_cases (.fvar name)
      simp only [mapFrame_leaf data occurs (.inr (.inl ⟨name, rfl⟩))]
    | depth, type, .subst body replacement', ready => by
      equi_cases (.subst body replacement')
      simp only [mapFrame_leaf data occurs (.inr (.inr ⟨body, replacement', rfl⟩))]
  termination_by _ _ body _ => sizeOf body
  decreasing_by all_goals sizeOf_pattern_dec

  theorem walkArgs_equivariant (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {g : Pattern} {innerData innerVariable outerData outerVariable : Nat → Pattern → Pattern}
      {dataOk variableOk : Nat → Pattern → Prop}
      (keepsInner : KeepsNotBare decl innerVariable) (keepsOuter : KeepsNotBare decl outerVariable)
      (dataCase : ∀ depth datum, dataOk depth datum →
        wordNormal decl reading (outerData depth (actData decl g (depth + 1) datum)) =
          wordNormal decl reading (actData decl g depth (innerData depth datum)))
      (occurrenceCase : ∀ depth type occurrence, actionType language decl = some type → type ≠ .base decl.dataSort →
        (decorated? decl occurrence).isSome → variableOk depth occurrence →
          normalWalkAt (language := language) reading depth type
              (outerVariable depth (actVariable decl g (depth + 1) occurrence)) =
            normalWalkAt (language := language) reading depth type
              (actWalkAt (language := language) (decl := decl) g depth type (innerVariable depth occurrence))) :
      ∀ (depth : Nat) (types : List TypeExpr) (arguments : List Pattern),
        FrameAllArgs language decl dataOk variableOk depth types arguments →
          mapFrameArgs language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth
              types (mapFrameArgs language decl outerData outerVariable depth types
                (mapFrameArgs language decl (actData decl g) (actVariable decl g) (depth + 1) types arguments)) =
            mapFrameArgs language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth
              types (mapFrameArgs language decl (actData decl g) (actVariable decl g) depth types
                (mapFrameArgs language decl innerData innerVariable depth types arguments))
    | depth, type :: types, argument :: arguments, ready => by
      rw [FrameAllArgs] at ready
      simp only [mapFrameArgs]
      have head := walk_equivariant bodyNotData keepsInner keepsOuter dataCase occurrenceCase depth type argument
        ready.1
      unfold normalWalkAt actWalkAt at head
      rw [head, walkArgs_equivariant bodyNotData keepsInner keepsOuter dataCase occurrenceCase depth types arguments
        ready.2]
    | depth, [], arguments, _ => by simp [mapFrameArgs]
    | depth, _ :: _, [], _ => by simp [mapFrameArgs]
  termination_by _ _ arguments _ => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem walkList_equivariant (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
      {g : Pattern} {innerData innerVariable outerData outerVariable : Nat → Pattern → Pattern}
      {dataOk variableOk : Nat → Pattern → Prop}
      (keepsInner : KeepsNotBare decl innerVariable) (keepsOuter : KeepsNotBare decl outerVariable)
      (dataCase : ∀ depth datum, dataOk depth datum →
        wordNormal decl reading (outerData depth (actData decl g (depth + 1) datum)) =
          wordNormal decl reading (actData decl g depth (innerData depth datum)))
      (occurrenceCase : ∀ depth type occurrence, actionType language decl = some type → type ≠ .base decl.dataSort →
        (decorated? decl occurrence).isSome → variableOk depth occurrence →
          normalWalkAt (language := language) reading depth type
              (outerVariable depth (actVariable decl g (depth + 1) occurrence)) =
            normalWalkAt (language := language) reading depth type
              (actWalkAt (language := language) (decl := decl) g depth type (innerVariable depth occurrence))) :
      ∀ (depth : Nat) (element : TypeExpr) (patterns : List Pattern),
        FrameAllList language decl dataOk variableOk depth element patterns →
          mapFrameList language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth
              element (mapFrameList language decl outerData outerVariable depth element
                (mapFrameList language decl (actData decl g) (actVariable decl g) (depth + 1) element patterns)) =
            mapFrameList language decl (fun _ datum => wordNormal decl reading datum) (normalVariable decl reading) depth
              element (mapFrameList language decl (actData decl g) (actVariable decl g) depth element
                (mapFrameList language decl innerData innerVariable depth element patterns))
    | depth, element, [], _ => by simp [mapFrameList]
    | depth, element, pattern :: patterns, ready => by
      rw [FrameAllList] at ready
      simp only [mapFrameList]
      have head := walk_equivariant bodyNotData keepsInner keepsOuter dataCase occurrenceCase depth element pattern
        ready.1
      unfold normalWalkAt actWalkAt at head
      rw [head, walkList_equivariant bodyNotData keepsInner keepsOuter dataCase occurrenceCase depth element patterns
        ready.2]
  termination_by _ _ patterns _ => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- What the substitution theorem asks of a body: every datum is a word without the instantiated level,
and every decoration's coefficient is a closed word. -/
def SubstitutionReady (reading : DataReading decl G) (depth : Nat) (type : TypeExpr) (body : Pattern) : Prop :=
  FrameAll language decl
    (fun k datum => ∃ found, letters decl reading.constant datum = some found ∧ LevelFree k found)
    (fun _ occurrence => (decorated? decl occurrence).isSome ∧
      ∀ c v, decorated? decl occurrence = some (some c, v) → ∃ y, read decl reading.constant c = some y)
    depth type body

/-- **Instantiating the acted body with the acted replacement is acting on the instantiated body**, in
normal form, at every depth. -/
theorem body_equivariant (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType)
    {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x)
    {replacement : Pattern} (replacementClosed : Closed replacement)
    (replacementParses : WordsParse language reading bodyType replacement)
    (depth : Nat) (type : TypeExpr) (body : Pattern)
    (ready : SubstitutionReady (language := language) reading depth type body) :
    normalWalkAt (language := language) reading depth type
        (instWalkAt (language := language) (decl := decl) bodyType
          (frameAct language decl g bodyType replacement) depth type
          (actWalkAt (language := language) (decl := decl) g (depth + 1) type body)) =
      normalWalkAt (language := language) reading depth type
        (actWalkAt (language := language) (decl := decl) g depth type
          (instWalkAt (language := language) (decl := decl) bodyType replacement depth type body)) := by
  unfold instWalkAt
  apply walk_equivariant bodyNotData (instVariable_keepsNotBare bodySort bodyNotData replacement)
    (instVariable_keepsNotBare bodySort bodyNotData _) _ _ depth type body ready
  · intro k datum ⟨found, parsed, free⟩
    rw [actData_instantiate gRead k _ replacement parsed free]
  · intro k type' occurrence sort _ occurs ⟨_, coefficients⟩
    have sameType : type' = bodyType := Option.some.inj (sort.symm.trans bodySort)
    subst sameType
    exact occurrence_equivariant bodyNotData bodySort gRead replacementClosed replacementParses k occurs coefficients

end Equivariance

/-! ## Instantiating a data variable -/

section DataInstantiation

variable {decl}
variable {G : Type} [Group G] {reading : DataReading decl G}

/-- **Instantiating a data variable as an endomorphism of `G ∗ F(V)`**: the variable of level `depth`
becomes the element `y`, and the deeper bound variables lose the level. -/
def instHom (y : G) (depth : Nat) : FreeData G →* FreeData G :=
  Monoid.CoprodI.lift fun i =>
    match i with
    | none => Monoid.CoprodI.of
    | some (.bound index) =>
        (zpowersHom (FreeData G)
          (if index = depth then constEval y
            else if depth < index then powerEval (.bound (index - 1)) 1 else powerEval (.bound index) 1) :
          Multiplicative ℤ →* FreeData G)
    | some (.free _) => Monoid.CoprodI.of

theorem instHom_const (y : G) (depth : Nat) (c : G) : instHom y depth (constEval c) = constEval c :=
  Monoid.CoprodI.lift_of _ _

theorem instHom_bound (y : G) (depth index : Nat) :
    instHom y depth (powerEval (.bound index) 1) =
      if index = depth then constEval y
      else if depth < index then powerEval (.bound (index - 1)) 1 else powerEval (.bound index) 1 := by
  refine (Monoid.CoprodI.lift_of _ _).trans ?_
  dsimp only
  refine (zpowersHom_apply _ _ _).trans ?_
  show (if index = depth then constEval y
      else if depth < index then powerEval (DataVar.bound (index - 1)) 1 else powerEval (DataVar.bound index) 1) ^
        (1 : ℤ) = _
  exact zpow_one _

theorem instHom_free (y : G) (depth : Nat) (name : String) :
    instHom y depth (powerEval (.free name) 1) = powerEval (.free name) 1 :=
  Monoid.CoprodI.lift_of _ _

/-- **Renaming then instantiating with the acted datum is instantiating then renaming**:
`σ_{x y} ∘ φ_{x, depth + 1} = φ_{x, depth} ∘ σ_y`. -/
theorem instHom_frameHom (x y : G) (depth : Nat) :
    (instHom (x * y) depth).comp (frameHom x (depth + 1)) = (frameHom x depth).comp (instHom y depth) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  match i with
  | none =>
    apply MonoidHom.ext
    intro c
    simp only [MonoidHom.comp_apply]
    exact (congrArg (instHom (x * y) depth) (frameHom_const x (depth + 1) (show G from c))).trans
      ((instHom_const _ depth (show G from c)).trans
        ((frameHom_const x depth (show G from c)).symm.trans
          (congrArg (frameHom x depth) (instHom_const y depth (show G from c)).symm)))
  | some (.bound index) =>
    apply MonoidHom.ext_mint
    show instHom (x * y) depth (frameHom x (depth + 1) (powerEval (.bound index) 1)) =
      frameHom x depth (instHom y depth (powerEval (.bound index) 1))
    rcases Nat.lt_trichotomy index depth with below | rfl | above
    · rw [frameHom_inside x (Nat.lt_succ_of_lt below), map_mul, instHom_const, instHom_bound, instHom_bound]
      simp only [if_neg (Nat.ne_of_lt below), if_neg (show ¬depth < index by omega)]
      rw [frameHom_inside x below]
    · rw [frameHom_inside x (Nat.lt_succ_self index), map_mul, instHom_const, instHom_bound, instHom_bound]
      simp only [↓reduceIte]
      rw [frameHom_const, ← constEval_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    · rw [frameHom_outside x (show ¬index < depth + 1 by omega) 1, instHom_bound, instHom_bound]
      simp only [if_neg (Nat.ne_of_gt above), if_pos above]
      rw [frameHom_outside x (show ¬index - 1 < depth by omega) 1]
  | some (.free name) =>
    apply MonoidHom.ext_mint
    show instHom (x * y) depth (frameHom x (depth + 1) (powerEval (.free name) 1)) =
      frameHom x depth (instHom y depth (powerEval (.free name) 1))
    rw [frameHom_free, instHom_free, instHom_free, frameHom_free]

/-- **Instantiating a data variable inside a word is the substitution endomorphism.** -/
theorem letters_instantiate {datum : Pattern} {y : G} (datumRead : read decl reading.constant datum = some y)
    (depth : Nat) :
    ∀ (word : Pattern) {found : List (Letter G)}, letters decl reading.constant word = some found →
      ∃ again, letters decl reading.constant (Substitution.instantiateBVarAt depth datum word) = some again ∧
        evalLetters again = instHom y depth (evalLetters found)
  | .bvar index, found, parsed => by
    rw [letters] at parsed
    cases parsed
    have single : evalLetters [Letter.power (G := G) (.bound index) 1] = powerEval (.bound index) 1 := by
      simp only [evalLetters, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]; rfl
    rw [single, instHom_bound]
    rcases Nat.lt_trichotomy index depth with below | rfl | above
    · refine ⟨[.power (.bound index) 1], ?_, ?_⟩
      · simp [Substitution.instantiateBVarAt, below, letters]
      · rw [single, if_neg (Nat.ne_of_lt below), if_neg (by omega)]
    · obtain ⟨datumLetters, datumParsed, datumValue⟩ := letters_of_read reading.constant datum datumRead
      refine ⟨datumLetters, ?_, ?_⟩
      · simp only [Substitution.instantiateBVarAt, Nat.lt_irrefl, if_false, if_true]
        rw [liftBVars_closed datumRead]
        exact datumParsed
      · rw [datumValue, if_pos rfl]
    · refine ⟨[.power (.bound (index - 1)) 1], ?_, ?_⟩
      · have notBelow : ¬index < depth := by omega
        have notSame : index ≠ depth := by omega
        simp [Substitution.instantiateBVarAt, notBelow, notSame, letters]
      · rw [if_neg (Nat.ne_of_gt above), if_pos above]
        simp only [evalLetters, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]; rfl
  | .fvar name, found, parsed => by
    rw [letters] at parsed
    cases parsed
    refine ⟨[.power (.free name) 1], by simp [Substitution.instantiateBVarAt, letters], ?_⟩
    have single : evalLetters [Letter.power (G := G) (.free name) 1] = powerEval (.free name) 1 := by
      simp only [evalLetters, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]; rfl
    rw [single, instHom_free]
  | .apply label [], found, parsed => by
    refine ⟨found, by simpa [Substitution.instantiateBVarAt] using parsed, ?_⟩
    rw [letters] at parsed
    split at parsed
    · cases parsed
      rw [evalLetters_nil, map_one]
    · obtain ⟨c, _, rfl⟩ := Option.map_eq_some_iff.mp parsed
      have single : evalLetters [Letter.const c] = constEval c := by
        simp only [evalLetters, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]; rfl
      rw [single, instHom_const]
  | .apply label [argument], found, parsed => by
    rw [letters] at parsed
    split at parsed
    · rename_i inverse
      obtain ⟨inner, innerParsed, rfl⟩ := Option.map_eq_some_iff.mp parsed
      obtain ⟨again, againParsed, value⟩ := letters_instantiate datumRead depth argument innerParsed
      refine ⟨invertLetters again, ?_, ?_⟩
      · simp only [Substitution.instantiateBVarAt, List.map_cons, List.map_nil]
        rw [letters, if_pos inverse, againParsed]
        rfl
      · rw [evalLetters_invert, evalLetters_invert, value, map_inv]
    · cases parsed
  | .apply label [left, right], found, parsed => by
    rw [letters] at parsed
    split at parsed
    · rename_i multiply
      split at parsed
      · rename_i leftLetters rightLetters leftParsed rightParsed
        cases parsed
        obtain ⟨leftAgain, leftAgainParsed, leftValue⟩ := letters_instantiate datumRead depth left leftParsed
        obtain ⟨rightAgain, rightAgainParsed, rightValue⟩ := letters_instantiate datumRead depth right rightParsed
        refine ⟨leftAgain ++ rightAgain, ?_, ?_⟩
        · simp only [Substitution.instantiateBVarAt, List.map_cons, List.map_nil]
          rw [letters, if_pos multiply, leftAgainParsed, rightAgainParsed]
        · rw [evalLetters_append, evalLetters_append, leftValue, rightValue, map_mul]
      · cases parsed
    · cases parsed
  | .apply label (_ :: _ :: _ :: _), found, parsed => by simp [letters] at parsed
  | .lambda _ _, found, parsed => by simp [letters] at parsed
  | .multiLambda _ _ _, found, parsed => by simp [letters] at parsed
  | .subst _ _, found, parsed => by simp [letters] at parsed
  | .collection _ _ _, found, parsed => by simp [letters] at parsed
termination_by word => sizeOf word
decreasing_by all_goals sizeOf_pattern_dec

variable [DecidableEq G]

/-- **At a datum, instantiating the acted datum after the action is the action after instantiating.** -/
theorem actData_instantiateDatum {g datum : Pattern} {x y : G} (gRead : read decl reading.constant g = some x)
    (datumRead : read decl reading.constant datum = some y) (depth : Nat) {word : Pattern}
    {found : List (Letter G)} (parsed : letters decl reading.constant word = some found) :
    wordNormal decl reading
        (Substitution.instantiateBVarAt depth (mulWord decl g datum) (actData decl g (depth + 1) word)) =
      wordNormal decl reading (actData decl g depth (Substitution.instantiateBVarAt depth datum word)) := by
  obtain ⟨acted, actedParsed, actedValue⟩ := letters_actData gRead (depth + 1) parsed
  obtain ⟨outer, outerParsed, outerValue⟩ :=
    letters_instantiate (read_mulWord gRead datumRead) depth _ actedParsed
  obtain ⟨inner, innerParsed, innerValue⟩ := letters_instantiate datumRead depth word parsed
  obtain ⟨both, bothParsed, bothValue⟩ := letters_actData gRead depth innerParsed
  apply (wordNormal_eq_iff outerParsed bothParsed).mpr
  rw [outerValue, actedValue, bothValue, innerValue, map_mul, instHom_const, ← MonoidHom.comp_apply,
    instHom_frameHom, MonoidHom.comp_apply]

end DataInstantiation

/-! ## The action commutes with instantiating a datum -/

section DatumEquivariance

variable {language decl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- **Instantiating a data variable**, as a walk from its binder: the datum replaces the variable inside
data words, and every bound variable deeper than it loses the level. -/
def instDatumWalk (datum : Pattern) (type : TypeExpr) (pattern : Pattern) : Pattern :=
  mapFrame language decl (fun k word => Substitution.instantiateBVarAt k datum word)
    (fun k occurrence => Substitution.instantiateBVarAt k datum occurrence) 0 type pattern

omit [Group G] [DecidableEq G] in
theorem instantiate_keepsNotBare (datum : Pattern) :
    KeepsNotBare decl (fun k occurrence => Substitution.instantiateBVarAt k datum occurrence) := by
  intro depth pattern occurs notBare
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  cases coefficient with
  | none => rw [plain rfl] at notBare; rw [notBare] at bare; cases bare
  | some c =>
    rw [applied c rfl]
    simp [Substitution.instantiateBVarAt, isBare]

/-- What the datum theorem asks of a body: every datum is a word, every decoration's coefficient a closed
word, and no occurrence of the body sort is the instantiated data variable. -/
def DatumReady (reading : DataReading decl G) (depth : Nat) (type : TypeExpr) (body : Pattern) : Prop :=
  FrameAll language decl (fun _ datum => (letters decl reading.constant datum).isSome)
    (fun k occurrence => (decorated? decl occurrence).isSome ∧
      (∀ c v, decorated? decl occurrence = some (some c, v) → ∃ y, read decl reading.constant c = some y) ∧
      (∀ c v, decorated? decl occurrence = some (c, v) → v ≠ .bvar k))
    depth type body

omit [DecidableEq G] in
theorem occurrence_instantiateDatum {g datum : Pattern} {x : G} (gRead : read decl reading.constant g = some x)
    (depth : Nat) {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome)
    (coefficients : ∀ c v, decorated? decl occurrence = some (some c, v) → ∃ z, read decl reading.constant c = some z)
    (notLevel : ∀ c v, decorated? decl occurrence = some (c, v) → v ≠ .bvar depth) :
    Substitution.instantiateBVarAt depth (mulWord decl g datum) (actVariable decl g (depth + 1) occurrence) =
      actVariable decl g depth (Substitution.instantiateBVarAt depth datum occurrence) := by
  have gInst : ∀ Q, Substitution.instantiateBVarAt depth Q g = g := fun Q =>
    Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped gRead depth)
  have gLift := liftBVars_closed gRead 0 (depth + 1)
  have gLift' := liftBVars_closed gRead 0 depth
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have variableNotLevel := notLevel coefficient occurrenceVar found
  cases coefficient with
  | none =>
    have same := (plain rfl).symm
    subst same
    match occurrenceVar, bare, variableNotLevel with
    | .bvar index, _, notSame =>
      have indexNe : index ≠ depth := fun equal => notSame (by rw [equal])
      rcases Nat.lt_or_gt_of_ne indexNe with below | above
      · rw [actVariable_bare_inside g (Nat.lt_succ_of_lt below)]
        simp [Substitution.instantiateBVarAt, below, actVariable_bare_inside g below]
      · rw [actVariable_bare_outside g (show ¬index < depth + 1 by omega), gLift]
        have notBelow : ¬index < depth := by omega
        simp only [Substitution.instantiateBVarAt, notBelow, indexNe, if_false, List.map_cons, List.map_nil,
          gInst]
        rw [actVariable_bare_outside g (show ¬index - 1 < depth by omega), gLift']
    | .fvar name, _, _ =>
      rw [actVariable_bare_free, gLift]
      simp only [Substitution.instantiateBVarAt, List.map_cons, List.map_nil, gInst]
      rw [actVariable_bare_free, gLift']
  | some c =>
    have same := (applied c rfl).symm
    subst same
    obtain ⟨z, cRead⟩ := coefficients c occurrenceVar found
    have cInst : ∀ Q, Substitution.instantiateBVarAt depth Q c = c := fun Q =>
      Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped cRead depth)
    have dataDeep := actData_closed_word gRead cRead (depth + 1)
    have dataShallow := actData_closed_word gRead cRead depth
    have productInst : ∀ Q, Substitution.instantiateBVarAt depth Q (mulWord decl g c) = mulWord decl g c := fun Q =>
      Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped (read_mulWord gRead cRead) depth)
    have inverseInst : ∀ Q, Substitution.instantiateBVarAt depth Q (invWord decl g) = invWord decl g := fun Q => by
      simp [invWord, Substitution.instantiateBVarAt, gInst]
    match occurrenceVar, bare, variableNotLevel with
    | .bvar index, _, notSame =>
      have indexNe : index ≠ depth := fun equal => notSame (by rw [equal])
      rcases Nat.lt_or_gt_of_ne indexNe with below | above
      · rw [actVariable_decorated_inside g c (Nat.lt_succ_of_lt below), dataDeep, gLift]
        simp only [Substitution.instantiateBVarAt, List.map_cons, List.map_nil, below, if_true]
        rw [show Substitution.instantiateBVarAt depth (mulWord decl g datum) (mulWord decl (mulWord decl g c)
            (invWord decl g)) = mulWord decl (mulWord decl g c) (invWord decl g) by
          simp [mulWord, Substitution.instantiateBVarAt] at productInst inverseInst ⊢
          exact ⟨productInst _, inverseInst _⟩, cInst]
        rw [actVariable_decorated_inside g c below, dataShallow, gLift']
      · rw [actVariable_decorated_outside g c (show ¬index < depth + 1 by omega), dataDeep]
        have notBelow : ¬index < depth := by omega
        simp only [Substitution.instantiateBVarAt, List.map_cons, List.map_nil, notBelow, indexNe, if_false]
        rw [productInst, cInst, actVariable_decorated_outside g c (show ¬index - 1 < depth by omega), dataShallow]
    | .fvar name, _, _ =>
      rw [actVariable_decorated_free g c, dataDeep]
      simp only [Substitution.instantiateBVarAt, List.map_cons, List.map_nil]
      rw [productInst, cInst, actVariable_decorated_free g c, dataShallow]

/-- **Instantiating the acted body with the acted datum is acting on the instantiated body**, in normal
form, at every depth. -/
theorem datum_equivariant (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {g datum : Pattern} {x y : G} (gRead : read decl reading.constant g = some x)
    (datumRead : read decl reading.constant datum = some y)
    (depth : Nat) (type : TypeExpr) (body : Pattern)
    (ready : DatumReady (language := language) reading depth type body) :
    normalWalkAt (language := language) reading depth type
        (mapFrame language decl (fun k word => Substitution.instantiateBVarAt k (mulWord decl g datum) word)
          (fun k occurrence => Substitution.instantiateBVarAt k (mulWord decl g datum) occurrence) depth type
          (actWalkAt (language := language) (decl := decl) g (depth + 1) type body)) =
      normalWalkAt (language := language) reading depth type
        (actWalkAt (language := language) (decl := decl) g depth type
          (mapFrame language decl (fun k word => Substitution.instantiateBVarAt k datum word)
            (fun k occurrence => Substitution.instantiateBVarAt k datum occurrence) depth type body)) := by
  apply walk_equivariant bodyNotData (instantiate_keepsNotBare datum) (instantiate_keepsNotBare _) _ _ depth type
    body ready
  · intro k word parsed
    obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsed
    exact actData_instantiateDatum gRead datumRead k parsed
  · intro k type' occurrence sort notData occurs ⟨_, coefficients, notLevel⟩
    rw [occurrence_instantiateDatum (datum := datum) gRead k occurs coefficients notLevel]
    have isOccurrence : (decorated? decl (Substitution.instantiateBVarAt k datum occurrence)).isSome := by
      obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
      obtain ⟨bare, plain, applied⟩ := decorated?_shape found
      have variableNotLevel := notLevel coefficient occurrenceVar found
      cases coefficient with
      | none =>
        rw [plain rfl]
        match occurrenceVar, bare, variableNotLevel with
        | .bvar index, _, notSame =>
          have indexNe : index ≠ k := fun equal => notSame (by rw [equal])
          by_cases below : index < k
          · simp [Substitution.instantiateBVarAt, below, decorated?]
          · simp [Substitution.instantiateBVarAt, below, indexNe, decorated?]
        | .fvar name, _, _ => simp [Substitution.instantiateBVarAt, decorated?]
      | some c =>
        rw [applied c rfl]
        match occurrenceVar, bare, variableNotLevel with
        | .bvar index, _, notSame =>
          have indexNe : index ≠ k := fun equal => notSame (by rw [equal])
          by_cases below : index < k
          · simp [Substitution.instantiateBVarAt, below, decorated?]
          · simp [Substitution.instantiateBVarAt, below, indexNe, decorated?]
        | .fvar name, _, _ => simp [Substitution.instantiateBVarAt, decorated?]
    unfold actWalkAt
    rw [mapFrame_variable notData ⟨isOccurrence, sort⟩]

end DatumEquivariance

/-! ## At a binder -/

section AtBinder

variable {language decl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- **The action commutes with substitution**: acting on an abstraction and instantiating its variable
with the acted replacement is acting on the instantiated body, in normal form. The replacement and the
acting word are closed, the body's data are words without the bound variable, and its decorations have
closed coefficients. -/
theorem instWalk_frameAct (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType)
    {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x)
    {replacement : Pattern} (replacementClosed : Closed replacement)
    (replacementParses : WordsParse language reading bodyType replacement)
    (binder : Option String) (domain type : TypeExpr) (body : Pattern)
    (ready : SubstitutionReady (language := language) reading 0 type body) :
    (∃ actedBody, frameAct language decl g (.arrow domain type) (.lambda binder body) = .lambda binder actedBody ∧
      frameNormal language decl reading type
          (instWalk language decl bodyType (frameAct language decl g bodyType replacement) type actedBody) =
        frameNormal language decl reading type
          (frameAct language decl g type (instWalk language decl bodyType replacement type body))) := by
  have arrowNotData : TypeExpr.arrow domain type ≠ .base decl.dataSort := by simp
  refine ⟨mapFrame language decl (actData decl g) (actVariable decl g) 1 type body, ?_, ?_⟩
  · unfold frameAct
    exact mapFrame_lambda arrowNotData
  · have equal := body_equivariant bodyNotData bodySort gRead replacementClosed replacementParses 0 type body ready
    unfold normalWalkAt instWalkAt actWalkAt at equal
    unfold frameNormal instWalk frameAct
    exact equal

/-- **The action commutes with instantiating a datum**: acting on an abstraction over a datum and
instantiating it with the acted datum `g · d` is acting on the instantiated body, in normal form. -/
theorem instDatum_frameAct (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {g datum : Pattern} {x y : G} (gRead : read decl reading.constant g = some x)
    (datumRead : read decl reading.constant datum = some y)
    (binder : Option String) (domain type : TypeExpr) (body : Pattern)
    (ready : DatumReady (language := language) reading 0 type body) :
    (∃ actedBody, frameAct language decl g (.arrow domain type) (.lambda binder body) = .lambda binder actedBody ∧
      frameNormal language decl reading type
          (instDatumWalk (language := language) (decl := decl) (mulWord decl g datum) type actedBody) =
        frameNormal language decl reading type
          (frameAct language decl g type (instDatumWalk (language := language) (decl := decl) datum type body))) := by
  have arrowNotData : TypeExpr.arrow domain type ≠ .base decl.dataSort := by simp
  refine ⟨mapFrame language decl (actData decl g) (actVariable decl g) 1 type body, ?_, ?_⟩
  · unfold frameAct
    exact mapFrame_lambda arrowNotData
  · have equal := datum_equivariant bodyNotData gRead datumRead 0 type body ready
    unfold normalWalkAt actWalkAt at equal
    unfold frameNormal instDatumWalk frameAct
    exact equal

end AtBinder

end Mettapedia.OSLF.MeTTaIL.Orientation
