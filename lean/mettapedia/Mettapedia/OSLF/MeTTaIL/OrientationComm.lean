import Mettapedia.OSLF.MeTTaIL.OrientationCongruence

/-!
# The action commutes with communication

A receive on a channel of orientation `a`, `for(@⟨c, a⟩ ⇒ λP.λδ. B)`, meets a message on a channel of
orientation `b`, `@⟨c, b⟩!(Q, d)`. Oriented communication superposes `(a b⁻¹) · K` and `(b a⁻¹) · K`,
where `K = B[Q/P, d/δ]` is the continuation (`commContinuation`): the payload instantiates the process
variable, discharging its decorations, and the datum instantiates the data variable.

Acting by `g` on the receive and the message gives the orientations `g a` and `g b`, the payload
`g · Q`, the datum `g d`, and the body acted on from under its two binders. Then, in normal form:

- `continuation_equivariant`: the continuation of the acted pair is the action on the continuation;
- `comm_equivariant`: each acted summand is the action on the summand,
  `((g a)(g b)⁻¹) · K' = g · ((a b⁻¹) · K)`, since `(g a)(g b)⁻¹ g = g (a b⁻¹)`;
- `commReduct_equivariant`: the reduct of the acted pair, both summands superposed, is the action on
  the reduct.

The body's data are words without `P`, its decorations have closed coefficients, and `δ` occurs only
at data (`BodyReady`); the payload is closed, with data words and closed coefficients (`PayloadReady`).

The proof instantiates `P` (`body_equivariant`), carries the equality of normal forms across the
instantiation of `δ` (`instDatumWalk_normal`, which needs the occurrences to avoid `δ` on both sides:
the acted side by reflection through the normal form, `frameAll_reflect`), and instantiates `δ`
(`datum_equivariant`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax

/-! ## What communication asks of its terms -/

section Readiness

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] {reading : DataReading decl G}

theorem read_invWord {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x) :
    read decl reading.constant (invWord decl g) = some x⁻¹ := by
  rw [invWord, read, if_pos rfl, gRead]
  rfl

/-- Every decoration's coefficient is a closed data word. -/
abbrev ClosedCoefficients (reading : DataReading decl G) (occurrence : Pattern) : Prop :=
  ∀ c v, decorated? decl occurrence = some (some c, v) → ∃ y, read decl reading.constant c = some y

/-- The occurrence's variable is not the bound variable of `level`. -/
abbrev NotVariable (decl : OrientationDecl) (level : Nat) (occurrence : Pattern) : Prop :=
  ∀ c v, decorated? decl occurrence = some (c, v) → v ≠ .bvar level

/-- **A payload ready for communication**: closed, its data words, its decorations' coefficients closed
words. -/
def PayloadReady (reading : DataReading decl G) (type : TypeExpr) (payload : Pattern) : Prop :=
  Closed payload ∧
    FrameAll language decl (fun _ datum => (letters decl reading.constant datum).isSome)
      (fun _ occurrence => (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence) 0 type payload

/-- **A receive's body ready for communication**, under its two binders: the process variable `P` outside
and the datum `δ` inside, so that `j` binders below the body `δ` is `j` and `P` is `j + 1`. Its data are
words without `P`, its decorations' coefficients are closed words, and no occurrence of the body sort
is `δ`. -/
def BodyReady (reading : DataReading decl G) (type : TypeExpr) (body : Pattern) : Prop :=
  FrameAll language decl
    (fun j datum => ∃ found, letters decl reading.constant datum = some found ∧ LevelFree (j + 1) found)
    (fun j occurrence => (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence ∧
      NotVariable decl j occurrence)
    0 type body

omit [Group G] in
/-- At an occurrence of the body sort, the position predicates are the variable predicate. -/
theorem frameAll_occurrence {dataOk variableOk : Nat → Pattern → Prop} {depth : Nat} {bodyType : TypeExpr}
    (bodySort : actionType language decl = some bodyType) (notData : bodyType ≠ .base decl.dataSort)
    {occurrence : Pattern} (occurs : (decorated? decl occurrence).isSome) :
    FrameAll language decl dataOk variableOk depth bodyType occurrence ↔ variableOk depth occurrence := by
  rw [FrameAll.eq_def, if_neg notData, if_pos ⟨occurs, bodySort⟩]

omit [Group G] in
/-- A scoped occurrence is not a variable bound further out. -/
theorem notVariable_of_scoped {occurrence : Pattern} {depth level : Nat}
    (inScope : occurrence.isWellScopedAt depth = true) (above : depth ≤ level) : NotVariable decl level occurrence := by
  intro c v found same
  subst same
  obtain ⟨_, plain, applied⟩ := decorated?_shape found
  cases c with
  | none =>
    rw [plain rfl] at inScope
    simp [Pattern.isWellScopedAt] at inScope
    omega
  | some c =>
    rw [applied c rfl] at inScope
    simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] at inScope
    omega

omit [Group G] in
theorem decorated?_some_of_bare {occurrenceVar : Pattern} (bare : isBare occurrenceVar = true) :
    (decorated? decl occurrenceVar).isSome := by
  rw [decorated?_of_bare bare]
  rfl

omit [Group G] in
theorem decorated?_some_of_action (coefficient : Pattern) {occurrenceVar : Pattern} (bare : isBare occurrenceVar = true) :
    (decorated? decl (.apply decl.action [coefficient, occurrenceVar])).isSome := by
  rw [decorated?_action _ _ bare]
  rfl

end Readiness

/-! ## Readiness along the walks -/

section Transport

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] {reading : DataReading decl G}

/-- The predicates of a continuation's body at the depth of the process variable: data words, decorated
occurrences with closed coefficients, none of them `δ`, one binder up. -/
abbrev BodyData (reading : DataReading decl G) : Nat → Pattern → Prop :=
  fun _ datum => (letters decl reading.constant datum).isSome

abbrev BodyVariables (reading : DataReading decl G) : Nat → Pattern → Prop :=
  fun k occurrence => (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence ∧
    NotVariable decl (k - 1) occurrence

/-- **A ready payload is ready at every positive depth**: its occurrences are bound inside it. -/
theorem payload_at {type : TypeExpr} {payload : Pattern}
    (ready : PayloadReady (language := language) reading type payload) {depth : Nat} (positive : 1 ≤ depth) :
    FrameAll language decl (BodyData reading) (BodyVariables reading) depth type payload := by
  have both := frameAll_and 0 type payload ready.2
    (scopedAll_of_scoped (language := language) (decl := decl) 0 type payload ready.1)
  have shifted := (frameAll_shift (language := language) (decl := decl) (dataOk := BodyData reading)
    (variableOk := BodyVariables reading) depth 0 type payload).mpr
    (frameAll_mono (fun _ _ h => h.1) (fun j _ h => ⟨h.1.1, h.1.2, notVariable_of_scoped h.2 (by omega)⟩)
      0 type payload both)
  rwa [Nat.zero_add] at shifted

/-- The action keeps a decoration's coefficients closed. -/
theorem actVariable_closedCoefficients {g : Pattern} {x : G} (gRead : read decl reading.constant g = some x)
    (depth : Nat) {occurrence : Pattern} (occurs : (decorated? decl occurrence).isSome)
    (closed : ClosedCoefficients reading occurrence) :
    ClosedCoefficients reading (actVariable decl g depth occurrence) := by
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have gLift := liftBVars_closed gRead 0 depth
  intro c v acted
  cases coefficient with
  | none =>
    rw [plain rfl] at acted
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_bare_inside g inside, decorated?_of_bare bare] at acted
        cases acted
      · rw [actVariable_bare_outside g inside, gLift, decorated?_action _ _ bare] at acted
        cases acted
        exact ⟨x, gRead⟩
    | .fvar name, bare =>
      rw [actVariable_bare_free, gLift, decorated?_action _ _ bare] at acted
      cases acted
      exact ⟨x, gRead⟩
  | some c₀ =>
    rw [applied c₀ rfl] at acted
    obtain ⟨z, c₀Read⟩ := closed c₀ occurrenceVar found
    have dataWord := actData_closed_word gRead c₀Read depth
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_decorated_inside g _ inside, dataWord, gLift, decorated?_action _ _ bare] at acted
        cases acted
        exact ⟨_, read_mulWord (read_mulWord gRead c₀Read) (read_invWord gRead)⟩
      · rw [actVariable_decorated_outside g _ inside, dataWord, decorated?_action _ _ bare] at acted
        cases acted
        exact ⟨_, read_mulWord gRead c₀Read⟩
    | .fvar name, bare =>
      rw [actVariable_decorated_free, dataWord, decorated?_action _ _ bare] at acted
      cases acted
      exact ⟨_, read_mulWord gRead c₀Read⟩

/-- **The action keeps a payload ready.** -/
theorem payloadReady_frameAct (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {g : Pattern} {x : G}
    (gRead : read decl reading.constant g = some x) {type : TypeExpr} {payload : Pattern}
    (ready : PayloadReady (language := language) reading type payload) :
    PayloadReady (language := language) reading type (frameAct language decl g type payload) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  refine ⟨frameAct_closed gRead type ready.1, ?_⟩
  apply frameAll_mapFrame (actVariable_keeps g).notBare bodyNotData bodySort _ _ 0 type payload ready.2
  · intro k datum parsed
    obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsed
    obtain ⟨acted, actedParsed, _⟩ := letters_actData gRead k parsed
    rw [actedParsed]
    rfl
  · intro k occurrence occurs ⟨_, closed⟩
    rw [frameAll_occurrence bodySort notData ((actVariable_keeps g).occurs k occurrence occurs)]
    exact ⟨(actVariable_keeps g).occurs k occurrence occurs, actVariable_closedCoefficients gRead k occurs closed⟩

/-- **Instantiating the process variable at an occurrence keeps the body ready**, one binder up. -/
theorem instVariable_ready (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {payload : Pattern}
    (payloadReady : PayloadReady (language := language) reading bodyType payload) {depth : Nat}
    (positive : 1 ≤ depth) {occurrence : Pattern} (occurs : (decorated? decl occurrence).isSome)
    (closed : ClosedCoefficients reading occurrence) (notDatum : NotVariable decl (depth - 1) occurrence) :
    FrameAll language decl (BodyData reading) (BodyVariables reading) depth bodyType
      (instVariable language decl bodyType payload depth occurrence) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  have payloadLift : Substitution.liftBVars 0 depth payload = payload :=
    Substitution.liftBVars_eq_self_of_isWellScopedAt payloadReady.1
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  have variableNe := notDatum _ _ found
  cases coefficient with
  | none =>
    rw [plain rfl]
    match occurrenceVar, bare with
    | .bvar index, bare =>
      rw [instVariable_bare]
      split_ifs with same below
      · rw [payloadLift]
        exact payload_at payloadReady positive
      · rw [frameAll_occurrence bodySort notData (decorated?_some_of_bare rfl)]
        refine ⟨decorated?_some_of_bare rfl, fun c v lowered => ?_, fun c v lowered => ?_⟩
        · rw [decorated?_of_bare rfl] at lowered
          cases lowered
        · rw [decorated?_of_bare rfl] at lowered
          cases lowered
          intro equal
          injection equal with equal
          omega
      · rw [frameAll_occurrence bodySort notData (decorated?_some_of_bare rfl)]
        refine ⟨decorated?_some_of_bare rfl, fun c v lowered => ?_, fun c v lowered => ?_⟩
        · rw [decorated?_of_bare rfl] at lowered
          cases lowered
        · rw [decorated?_of_bare rfl] at lowered
          cases lowered
          exact variableNe
    | .fvar name, bare =>
      rw [instVariable_free, frameAll_occurrence bodySort notData (decorated?_some_of_bare rfl)]
      refine ⟨decorated?_some_of_bare rfl, fun c v lowered => ?_, fun c v lowered => ?_⟩
      · rw [decorated?_of_bare rfl] at lowered
        cases lowered
      · rw [decorated?_of_bare rfl] at lowered
        cases lowered
        simp
  | some c =>
    rw [applied c rfl]
    obtain ⟨z, cRead⟩ := closed c occurrenceVar found
    have cInst : Substitution.instantiateBVarAt depth payload c = c :=
      Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped cRead depth)
    match occurrenceVar, bare with
    | .bvar index, bare =>
      rw [instVariable_decorated, cInst]
      split_ifs with same below
      · rw [payloadLift]
        exact payload_at (payloadReady_frameAct bodyNotData bodySort cRead payloadReady) positive
      · rw [frameAll_occurrence bodySort notData (decorated?_some_of_action c rfl)]
        refine ⟨decorated?_some_of_action c rfl, fun c' v lowered => ?_, fun c' v lowered => ?_⟩
        · rw [decorated?_action _ _ rfl] at lowered
          cases lowered
          exact ⟨z, cRead⟩
        · rw [decorated?_action _ _ rfl] at lowered
          cases lowered
          intro equal
          injection equal with equal
          omega
      · rw [frameAll_occurrence bodySort notData (decorated?_some_of_action c rfl)]
        refine ⟨decorated?_some_of_action c rfl, fun c' v lowered => ?_, fun c' v lowered => ?_⟩
        · rw [decorated?_action _ _ rfl] at lowered
          cases lowered
          exact ⟨z, cRead⟩
        · rw [decorated?_action _ _ rfl] at lowered
          cases lowered
          exact variableNe
    | .fvar name, bare =>
      rw [instVariable_decorated_free, cInst, frameAll_occurrence bodySort notData (decorated?_some_of_action c rfl)]
      refine ⟨decorated?_some_of_action c rfl, fun c' v lowered => ?_, fun c' v lowered => ?_⟩
      · rw [decorated?_action _ _ rfl] at lowered
        cases lowered
        exact ⟨z, cRead⟩
      · rw [decorated?_action _ _ rfl] at lowered
        cases lowered
        simp

end Transport

/-! ## Occurrences keep their variable -/

section Variables

variable {language : LanguageDef} {decl : OrientationDecl}
variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

omit [Group G] [DecidableEq G] in
/-- The action keeps an occurrence's variable. -/
theorem decorated?_actVariable (g : Pattern) (depth : Nat) {occurrence : Pattern} {coefficient : Option Pattern}
    {occurrenceVar : Pattern} (found : decorated? decl occurrence = some (coefficient, occurrenceVar)) :
    ∃ acted, decorated? decl (actVariable decl g depth occurrence) = some (acted, occurrenceVar) := by
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  cases coefficient with
  | none =>
    rw [plain rfl]
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_bare_inside g inside]
        exact ⟨none, rfl⟩
      · rw [actVariable_bare_outside g inside, decorated?_action _ _ bare]
        exact ⟨_, rfl⟩
    | .fvar name, bare =>
      rw [actVariable_bare_free, decorated?_action _ _ bare]
      exact ⟨_, rfl⟩
  | some c =>
    rw [applied c rfl]
    match occurrenceVar, bare with
    | .bvar index, bare =>
      by_cases inside : index < depth
      · rw [actVariable_decorated_inside g _ inside, decorated?_action _ _ bare]
        exact ⟨_, rfl⟩
      · rw [actVariable_decorated_outside g _ inside, decorated?_action _ _ bare]
        exact ⟨_, rfl⟩
    | .fvar name, bare =>
      rw [actVariable_decorated_free, decorated?_action _ _ bare]
      exact ⟨_, rfl⟩

omit [Group G] [DecidableEq G] in
theorem actVariable_notVariable (g : Pattern) (depth : Nat) {level : Nat} {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome) (notVariable : NotVariable decl level occurrence) :
    NotVariable decl level (actVariable decl g depth occurrence) := by
  intro c v acted
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨_, same⟩ := decorated?_actVariable g depth found
  rw [same] at acted
  cases acted
  exact notVariable _ _ found

/-- The normal form keeps an occurrence's variable. -/
theorem decorated?_normalVariable (depth : Nat) {occurrence : Pattern} {coefficient : Option Pattern}
    {occurrenceVar : Pattern} (found : decorated? decl occurrence = some (coefficient, occurrenceVar)) :
    ∃ normal, decorated? decl (normalVariable decl reading depth occurrence) = some (some normal, occurrenceVar) := by
  obtain ⟨bare, plain, applied⟩ := decorated?_shape found
  cases coefficient with
  | none =>
    rw [plain rfl, normalVariable_bare bare, decorated?_action _ _ bare]
    exact ⟨_, rfl⟩
  | some c =>
    rw [applied c rfl, normalVariable_decorated bare, decorated?_action _ _ bare]
    exact ⟨_, rfl⟩

theorem normalVariable_notVariable (depth : Nat) {level : Nat} {occurrence : Pattern}
    (occurs : (decorated? decl occurrence).isSome) (notVariable : NotVariable decl level occurrence) :
    NotVariable decl level (normalVariable decl reading depth occurrence) := by
  intro c v normal
  obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
  obtain ⟨_, same⟩ := decorated?_normalVariable (reading := reading) depth found
  rw [same] at normal
  cases normal
  exact notVariable _ _ found

theorem notVariable_of_normalVariable (depth : Nat) {level : Nat} {occurrence : Pattern}
    (notVariable : NotVariable decl level (normalVariable decl reading depth occurrence)) :
    NotVariable decl level occurrence := by
  intro c v found
  obtain ⟨_, same⟩ := decorated?_normalVariable (reading := reading) depth found
  exact notVariable _ _ same

/-- **The normal form keeps occurrences away from a level.** -/
theorem avoidsLevel_normal (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {depth : Nat} {type : TypeExpr}
    {pattern : Pattern} (avoids : AvoidsLevel (language := language) (decl := decl) depth type pattern) :
    AvoidsLevel (language := language) (decl := decl) depth type
      (normalWalkAt (language := language) reading depth type pattern) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  apply frameAll_mapFrame normalVariable_keeps.notBare bodyNotData bodySort _ _ depth type pattern avoids
  · intro _ _ _
    trivial
  · intro k occurrence occurs ⟨_, notVariable⟩
    rw [frameAll_occurrence bodySort notData (normalVariable_keeps.occurs k occurrence occurs)]
    exact ⟨normalVariable_keeps.occurs k occurrence occurs, normalVariable_notVariable k occurs notVariable⟩

/-- **A term whose normal form avoids a level avoids it.** -/
theorem avoidsLevel_of_normal (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {depth : Nat} {type : TypeExpr} {pattern : Pattern}
    (avoids : AvoidsLevel (language := language) (decl := decl) depth type
      (normalWalkAt (language := language) reading depth type pattern)) :
    AvoidsLevel (language := language) (decl := decl) depth type pattern :=
  frameAll_reflect normalVariable_keeps bodyNotData (fun _ _ _ => trivial)
    (fun k _ occurs ⟨_, notVariable⟩ => ⟨occurs, notVariable_of_normalVariable k notVariable⟩) depth type pattern
    avoids

end Variables

/-! ## The continuation -/

section Continuation

variable {language : LanguageDef} {decl : OrientationDecl}

/-- **The continuation of a communication**: the receive's body under its two binders, its process
variable instantiated by the payload, discharging decorations, and its datum by the message's datum. -/
def commContinuation (bodyType type : TypeExpr) (body payload datum : Pattern) : Pattern :=
  instDatumWalk (language := language) (decl := decl) datum type
    (instWalkAt (language := language) (decl := decl) bodyType payload 1 type body)

variable {G : Type} [Group G] [DecidableEq G] {reading : DataReading decl G}

/-- The predicates of instantiating the process variable, at the binder depth of the process variable. -/
abbrev SubstData (reading : DataReading decl G) : Nat → Pattern → Prop :=
  fun k datum => ∃ found, letters decl reading.constant datum = some found ∧ LevelFree k found

abbrev SubstVariables (reading : DataReading decl G) : Nat → Pattern → Prop :=
  fun k occurrence => 1 ≤ k ∧ (decorated? decl occurrence).isSome ∧ ClosedCoefficients reading occurrence ∧
    NotVariable decl (k - 1) occurrence

omit [DecidableEq G] in
theorem bodyReady_at_one {type : TypeExpr} {body : Pattern} (ready : BodyReady (language := language) reading type body) :
    FrameAll language decl (SubstData reading) (SubstVariables reading) 1 type body :=
  (frameAll_shift (language := language) (decl := decl) (dataOk := SubstData reading)
    (variableOk := SubstVariables reading) 1 0 type body).mpr
    (frameAll_mono (fun _ _ h => h) (fun j _ h => ⟨by omega, h.1, h.2.1, by rw [Nat.add_sub_cancel]; exact h.2.2⟩)
      0 type body ready)

omit [DecidableEq G] in
theorem substitutionReady_of_body {type : TypeExpr} {body : Pattern}
    (ready : BodyReady (language := language) reading type body) :
    SubstitutionReady (language := language) reading 1 type body :=
  frameAll_mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2.1⟩) 1 type body (bodyReady_at_one ready)

omit [DecidableEq G] in
/-- **The body with its process variable instantiated is ready for its datum**, one binder up. -/
theorem continuationBody_ready (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {payload : Pattern}
    (payloadReady : PayloadReady (language := language) reading bodyType payload) {type : TypeExpr} {body : Pattern}
    (ready : BodyReady (language := language) reading type body) :
    FrameAll language decl (BodyData reading) (BodyVariables reading) 1 type
      (instWalkAt (language := language) (decl := decl) bodyType payload 1 type body) := by
  unfold instWalkAt
  apply frameAll_mapFrame (instVariable_keepsNotBare bodySort bodyNotData payload) bodyNotData bodySort _ _ 1 type
    body (bodyReady_at_one ready)
  · intro k datum ⟨found, parsed, free⟩
    rw [instantiate_levelFree k payload (unitWord (decl := decl)) datum parsed free]
    obtain ⟨again, againParsed, _⟩ := letters_instantiate (read_unitWord (reading := reading)) k datum parsed
    show (letters decl reading.constant _).isSome = true
    rw [againParsed]
    rfl
  · intro k occurrence occurs ⟨positive, _, closed, notDatum⟩
    exact instVariable_ready bodyNotData bodySort payloadReady positive occurs closed notDatum

omit [DecidableEq G] in
theorem continuationBody_datumReady (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {payload : Pattern}
    (payloadReady : PayloadReady (language := language) reading bodyType payload) {type : TypeExpr} {body : Pattern}
    (ready : BodyReady (language := language) reading type body) :
    DatumReady (language := language) reading 0 type
      (instWalkAt (language := language) (decl := decl) bodyType payload 1 type body) :=
  frameAll_mono (fun _ _ h => h) (fun _ _ h => ⟨h.1, h.2.1, by have := h.2.2; rwa [Nat.add_sub_cancel] at this⟩)
    0 type _ ((frameAll_shift (language := language) (decl := decl) 1 0 type _).mp
      (continuationBody_ready bodyNotData bodySort payloadReady ready))

omit [DecidableEq G] in
/-- After the action, the occurrences still avoid the datum. -/
theorem continuationActed_avoids (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) (g : Pattern) {payload : Pattern}
    (payloadReady : PayloadReady (language := language) reading bodyType payload) {type : TypeExpr} {body : Pattern}
    (ready : BodyReady (language := language) reading type body) :
    AvoidsLevel (language := language) (decl := decl) 0 type
      (actWalkAt (language := language) (decl := decl) g 1 type
        (instWalkAt (language := language) (decl := decl) bodyType payload 1 type body)) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  have acted : FrameAll language decl (fun _ _ => True)
      (fun k occurrence => (decorated? decl occurrence).isSome ∧ NotVariable decl (k - 1) occurrence) 1 type
      (actWalkAt (language := language) (decl := decl) g 1 type
        (instWalkAt (language := language) (decl := decl) bodyType payload 1 type body)) := by
    unfold actWalkAt
    apply frameAll_mapFrame (actVariable_keeps g).notBare bodyNotData bodySort _ _ 1 type _
      (continuationBody_ready bodyNotData bodySort payloadReady ready)
    · intro _ _ _
      trivial
    · intro k occurrence occurs ⟨_, _, notDatum⟩
      rw [frameAll_occurrence bodySort notData ((actVariable_keeps g).occurs k occurrence occurs)]
      exact ⟨(actVariable_keeps g).occurs k occurrence occurs, actVariable_notVariable g k occurs notDatum⟩
  exact frameAll_mono (fun _ _ h => h) (fun _ _ h => ⟨h.1, by have := h.2; rwa [Nat.add_sub_cancel] at this⟩)
    0 type _ ((frameAll_shift (language := language) (decl := decl) 1 0 type _).mp acted)

omit [DecidableEq G] in
/-- **The continuation's data and coefficients are words.** -/
theorem continuation_parses (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {datum : Pattern} {y : G}
    (datumRead : read decl reading.constant datum = some y) {type : TypeExpr} {pattern : Pattern}
    (ready : DatumReady (language := language) reading 0 type pattern) :
    WordsParse language reading type (instDatumWalk (language := language) (decl := decl) datum type pattern) := by
  have notData : bodyType ≠ .base decl.dataSort := fun same => bodyNotData (bodySort.trans (by rw [same]))
  unfold WordsParse instDatumWalk
  apply frameAll_mapFrame (instantiate_keepsNotBare datum) bodyNotData bodySort _ _ 0 type pattern ready
  · intro k word parsed
    obtain ⟨found, parsed⟩ := Option.isSome_iff_exists.mp parsed
    obtain ⟨again, againParsed, _⟩ := letters_instantiate datumRead k word parsed
    show (letters decl reading.constant _).isSome = true
    rw [againParsed]
    rfl
  · intro k occurrence occurs ⟨_, closed, notLevel⟩
    obtain ⟨⟨coefficient, occurrenceVar⟩, found⟩ := Option.isSome_iff_exists.mp occurs
    obtain ⟨bare, plain, applied⟩ := decorated?_shape found
    have lowered := instantiate_bare bare (notLevel _ _ found) datum
    cases coefficient with
    | none =>
      rw [plain rfl, frameAll_occurrence bodySort notData (decorated?_some_of_bare lowered)]
      refine ⟨decorated?_some_of_bare lowered, fun c v acted => ?_⟩
      rw [decorated?_of_bare lowered] at acted
      cases acted
    | some c =>
      obtain ⟨z, cRead⟩ := closed c occurrenceVar found
      have cInst : Substitution.instantiateBVarAt k datum c = c :=
        Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (read_scoped cRead k)
      have instantiated : Substitution.instantiateBVarAt k datum (.apply decl.action [c, occurrenceVar]) =
          .apply decl.action [c, Substitution.instantiateBVarAt k datum occurrenceVar] := by
        simp only [Substitution.instantiateBVarAt, List.map_cons, List.map_nil]
        rw [cInst]
      rw [applied c rfl, instantiated, frameAll_occurrence bodySort notData (decorated?_some_of_action c lowered)]
      refine ⟨decorated?_some_of_action c lowered, fun c' v acted => ?_⟩
      rw [decorated?_action _ _ lowered] at acted
      cases acted
      obtain ⟨cLetters, cParsed, _⟩ := letters_of_read reading.constant c cRead
      rw [cParsed]
      rfl

/-- **The continuation of the acted pair is the action on the continuation**, in normal form: the body
acted on from under its two binders, the acted payload `g · Q` and the acted datum `g d` continue as
`g · K`. -/
theorem continuation_equivariant (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {g datum : Pattern} {x y : G}
    (gRead : read decl reading.constant g = some x) (datumRead : read decl reading.constant datum = some y)
    {payload : Pattern} (payloadReady : PayloadReady (language := language) reading bodyType payload)
    (type : TypeExpr) {body : Pattern} (ready : BodyReady (language := language) reading type body) :
    frameNormal language decl reading type
        (commContinuation (language := language) (decl := decl) bodyType type
          (actWalkAt (language := language) (decl := decl) g 2 type body)
          (frameAct language decl g bodyType payload) (mulWord decl g datum)) =
      frameNormal language decl reading type
        (frameAct language decl g type
          (commContinuation (language := language) (decl := decl) bodyType type body payload datum)) := by
  have actedDatum := read_mulWord gRead datumRead
  have payloadParses : WordsParse language reading bodyType payload :=
    frameAll_mono (fun _ _ h => h)
      (fun _ _ h => ⟨h.1, fun c v found => by
        obtain ⟨z, cRead⟩ := h.2 c v found
        obtain ⟨cLetters, cParsed, _⟩ := letters_of_read reading.constant c cRead
        rw [cParsed]
        rfl⟩) 0 bodyType payload payloadReady.2
  -- instantiating the process variable
  have process : frameNormal language decl reading type
      (instWalkAt (language := language) (decl := decl) bodyType (frameAct language decl g bodyType payload) 1 type
        (actWalkAt (language := language) (decl := decl) g 2 type body)) =
      frameNormal language decl reading type
        (actWalkAt (language := language) (decl := decl) g 1 type
          (instWalkAt (language := language) (decl := decl) bodyType payload 1 type body)) := by
    have equal := body_equivariant bodyNotData bodySort gRead payloadReady.1 payloadParses 1 type body
      (substitutionReady_of_body ready)
    rwa [normalWalk_depth, normalWalk_depth] at equal
  -- both sides avoid the datum
  have actedAvoids := continuationActed_avoids bodyNotData bodySort g payloadReady ready
  have instantiatedAvoids : AvoidsLevel (language := language) (decl := decl) 0 type
      (instWalkAt (language := language) (decl := decl) bodyType (frameAct language decl g bodyType payload) 1 type
        (actWalkAt (language := language) (decl := decl) g 2 type body)) := by
    apply avoidsLevel_of_normal (reading := reading) bodyNotData
    have normal := avoidsLevel_normal (reading := reading) bodyNotData bodySort actedAvoids
    rw [normalWalk_depth] at normal ⊢
    rw [process]
    exact normal
  -- carrying the equality across the datum
  have first := instDatumWalk_normal bodyNotData bodySort actedDatum 0 type _ instantiatedAvoids
  have second := instDatumWalk_normal bodyNotData bodySort actedDatum 0 type _ actedAvoids
  rw [normalWalk_depth, normalWalk_depth, normalWalk_depth] at first second
  -- instantiating the datum
  have datumStep := datum_equivariant bodyNotData gRead datumRead 0 type _
    (continuationBody_datumReady bodyNotData bodySort payloadReady ready)
  unfold commContinuation instDatumWalk
  rw [← first, process, second]
  exact datumStep

/-- **The action commutes with communication**: the acted summand `((g a)(g b)⁻¹) · K'` of the acted
pair is the action on the summand `(a b⁻¹) · K`, in normal form. -/
theorem comm_equivariant (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {g a b datum : Pattern}
    {x xa xb y : G} (gRead : read decl reading.constant g = some x) (aRead : read decl reading.constant a = some xa)
    (bRead : read decl reading.constant b = some xb) (datumRead : read decl reading.constant datum = some y)
    {payload : Pattern} (payloadReady : PayloadReady (language := language) reading bodyType payload)
    (type : TypeExpr) {body : Pattern} (ready : BodyReady (language := language) reading type body) :
    frameNormal language decl reading type
        (frameAct language decl (mulWord decl (mulWord decl g a) (invWord decl (mulWord decl g b))) type
          (commContinuation (language := language) (decl := decl) bodyType type
            (actWalkAt (language := language) (decl := decl) g 2 type body)
            (frameAct language decl g bodyType payload) (mulWord decl g datum))) =
      frameNormal language decl reading type
        (frameAct language decl g type
          (frameAct language decl (mulWord decl a (invWord decl b)) type
            (commContinuation (language := language) (decl := decl) bodyType type body payload datum))) := by
  have coefficient := read_mulWord (read_mulWord gRead aRead) (read_invWord (read_mulWord gRead bRead))
  have relative := read_mulWord aRead (read_invWord bRead)
  have parses : WordsParse language reading type
      (commContinuation (language := language) (decl := decl) bodyType type body payload datum) :=
    continuation_parses bodyNotData bodySort datumRead
      (continuationBody_datumReady bodyNotData bodySort payloadReady ready)
  rw [frameAct_respects bodyNotData coefficient type
      (continuation_equivariant bodyNotData bodySort gRead datumRead payloadReady type ready),
    frameAct_mul bodyNotData coefficient gRead type _ parses, frameAct_mul bodyNotData gRead relative type _ parses]
  apply frameAct_congr bodyNotData (read_mulWord coefficient gRead) _ type _ parses
  rw [read_mulWord gRead relative]
  congr 1
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

/-- **The reduct of a communication**: the continuation acted on by the relative orientation and by its
inverse, superposed in the summation's collection. -/
def commReduct (sum : CollType) (bodyType type : TypeExpr) (a b body payload datum : Pattern) : Pattern :=
  .collection sum
    [frameAct language decl (mulWord decl a (invWord decl b)) type
        (commContinuation (language := language) (decl := decl) bodyType type body payload datum),
      frameAct language decl (mulWord decl b (invWord decl a)) type
        (commContinuation (language := language) (decl := decl) bodyType type body payload datum)] none

/-- **Communication is equivariant**: communicating the acted receive and message is acting on the
reduct of communicating them, in normal form. -/
theorem commReduct_equivariant (bodyNotData : actionType language decl ≠ some (.base decl.dataSort))
    {bodyType : TypeExpr} (bodySort : actionType language decl = some bodyType) {sum : CollType} {type : TypeExpr}
    (summands : elementType language type sum = some type) (notData : type ≠ .base decl.dataSort)
    {g a b datum : Pattern} {x xa xb y : G} (gRead : read decl reading.constant g = some x)
    (aRead : read decl reading.constant a = some xa) (bRead : read decl reading.constant b = some xb)
    (datumRead : read decl reading.constant datum = some y) {payload : Pattern}
    (payloadReady : PayloadReady (language := language) reading bodyType payload) {body : Pattern}
    (ready : BodyReady (language := language) reading type body) :
    frameNormal language decl reading type
        (commReduct (language := language) (decl := decl) sum bodyType type (mulWord decl g a) (mulWord decl g b)
          (actWalkAt (language := language) (decl := decl) g 2 type body)
          (frameAct language decl g bodyType payload) (mulWord decl g datum)) =
      frameNormal language decl reading type
        (frameAct language decl g type
          (commReduct (language := language) (decl := decl) sum bodyType type a b body payload datum)) := by
  unfold commReduct frameNormal frameAct
  simp only [mapFrame_collection notData summands, mapFrameList]
  have first := comm_equivariant bodyNotData bodySort gRead aRead bRead datumRead payloadReady type ready
  have second := comm_equivariant bodyNotData bodySort gRead bRead aRead datumRead payloadReady type ready
  unfold frameNormal frameAct at first second
  rw [first, second]

end Continuation

end Mettapedia.OSLF.MeTTaIL.Orientation
