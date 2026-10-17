import Mettapedia.OSLF.Syntax.SignatureMorphismMetas
import Mettapedia.OSLF.Syntax.VariablePosition
import Mettapedia.OSLF.Syntax.BindingWireCodec

/-!
# Executable partial inverses of binding-signature morphisms

Primitive constructor readers extend through the original scoped term and
metavariable syntax. Every successful read projects to its literal source.
A primitive left inverse gives image roundtrip and faithful fixed-fibre
encoding. Injective sort maps and constructor coverage give coverage of every
source term in the selected contexts and result sorts.

The reader has an explicit syntax-derived finite depth budget. This budget is
not a transition count or a polynomial-time implementation theorem. Binding
arities come from the existing signature map; no second binding grammar is
introduced.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

variable {S T : Signature}

/-- A partial inverse on primitive constructors; the arity is supplied by the
original signature morphism, rather than by a second binding grammar. -/
structure SigMor.OperatorReader (F : SigMor T S) where
  read : {sort : T.Srt} → S.Op (F.sortMap sort) → Option (T.Op sort)
  projects : ∀ {sort : T.Srt} (original : S.Op (F.sortMap sort)) (selected : T.Op sort),
    read original = some selected → F.opMap selected = original

theorem WireCodec.putVar_mapVar (F : SigMor T S) {context : Ctx T} {sort : T.Srt}
    (position : Var context sort) :
    putVar (S := S) (mapVar F.sortMap sort position) = putVar (S := T) position := by
  induction position with
  | zero => rfl
  | succ prior ih => simp only [mapVar, putVar, ih]

private theorem putVar_value {context : Ctx S} {sort : S.Srt} (position : Var context sort) :
    WireCodec.putVar (S := S) position = (varIdx (S := S) position).val := by
  induction position with
  | zero => rfl
  | succ prior ih => simp only [WireCodec.putVar, varIdx, Fin.val_succ, ih]

private theorem putVar_injective {context : Ctx S} {sort : S.Srt}
    (first second : Var context sort)
    (same : WireCodec.putVar (S := S) first = WireCodec.putVar (S := S) second) :
    first = second := by
  apply varIdx_injective
  apply Fin.ext
  simpa only [putVar_value] using same

theorem WireCodec.getVar_position [DecidableEq T.Srt]
    (context : Ctx T) (sort : T.Srt) (index : Nat) (position : Var context sort)
    (found : getVar context sort index = some position) : putVar (S := T) position = index := by
  induction index generalizing context with
  | zero =>
      cases context with
      | nil => simp only [getVar] at found; cases found
      | cons first rest =>
          simp only [getVar] at found
          split at found
          · rename_i equal
            subst first
            cases Option.some.inj found
            rfl
          · cases found
  | succ index ih =>
      cases context with
      | nil => simp only [getVar] at found; cases found
      | cons first rest =>
          simp only [getVar] at found
          obtain ⟨prior, read, same⟩ := Option.map_eq_some_iff.mp found
          cases same
          simp only [putVar, ih rest prior read]

private theorem mapVar_append (F : SigMor T S) (bound context : Ctx T)
    {sort : T.Srt} (position : Var (bound ++ context) sort) :
    castVarCtx (List.map_append (f := F.sortMap) (l₁ := bound) (l₂ := context))
      (mapVar F.sortMap sort position) =
      liftVarMap F.sortMap (mapVar F.sortMap) bound sort position := by
  induction bound with
  | nil => rfl
  | cons first rest ih =>
      cases position with
      | zero =>
          exact castVarCtx_zero (List.map_append (f := F.sortMap) (l₁ := rest) (l₂ := context))
      | succ prior =>
          change castVarCtx
            (congrArg (List.cons (F.sortMap first))
              (List.map_append (f := F.sortMap) (l₁ := rest) (l₂ := context)))
            (Var.succ (mapVar F.sortMap sort prior)) =
            Var.succ (liftVarMap F.sortMap (mapVar F.sortMap) rest sort prior)
          rw [castVarCtx_succ
            (List.map_append (f := F.sortMap) (l₁ := rest) (l₂ := context)), ih]

private theorem onTerm_append (F : SigMor T S) {bound context : Ctx T}
    {sort : T.Srt} (term : Term T (bound ++ context) sort) :
    castTermCtx (List.map_append (f := F.sortMap) (l₁ := bound) (l₂ := context))
      (F.onTerm term) = mapTerm F (liftVarMap F.sortMap (mapVar F.sortMap) bound) term := by
  rw [← mapTerm_castVarCtx]
  exact mapTerm_congr F _ _ (fun _ position => mapVar_append F bound context position) term

private theorem castTermCtx_cancel {first second : Ctx S} (same : first = second)
    {sort : S.Srt} (term : Term S second sort) :
    castTermCtx same (castTermCtx same.symm term) = term := by
  cases same
  rfl

mutual
/-- A property of the actual primitive operators occurring in an intrinsic
term. Variables introduce no additional operator requirement. -/
inductive Term.AllOperators (property : {sort : S.Srt} → S.Op sort → Prop) :
    {context : Ctx S} → {sort : S.Srt} → Term S context sort → Prop where
  | var {context : Ctx S} {sort : S.Srt} (position : Var context sort) :
      Term.AllOperators property (.var position)
  | op {context : Ctx S} {sort : S.Srt} (operator : S.Op sort)
      (arguments : Args S (S.arity operator) context) :
      property operator → Args.AllOperators property arguments →
      Term.AllOperators property (.op operator arguments)

/-- Every argument is checked under its own original binding telescope. -/
inductive Args.AllOperators (property : {sort : S.Srt} → S.Op sort → Prop) :
    {arity : List (List S.Srt × S.Srt)} → {context : Ctx S} → Args S arity context → Prop where
  | nil {context : Ctx S} : Args.AllOperators property (Args.nil (Γ := context))
  | cons {context : Ctx S} {bound : List S.Srt} {sort : S.Srt}
      {rest : List (List S.Srt × S.Srt)}
      (body : Term S (bound ++ context) sort) (tail : Args S rest context) :
      Term.AllOperators property body → Args.AllOperators property tail →
      Args.AllOperators property (.cons body tail)
end

theorem Term.AllOperators.castContext {property : {sort : S.Srt} → S.Op sort → Prop}
    {context other : Ctx S} (same : context = other) {sort : S.Srt}
    {term : Term S context sort} (supported : term.AllOperators property) :
    (castTermCtx same term).AllOperators property := by
  cases same
  exact supported

theorem Args.AllOperators.castArity {property : {sort : S.Srt} → S.Op sort → Prop}
    {arity other : List (List S.Srt × S.Srt)} (same : arity = other)
    {context : Ctx S} {arguments : Args S arity context}
    (supported : arguments.AllOperators property) :
    (castArgsArity same arguments).AllOperators property := by
  cases same
  exact supported

mutual
theorem Term.allOperators {property : {sort : S.Srt} → S.Op sort → Prop}
    (everywhere : ∀ {sort} (operator : S.Op sort), property operator) :
    ∀ {context : Ctx S} {sort : S.Srt} (term : Term S context sort), term.AllOperators property
  | _, _, .var position => .var position
  | _, _, .op operator arguments => .op operator arguments (everywhere operator)
      (Args.allOperators everywhere arguments)

theorem Args.allOperators {property : {sort : S.Srt} → S.Op sort → Prop}
    (everywhere : ∀ {sort} (operator : S.Op sort), property operator) :
    ∀ {arity : List (List S.Srt × S.Srt)} {context : Ctx S}
      (arguments : Args S arity context), arguments.AllOperators property
  | _, _, .nil => .nil
  | _, _, .cons body tail => .cons body tail (Term.allOperators everywhere body)
      (Args.allOperators everywhere tail)
end

mutual
theorem Term.AllOperators.mono
    {property other : {sort : S.Srt} → S.Op sort → Prop}
    (implies : ∀ {sort} (operator : S.Op sort), property operator → other operator) :
    ∀ {context : Ctx S} {sort : S.Srt} {term : Term S context sort},
      term.AllOperators property → term.AllOperators other
  | _, _, _, .var position => .var position
  | _, _, _, .op operator arguments supported allArguments =>
      .op operator arguments (implies operator supported) (allArguments.mono implies)

theorem Args.AllOperators.mono
    {property other : {sort : S.Srt} → S.Op sort → Prop}
    (implies : ∀ {sort} (operator : S.Op sort), property operator → other operator) :
    ∀ {arity : List (List S.Srt × S.Srt)} {context : Ctx S} {arguments : Args S arity context},
      arguments.AllOperators property → arguments.AllOperators other
  | _, _, _, .nil => .nil
  | _, _, _, .cons body tail bodySupported tailSupported =>
      .cons body tail (bodySupported.mono implies) (tailSupported.mono implies)
end

mutual
theorem Term.allOperators_mapTerm (F : SigMor T S)
    {property : {sort : S.Srt} → S.Op sort → Prop}
    (images : ∀ {sort} (operator : T.Op sort), property (F.opMap operator)) :
    ∀ {context : Ctx T} {target : Ctx S} (mapping : VarMap F.sortMap context target)
      {sort : T.Srt} (term : Term T context sort),
      (mapTerm F mapping term).AllOperators property
  | _, _, _, _, .var _position => .var _
  | _, _, mapping, _, .op operator arguments =>
      .op (F.opMap operator) _ (images operator)
        ((Args.allOperators_mapArgs F images mapping arguments).castArity (F.carriesArity operator).symm)

theorem Args.allOperators_mapArgs (F : SigMor T S)
    {property : {sort : S.Srt} → S.Op sort → Prop}
    (images : ∀ {sort} (operator : T.Op sort), property (F.opMap operator)) :
    ∀ {arity : List (List T.Srt × T.Srt)} {context : Ctx T} {target : Ctx S}
      (mapping : VarMap F.sortMap context target) (arguments : Args T arity context),
      (mapArgs F mapping arguments).AllOperators property
  | _, _, _, _, .nil => .nil
  | _, _, _, mapping, .cons body tail =>
      .cons _ _ (Term.allOperators_mapTerm F images _ body) (Args.allOperators_mapArgs F images mapping tail)
end

namespace SigMor.OperatorReader

variable (F : SigMor T S) (reader : F.OperatorReader)

private theorem arity_eq {sort : T.Srt}
    (original : S.Op (F.sortMap sort)) (selected : T.Op sort)
    (found : reader.read original = some selected) :
    S.arity original = mapArities F.sortMap (T.arity selected) :=
  (congrArg (fun op => S.arity op) (reader.projects original selected found)).symm.trans
    (F.carriesArity selected)

variable [DecidableEq T.Srt]

mutual
/-- Read along the original constructor map, with an explicit finite recursion
budget. Zero budget refuses without changing the original source term. -/
def readTermWithFuel (fuel : Nat) {context : Ctx T} {sort : T.Srt}
    (term : Term S (context.map F.sortMap) (F.sortMap sort)) : Option (Term T context sort) :=
  match fuel with
  | 0 => none
  | fuel + 1 => match term with
      | .var position =>
          (WireCodec.getVar context sort (WireCodec.putVar position)).map Term.var
      | .op operator arguments =>
          match found : reader.read operator with
          | none => none
          | some selected =>
              (readArgsWithFuel fuel (T.arity selected)
                (castArgsArity (arity_eq F reader operator selected found) arguments)).map
                  (Term.op selected)

/-- Arguments use the very same reader under each constructor's declared
binding telescope. The budget is shared as a depth bound, not a step count. -/
def readArgsWithFuel (fuel : Nat) {context : Ctx T}
    (arity : List (List T.Srt × T.Srt))
    (arguments : Args S (mapArities F.sortMap arity) (context.map F.sortMap)) :
    Option (Args T arity context) :=
  match fuel with
  | 0 => none
  | fuel + 1 => match arity, arguments with
      | [], .nil => some .nil
      | (bound, sort) :: rest, .cons head tail => do
          let body ← readTermWithFuel fuel
            (castTermCtx
              (List.map_append (f := F.sortMap) (l₁ := bound) (l₂ := context)).symm head)
          let remaining ← readArgsWithFuel fuel rest tail
          pure (.cons body remaining)
end

/-- A syntax-derived finite budget. It does not assert a machine-time bound. -/
def readTerm {context : Ctx T} {sort : T.Srt}
    (term : Term S (context.map F.sortMap) (F.sortMap sort)) : Option (Term T context sort) :=
  readTermWithFuel F reader (2 * termSize term + 1) term

def readArgs {context : Ctx T} (arity : List (List T.Srt × T.Srt))
    (arguments : Args S (mapArities F.sortMap arity) (context.map F.sortMap)) :
    Option (Args T arity context) :=
  readArgsWithFuel F reader (2 * argsSize arguments + 1) arity arguments

mutual
/-- Every successful read projects to the literal original scoped term. -/
theorem readTermWithFuel_projects : ∀ (fuel : Nat) {context : Ctx T} {sort : T.Srt}
    (original : Term S (context.map F.sortMap) (F.sortMap sort))
    (selected : Term T context sort),
    readTermWithFuel F reader fuel original = some selected → F.onTerm selected = original
  | 0, _, _, _, _, found => by cases found
  | fuel + 1, context, sort, .var position, selected, found => by
      simp only [readTermWithFuel] at found
      obtain ⟨localPosition, read, same⟩ := Option.map_eq_some_iff.mp found
      cases same
      change Term.var (mapVar F.sortMap sort localPosition) = Term.var position
      congr 1
      apply putVar_injective
      rw [WireCodec.putVar_mapVar]
      exact WireCodec.getVar_position context sort _ localPosition read
  | fuel + 1, _, _, .op operator arguments, selected, found => by
      simp only [readTermWithFuel] at found
      split at found
      · cases found
      · rename_i localOperator opFound
        obtain ⟨localArguments, argsFound, same⟩ := Option.map_eq_some_iff.mp found
        cases same
        change Term.op (F.opMap localOperator)
          (castArgsArity (F.carriesArity localOperator).symm
            (mapArgs F (mapVar F.sortMap) localArguments)) = Term.op operator arguments
        rw [readArgsWithFuel_projects fuel _ _ localArguments argsFound]
        cases reader.projects operator localOperator opFound
        simp only [castArgsArity_trans, castArgsArity_self]

/-- The argument reader preserves both the original argument order and the
binding telescope of every argument. -/
theorem readArgsWithFuel_projects : ∀ (fuel : Nat) {context : Ctx T}
    (arity : List (List T.Srt × T.Srt))
    (original : Args S (mapArities F.sortMap arity) (context.map F.sortMap))
    (selected : Args T arity context),
    readArgsWithFuel F reader fuel arity original = some selected →
      mapArgs F (mapVar F.sortMap) selected = original
  | 0, _, _, _, _, found => by cases found
  | _ + 1, _, [], .nil, selected, found => by
      change some Args.nil = some selected at found
      cases Option.some.inj found
      rfl
  | fuel + 1, context, (bound, sort) :: rest, .cons head tail, selected, found => by
      simp only [readArgsWithFuel] at found
      obtain ⟨localHead, headFound, restFound⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨localTail, tailFound, same⟩ := Option.bind_eq_some_iff.mp restFound
      cases Option.some.inj same
      have headProjects := readTermWithFuel_projects fuel _ localHead headFound
      have tailProjects := readArgsWithFuel_projects fuel rest tail localTail tailFound
      change Args.cons (mapTerm F (liftVarMap F.sortMap (mapVar F.sortMap) bound) localHead)
        (mapArgs F (mapVar F.sortMap) localTail) = Args.cons head tail
      rw [← onTerm_append, headProjects, castTermCtx_cancel, tailProjects]
      rfl
end

theorem readTerm_projects {context : Ctx T} {sort : T.Srt}
    (original : Term S (context.map F.sortMap) (F.sortMap sort))
    (selected : Term T context sort) (found : readTerm F reader original = some selected) :
    F.onTerm selected = original :=
  readTermWithFuel_projects F reader _ original selected found

theorem readArgs_projects {context : Ctx T} (arity : List (List T.Srt × T.Srt))
    (original : Args S (mapArities F.sortMap arity) (context.map F.sortMap))
    (selected : Args T arity context) (found : readArgs F reader arity original = some selected) :
    mapArgs F (mapVar F.sortMap) selected = original :=
  readArgsWithFuel_projects F reader _ arity original selected found

end SigMor.OperatorReader

mutual

theorem termSize_mapTerm (F : SigMor T S) :
    ∀ {context : Ctx T} {target : Ctx S} (mapping : VarMap F.sortMap context target)
      {sort : T.Srt} (term : Term T context sort),
      termSize (mapTerm F mapping term) = termSize term
  | _, _, _, _, .var _ => rfl
  | _, _, mapping, _, .op operator arguments => by
      simp only [mapTerm, termSize, argsSize_castArgsArity, argsSize_mapArgs F mapping]

theorem argsSize_mapArgs (F : SigMor T S) :
    ∀ {context : Ctx T} {target : Ctx S} (mapping : VarMap F.sortMap context target)
      {arity : List (List T.Srt × T.Srt)} (arguments : Args T arity context),
      argsSize (mapArgs F mapping arguments) = argsSize arguments
  | _, _, _, _, .nil => rfl
  | _, _, mapping, _, .cons body rest => by
      simp only [mapArgs, argsSize, termSize_mapTerm F]
      exact congrArg (termSize body + ·) (argsSize_mapArgs F mapping rest)

end

private theorem putVar_cast {first second : Ctx S} (same : first = second)
    {sort : S.Srt} (position : Var first sort) :
    WireCodec.putVar (S := S) (castVarCtx same position) = WireCodec.putVar (S := S) position := by
  cases same
  rfl

private theorem putVar_lift (F : SigMor T S) {context : Ctx T} {target : Ctx S}
    (mapping : VarMap F.sortMap context target)
    (positions : ∀ sort position, WireCodec.putVar (S := S) (mapping sort position) =
      WireCodec.putVar (S := T) position) :
    ∀ (bound : List T.Srt) (sort : T.Srt) (position : Var (bound ++ context) sort),
      WireCodec.putVar (S := S) (liftVarMap F.sortMap mapping bound sort position) =
        WireCodec.putVar (S := T) position
  | [], sort, position => positions sort position
  | _ :: _, _, .zero => rfl
  | _ :: bound, sort, .succ position => by
      simp only [liftVarMap, WireCodec.putVar, putVar_lift F mapping positions bound sort position]

private theorem putVar_sortCast {context : Ctx S} {first second : S.Srt}
    (same : first = second) (position : Var context first) :
    WireCodec.putVar (S := S) (same ▸ position) = WireCodec.putVar (S := S) position := by
  cases same
  rfl

private theorem getVar_mapped_exists [DecidableEq T.Srt] (F : SigMor T S)
    (injective : Function.Injective F.sortMap) {context : Ctx T} {sort : T.Srt}
    (position : Var (context.map F.sortMap) (F.sortMap sort)) :
    ∃ original, WireCodec.getVar (S := T) context sort (WireCodec.putVar (S := S) position) = some original := by
  let index : Fin context.length :=
    ⟨(varIdx position).val, by simpa only [List.length_map] using (varIdx position).isLt⟩
  have mapped : F.sortMap (context.get index) = F.sortMap sort := by
    simpa only [List.get_eq_getElem, List.getElem_map] using get_varIdx position
  have same : context.get index = sort := injective mapped
  let original : Var context sort := same ▸ varOfIdx context index
  have positions : WireCodec.putVar (S := T) original = WireCodec.putVar (S := S) position := by
    calc
      WireCodec.putVar (S := T) original = WireCodec.putVar (S := T) (varOfIdx context index) :=
        putVar_sortCast same _
      _ = (varIdx (varOfIdx context index)).val := putVar_value _
      _ = index.val := congrArg Fin.val (varIdx_varOfIdx context index)
      _ = WireCodec.putVar (S := S) position := (putVar_value position).symm
  exact ⟨original, positions ▸ WireCodec.get_putVar original⟩


namespace SigMor.OperatorReader

variable [DecidableEq T.Srt] (F : SigMor T S) (reader : F.OperatorReader)
/-- Availability is requested only when an actual occurrence has the image
result sort; the source operator and its binding arity remain unchanged. -/
def SupportedOperator {sort : S.Srt} (operator : S.Op sort) : Prop :=
  ∀ (selectedSort : T.Srt) (same : F.sortMap selectedSort = sort),
    ∃ selected, reader.read (same.symm ▸ operator) = some selected


variable (operators : ∀ {sort} (operator : T.Op sort), reader.read (F.opMap operator) = some operator)

include operators in
theorem readWithFuel_roundtrip (fuel : Nat) :
    (∀ {context : Ctx T} (mapping : VarMap F.sortMap context (context.map F.sortMap))
      (_positions : ∀ sort position, WireCodec.putVar (S := S) (mapping sort position) =
        WireCodec.putVar (S := T) position)
      {sort : T.Srt} (term : Term T context sort), 2 * termSize term ≤ fuel →
      readTermWithFuel F reader fuel (mapTerm F mapping term) = some term) ∧
    (∀ {context : Ctx T} (mapping : VarMap F.sortMap context (context.map F.sortMap))
      (_positions : ∀ sort position, WireCodec.putVar (S := S) (mapping sort position) =
        WireCodec.putVar (S := T) position)
      {arity : List (List T.Srt × T.Srt)} (arguments : Args T arity context),
      2 * argsSize arguments + 1 ≤ fuel →
      readArgsWithFuel F reader fuel arity (mapArgs F mapping arguments) = some arguments) := by
  induction fuel with
  | zero =>
      constructor
      · intro context mapping positions sort term small
        have positive := termSize_pos term
        omega
      · intro context mapping positions arity arguments small
        omega
  | succ fuel inductionHypothesis =>
      constructor
      · intro context mapping positions sort term small
        cases term with
        | var position =>
            simp only [readTermWithFuel, mapTerm, positions, WireCodec.get_putVar, Option.map_some]
        | op operator arguments =>
            have enough : 2 * argsSize arguments + 1 ≤ fuel := by
              simp only [termSize] at small
              omega
            have parsed := inductionHypothesis.2 mapping positions arguments enough
            simp only [readTermWithFuel, mapTerm]
            split
            · rename_i missing
              rw [operators operator] at missing
              cases missing
            · rename_i selected found
              have same : selected = operator := Option.some.inj
                (found.symm.trans (operators operator))
              cases same
              simpa only [castArgsArity_trans, castArgsArity_self, Option.map_some] using
                congrArg (Option.map (Term.op operator)) parsed

      · intro context mapping positions arity arguments small
        cases arguments with
        | nil => rfl
        | @cons bound sort rest context body tail =>
            have bodySmall : 2 * termSize body ≤ fuel := by
              simp only [argsSize] at small
              omega
            have tailSmall : 2 * argsSize tail + 1 ≤ fuel := by
              have positive := termSize_pos body
              simp only [argsSize] at small
              omega
            let moved : VarMap F.sortMap (bound ++ context) ((bound ++ context).map F.sortMap) :=
              fun sort position => castVarCtx (List.map_append (f := F.sortMap) (l₁ := bound) (l₂ := context)).symm
                (liftVarMap F.sortMap mapping bound sort position)
            have movedPositions : ∀ sort position, WireCodec.putVar (S := S) (moved sort position) =
                WireCodec.putVar (S := T) position := by
              intro sort position
              exact (putVar_cast _ _).trans (putVar_lift F mapping positions bound sort position)
            have bodyParsed := inductionHypothesis.1 moved movedPositions body bodySmall
            have tailParsed := inductionHypothesis.2 mapping positions tail tailSmall
            change (do
              let parsedBody ← readTermWithFuel F reader fuel
                (castTermCtx (List.map_append (f := F.sortMap) (l₁ := bound) (l₂ := context)).symm
                  (mapTerm F (liftVarMap F.sortMap mapping bound) body))
              let remaining ← readArgsWithFuel F reader fuel rest (mapArgs F mapping tail)
              pure (Args.cons parsedBody remaining)) = some (.cons body tail)
            rw [← mapTerm_castVarCtx]
            change (do
              let body ← readTermWithFuel F reader fuel (mapTerm F moved body)
              let remaining ← readArgsWithFuel F reader fuel rest (mapArgs F mapping tail)
              pure (Args.cons body remaining)) = some (.cons body tail)
            rw [bodyParsed, tailParsed]
            rfl

include operators in
theorem readTerm_roundtrip {context : Ctx T} {sort : T.Srt} (term : Term T context sort) :
    readTerm F reader (F.onTerm term) = some term := by
  unfold readTerm
  apply (readWithFuel_roundtrip F reader operators _).1
    (mapVar F.sortMap) (fun _ position => WireCodec.putVar_mapVar F position) term
  rw [termSize_mapTerm]
  omega

variable (injective : Function.Injective F.sortMap)
variable (available : ∀ {sort} (operator : S.Op (F.sortMap sort)),
  ∃ selected, reader.read operator = some selected)

include injective in
/-- A finite term needs only its own primitive operations. No global signature
coverage is assumed and no second parser is introduced. -/
theorem readWithFuel_complete_on (fuel : Nat) :
    (∀ {context : Ctx T} {sort : T.Srt}
      (term : Term S (context.map F.sortMap) (F.sortMap sort)),
      term.AllOperators (SupportedOperator F reader) →
      2 * termSize term ≤ fuel → ∃ selected, readTermWithFuel F reader fuel term = some selected) ∧
    (∀ {context : Ctx T} (arity : List (List T.Srt × T.Srt))
      (arguments : Args S (mapArities F.sortMap arity) (context.map F.sortMap)),
      arguments.AllOperators (SupportedOperator F reader) →
      2 * argsSize arguments + 1 ≤ fuel →
      ∃ selected, readArgsWithFuel F reader fuel arity arguments = some selected) := by
  induction fuel with
  | zero =>
      constructor
      · intro context sort term _ small
        have positive := termSize_pos term
        omega
      · intro context arity arguments _ small
        omega
  | succ fuel inductionHypothesis =>
      constructor
      · intro context sort term supported small
        cases term with
        | var position =>
            obtain ⟨original, parsed⟩ := getVar_mapped_exists F injective position
            exact ⟨.var original, by simp only [readTermWithFuel, parsed, Option.map_some]⟩
        | op operator arguments =>
            cases supported with
            | op _ _ available argumentsSupported =>
              obtain ⟨selected, found⟩ := available sort rfl
              simp only [readTermWithFuel]
              split
              · rename_i missing
                rw [found] at missing
                cases missing
              · rename_i chosen decoded
                let carries : S.arity operator = mapArities F.sortMap (T.arity chosen) :=
                  (congrArg (fun op => S.arity op) (reader.projects operator chosen decoded)).symm.trans
                    (F.carriesArity chosen)
                have enough : 2 * argsSize (castArgsArity carries arguments) + 1 ≤ fuel := by
                  simp only [argsSize_castArgsArity, termSize] at *
                  omega
                obtain ⟨values, parsed⟩ := inductionHypothesis.2 (T.arity chosen)
                  (castArgsArity carries arguments) (argumentsSupported.castArity carries) enough
                exact ⟨.op chosen values, congrArg (Option.map (Term.op chosen)) parsed⟩
      · intro context arity arguments supported small
        cases arity with
        | nil => cases arguments; exact ⟨.nil, rfl⟩
        | cons slot rest =>
            rcases slot with ⟨bound, sort⟩
            cases arguments with
            | cons head tail =>
                cases supported with
                | cons _ _ headSupported tailSupported =>
                  let source := castTermCtx
                    (List.map_append (f := F.sortMap) (l₁ := bound) (l₂ := context)).symm head
                  have bodySmall : 2 * termSize source ≤ fuel := by
                    simp only [source, termSize_castTermCtx, argsSize] at *
                    omega
                  have tailSmall : 2 * argsSize tail + 1 ≤ fuel := by
                    have positive := termSize_pos head
                    simp only [argsSize] at small
                    omega
                  obtain ⟨body, bodyParsed⟩ := inductionHypothesis.1 source
                    (headSupported.castContext _) bodySmall
                  obtain ⟨remaining, tailParsed⟩ := inductionHypothesis.2 rest tail tailSupported tailSmall
                  refine ⟨.cons body remaining, ?_⟩
                  change (do
                    let parsedBody ← readTermWithFuel F reader fuel source
                    let parsedRest ← readArgsWithFuel F reader fuel rest tail
                    pure (Args.cons parsedBody parsedRest)) = some (.cons body remaining)
                  rw [bodyParsed, tailParsed]
                  rfl

include injective in
theorem readTerm_complete_on {context : Ctx T} {sort : T.Srt}
    (term : Term S (context.map F.sortMap) (F.sortMap sort))
    (supported : term.AllOperators (SupportedOperator F reader)) :
    ∃ selected, readTerm F reader term = some selected :=
  (readWithFuel_complete_on F reader injective _).1 term supported (by omega)

include injective in
theorem readArgs_complete_on {context : Ctx T} (arity : List (List T.Srt × T.Srt))
    (arguments : Args S (mapArities F.sortMap arity) (context.map F.sortMap))
    (supported : arguments.AllOperators (SupportedOperator F reader)) :
    ∃ selected, readArgs F reader arity arguments = some selected :=
  (readWithFuel_complete_on F reader injective _).2 arity arguments supported (by omega)


include injective available in
theorem readWithFuel_complete (fuel : Nat) :
    (∀ {context : Ctx T} {sort : T.Srt}
      (term : Term S (context.map F.sortMap) (F.sortMap sort)),
      2 * termSize term ≤ fuel → ∃ selected, readTermWithFuel F reader fuel term = some selected) ∧
    (∀ {context : Ctx T} (arity : List (List T.Srt × T.Srt))
      (arguments : Args S (mapArities F.sortMap arity) (context.map F.sortMap)),
      2 * argsSize arguments + 1 ≤ fuel →
      ∃ selected, readArgsWithFuel F reader fuel arity arguments = some selected) := by
  have primitives : ∀ {originalSort : S.Srt} (operator : S.Op originalSort),
      SupportedOperator F reader operator := by
    intro originalSort operator selectedSort same
    cases same
    exact available operator
  have restricted := readWithFuel_complete_on F reader injective fuel
  constructor
  · intro context sort term small
    exact restricted.1 term (Term.allOperators primitives term) small
  · intro context arity arguments small
    exact restricted.2 arity arguments (Args.allOperators primitives arguments) small

include injective available in
theorem readTerm_complete {context : Ctx T} {sort : T.Srt}
    (term : Term S (context.map F.sortMap) (F.sortMap sort)) :
    ∃ selected, readTerm F reader term = some selected := by
  exact (readWithFuel_complete F reader injective available _).1 term (by omega)

include injective available in
theorem readArgs_complete {context : Ctx T} (arity : List (List T.Srt × T.Srt))
    (arguments : Args S (mapArities F.sortMap arity) (context.map F.sortMap)) :
    ∃ selected, readArgs F reader arity arguments = some selected := by
  exact (readWithFuel_complete F reader injective available _).2 arity arguments (by omega)


include operators in
theorem readArgs_roundtrip {context : Ctx T} {arity : List (List T.Srt × T.Srt)}
    (arguments : Args T arity context) :
    readArgs F reader arity (mapArgs F (mapVar F.sortMap) arguments) = some arguments := by
  unfold readArgs
  apply (readWithFuel_roundtrip F reader operators _).2
    (mapVar F.sortMap) (fun _ position => WireCodec.putVar_mapVar F position) arguments
  rw [argsSize_mapArgs]

include operators in
theorem readTerm_eq_some_iff {context : Ctx T} {sort : T.Srt}
    (original : Term S (context.map F.sortMap) (F.sortMap sort))
    (selected : Term T context sort) :
    readTerm F reader original = some selected ↔ F.onTerm selected = original := by
  constructor
  · exact readTerm_projects F reader original selected
  · intro same
    rw [← same]
    exact readTerm_roundtrip F reader operators selected

include operators in
theorem onTerm_injective {context : Ctx T} {sort : T.Srt} :
    Function.Injective (F.onTerm : Term T context sort →
      Term S (context.map F.sortMap) (F.sortMap sort)) := by
  intro first second same
  have readback := congrArg (readTerm F reader) same
  rw [readTerm_roundtrip F reader operators, readTerm_roundtrip F reader operators] at readback
  exact Option.some.inj readback

end SigMor.OperatorReader

instance Signature.reindexedSortDecidableEq {A : Type} (sorts : A → S.Srt)
    [DecidableEq A] : DecidableEq (S.reindexSorts sorts).Srt :=
  inferInstanceAs (DecidableEq A)

def Signature.reindexOperatorReader {A : Type} (S : Signature) (sorts : A → S.Srt)
    (decode : S.Srt → Option A)
    (sound : ∀ source target, decode source = some target → sorts target = source) :
    (S.reindexProjection sorts).OperatorReader where
  read := S.reindexOperator? sorts decode sound
  projects := S.reindexOperator?_original sorts decode sound

def Signature.reindexTerm? {A : Type} [DecidableEq A] (S : Signature) (sorts : A → S.Srt)
    (decode : S.Srt → Option A)
    (sound : ∀ source target, decode source = some target → sorts target = source)
    {context : List A} {sort : A}
    (original : Term S (context.map sorts) (sorts sort)) :
    Option (Term (S.reindexSorts sorts) context sort) :=
  SigMor.OperatorReader.readTerm (S.reindexProjection sorts)
    (S.reindexOperatorReader sorts decode sound) original

def Signature.reindexArgs? {A : Type} [DecidableEq A] (S : Signature) (sorts : A → S.Srt)
    (decode : S.Srt → Option A)
    (sound : ∀ source target, decode source = some target → sorts target = source)
    {context : List A} (arity : List (List A × A))
    (original : Args S (mapArities sorts arity) (context.map sorts)) :
    Option (Args (S.reindexSorts sorts) arity context) :=
  SigMor.OperatorReader.readArgs (S.reindexProjection sorts)
    (S.reindexOperatorReader sorts decode sound) arity original

theorem Signature.reindexTerm?_projects {A : Type} [DecidableEq A]
    (S : Signature) (sorts : A → S.Srt) (decode : S.Srt → Option A)
    (sound : ∀ source target, decode source = some target → sorts target = source)
    {context : List A} {sort : A}
    (original : Term S (context.map sorts) (sorts sort))
    (selected : Term (S.reindexSorts sorts) context sort)
    (found : S.reindexTerm? sorts decode sound original = some selected) :
    (S.reindexProjection sorts).onTerm selected = original :=
  SigMor.OperatorReader.readTerm_projects (S.reindexProjection sorts)
    (S.reindexOperatorReader sorts decode sound) original selected found

theorem Signature.reindexTerm?_roundtrip {A : Type} [DecidableEq A]
    (S : Signature) (sorts : A → S.Srt) (decode : S.Srt → Option A)
    (sound : ∀ source target, decode source = some target → sorts target = source)
    (roundtrip : ∀ target, decode (sorts target) = some target)
    {context : List A} {sort : A} (term : Term (S.reindexSorts sorts) context sort) :
    S.reindexTerm? sorts decode sound ((S.reindexProjection sorts).onTerm term) = some term := by
  exact SigMor.OperatorReader.readTerm_roundtrip (S.reindexProjection sorts)
    (S.reindexOperatorReader sorts decode sound)
    (S.reindexOperator?_roundtrip sorts decode sound roundtrip) term

theorem Signature.reindexTerm?_complete {A : Type} [DecidableEq A]
    (S : Signature) (sorts : A → S.Srt) (decode : S.Srt → Option A)
    (sound : ∀ source target, decode source = some target → sorts target = source)
    (injective : Function.Injective sorts)
    (available : ∀ {sort : A} (operator : S.Op (sorts sort)),
      ∃ selected, S.reindexOperator? sorts decode sound operator = some selected)
    {context : List A} {sort : A} (original : Term S (context.map sorts) (sorts sort)) :
    ∃ selected, S.reindexTerm? sorts decode sound original = some selected :=
  SigMor.OperatorReader.readTerm_complete (S.reindexProjection sorts)
    (S.reindexOperatorReader sorts decode sound) injective available original

def MetaOp.index {M : List (MetaArity S)} {sort : S.Srt} : MetaOp M sort → Fin M.length
  | .mk index => index

theorem MetaOp.index_sort {M : List (MetaArity S)} {sort : S.Srt}
    (operator : MetaOp M sort) : (M.get operator.index).2 = sort := by
  cases operator
  rfl

theorem MetaOp.heq_of_index_eq {M : List (MetaArity S)} {firstSort secondSort : S.Srt}
    (first : MetaOp M firstSort) (second : MetaOp M secondSort)
    (same : first.index = second.index) : HEq first second := by
  cases first with
  | mk first =>
      cases second with
      | mk second =>
          change first = second at same
          cases same
          rfl

theorem MetaOp.index_injective {M : List (MetaArity S)} {sort : S.Srt}
    (first second : MetaOp M sort) (same : first.index = second.index) : first = second :=
  eq_of_heq (MetaOp.heq_of_index_eq first second same)

private theorem metaIndex_cast {M : List (MetaArity S)} {first second : S.Srt}
    (same : first = second) (operator : MetaOp M first) :
    (same ▸ operator).index = operator.index := by
  cases same
  rfl

private theorem metaIndex_mp {M : List (MetaArity S)} {first second : S.Srt}
    (same : first = second) (operator : MetaOp M first) :
    (Eq.mp (congrArg (MetaOp M) same) operator).index = operator.index := by
  cases same
  rfl

theorem SigMor.mapMetaOp_index (F : SigMor T S) {M : List (MetaArity T)}
    {sort : T.Srt} (operator : MetaOp M sort) :
    (F.mapMetaOp operator).index = F.mapMetaIndex operator.index := by
  cases operator with
  | mk index =>
      change (Eq.mp (congrArg (MetaOp (F.mapMetas M))
        (congrArg Prod.snd (F.get_mapMetas index)))
        (MetaOp.mk (F.mapMetaIndex index))).index = F.mapMetaIndex index
      exact metaIndex_mp (congrArg Prod.snd (F.get_mapMetas index))
        (MetaOp.mk (F.mapMetaIndex index))

/-- Read the original declaration position and check its local result sort.
No metavariable identity is inferred by matching its assigned body. -/
def SigMor.unmapMetaOp? (F : SigMor T S) [DecidableEq T.Srt] (M : List (MetaArity T))
    {sort : T.Srt} (operator : MetaOp (F.mapMetas M) (F.sortMap sort)) :
    Option (MetaOp M sort) :=
  let original := F.unmapMetaIndex operator.index
  if same : (M.get original).2 = sort then some (same ▸ MetaOp.mk original) else none

theorem SigMor.unmapMetaOp?_projects (F : SigMor T S) [DecidableEq T.Srt]
    (M : List (MetaArity T)) {sort : T.Srt}
    (original : MetaOp (F.mapMetas M) (F.sortMap sort)) (selected : MetaOp M sort)
    (found : F.unmapMetaOp? M original = some selected) : F.mapMetaOp selected = original := by
  unfold unmapMetaOp? at found
  dsimp only at found
  split at found
  · rename_i same
    cases Option.some.inj found
    apply MetaOp.index_injective
    rw [F.mapMetaOp_index, metaIndex_cast]
    rfl
  · cases found

theorem SigMor.unmapMetaOp?_roundtrip (F : SigMor T S) [DecidableEq T.Srt]
    (M : List (MetaArity T)) {sort : T.Srt} (operator : MetaOp M sort) :
    F.unmapMetaOp? M (F.mapMetaOp operator) = some operator := by
  unfold unmapMetaOp?
  rw [F.mapMetaOp_index, F.unmap_mapMetaIndex]
  simp only [operator.index_sort, dite_true]
  congr 1
  apply MetaOp.index_injective
  rw [metaIndex_cast]
  rfl

theorem SigMor.unmapMetaOp?_complete (F : SigMor T S) [DecidableEq T.Srt]
    (injective : Function.Injective F.sortMap) (M : List (MetaArity T)) {sort : T.Srt}
    (operator : MetaOp (F.mapMetas M) (F.sortMap sort)) :
    ∃ selected, F.unmapMetaOp? M operator = some selected := by
  have projected : F.sortMap (M.get (F.unmapMetaIndex operator.index)).2 = F.sortMap sort := by
    have mapped := congrArg Prod.snd (F.get_mapMetas (F.unmapMetaIndex operator.index))
    simpa only [mapArity, F.map_unmapMetaIndex] using mapped.symm.trans operator.index_sort
  have same := injective projected
  exact ⟨same ▸ MetaOp.mk _, by simp only [unmapMetaOp?, same, dite_true]⟩

namespace SigMor.OperatorReader

variable (F : SigMor T S) (reader : F.OperatorReader) [DecidableEq T.Srt]

def withMetas (metas : List (MetaArity T)) : (F.withMetas metas).OperatorReader where
  read operator := match operator with
    | .inl constructor => (reader.read constructor).map Sum.inl
    | .inr metavariable => (F.unmapMetaOp? metas metavariable).map Sum.inr
  projects original selected found := by
    cases original with
    | inl original =>
        obtain ⟨constructor, accepted, same⟩ := Option.map_eq_some_iff.mp found
        cases same
        exact congrArg Sum.inl (reader.projects original constructor accepted)
    | inr original =>
        obtain ⟨metavariable, accepted, same⟩ := Option.map_eq_some_iff.mp found
        cases same
        exact congrArg Sum.inr (F.unmapMetaOp?_projects metas original metavariable accepted)

theorem withMetas_roundtrip
    (operators : ∀ {sort} (operator : T.Op sort), reader.read (F.opMap operator) = some operator)
    (metas : List (MetaArity T)) {sort : T.Srt}
    (operator : (Binding.withMetas T metas).Op sort) :
    (withMetas F reader metas).read ((F.withMetas metas).opMap operator) = some operator := by
  cases operator with
  | inl constructor =>
      change (reader.read (F.opMap constructor)).map Sum.inl = some (.inl constructor)
      rw [operators constructor]
      rfl
  | inr metavariable =>
      change (F.unmapMetaOp? metas (F.mapMetaOp metavariable)).map Sum.inr = some (.inr metavariable)
      rw [F.unmapMetaOp?_roundtrip]
      rfl

theorem withMetas_complete (injective : Function.Injective F.sortMap)
    (available : ∀ {sort} (operator : S.Op (F.sortMap sort)),
      ∃ selected, reader.read operator = some selected)
    (metas : List (MetaArity T)) {sort : T.Srt}
    (operator : (Binding.withMetas S (F.mapMetas metas)).Op (F.sortMap sort)) :
    ∃ selected, (withMetas F reader metas).read operator = some selected := by
  cases operator with
  | inl constructor =>
      obtain ⟨selected, found⟩ := available constructor
      exact ⟨.inl selected, by change (reader.read constructor).map Sum.inl = _; rw [found]; rfl⟩
  | inr metavariable =>
      obtain ⟨selected, found⟩ := F.unmapMetaOp?_complete injective metas metavariable
      exact ⟨.inr selected, by change (F.unmapMetaOp? metas metavariable).map Sum.inr = _; rw [found]; rfl⟩

theorem readWithMetas_roundtrip
    (operators : ∀ {sort} (operator : T.Op sort), reader.read (F.opMap operator) = some operator)
    (metas : List (MetaArity T)) {context : Ctx T} {sort : T.Srt}
    (term : Term (Binding.withMetas T metas) context sort) :
    readTerm (F.withMetas metas) (withMetas F reader metas) ((F.withMetas metas).onTerm term) = some term :=
  readTerm_roundtrip (F.withMetas metas) (withMetas F reader metas)
    (withMetas_roundtrip F reader operators metas) term

theorem readWithMetas_complete (injective : Function.Injective F.sortMap)
    (available : ∀ {sort} (operator : S.Op (F.sortMap sort)),
      ∃ selected, reader.read operator = some selected)
    (metas : List (MetaArity T)) {context : Ctx T} {sort : T.Srt}
    (term : Term (Binding.withMetas S (F.mapMetas metas))
      (context.map F.sortMap) (F.sortMap sort)) :
    ∃ selected, readTerm (F.withMetas metas) (withMetas F reader metas) term = some selected :=
  readTerm_complete (F.withMetas metas) (withMetas F reader metas) injective
    (withMetas_complete F reader injective available metas) term

variable (injective : Function.Injective F.sortMap)

/-- Constructor support is local; declared metavariables are checked by the
original positional inverse and its original result-sort comparison. -/
def ConstructorSupport (metas : List (MetaArity T))
    {sort : S.Srt} (operator : (Binding.withMetas S (F.mapMetas metas)).Op sort) : Prop :=
  match operator with
  | .inl primitive => SupportedOperator F reader primitive
  | .inr _ => True

include injective in
theorem supportedOperator_withMetas (metas : List (MetaArity T)) {sort : S.Srt}
    (operator : (Binding.withMetas S (F.mapMetas metas)).Op sort)
    (supported : ConstructorSupport F reader metas operator) :
    SupportedOperator (F.withMetas metas) (withMetas F reader metas) operator := by
  intro targetSort same
  cases same
  cases operator with
  | inl primitive =>
      obtain ⟨selected, found⟩ := supported targetSort rfl
      exact ⟨.inl selected, by change (reader.read primitive).map Sum.inl = _; rw [found]; rfl⟩
  | inr metavariable =>
      obtain ⟨selected, found⟩ := F.unmapMetaOp?_complete injective metas metavariable
      exact ⟨.inr selected, by change (F.unmapMetaOp? metas metavariable).map Sum.inr = _; rw [found]; rfl⟩

include injective in
theorem readWithMetas_complete_on (metas : List (MetaArity T))
    {context : Ctx T} {sort : T.Srt}
    (term : Term (Binding.withMetas S (F.mapMetas metas))
      (context.map F.sortMap) (F.sortMap sort))
    (supported : term.AllOperators (ConstructorSupport F reader metas)) :
    ∃ selected, readTerm (F.withMetas metas) (withMetas F reader metas) term = some selected :=
  readTerm_complete_on (F.withMetas metas) (withMetas F reader metas) injective term
    (supported.mono (supportedOperator_withMetas F reader injective metas))

end SigMor.OperatorReader

end Mettapedia.OSLF.Binding


set_option autoImplicit false
namespace Mettapedia.OSLF.Binding.SortArityDecoder
variable {S T : Signature}

def castSchemaRows {source : Signature} {first second : List (MetaArity source)}
    (same : first = second) {context : Ctx source} {sort : source.Srt}
    (term : Term (withMetas source first) context sort) :
    Term (withMetas source second) context sort := same ▸ term

theorem castSchemaRows_cancel {source : Signature} {first second : List (MetaArity source)}
    (same : first = second) {context : Ctx source} {sort : source.Srt}
    (term : Term (withMetas source second) context sort) :
    castSchemaRows same (castSchemaRows same.symm term) = term := by cases same; rfl

namespace Interface
variable {decode : S.Srt → Option T.Srt} {original : List (MetaArity S)}
    (interface : Interface decode original) (F : SigMor T S)
    (sound : ∀ source target, decode source = some target → F.sortMap target = source)

/-- Only the actual decoded row equality is transported. Constructor scopes,
metavariable positions and all dependency arguments remain literal. -/
def schemaSource {context : Ctx T} {sort : T.Srt}
    (term : Term (withMetas T interface.entries) context sort) :
    Term (withMetas S original) (context.map F.sortMap) (F.sortMap sort) :=
  castSchemaRows (interface.projects F.sortMap sound)
    ((F.withMetas interface.entries).onTerm term)

variable [DecidableEq T.Srt] (reader : F.OperatorReader)

def schema? {context : Ctx T} {sort : T.Srt}
    (source : Term (withMetas S original) (context.map F.sortMap) (F.sortMap sort)) :
    Option (Term (withMetas T interface.entries) context sort) :=
  SigMor.OperatorReader.readTerm (F.withMetas interface.entries)
    (SigMor.OperatorReader.withMetas F reader interface.entries)
    (castSchemaRows (interface.projects F.sortMap sound).symm source)

theorem schema?_projects {context : Ctx T} {sort : T.Srt}
    (source : Term (withMetas S original) (context.map F.sortMap) (F.sortMap sort))
    (selected : Term (withMetas T interface.entries) context sort)
    (accepted : interface.schema? F sound reader source = some selected) :
    interface.schemaSource F sound selected = source := by
  have projected := SigMor.OperatorReader.readTerm_projects (F.withMetas interface.entries)
    (SigMor.OperatorReader.withMetas F reader interface.entries)
    (castSchemaRows (interface.projects F.sortMap sound).symm source) selected accepted
  exact (congrArg (castSchemaRows (interface.projects F.sortMap sound)) projected).trans
    (castSchemaRows_cancel _ source)

theorem schema?_roundtrip
    (operators : ∀ {sort} (operator : T.Op sort), reader.read (F.opMap operator) = some operator)
    {context : Ctx T} {sort : T.Srt}
    (term : Term (withMetas T interface.entries) context sort) :
    interface.schema? F sound reader (interface.schemaSource F sound term) = some term := by
  unfold schema? schemaSource
  rw [castSchemaRows_cancel]
  exact SigMor.OperatorReader.readWithMetas_roundtrip F reader operators interface.entries term

theorem schemaSource_injective
    (operators : ∀ {sort} (operator : T.Op sort), reader.read (F.opMap operator) = some operator)
    {context : Ctx T} {sort : T.Srt} :
    Function.Injective (interface.schemaSource F sound (context := context) (sort := sort)) := by
  intro first second same
  have recovered := congrArg (interface.schema? F sound reader) same
  rw [interface.schema?_roundtrip F sound reader operators,
    interface.schema?_roundtrip F sound reader operators] at recovered
  exact Option.some.inj recovered

/-- The original reader checks only the constructor occurrences actually
used; the already decoded metavariable rows are handled positionally. -/
theorem schema?_complete_on (injective : Function.Injective F.sortMap)
    {context : Ctx T} {sort : T.Srt}
    (source : Term (withMetas S original) (context.map F.sortMap) (F.sortMap sort))
    (supported : (castSchemaRows (interface.projects F.sortMap sound).symm source).AllOperators
      (SigMor.OperatorReader.ConstructorSupport F reader interface.entries)) :
    ∃ selected, interface.schema? F sound reader source = some selected :=
  SigMor.OperatorReader.readWithMetas_complete_on F reader injective interface.entries
    (castSchemaRows (interface.projects F.sortMap sound).symm source) supported

end Interface
end Mettapedia.OSLF.Binding.SortArityDecoder
