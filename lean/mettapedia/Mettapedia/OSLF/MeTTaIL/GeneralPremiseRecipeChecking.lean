import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchReplay

/-!
# Guided replay of finite authored premise recipes

A recipe selects the original declaration, scoped matcher choices, provider
row occurrences and finite premise events. Replay follows those choices
without enumerating matcher answers, query answers or child declarations.
Intermediate assignments are reconstructed sequentially by the original
capture and instantiation operations. No source derivation or validity proof
is accepted as evidence input.

The checker is exact for the independently defined RootFiring, PremiseHolds,
PremisesHold, QuantifiedElements and TracedQuery judgments. It accepts all
finite source derivations, with no declaration-order or global execution
readiness restriction. Every event, including unused suffixes and repeated
quantified occurrences, is checked at its actual source position.

Finite provider rows and dynamic service rows have the original disjoint
ordinals. An installed dynamic service is invoked once on the resolved inputs;
its existing independent source relation and exactness contract supply only
that primitive's authority. Unknown acquisition is distinct from a completed
empty table. Replay does not certify a complete answer set.

This is a total guided recipe checker, not a complete primitive execution
trace. Contextual capture, substitution, sorting, reflection and dynamic
services retain their actual computation. No polynomial or physical-time
bound follows from these exactness theorems.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.RecipeChecking

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Resolve exactly the primitive inputs in the original incoming assignment.
Output schemas remain holes. This follows one supplied query, not an agenda. -/
def resolveInputs (context : Context) (index : Nat) (initial : Assignment) :
    List Pattern → List RelationArgMode → Option (List Pattern)
  | [], [] => some []
  | schema :: schemas, .input :: modes => do
      return (← instantiateAt? context.rule context.spec context.bound.length
        (context.site index) [] 0 initial schema) :: (← resolveInputs context (index + 1) initial schemas modes)
  | schema :: schemas, .output :: modes =>
      (resolveInputs context (index + 1) initial schemas modes).map (schema :: ·)
  | _, _ => none

theorem resolveInputs_sound {context : Context} {index : Nat} {initial : Assignment}
    {schemas : List Pattern} {modes : List RelationArgMode} {values : List Pattern}
    (resolved : resolveInputs context index initial schemas modes = some values) :
    DynamicInputs context index initial schemas modes values := by
  induction schemas generalizing index modes values with
  | nil =>
      cases modes with
      | nil => cases Option.some.inj resolved; exact .nil
      | cons mode modes => cases resolved
  | cons schema schemas ih =>
      cases modes with
      | nil => cases resolved
      | cons mode modes =>
          cases mode with
          | input =>
              simp only [resolveInputs, Option.bind_eq_bind, Option.bind_eq_some_iff] at resolved
              obtain ⟨value, interpreted, rest, later, same⟩ := resolved
              cases same
              exact .input interpreted (ih later)
          | output =>
              obtain ⟨rest, later, same⟩ := Option.map_eq_some_iff.mp resolved
              cases same
              exact .output (ih later)

theorem resolveInputs_complete {context : Context} {index : Nat} {initial : Assignment}
    {schemas : List Pattern} {modes : List RelationArgMode} {values : List Pattern}
    (held : DynamicInputs context index initial schemas modes values) :
    resolveInputs context index initial schemas modes = some values := by
  induction held with
  | nil => rfl
  | input interpreted _ ih => simp only [resolveInputs, interpreted, ih]; rfl
  | output _ ih => simp only [resolveInputs, ih, Option.map_some]

theorem resolveInputs_exact (context : Context) (index : Nat) (initial : Assignment)
    (schemas : List Pattern) (modes : List RelationArgMode) (values : List Pattern) :
    resolveInputs context index initial schemas modes = some values ↔
      DynamicInputs context index initial schemas modes values :=
  ⟨resolveInputs_sound, resolveInputs_complete⟩

private def argumentRequest (context : Context) (index : Nat) (initial : Assignment)
    (schema value : Pattern) : GeneralScopedMatchMachine.Request :=
  ⟨context.rule, context.spec, context.bound.length, context.site index, [], 0, initial, schema, value⟩

/-- One argument origin per source position; output matching follows the
supplied choices and computes exactly one continuation assignment. -/
def arguments? (context : Context) (index : Nat) (initial : Assignment) :
    (schemas values : List Pattern) → (modes : List RelationArgMode) →
    (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) →
    Option {final : Assignment // TracedArgumentsHold context index initial schemas values modes final origins}
  | [], [], [], [] => some ⟨initial, .nil⟩
  | schema :: schemas, value :: values, .input :: modes, (recorded, trace) :: origins =>
      if metadata : recorded = index ∧ trace = [] then
        if interpreted : instantiateAt? context.rule context.spec context.bound.length
            (context.site index) [] 0 initial schema = some value then do
          let later ← arguments? context (index + 1) initial schemas values modes origins
          pure ⟨later.val, by rcases metadata with ⟨rfl, rfl⟩; exact .input interpreted later.property⟩
        else none
      else none
  | schema :: schemas, value :: values, .output :: modes, (recorded, trace) :: origins =>
      if numbered : recorded = index then
        match matched : GeneralScopedMatchReplay.replay (argumentRequest context index initial schema value) trace with
        | none => none
        | some middle => do
            let later ← arguments? context (index + 1) middle schemas values modes origins
            pure ⟨later.val, by
              subst recorded
              exact .output ((GeneralScopedMatchReplay.replay_exact _ _ _).mp matched) later.property⟩
      else none
  | _, _, _, _ => none

theorem arguments_complete {context : Context} {index : Nat} {initial final : Assignment}
    {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedArgumentsHold context index initial schemas values modes final origins) :
    (arguments? context index initial schemas values modes origins).map Subtype.val = some final := by
  induction held with
  | nil => rfl
  | input interpreted tail ih =>
      obtain ⟨later, ran, same⟩ := Option.map_eq_some_iff.mp ih
      cases same
      simp only [arguments?.eq_2, interpreted, ↓reduceDIte, ran]
      rfl
  | @output index initial middle final schema value schemas values modes trace origins matching tail ih =>
      obtain ⟨later, ran, same⟩ := Option.map_eq_some_iff.mp ih
      cases same
      have guided := (GeneralScopedMatchReplay.replay_exact
        (argumentRequest context index initial schema value) trace middle).mpr matching
      simp only [arguments?.eq_3, ↓reduceDIte]
      split
      · rename_i absent
        simp [guided] at absent
      · rename_i actual found
        cases Option.some.inj (found.symm.trans guided)
        simp only [ran, Bind.bind, Option.bind]
        rfl

/-- This helper checks the actual selected row in the complete caller typing
context. Its proof is output data justified by local checks, never an input
claim that the whole query is valid. -/
def row? (environment : Environment) (context : Context) (signature : Signature)
    (arguments : List Pattern) (row : ProviderRow) (initial : Assignment)
    (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) :
    Option {final : Assignment //
      RowTyped environment.language environment.free context.bound signature row ∧
      TracedArgumentsHold context 0 initial arguments row.values signature.modes final origins ∧
      TypedAssignment environment context final} :=
  if typed : checkRow environment.language environment.free context.bound signature row then do
    let matched ← arguments? context 0 initial arguments row.values signature.modes origins
    if completed : checkTypedAssignment environment context matched.val then
      pure ⟨matched.val, checkRow_sound typed, matched.property, checkTypedAssignment_sound completed⟩
    else none
  else none

theorem row_complete {environment : Environment} {context : Context} {signature : Signature}
    {arguments : List Pattern} {row : ProviderRow} {initial final : Assignment}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (typed : RowTyped environment.language environment.free context.bound signature row)
    (matched : TracedArgumentsHold context 0 initial arguments row.values signature.modes final origins)
    (completed : TypedAssignment environment context final) :
    (row? environment context signature arguments row initial origins).map Subtype.val = some final := by
  obtain ⟨later, ran, same⟩ := Option.map_eq_some_iff.mp (arguments_complete matched)
  cases same
  simp only [row?, checkRow_complete typed, ↓reduceDIte, ran, Bind.bind, Option.bind,
    checkTypedAssignment_complete completed]
  rfl

/-- Select precisely the supplied provider occurrence. Dynamic services, when
installed, are executed once on resolved inputs; their independent rows_exact
contract supplies primitive authority. Their execution cost is not hidden in
a constant-cost or purely finite-table claim. -/
def query? (environment : Environment) (context : Context) (relation : String)
    (arguments : List Pattern) (initial : Assignment) (ordinal : Nat)
    (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) :
    Option {final : Assignment // TracedQuery environment context relation arguments initial ordinal final origins} :=
  match declared : signature? environment.provider relation arguments.length with
  | none => none
  | some signature =>
      match selected : environment.provider.rows[ordinal]? with
      | some row => do
          let checked ← row? environment context signature arguments row initial origins
          pure ⟨checked.val, .row selected declared checked.property.1 checked.property.2.1 checked.property.2.2⟩
      | none =>
          if native : environment.provider.rows.length ≤ ordinal ∧ relation ∈ environment.provider.dynamicRelations then
            match resolved : resolveInputs context 0 initial arguments signature.modes with
            | none => none
            | some inputs =>
                match acquired : environment.dynamic.rows? relation inputs with
                | none => none
                | some rows =>
                    match selected : rows[ordinal - environment.provider.rows.length]? with
                    | none => none
                    | some values => do
                        let checked ← row? environment context signature arguments ⟨relation, values⟩ initial origins
                        pure ⟨checked.val, by
                          have same : environment.provider.rows.length + (ordinal - environment.provider.rows.length) = ordinal := by omega
                          simpa only [same] using
                            (TracedQuery.dynamicRow native.2 declared ((resolveInputs_exact _ _ _ _ _ _).mp resolved)
                              ((environment.dynamic.rows_exact _ _ _).mp acquired) selected
                              checked.property.1 checked.property.2.1 checked.property.2.2)⟩
          else none

theorem query_complete {environment : Environment} {context : Context} {relation : String}
    {arguments : List Pattern} {initial final : Assignment} {ordinal : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedQuery environment context relation arguments initial ordinal final origins) :
    (query? environment context relation arguments initial ordinal origins).map Subtype.val = some final := by
  cases held with
  | row selected declared typed matched completed =>
      obtain ⟨checked, ran, same⟩ := Option.map_eq_some_iff.mp (row_complete typed matched completed)
      cases same
      unfold query?
      split
      · rename_i absent
        simp [declared] at absent
      · rename_i signature present
        cases Option.some.inj (present.symm.trans declared)
        split
        · rename_i selectedRow found
          cases Option.some.inj (found.symm.trans selected)
          simp only [ran, Bind.bind, Option.bind]
          rfl
        · rename_i absent
          simp [selected] at absent
  | @dynamicRow nativeIndex signature final resolved rows values origins registered declared inputs source selected typed matched completed =>
      have missing : environment.provider.rows[environment.provider.rows.length + nativeIndex]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      have input := resolveInputs_complete inputs
      have acquired := (environment.dynamic.rows_exact _ _ _).mpr source
      obtain ⟨checked, ran, same⟩ := Option.map_eq_some_iff.mp (row_complete typed matched completed)
      cases same
      unfold query?
      split
      · rename_i absent
        simp [declared] at absent
      · rename_i signature present
        cases Option.some.inj (present.symm.trans declared)
        split
        · rename_i selectedRow found
          simp at found
        · rw [dif_pos ⟨by omega, registered⟩]
          split
          · rename_i absent
            simp [input] at absent
          · rename_i inputs present
            cases Option.some.inj (present.symm.trans input)
            split
            · rename_i absent
              simp [acquired] at absent
            · rename_i actualRows present
              cases Option.some.inj (present.symm.trans acquired)
              split
              · rename_i absent
                simp [selected] at absent
              · rename_i actualValues found
                simp only [Nat.add_sub_cancel_left] at found
                cases Option.some.inj (found.symm.trans selected)
                simp only [ran, Bind.bind, Option.bind]
                rfl

mutual
/-- Validate a single supplied finite firing recipe. No matching or query
agenda is enumerated. Proof output is reconstructed from the original source
constructors after the local executable checks. -/
def root? (environment : Environment) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern) :
    Option (PLift (RootFiring environment bound type source index trace captured completed history target)) :=
  match declared : environment.language.rewrites[index]?, specified : specification? environment index with
  | some rule, some spec =>
      if ready : admittedFor rule spec = true ∧
          checkOpenPatternWellSorted environment.language environment.free bound type source = true ∧
          GeneralScopedMatchReplay.replay ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩ trace = some captured ∧
          checkTypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured = true ∧
          (premises? environment ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured history).map Subtype.val = some completed ∧
          reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
            rule spec bound.length completed = some target ∧
          checkOpenPatternWellSorted environment.language environment.free bound type target = true then
        some ⟨.fire declared specified ready.1 (checkOpenPatternWellSorted_sound ready.2.1)
          ((GeneralScopedMatchReplay.replay_exact _ _ _).mp ready.2.2.1)
          (checkTypedAssignment_sound ready.2.2.2.1) (by
            obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp ready.2.2.2.2.1
            exact same ▸ packet.property)
          ready.2.2.2.2.2.1 (checkOpenPatternWellSorted_sound ready.2.2.2.2.2.2)⟩
      else none
  | _, _ => none
termination_by 4 * sizeOf history + 3

/-- Follow precisely one original event, with the original sequential binding
and scoped child conventions. No whole-premise validity callback is supplied. -/
def premise? (environment : Environment) (context : Context) (body : Premise)
    (initial : Assignment) (event : Event) :
    Option {final : Assignment // PremiseHolds environment context body initial final event} :=
  match body, event with
  | .relationQuery relation arguments, .query p q ordinal origins =>
      if metadata : p = context.premiseIndex ∧ q = context.quantifierDepth then do
        let checked ← query? environment context relation arguments initial ordinal origins
        pure ⟨checked.val, by rcases metadata with ⟨rfl, rfl⟩; exact .query checked.property⟩
      else none
  | .freshness condition, .freshness p q atom subject =>
      if metadata : p = context.premiseIndex ∧ q = context.quantifierDepth ∧
          freshnessSubject? context.rule context.spec context.bound context.premiseIndex
            context.quantifierDepth initial condition = some (atom, subject) ∧
          Substitution.isFresh atom subject = true then
        some ⟨initial, by
          rcases metadata with ⟨rfl, rfl, interpreted, fresh⟩
          exact .freshness interpreted ((syntactic_freshness_iff _ _).mp fresh)⟩
      else none
  | .congruence source target,
      .child p q childIndex bound actualSource actualTarget trace targetTrace captured completed history =>
      match typed : sourceType? environment.language context.rule source with
      | none => none
      | some type =>
          if metadata : p = context.premiseIndex ∧ q = context.quantifierDepth ∧ bound = context.bound ∧
              instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0
                initial source = some actualSource then do
            let child ← root? environment context.bound type actualSource childIndex trace captured completed history actualTarget
            match matched : GeneralScopedMatchReplay.replay
                ⟨context.rule, context.spec, context.bound.length, context.site 1, [], 0, initial, target, actualTarget⟩ targetTrace with
            | none => none
            | some final =>
                if completed : checkTypedAssignment environment context final then
                  some ⟨final, by
                    rcases metadata with ⟨rfl, rfl, rfl, interpreted⟩
                    exact .step typed interpreted child.down ((GeneralScopedMatchReplay.replay_exact _ _ _).mp matched)
                      (checkTypedAssignment_sound completed)⟩
                else none
          else none
  | .scopedStep step,
      .child p q childIndex bound actualSource actualTarget trace targetTrace captured completed history =>
      if metadata : p = context.premiseIndex ∧ q = context.quantifierDepth ∧
          bound = step.binders ++ context.bound ∧
          instantiateAt? context.rule context.spec context.bound.length (context.site 0) []
            step.binders.length initial step.source = some actualSource then do
        let child ← root? environment (step.binders ++ context.bound) step.resultType actualSource childIndex
          trace captured completed history actualTarget
        match matched : GeneralScopedMatchReplay.replay
            ⟨context.rule, context.spec, context.bound.length, context.site 1, [], step.binders.length,
              initial, step.target, actualTarget⟩ targetTrace with
        | none => none
        | some final =>
            if completed : checkTypedAssignment environment context final then
              some ⟨final, by
                rcases metadata with ⟨rfl, rfl, rfl, interpreted⟩
                exact .scopedStep interpreted child.down ((GeneralScopedMatchReplay.replay_exact _ _ _).mp matched)
                  (checkTypedAssignment_sound completed)⟩
            else none
      else none
  | .forAll collection parameter body, .quantified p q kind history =>
      match interpreted : finiteCollection? context.bound.length initial collection with
      | none => none
      | some (actualKind, elements) =>
          if metadata : p = context.premiseIndex ∧ q = context.quantifierDepth ∧ actualKind = kind then do
            let checked ← quantified? environment context parameter body 0 elements initial history
            pure ⟨checked.val, by rcases metadata with ⟨rfl, rfl, rfl⟩; exact .quantified interpreted checked.property⟩
          else none
  | _, _ => none
termination_by 4 * sizeOf event + 1

def premises? (environment : Environment) (context : Context) (bodies : List Premise)
    (initial : Assignment) (events : List Event) :
    Option {final : Assignment // PremisesHold environment context bodies initial final events} :=
  match bodies, events with
  | [], [] => some ⟨initial, .nil⟩
  | body :: bodies, event :: events => do
      let first ← premise? environment context body initial event
      let later ← premises? environment context.next bodies first.val events
      pure ⟨later.val, .cons first.property later.property⟩
  | _, _ => none
termination_by 4 * sizeOf events + 2

def quantified? (environment : Environment) (context : Context) (parameter : String) (body : Premise)
    (index : Nat) (elements : List Pattern) (initial : Assignment)
    (events : List (Nat × Pattern × List Event)) :
    Option {final : Assignment // QuantifiedElements environment context parameter body index elements initial final events} :=
  match elements, events with
  | [], [] => some ⟨initial, .nil⟩
  | element :: elements, (recordedIndex, recordedElement, [event]) :: events =>
      if metadata : recordedIndex = index ∧ recordedElement = element ∧
          checkTypedAssignment environment context.quantified
            (bindParameter parameter (localValue context.bound element) initial) = true then do
        let first ← premise? environment context.quantified body
          (bindParameter parameter (localValue context.bound element) initial) event
        let later ← quantified? environment context parameter body (index + 1) elements
          (restoreParameter parameter initial first.val) events
        pure ⟨later.val, by
          rcases metadata with ⟨rfl, rfl, typed⟩
          exact .cons (checkTypedAssignment_sound typed) first.property later.property⟩
      else none
  | _, _ => none
termination_by 4 * sizeOf events
end

private theorem guided_complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial : Assignment}
    {schema target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice} {final : Assignment}
    (matched : GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth initial schema target trace final) :
    GeneralScopedMatchReplay.replay ⟨rule, spec, ambient, site, path, depth, initial, schema, target⟩ trace = some final :=
  (GeneralScopedMatchReplay.replay_exact _ _ _).mpr matched

mutual
 theorem root_complete {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event}
    (held : RootFiring environment bound type source index trace captured completed history target) :
    (root? environment bound type source index trace captured completed history target).isSome = true :=
  match held with
  | .fire declared specified admitted sorted matched captureTyped premises reduced targetTyped => by
      have guided := guided_complete matched
      have finished := premises_complete premises
      unfold root?
      split
      · rename_i actualRule actualSpec gotRule gotSpec
        cases Option.some.inj (gotRule.symm.trans declared)
        cases Option.some.inj (gotSpec.symm.trans specified)
        rw [dif_pos ⟨admitted, checkOpenPatternWellSorted_complete sorted, guided,
          checkTypedAssignment_complete captureTyped, finished, reduced,
          checkOpenPatternWellSorted_complete targetTyped⟩]
        rfl
      · rename_i gotRule gotSpec
        simp_all
 termination_by structural held

 theorem premise_complete {environment : Environment} {context : Context} {body : Premise}
    {initial final : Assignment} {event : Event}
    (held : PremiseHolds environment context body initial final event) :
    (premise? environment context body initial event).map Subtype.val = some final :=
  match held with
  | .query source => by
      obtain ⟨packet, ran, same⟩ := Option.map_eq_some_iff.mp (query_complete source)
      cases same
      rw [premise?.eq_1, dif_pos ⟨rfl, rfl⟩]
      simp only [ran, Bind.bind, Option.bind]
      rfl
  | .freshness interpreted fresh => by
      rw [premise?.eq_2]
      rw [dif_pos ⟨rfl, rfl, interpreted, (syntactic_freshness_iff _ _).mpr fresh⟩]
      rfl
  | .step typed interpreted child matched finalTyped => by
      obtain ⟨packet, ran⟩ := Option.isSome_iff_exists.mp (root_complete child)
      have guided := guided_complete matched
      rw [premise?.eq_3]
      split
      · rename_i absent
        simp [typed] at absent
      · rename_i actualType present
        cases Option.some.inj (present.symm.trans typed)
        rw [dif_pos ⟨rfl, rfl, rfl, interpreted⟩]
        simp only [ran, Bind.bind, Option.bind]
        split
        · rename_i absent
          simp [guided] at absent
        · rename_i actualFinal present
          cases Option.some.inj (present.symm.trans guided)
          rw [dif_pos (checkTypedAssignment_complete finalTyped)]
          rfl
  | .scopedStep interpreted child matched finalTyped => by
      obtain ⟨packet, ran⟩ := Option.isSome_iff_exists.mp (root_complete child)
      have guided := guided_complete matched
      rw [premise?.eq_4, dif_pos ⟨rfl, rfl, rfl, interpreted⟩]
      simp only [ran, Bind.bind, Option.bind]
      split
      · rename_i absent
        simp [guided] at absent
      · rename_i actualFinal present
        cases Option.some.inj (present.symm.trans guided)
        rw [dif_pos (checkTypedAssignment_complete finalTyped)]
        rfl
  | .quantified interpreted elements => by
      obtain ⟨packet, ran, same⟩ := Option.map_eq_some_iff.mp (quantified_complete elements)
      cases same
      rw [premise?.eq_5]
      split
      · rename_i absent
        simp [interpreted] at absent
      · rename_i actualKind actualElements present
        cases Option.some.inj (present.symm.trans interpreted)
        rw [dif_pos ⟨rfl, rfl, rfl⟩]
        simp only [ran, Bind.bind, Option.bind]
        rfl
 termination_by structural held

 theorem premises_complete {environment : Environment} {context : Context}
    {bodies : List Premise} {initial final : Assignment} {events : List Event}
    (held : PremisesHold environment context bodies initial final events) :
    (premises? environment context bodies initial events).map Subtype.val = some final :=
  match held with
  | .nil => by rw [premises?.eq_1]; rfl
  | .cons first later => by
      have headComplete := premise_complete first
      have tailComplete := premises_complete later
      obtain ⟨head, ranHead, same⟩ := Option.map_eq_some_iff.mp headComplete
      cases same
      obtain ⟨tail, ranTail, same⟩ := Option.map_eq_some_iff.mp tailComplete
      cases same
      rw [premises?.eq_2]
      simp only [ranHead, ranTail, Bind.bind, Option.bind]
      rfl
 termination_by structural held

 theorem quantified_complete {environment : Environment} {context : Context} {parameter : String}
    {body : Premise} {index : Nat} {elements : List Pattern} {initial final : Assignment}
    {events : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment context parameter body index elements initial final events) :
    (quantified? environment context parameter body index elements initial events).map Subtype.val = some final :=
  match held with
  | .nil => by rw [quantified?.eq_1]; rfl
  | .cons typed first later => by
      have headComplete := premise_complete first
      have tailComplete := quantified_complete later
      obtain ⟨head, ranHead, same⟩ := Option.map_eq_some_iff.mp headComplete
      cases same
      obtain ⟨tail, ranTail, same⟩ := Option.map_eq_some_iff.mp tailComplete
      cases same
      rw [quantified?.eq_2]
      rw [dif_pos ⟨rfl, rfl, checkTypedAssignment_complete typed⟩]
      simp only [ranHead, ranTail, Bind.bind, Option.bind]
      rfl
 termination_by structural held
end

/-- Public raw replay data erase only reconstructed proof fields. -/
def replayArguments (context : Context) (index : Nat) (initial : Assignment)
    (schemas values : List Pattern) (modes : List RelationArgMode)
    (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) : Option Assignment :=
  (arguments? context index initial schemas values modes origins).map Subtype.val

def replayQuery (environment : Environment) (context : Context) (relation : String)
    (arguments : List Pattern) (initial : Assignment) (ordinal : Nat)
    (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) : Option Assignment :=
  (query? environment context relation arguments initial ordinal origins).map Subtype.val

def replayPremise (environment : Environment) (context : Context) (body : Premise)
    (initial : Assignment) (event : Event) : Option Assignment :=
  (premise? environment context body initial event).map Subtype.val

def replayPremises (environment : Environment) (context : Context) (bodies : List Premise)
    (initial : Assignment) (events : List Event) : Option Assignment :=
  (premises? environment context bodies initial events).map Subtype.val

def replayQuantified (environment : Environment) (context : Context) (parameter : String)
    (body : Premise) (index : Nat) (elements : List Pattern) (initial : Assignment)
    (events : List (Nat × Pattern × List Event)) : Option Assignment :=
  (quantified? environment context parameter body index elements initial events).map Subtype.val

def checkRoot (environment : Environment) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern) : Bool :=
  (root? environment bound type source index trace captured completed history target).isSome

theorem replayArguments_exact (context : Context) (index : Nat) (initial : Assignment)
    (schemas values : List Pattern) (modes : List RelationArgMode) (final : Assignment)
    (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) :
    replayArguments context index initial schemas values modes origins = some final ↔
      TracedArgumentsHold context index initial schemas values modes final origins := by
  constructor
  · intro ran
    obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp ran
    exact same ▸ packet.property
  · exact arguments_complete

theorem replayQuery_exact (environment : Environment) (context : Context) (relation : String)
    (arguments : List Pattern) (initial final : Assignment) (ordinal : Nat)
    (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) :
    replayQuery environment context relation arguments initial ordinal origins = some final ↔
      TracedQuery environment context relation arguments initial ordinal final origins := by
  constructor
  · intro ran
    obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp ran
    exact same ▸ packet.property
  · exact query_complete

theorem replayPremise_exact (environment : Environment) (context : Context) (body : Premise)
    (initial final : Assignment) (event : Event) :
    replayPremise environment context body initial event = some final ↔
      PremiseHolds environment context body initial final event := by
  constructor
  · intro ran
    obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp ran
    exact same ▸ packet.property
  · exact premise_complete

theorem replayPremises_exact (environment : Environment) (context : Context) (bodies : List Premise)
    (initial final : Assignment) (events : List Event) :
    replayPremises environment context bodies initial events = some final ↔
      PremisesHold environment context bodies initial final events := by
  constructor
  · intro ran
    obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp ran
    exact same ▸ packet.property
  · exact premises_complete

theorem replayQuantified_exact (environment : Environment) (context : Context) (parameter : String)
    (body : Premise) (index : Nat) (elements : List Pattern) (initial final : Assignment)
    (events : List (Nat × Pattern × List Event)) :
    replayQuantified environment context parameter body index elements initial events = some final ↔
      QuantifiedElements environment context parameter body index elements initial final events := by
  constructor
  · intro ran
    obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp ran
    exact same ▸ packet.property
  · exact quantified_complete

theorem checkRoot_exact (environment : Environment) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List Event) (target : Pattern) :
    checkRoot environment bound type source index trace captured completed history target = true ↔
      RootFiring environment bound type source index trace captured completed history target := by
  constructor
  · intro checked
    obtain ⟨packet, _⟩ := Option.isSome_iff_exists.mp checked
    exact packet.down
  · exact root_complete

/-- Compare the reconstructed sequential output with the submitted endpoint. -/
def checkPremises (environment : Environment) (context : Context) (bodies : List Premise)
    (initial final : Assignment) (events : List Event) : Bool :=
  decide (replayPremises environment context bodies initial events = some final)

theorem checkPremises_exact (environment : Environment) (context : Context) (bodies : List Premise)
    (initial final : Assignment) (events : List Event) :
    checkPremises environment context bodies initial final events = true ↔
      PremisesHold environment context bodies initial final events := by
  rw [checkPremises, decide_eq_true_eq]
  exact replayPremises_exact environment context bodies initial final events

/-- A fixed history determines one sequential continuation assignment. -/
theorem premises_unique {environment : Environment} {context : Context} {bodies : List Premise}
    {initial first last : Assignment} {events : List Event}
    (left : PremisesHold environment context bodies initial first events)
    (right : PremisesHold environment context bodies initial last events) : first = last :=
  Option.some.inj ((premises_complete left).symm.trans (premises_complete right))

/-- A fixed query row occurrence and guided output choices determine one result. -/
theorem query_unique {environment : Environment} {context : Context} {relation : String}
    {arguments : List Pattern} {initial first last : Assignment} {ordinal : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (left : TracedQuery environment context relation arguments initial ordinal first origins)
    (right : TracedQuery environment context relation arguments initial ordinal last origins) : first = last :=
  Option.some.inj ((query_complete left).symm.trans (query_complete right))
end Mettapedia.OSLF.MeTTaIL.GeneralPremise.RecipeChecking
