import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialSource

/-! # The MeTTa spatial evaluator computes the shared strategy -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialRuntime

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Spatial Execution
open MeTTaIL WireKit Eval BridgeKit

syntax "spatial_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| spatial_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call library_checked; metta_eval [$facts,*] with library_checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, $extra,*]))

@[simp] theorem bagTerm_eq_iff (first second : Bag) : bagTerm first = bagTerm second ↔ first = second :=
  ⟨fun same => CettaWire.encodeList_injective _ InferenceCettaWire.encodePattern_injective same, congrArg bagTerm⟩

theorem prependRight_returns (state : Effects.State) (item : Pattern) (pairs : Splits) :
    PureReturns library.runtime [] state
      (apply "native:spatial:prepend-right" [encoded (InferenceCettaWire.encodePattern item), encoded (splitsTerm pairs)])
      state (encoded (splitsTerm (pairs.map fun pair => (pair.1, item :: pair.2)))) := by
  induction pairs with
  | nil => spatial_eval unfolding [splitsTerm, encodeList]
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    spatial_eval [ih] unfolding [splitsTerm, splitTerm, bagTerm, encodeList]

theorem prependLeft_returns (state : Effects.State) (item : Pattern) (pairs tail : Splits) :
    PureReturns library.runtime [] state
      (apply "native:spatial:prepend-left"
        [encoded (InferenceCettaWire.encodePattern item), encoded (splitsTerm pairs), encoded (splitsTerm tail)])
      state (encoded (splitsTerm ((pairs.map fun pair => (item :: pair.1, pair.2)) ++ tail))) := by
  induction pairs with
  | nil => spatial_eval unfolding [splitsTerm, encodeList]
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    spatial_eval [ih] unfolding [splitsTerm, splitTerm, bagTerm, encodeList]

theorem splits_returns (state : Effects.State) (bag : Bag) :
    PureReturns library.runtime [] state
      (apply "native:spatial:splits" [encoded (bagTerm bag)]) state
      (encoded (splitsTerm (BagSplits.enumerate bag))) := by
  induction bag with
  | nil => spatial_eval unfolding [BagSplits.enumerate, splitsTerm, splitTerm, bagTerm, encodeList]
  | cons item rest ih =>
    have rights := prependRight_returns state item (BagSplits.enumerate rest)
    have lefts := prependLeft_returns state item (BagSplits.enumerate rest)
      ((BagSplits.enumerate rest).map fun pair => (pair.1, item :: pair.2))
    spatial_eval [ih, rights, lefts] unfolding [BagSplits.enumerate, bagTerm, encodeList]

theorem binary_returns (state : Effects.State) (op : Binary) (left right : Bool) :
    PureReturns library.runtime [] state
      (apply "native:spatial:binary" [encoded (binaryTerm op), encoded (boolTerm left), encoded (boolTerm right)])
      state (encoded (boolTerm (op.apply left right))) := by
  cases op <;> cases left <;> cases right <;>
    spatial_eval unfolding [binaryTerm, boolTerm, Binary.apply]

theorem leaf_returns (state : Effects.State) (leaf : BagModel.Leaf) (bag : Bag) :
    PureReturns library.runtime [] state
      (apply "native:spatial:leaf" [encoded (leafTerm leaf), encoded (bagTerm bag)])
      state (encoded (boolTerm (BagModel.evalLeaf leaf bag))) := by
  cases leaf with
  | emp =>
    have equivalent : bagTerm bag = .symbol "LNil" ↔ bag = [] := bagTerm_eq_iff bag []
    by_cases empty : bag = []
    · subst bag
      spatial_eval unfolding [leafTerm, bagTerm, encodeList, boolTerm, BagModel.evalLeaf]
      apply pure_if_returns
      · apply term_equal_returns (first := bagTerm []) (second := bagTerm [])
        · exact bound_returns _ _ _ (by rfl)
        · exact Eval.symbol_returns _ _ _ _
      · simp only [decide_true, ↓reduceIte]
        simpa [BagModel.evalLeaf, boolTerm, encoded, number, CettaWireAtom.encode] using
          (literal_returns library.runtime _ state 1)
    · have different := mt equivalent.mp empty
      spatial_eval unfolding [leafTerm, boolTerm, BagModel.evalLeaf, empty, different]
      apply pure_if_returns
      · apply term_equal_returns (first := bagTerm bag) (second := .symbol "LNil")
        · exact bound_returns _ _ _ (by rfl)
        · exact Eval.symbol_returns _ _ _ _
      · simp only [different, decide_false, Bool.false_eq_true, ↓reduceIte]
        simpa [BagModel.evalLeaf, empty, boolTerm, encoded, number, CettaWireAtom.encode] using
          (literal_returns library.runtime _ state 0)
  | singleton item =>
    have equivalent : bagTerm bag = .application "LCons" [InferenceCettaWire.encodePattern item, .symbol "LNil"] ↔
        bag = [item] := bagTerm_eq_iff bag [item]
    by_cases single : bag = [item]
    · subst bag
      spatial_eval unfolding [leafTerm, bagTerm, encodeList, boolTerm, BagModel.evalLeaf]
      apply pure_if_returns
      · apply term_equal_returns (first := bagTerm [item]) (second := bagTerm [item])
        · exact bound_returns _ _ _ (by rfl)
        · metta_eval with library_checked unfolding [bagTerm, encodeList]
      · simp only [decide_true, ↓reduceIte]
        simpa [BagModel.evalLeaf, boolTerm, encoded, number, CettaWireAtom.encode] using
          (literal_returns library.runtime _ state 1)
    · have different := mt equivalent.mp single
      spatial_eval unfolding [leafTerm, boolTerm, BagModel.evalLeaf, single, different]
      apply pure_if_returns
      · apply term_equal_returns (first := bagTerm bag) (second := bagTerm [item])
        · exact bound_returns _ _ _ (by rfl)
        · metta_eval with library_checked unfolding [bagTerm, encodeList]
      · have other : ¬ bagTerm bag = bagTerm [item] := mt (bagTerm_eq_iff bag [item]).mp single
        simp only [other, decide_false, Bool.false_eq_true, ↓reduceIte]
        simpa [BagModel.evalLeaf, single, boolTerm, encoded, number, CettaWireAtom.encode] using
          (literal_returns library.runtime _ state 0)

private theorem evalStep_returns (state : Effects.State) (formula : Expression) (bag : Bag) (next : Continuation) :
    PureReturns library.runtime [] state
      (apply "native:spatial:step" [encoded (stateTerm (.eval formula bag next))]) state
      (encoded (stateTerm (Execution.step (.eval formula bag next)))) := by
  cases formula with
  | atom leaf =>
    spatial_eval [leaf_returns state leaf bag] unfolding [stateTerm, formulaTerm, Execution.step]
  | top | bottom | neg _ | conj _ _ | disj _ _ | imp _ _ | possibility _ | outgoingUniversal _ =>
    spatial_eval unfolding [stateTerm, formulaTerm, continuationTerm, boolTerm, binaryTerm, Execution.step]
  | separating index left right =>
    cases index with
    | zero =>
      spatial_eval [splits_returns state bag] unfolding [stateTerm, formulaTerm, continuationTerm, Execution.step]
    | succ index =>
      spatial_eval unfolding [stateTerm, formulaTerm, boolTerm, Execution.step]

private theorem chooseStep_returns (state : Effects.State) (left right : Expression) (remaining : Splits) (next : Continuation) :
    PureReturns library.runtime [] state
      (apply "native:spatial:step" [encoded (stateTerm (.choose left right remaining next))]) state
      (encoded (stateTerm (Execution.step (.choose left right remaining next)))) := by
  cases remaining with
  | nil => spatial_eval unfolding [stateTerm, splitsTerm, encodeList, boolTerm, Execution.step]
  | cons pair rest =>
    rcases pair with ⟨first, second⟩
    spatial_eval unfolding [stateTerm, splitsTerm, splitTerm, encodeList, continuationTerm, Execution.step]

private theorem returnStep_returns (state : Effects.State) (value : Bool) (next : Continuation) :
    PureReturns library.runtime [] state
      (apply "native:spatial:step" [encoded (stateTerm (.ret value next))]) state
      (encoded (stateTerm (Execution.step (.ret value next)))) := by
  cases next with
  | halt => spatial_eval unfolding [stateTerm, continuationTerm, Execution.step]
  | negate next =>
    cases value <;> spatial_eval unfolding [stateTerm, continuationTerm, boolTerm, Execution.step]
  | binaryLeft op right bag next =>
    spatial_eval unfolding [stateTerm, continuationTerm, Execution.step]
  | binaryRight op left next =>
    spatial_eval [binary_returns state op left value] unfolding [stateTerm, continuationTerm, Execution.step]
  | splitLeft left right rightBag rest next =>
    spatial_eval unfolding [stateTerm, continuationTerm, Execution.step]
  | splitRight left right first rest next =>
    cases first <;> spatial_eval unfolding [stateTerm, continuationTerm, boolTerm, Execution.step]
  | splitRest found next =>
    cases found <;> spatial_eval unfolding [stateTerm, continuationTerm, boolTerm, Execution.step]


theorem step_returns (state : Effects.State) (cursor : Execution.State) :
    PureReturns library.runtime [] state
      (apply "native:spatial:step" [encoded (stateTerm cursor)]) state
      (encoded (stateTerm (Execution.step cursor))) := by
  cases cursor with
  | eval formula bag next => exact evalStep_returns state formula bag next
  | choose left right remaining next => exact chooseStep_returns state left right remaining next
  | ret value next => exact returnStep_returns state value next

theorem run_returns (state : Effects.State) (fuel : Nat) (cursor : Execution.State) :
    PureReturns library.runtime [] state
      (apply "native:spatial:run" [number fuel, encoded (stateTerm cursor)]) state
      (encoded (stateTerm (Execution.run fuel cursor))) := by
  induction fuel generalizing cursor with
  | zero => spatial_eval unfolding [Execution.run]
  | succ fuel ih =>
    spatial_eval [step_returns state cursor, ih (Execution.step cursor)] unfolding [Execution.run]

theorem answer_returns (state : Effects.State) (cursor : Execution.State) :
    PureReturns library.runtime [] state
      (apply "native:spatial:answer" [encoded (stateTerm cursor)]) state
      (encoded (answerTerm (Execution.answer cursor))) := by
  cases cursor with
  | eval formula bag next => spatial_eval unfolding [stateTerm, Execution.answer, answerTerm]
  | choose left right remaining next => spatial_eval unfolding [stateTerm, Execution.answer, answerTerm]
  | ret value next =>
    cases value <;> cases next <;>
      spatial_eval unfolding [stateTerm, continuationTerm, boolTerm, Execution.answer, answerTerm]

theorem admitted_returns (state : Effects.State) (formula : Expression) :
    PureReturns library.runtime [] state
      (apply "native:spatial:admitted" [encoded (formulaTerm formula)]) state
      (encoded (boolTerm (Execution.admitted formula))) := by
  induction formula with
  | atom leaf | top | bottom | possibility _ | outgoingUniversal _ =>
    spatial_eval unfolding [formulaTerm, boolTerm, Execution.admitted]
  | neg inner ih => spatial_eval [ih] unfolding [formulaTerm, Execution.admitted]
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight | imp left right ihLeft ihRight =>
    spatial_eval [ihLeft, ihRight, binary_returns state .conj (Execution.admitted left) (Execution.admitted right)]
      unfolding [formulaTerm, Execution.admitted, Binary.apply, binaryTerm]
  | separating index left right ihLeft ihRight =>
    cases index with
    | zero =>
      spatial_eval [ihLeft, ihRight, binary_returns state .conj (Execution.admitted left) (Execution.admitted right)]
        unfolding [formulaTerm, Execution.admitted, Binary.apply, binaryTerm]
    | succ index => spatial_eval unfolding [formulaTerm, boolTerm, Execution.admitted]

theorem start_returns (state : Effects.State) (formula : Expression) (bag : Bag)
    (accepted : Execution.admitted formula = true) (fuel : Nat) :
    PureReturns library.runtime [] state
      (apply "native:spatial:start" [encoded (formulaTerm formula), encoded (bagTerm bag), number fuel]) state
      (encoded (sessionTerm ((Execution.Session.begin formula bag accepted).resume fuel))) := by
  have admit := admitted_returns state formula
  rw [accepted] at admit
  spatial_eval [admit, run_returns state fuel (Execution.begin formula bag)]
    unfolding [boolTerm, sessionTerm, Execution.Session.begin, Execution.Session.resume,
      Execution.begin, stateTerm, continuationTerm]

theorem start_unsupported (state : Effects.State) (formula : Expression) (bag : Bag)
    (unsupported : Execution.admitted formula = false) (fuel : Nat) :
    PureReturns library.runtime [] state
      (apply "native:spatial:start" [encoded (formulaTerm formula), encoded (bagTerm bag), number fuel]) state
      (encoded (unsupportedTerm formula bag)) := by
  have admit := admitted_returns state formula
  rw [unsupported] at admit
  spatial_eval [admit] unfolding [boolTerm, unsupportedTerm]

theorem resume_returns (state : Effects.State) (session : Execution.Session) (fuel : Nat) :
    PureReturns library.runtime [] state
      (apply "native:spatial:resume" [number fuel, encoded (sessionTerm session)]) state
      (encoded (sessionTerm (session.resume fuel))) := by
  have admit := admitted_returns state session.formula
  rw [session.accepted] at admit
  spatial_eval [admit, run_returns state fuel session.cursor]
    unfolding [sessionTerm, Execution.Session.resume, boolTerm]

theorem read_returns (state : Effects.State) (session : Execution.Session) :
    PureReturns library.runtime [] state
      (apply "native:spatial:read" [encoded (sessionTerm session)]) state
      (encoded (answerTerm (Execution.answer session.cursor))) := by
  have admit := admitted_returns state session.formula
  rw [session.accepted] at admit
  spatial_eval [admit, answer_returns state session.cursor] unfolding [sessionTerm, boolTerm]

private theorem answerTerm_injective : Function.Injective answerTerm := by
  intro first second same
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some value => cases value <;> simp [answerTerm] at same
  | some first =>
    cases second with
    | none => cases first <;> simp [answerTerm] at same
    | some second => cases first <;> cases second <;> simp_all [answerTerm]

/-- A completed evaluator run, as opposed to an untrusted supplied verdict. -/
def ReadCompletes (before : Effects.State) (session : Execution.Session) (result : Option Bool) : Prop :=
  ∃ fuel, Eval.run library.runtime fuel
    {state := before, control := .evaluate [] (apply "native:spatial:read" [encoded (sessionTerm session)])} =
      .complete before [encoded (answerTerm result)] [] []

theorem read_completes_iff (before : Effects.State) (session : Execution.Session) (result : Option Bool) :
    ReadCompletes before session result ↔ Execution.answer session.cursor = result := by
  have exactResult := Eval.pure_returns_completed_iff library.runtime [] before before
    (apply "native:spatial:read" [encoded (sessionTerm session)])
    (encoded (answerTerm (Execution.answer session.cursor))) (read_returns before session)
    before [encoded (answerTerm result)] [] []
  constructor
  · intro completed
    have same := (List.cons.inj ((exactResult.mp completed).2.1)).1
    exact (answerTerm_injective (CettaWireAtom.encode_injective _ _ same)).symm
  · intro same
    apply exactResult.mpr
    exact ⟨rfl, by rw [same], rfl, rfl⟩

theorem completed_positive (before : Effects.State) (session : Execution.Session)
    (completed : ReadCompletes before session (some true)) : BagModel.holds session.formula session.bag :=
  session.proved ((read_completes_iff before session _).mp completed)

theorem completed_negative (before : Effects.State) (session : Execution.Session)
    (completed : ReadCompletes before session (some false)) : ¬ BagModel.holds session.formula session.bag :=
  session.refuted ((read_completes_iff before session _).mp completed)

/-- Actual target-side native checking is complete for every admitted formula
of this finite bag strategy; target instruction fuel and strategy fuel differ. -/
theorem eventually_positive_iff (before : Effects.State) (session : Execution.Session) :
    (∃ work, ReadCompletes before (session.resume work) (some true)) ↔
      BagModel.holds session.formula session.bag := by
  constructor
  · rintro ⟨work, completed⟩
    exact completed_positive before (session.resume work) completed
  · intro holds
    obtain ⟨work, complete⟩ := session.eventually_decided
    have positive := (Execution.evaluate_exact session.formula session.bag session.accepted).mpr holds
    refine ⟨work, (read_completes_iff before (session.resume work) _).mpr ?_⟩
    simpa only [positive] using complete

theorem eventually_negative_iff (before : Effects.State) (session : Execution.Session) :
    (∃ work, ReadCompletes before (session.resume work) (some false)) ↔
      ¬ BagModel.holds session.formula session.bag := by
  constructor
  · rintro ⟨work, completed⟩
    exact completed_negative before (session.resume work) completed
  · intro notHolds
    obtain ⟨work, complete⟩ := session.eventually_decided
    have negative : Execution.evaluate session.formula session.bag = false := by
      cases found : Execution.evaluate session.formula session.bag with
      | false => rfl
      | true => exact False.elim (notHolds
          ((Execution.evaluate_exact session.formula session.bag session.accepted).mp found))
    refine ⟨work, (read_completes_iff before (session.resume work) _).mpr ?_⟩
    simpa only [negative] using complete

/-- A session reached from its admitted originating request resumes to exactly
its next cursor, without search replay or any change to store and I/O. -/
theorem resume_completed_iff (before : Effects.State) (session : Execution.Session) (work : Nat)
    (after : Effects.State) (answers input output : List Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    (∃ fuel, Eval.run library.runtime fuel
      {state := before, control := .evaluate []
        (apply "native:spatial:resume" [number work, encoded (sessionTerm session)])} =
        .complete after answers input output) ↔
      after = before ∧ answers = [encoded (sessionTerm (session.resume work))] ∧ input = [] ∧ output = [] :=
  Eval.pure_returns_completed_iff library.runtime [] before before _ _
    (resume_returns before session work) after answers input output

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialRuntime
