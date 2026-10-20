import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendSource

/-! # Execution of the composed append and observation library -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Execution
open MeTTaIL WireKit BridgeKit Eval

syntax "append_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| append_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call library_checked
       try simp only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
         Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil.applySubstList_nil]
       metta_eval [$facts,*] with library_checked
         unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil.applySubstList_nil, $extra,*]))

theorem append_returns (state : Effects.State) (left right : List Atom) :
    PureReturns library.runtime [] state
      (IndexedInductiveAppend.appendCall (.expression left) (.expression right)) state
      (.expression (left ++ right)) := by
  exact transport_call append_closed append_agreement (by decide +kernel) (by decide)
    (by decide +kernel) (by decide) ["left", "right"] (by decide) rfl
    (by decide +kernel) (IndexedInductiveAppend.append_returns state left right)

theorem length_returns (state : Effects.State) (values : List Atom) :
    PureReturns library.runtime [] state
      (apply "gslt:inductive:length" [.expression values]) state (number values.length) := by
  exact transport_call append_closed append_agreement (by decide +kernel) (by decide)
    (by decide +kernel) (by decide) ["values"] (by decide) rfl
    (by decide +kernel) (IndexedInductiveAppend.length_returns state values)

theorem start_returns (state : Effects.State) (formula : Execution.Expression) (bag : Bag)
    (accepted : Execution.admitted formula = true) (fuel : Nat) :
    PureReturns library.runtime [] state
      (apply "native:spatial:start" [encoded (SpatialRuntime.formulaTerm formula),
        encoded (SpatialRuntime.bagTerm bag), number fuel]) state
      (encoded (SpatialRuntime.sessionTerm ((Execution.Session.begin formula bag accepted).resume fuel))) := by
  exact transport_call spatial_closed spatial_agreement (by decide +kernel) (by decide)
    (by decide +kernel) (by decide) ["formula", "bag", "fuel"] (by decide) rfl
    (by decide +kernel) (SpatialRuntime.start_returns state formula bag accepted fuel)

theorem spatial_resume_returns (state : Effects.State) (session : Execution.Session) (fuel : Nat) :
    PureReturns library.runtime [] state
      (apply "native:spatial:resume" [number fuel, encoded (SpatialRuntime.sessionTerm session)]) state
      (encoded (SpatialRuntime.sessionTerm (session.resume fuel))) := by
  exact transport_call spatial_closed spatial_agreement (by decide +kernel) (by decide)
    (by decide +kernel) (by decide) ["fuel", "session"] (by decide) rfl
    (by decide +kernel) (SpatialRuntime.resume_returns state session fuel)

theorem spatial_read_returns (state : Effects.State) (session : Execution.Session) :
    PureReturns library.runtime [] state
      (apply "native:spatial:read" [encoded (SpatialRuntime.sessionTerm session)]) state
      (encoded (SpatialRuntime.answerTerm (Execution.answer session.cursor))) := by
  exact transport_call spatial_closed spatial_agreement (by decide +kernel) (by decide)
    (by decide +kernel) (by decide) ["session"] (by decide) rfl
    (by decide +kernel) (SpatialRuntime.read_returns state session)

theorem markers_returns (state : Effects.State) (count : Nat) :
    PureReturns library.runtime [] state (apply "native:append:markers" [number count]) state
      (encoded (SpatialRuntime.bagTerm (List.replicate count IndexedAppend.marker))) := by
  induction count with
  | zero => append_eval unfolding [SpatialRuntime.bagTerm, encodeList]
  | succ count ih =>
    append_eval [ih] unfolding [SpatialRuntime.bagTerm, encodeList, IndexedAppend.marker,
      InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns, List.replicate_succ]

/-- Each captured array occurrence contributes exactly one marker. This
agrees with the original occurrence map even when payloads are repeated. -/
theorem observe_returns (state : Effects.State) (values : List Atom) :
    PureReturns library.runtime [] state (apply "native:append:observe" [.expression values]) state
      (encoded (SpatialRuntime.bagTerm (IndexedAppend.observe values))) := by
  have markers := markers_returns state values.length
  have same : IndexedAppend.observe values = List.replicate values.length IndexedAppend.marker := by
    simp [IndexedAppend.observe]
  rw [same]
  append_eval [length_returns state values, markers]

theorem begin_returns (state : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) :
    PureReturns library.runtime [] state
      (apply "native:append:begin" [encoded (SpatialRuntime.formulaTerm formula),
        .expression left, .expression right]) state
      (packet (left ++ right) (Execution.Session.begin formula (IndexedAppend.observe (left ++ right)) accepted)) := by
  append_eval [append_returns state left right, observe_returns state (left ++ right),
    start_returns state formula (IndexedAppend.observe (left ++ right)) accepted 0]
    unfolding [packet, Execution.Session.resume, Execution.Session.begin, Execution.run]

theorem resume_returns (state : Effects.State) (values : List Atom) (session : Execution.Session)
    (work : Nat) :
    PureReturns library.runtime [] state
      (apply "native:append:resume" [number work, packet values session]) state
      (packet values (session.resume work)) := by
  append_eval [spatial_resume_returns state session work]
    unfolding [packet, Execution.Session.resume]

theorem read_returns (state : Effects.State) (values : List Atom) (session : Execution.Session) :
    PureReturns library.runtime [] state (apply "native:append:read" [packet values session]) state
      (observation values session) := by
  append_eval [spatial_read_returns state session] unfolding [packet, observation]

/-- Work is resumed inside the emitted program. Its sum measures checker
steps, independently of evaluator fuel or host instruction costs. -/
theorem rounds_returns (state : Effects.State) (values : List Atom)
    (session : Execution.Session) (rounds : List Nat) :
    PureReturns library.runtime [] state
      (apply "native:append:rounds" [encoded (encodeList Term.natural rounds), packet values session]) state
      (packet values (session.resume rounds.sum)) := by
  induction rounds generalizing session with
  | nil => append_eval unfolding [encodeList, packet, Execution.Session.resume, Execution.run]
  | cons work rest ih =>
    have resumed := resume_returns state values session work
    have continued := ih (session.resume work)
    rw [Execution.Session.resume_add] at continued
    append_eval [resumed, continued] unfolding [encodeList, List.sum_cons, packet]

def checkCall (formula : Execution.Expression) (left right : List Atom) (rounds : List Nat) : Atom :=
  apply "native:append:check" [encoded (SpatialRuntime.formulaTerm formula),
    .expression left, .expression right, encoded (encodeList Term.natural rounds)]

def result (formula : Execution.Expression) (accepted : Execution.admitted formula = true)
    (left right : List Atom) (rounds : List Nat) : Execution.Session :=
  (Execution.Session.begin formula (IndexedAppend.observe (left ++ right)) accepted).resume rounds.sum

theorem check_returns (state : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) (rounds : List Nat) :
    PureReturns library.runtime [] state (checkCall formula left right rounds) state
      (observation (left ++ right) (result formula accepted left right rounds)) := by
  unfold checkCall
  append_eval [begin_returns state formula accepted left right,
    rounds_returns state (left ++ right)
      (Execution.Session.begin formula (IndexedAppend.observe (left ++ right)) accepted) rounds,
    read_returns state (left ++ right) (result formula accepted left right rounds)]
    unfolding [result]

/-- Every completed packet retains the full ordered append, occurrence bag,
resumption cursor and verdict, with no additional answers or store effects. -/
theorem check_completed_iff (before after : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) (rounds : List Nat)
    (answers input output : List Atom) :
    (∃ fuel, Eval.run library.runtime fuel
      { state := before, control := .evaluate [] (checkCall formula left right rounds) } =
        .complete after answers input output) ↔
      after = before ∧ answers = [observation (left ++ right) (result formula accepted left right rounds)] ∧
        input = [] ∧ output = [] :=
  Eval.pure_returns_completed_iff library.runtime [] before before _ _
    (check_returns before formula accepted left right rounds) after answers input output

theorem result_rounds (formula : Execution.Expression) (accepted : Execution.admitted formula = true)
    (left right : List Atom) (first more : List Nat) :
    result formula accepted left right (first ++ more) =
      (result formula accepted left right first).resume more.sum := by
  simp only [result, List.sum_append, Execution.Session.resume_add]

theorem no_work_unknown (formula : Execution.Expression) (accepted : Execution.admitted formula = true)
    (left right : List Atom) : Execution.answer (result formula accepted left right []).cursor = none := rfl

/-- A proposed verdict is compared with the whole executed packet, including
its array, bag and cursor. Merely submitting this wire data proves nothing. -/
def verdictPacket (values : List Atom) (session : Execution.Session) (verdict : Option Bool) : Atom :=
  apply "NativeAppendObservation" [.expression values, encoded (SpatialRuntime.bagTerm session.bag),
    encoded (SpatialRuntime.sessionTerm session), encoded (SpatialRuntime.answerTerm verdict)]

private theorem verdictPacket_eq_iff (values : List Atom) (session : Execution.Session)
    (verdict : Option Bool) :
    verdictPacket values session verdict = observation values session ↔
      verdict = Execution.answer session.cursor := by
  rcases verdict with _ | (_ | _) <;>
    rcases found : Execution.answer session.cursor with _ | (_ | _) <;>
    simp [verdictPacket, observation, apply, encoded, SpatialRuntime.answerTerm, found,
      CettaWireAtom.encode]

def VerdictCompletes (before : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) (rounds : List Nat)
    (verdict : Option Bool) : Prop :=
  ∃ fuel, Eval.run library.runtime fuel
    { state := before, control := .evaluate [] (checkCall formula left right rounds) } =
      .complete before [verdictPacket (left ++ right) (result formula accepted left right rounds) verdict] [] []

theorem verdict_completes_iff (before : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) (rounds : List Nat)
    (verdict : Option Bool) :
    VerdictCompletes before formula accepted left right rounds verdict ↔
      Execution.answer (result formula accepted left right rounds).cursor = verdict := by
  unfold VerdictCompletes
  rw [check_completed_iff before before formula accepted left right rounds]
  simp only [true_and, and_true, List.cons.injEq]
  exact (verdictPacket_eq_iff _ _ _).trans eq_comm

theorem positive (before : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) (rounds : List Nat)
    (completed : VerdictCompletes before formula accepted left right rounds (some true)) :
    BagModel.holds formula (IndexedAppend.observe (left ++ right)) :=
  (result formula accepted left right rounds).proved
    ((verdict_completes_iff before formula accepted left right rounds _).mp completed)

theorem negative (before : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) (rounds : List Nat)
    (completed : VerdictCompletes before formula accepted left right rounds (some false)) :
    ¬ BagModel.holds formula (IndexedAppend.observe (left ++ right)) :=
  (result formula accepted left right rounds).refuted
    ((verdict_completes_iff before formula accepted left right rounds _).mp completed)

theorem eventually_positive_iff (before : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) :
    (∃ rounds, VerdictCompletes before formula accepted left right rounds (some true)) ↔
      BagModel.holds formula (IndexedAppend.observe (left ++ right)) := by
  constructor
  · rintro ⟨rounds, completed⟩
    exact positive before formula accepted left right rounds completed
  · intro holds
    obtain ⟨work, complete⟩ := (Execution.Session.begin formula (IndexedAppend.observe (left ++ right)) accepted).eventually_decided
    have yes := (Execution.evaluate_exact formula (IndexedAppend.observe (left ++ right)) accepted).mpr holds
    refine ⟨[work], (verdict_completes_iff before formula accepted left right [work] _).mpr ?_⟩
    simpa only [result, List.sum_cons, List.sum_nil, Nat.add_zero, Execution.Session.begin, yes] using complete

theorem eventually_negative_iff (before : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) :
    (∃ rounds, VerdictCompletes before formula accepted left right rounds (some false)) ↔
      ¬ BagModel.holds formula (IndexedAppend.observe (left ++ right)) := by
  constructor
  · rintro ⟨rounds, completed⟩
    exact negative before formula accepted left right rounds completed
  · intro notHolds
    obtain ⟨work, complete⟩ := (Execution.Session.begin formula (IndexedAppend.observe (left ++ right)) accepted).eventually_decided
    have no : Execution.evaluate formula (IndexedAppend.observe (left ++ right)) = false := by
      cases found : Execution.evaluate formula (IndexedAppend.observe (left ++ right)) with
      | false => rfl
      | true => exact False.elim (notHolds ((Execution.evaluate_exact _ _ accepted).mp found))
    refine ⟨[work], (verdict_completes_iff before formula accepted left right [work] _).mpr ?_⟩
    simpa only [result, List.sum_cons, List.sum_nil, Nat.add_zero, Execution.Session.begin, no] using complete

theorem length_iff (before : Effects.State) (count : Nat) (left right : List Atom) :
    (∃ rounds, VerdictCompletes before (BagModel.sizeExactly count)
      (Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend.sizeExactly_admitted count)
      left right rounds (some true)) ↔ left.length + right.length = count := by
  rw [eventually_positive_iff, BagModel.sizeExactly_iff, IndexedAppend.observe_length, List.length_append]

theorem wrong_length_iff (before : Effects.State) (count : Nat) (left right : List Atom) :
    (∃ rounds, VerdictCompletes before (BagModel.sizeExactly count)
      (Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend.sizeExactly_admitted count)
      left right rounds (some false)) ↔ left.length + right.length ≠ count := by
  rw [eventually_negative_iff, BagModel.sizeExactly_iff, IndexedAppend.observe_length, List.length_append]

open IndexedInductive IndexedInductiveNatVec

/-- The completed native query states the length of the original polynomial
vectors, transported through their independently checked array realization. -/
theorem source_length_iff (before : Effects.State) (count : Nat) {n m : Natural.Carrier}
    (left : Vectors.Vector Atom n) (right : Vectors.Vector Atom m) :
    (∃ rounds, VerdictCompletes before (BagModel.sizeExactly count)
      (Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend.sizeExactly_admitted count)
      (VectorArray.encode left).val.toList (VectorArray.encode right).val.toList rounds (some true)) ↔
      Natural.toNat n + Natural.toNat m = count := by
  rw [length_iff, Array.length_toList, Array.length_toList,
    (VectorArray.encode left).property, (VectorArray.encode right).property]

theorem no_work_completes (before : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) :
    VerdictCompletes before formula accepted left right [] none :=
  (verdict_completes_iff before formula accepted left right [] none).mpr rfl

theorem no_work_not_decided (before : Effects.State) (formula : Execution.Expression)
    (accepted : Execution.admitted formula = true) (left right : List Atom) (verdict : Bool) :
    ¬ VerdictCompletes before formula accepted left right [] (some verdict) := by
  rw [verdict_completes_iff, no_work_unknown]
  simp

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecution
