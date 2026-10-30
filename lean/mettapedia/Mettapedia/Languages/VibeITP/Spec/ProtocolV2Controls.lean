import Mettapedia.Languages.VibeITP.Spec.ProtocolV2

/-!
Complete certificate controls for the versioned protocol. The source theorem
comes from an admitted definition with two free parameters; no axiom instruction
is used. The same encoded files are exported for independent native replay.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Spec.ProtocolV2.Controls

/-- Define `D(F,G) = (F = G)` and challenge its selected instance. The last
stored term is an open variable used only by a refusal control. -/
def setup (left right : Nat) : List Instruction :=
  ([.fvarNew 0 13, .fvarNew 0 14,
    .termNewApp 13 [] 1, .termNewApp 14 [] 2,
    .termNewApp 3 [1, 2] 3,
    .defineConst [13, 14] [0, 1] 3 15 1,
    .termNewLiteral [7] 4,
    .termNewApp 15 [left, right] 5,
    .termNewApp 3 [left, right] 6,
    .termNewApp 3 [5, 6] 7,
    .challengeAdd 7 0, .termNewBVar 0 8] : List Instr).map .legacy

def proof (assignments : List (Nat × Nat)) : List Instruction :=
  [.instantiateMany 1 assignments 2, .legacy (.challengeSatisfy 0 2)]

structure Case where
  name : String
  setupFiles : List (List UInt8)
  proofFiles : List (List UInt8)
  expected : Verdict

def complete (name : String) (left right : Nat) (assignments : List (Nat × Nat)) : Case :=
  ⟨name, [encodeFile (setup left right)], [encodeFile (proof assignments)], .proofs 1 0 0⟩

def caseTable : List Case := [
  complete "crossing" 2 4 [(13, 2), (14, 4)],
  complete "swap" 2 1 [(13, 2), (14, 1)],
  complete "duplicate-first" 2 2 [(13, 2), (13, 4)],
  complete "zero-copy" 1 2 [],
  ⟨"singleton", [encodeFile (setup 2 2)], [encodeFile (proof [(13, 2)])], .proofs 1 0 0⟩,
  ⟨"legacy-singleton", [encodeFile (setup 2 2)],
    [encodeFile [.legacy (.thmInstantiate 1 13 2 2), .legacy (.challengeSatisfy 0 2)]], .proofs 1 0 0⟩,
  ⟨"legacy-noncanonical", [encodeFile (setup 2 2)],
    [[16, 249, 1, 0, 13, 2, 2, 14, 0, 2]], .proofs 1 0 0⟩,
  ⟨"invalid-shadow", [encodeFile (setup 2 2)], [encodeFile (proof [(13, 2), (13, 8)])],
    .rejected 1 0 .theoremFailed⟩,
  ⟨"constant-target", [encodeFile (setup 2 2)], [encodeFile (proof [(15, 2)])],
    .rejected 1 0 .theoremFailed⟩,
  ⟨"missing-theorem", [encodeFile (setup 2 2)],
    [encodeFile [.instantiateMany 99 [(999, 999)] 2]], .rejected 1 0 (.missing .theorem)⟩,
  ⟨"missing-symbol", [encodeFile (setup 2 2)], [encodeFile (proof [(999, 999)])],
    .rejected 1 0 (.missing .symbol)⟩,
  ⟨"missing-value-before-kind", [encodeFile (setup 2 2)], [encodeFile (proof [(0, 99)])],
    .rejected 1 0 (.missing .term)⟩,
  ⟨"occupied-destination", [encodeFile (setup 2 2)],
    [encodeFile [.instantiateMany 1 [(13, 2)] 1]], .rejected 1 0 (.occupied .theorem)⟩,
  ⟨"invalid-before-occupied", [encodeFile (setup 2 2)],
    [encodeFile [.instantiateMany 1 [(15, 2)] 1]], .rejected 1 0 .theoremFailed⟩,
  ⟨"wrong-conclusion", [encodeFile (setup 4 4)], [encodeFile (proof [(13, 2), (14, 4)])],
    .rejected 1 1 .challengeMismatch⟩,
  ⟨"incomplete", [encodeFile (setup 2 4)], [encodeFile [.instantiateMany 1 [(13, 2), (14, 4)] 2]],
    .proofs 1 0 1⟩,
  ⟨"wrong-phase", [encodeFile (setup 2 4 ++ [.instantiateMany 1 [(13, 2), (14, 4)] 2])], [],
    .rejected 0 12 (.inferenceInSetup .instantiate)⟩,
  ⟨"truncated", [encodeFile (setup 2 4)], [[26, 2, 1, 13, 14, 2]],
    .malformed 1 .truncatedInteger⟩,
  ⟨"malformed-priority", [encodeFile (setup 2 4 ++ [.instantiateMany 1 [] 2])], [[27]],
    .malformed 1 (.unknownOpcode 27)⟩]

def verdicts : List (String × Bool) := caseTable.map fun entry =>
  (entry.name, decide (checkRun entry.setupFiles entry.proofFiles = entry.expected))

theorem verdicts_all : verdicts.all Prod.snd = true := by decide +kernel

theorem crossing_wire : encode (.instantiateMany 1 [(13, 2), (14, 4)] 2) =
    [26, 2, 1, 13, 14, 2, 4, 2] := by decide +kernel

theorem crossing_roundtrip :
    decodeFile (encodeFile (proof [(13, 2), (14, 4)])) =
      .ok (proof [(13, 2), (14, 4)]) :=
  decodeFile_encodeFile _ (by decide +kernel)

theorem framed_crossing :
    decodeOne (encode (.instantiateMany 1 [(13, 2), (14, 4)] 2) ++ [18, 3, 3]) =
      .ok (.instantiateMany 1 [(13, 2), (14, 4)] 2, [18, 3, 3]) :=
  decodeOne_encode _ _ (by decide +kernel)

def preparedState : Option State :=
  match runInstrs initialState 0 (setup 2 4) with
  | .ok state => some state
  | _ => none

theorem preparedState_exists : preparedState.isSome = true := by decide +kernel

def beforeCrossing : State := enterProofs (preparedState.get preparedState_exists)

def crossingResult : Term :=
  .eq (.app (.fresh 2) [.app (.fresh 1) [], .natLit 7])
    (.eq (.app (.fresh 1) []) (.natLit 7))

def crossingOutput : Option State :=
  (executeMany beforeCrossing 1 [(13, 2), (14, 4)] 2).toOption

theorem crossing_publishes :
    crossingOutput.bind (fun state => state.theorems 2) = some crossingResult := by decide +kernel

theorem crossingOutput_exists : crossingOutput.isSome = true := by decide +kernel

def afterCrossing : State := crossingOutput.get crossingOutput_exists

theorem crossing_accepted :
    executeMany beforeCrossing 1 [(13, 2), (14, 4)] 2 = .ok afterCrossing := by
  have output := Option.eq_some_of_isSome crossingOutput_exists
  change (executeMany beforeCrossing 1 [(13, 2), (14, 4)] 2).toOption = some afterCrossing at output
  cases executed : executeMany beforeCrossing 1 [(13, 2), (14, 4)] 2 with
  | error error => simp [executed, Except.toOption] at output
  | ok state =>
      simp only [executed, Except.toOption, Option.some.injEq] at output
      exact congrArg Except.ok output

theorem crossing_frame :
    ∃ result, beforeCrossing.theorems 2 = none ∧
      afterCrossing = { beforeCrossing with theorems := setSlot beforeCrossing.theorems 2 (some result) } :=
  executeMany_updates_only_theorem 1 2 [(13, 2), (14, 4)] crossing_accepted

theorem crossing_changes_only_destination :
    ∃ after, executeMany beforeCrossing 1 [(13, 2), (14, 4)] 2 = .ok after ∧
      after.theorems 2 = some crossingResult ∧
      ∃ result, beforeCrossing.theorems 2 = none ∧
        after = { beforeCrossing with theorems := setSlot beforeCrossing.theorems 2 (some result) } := by
  have published := crossing_publishes
  unfold crossingOutput at published
  cases executed : executeMany beforeCrossing 1 [(13, 2), (14, 4)] 2 with
  | error error => simp [executed, Except.toOption] at published
  | ok after =>
      simp only [executed, Except.toOption, Option.bind_some] at published
      exact ⟨after, rfl, published, executeMany_updates_only_theorem 1 2 _ executed⟩

theorem singleton_execution_agrees :
    execute beforeCrossing (.instantiateMany 1 [(13, 2)] 2) =
      Spec.execute beforeCrossing (.thmInstantiate 1 13 2 2) :=
  execute_singleton beforeCrossing 1 13 2 2

theorem legacy_execution_agrees :
    runInstrs beforeCrossing 0 [.legacy (.thmInstantiate 1 13 2 2)] =
      Spec.runInstrs beforeCrossing 0 [.thmInstantiate 1 13 2 2] :=
  runInstrs_legacy [.thmInstantiate 1 13 2 2] beforeCrossing 0

theorem legacy_noncanonical_preserved :
    decodeFile [16, 249, 1, 0, 13, 2, 2] = .ok [.legacy (.thmInstantiate 1 13 2 2)] :=
  decodeFile_legacy (bytes := [16, 249, 1, 0, 13, 2, 2])
    (instructions := [.thmInstantiate 1 13 2 2]) (by decide +kernel)

theorem legacy_decoder_refuses_new_opcode :
    Spec.decodeFile (encode (.instantiateMany 1 [(13, 2), (14, 4)] 2)) =
      .error (.unknownOpcode 26) := by decide +kernel

theorem completed_without_satisfaction_is_not_success :
    (checkRun [encodeFile (setup 2 4)]
      [encodeFile [.instantiateMany 1 [(13, 2), (14, 4)] 2]]).success = false := by decide +kernel

#print axioms verdicts_all
#print axioms crossing_wire
#print axioms completed_without_satisfaction_is_not_success

end Mettapedia.Languages.VibeITP.Spec.ProtocolV2.Controls
