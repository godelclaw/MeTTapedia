import Mettapedia.OSLF.MeTTaIL.GeneralRhoBinding

/-!
# Contextual COMM capture and readout for arbitrary source bodies

The family below ranges over raw object patterns in every ambient binder
context. A received input body remains the exact original syntax together
with its Name dependency. Matching records both physical parallel choices;
the residual retains all unmatched components in their actual order.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open GeneralScopedMatchMachine
open Mettapedia.GSLT.Examples.ScopedRhoBinding

def input (channel body : Pattern) : Pattern :=
  .apply "PInput" [channel, .lambda none body]

def output (channel payload : Pattern) : Pattern :=
  .apply "POutput" [channel, payload]

def source (channel body payload : Pattern) (rest : List Pattern) : Pattern :=
  .collection .hashBag (input channel body :: output channel payload :: rest) none

def captured (ambient : Nat) (channel body payload : Pattern) (rest : List Pattern) :
    ScopedRuleMatching.Assignment :=
  [("rest", rootValue ambient (.collection .hashBag rest none)),
    ("q", rootValue ambient payload), ("p", bodyValue ambient body),
    ("n", rootValue ambient channel)]

def commTrace : List BagChoice :=
  [{ path := [0], selected := 0 }, { path := [1], selected := 0 }]

def request (ambient : Nat) (channel body payload : Pattern) (rest : List Pattern) : Request where
  rule := comm
  spec := scopedCommBindingSpec
  ambient := ambient
  site := .left
  path := []
  depth := 0
  initial := []
  schema := comm.left
  target := source channel body payload rest

private theorem dependencies_n : dependencies? scopedCommBindingSpec "n" = some [] := by decide +kernel
private theorem dependencies_p : dependencies? scopedCommBindingSpec "p" = some [.base "Name"] := by decide +kernel
private theorem dependencies_q : dependencies? scopedCommBindingSpec "q" = some [] := by decide +kernel
private theorem dependencies_rest : dependencies? scopedCommBindingSpec "rest" = some [] := by decide +kernel

private theorem input_n_arguments : arguments? comm scopedCommBindingSpec "n" .left [0, 0] = some [] := by decide +kernel
private theorem input_p_arguments : arguments? comm scopedCommBindingSpec "p" .left [0, 1, 0] = some [.bvar 0] := by decide +kernel
private theorem output_n_arguments : arguments? comm scopedCommBindingSpec "n" .left [1, 0] = some [] := by decide +kernel
private theorem output_q_arguments : arguments? comm scopedCommBindingSpec "q" .left [1, 1] = some [] := by decide +kernel
private theorem source_rest_arguments : arguments? comm scopedCommBindingSpec "rest" .left [2] = some [] := by decide +kernel
private theorem target_p_arguments : arguments? comm scopedCommBindingSpec "p" .right [0, 0] = some [.bvar 0] := by decide +kernel
private theorem target_q_arguments : arguments? comm scopedCommBindingSpec "q" .right [0, 1, 0] = some [] := by decide +kernel
private theorem target_rest_arguments : arguments? comm scopedCommBindingSpec "rest" .right [1] = some [] := by decide +kernel

private theorem input_n_capture {ambient : Nat} {channel : Pattern}
    (safe : channel.isWellScopedAt ambient = true) :
    capture? comm scopedCommBindingSpec ambient 0 .left [0, 0] [] "n" channel =
      some [("n", rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_n, input_n_arguments, Option.bind_some, recover_root safe]
  rfl

private theorem input_p_capture {ambient : Nat} {channel body : Pattern}
    (safe : body.isWellScopedAt (ambient + 1) = true) :
    capture? comm scopedCommBindingSpec ambient 1 .left [0, 1, 0]
      [("n", rootValue ambient channel)] "p" body =
      some [("p", bodyValue ambient body), ("n", rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_p, input_p_arguments, Option.bind_some, recover_body safe]
  rfl

private theorem output_n_capture {ambient : Nat} {channel body : Pattern}
    (safe : channel.isWellScopedAt ambient = true) :
    capture? comm scopedCommBindingSpec ambient 0 .left [1, 0]
      [("p", bodyValue ambient body), ("n", rootValue ambient channel)] "n" channel =
      some [("p", bodyValue ambient body), ("n", rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_n, output_n_arguments, Option.bind_some, recover_root safe]
  simp [assign, lookup]

private theorem output_q_capture {ambient : Nat} {channel body payload : Pattern}
    (safe : payload.isWellScopedAt ambient = true) :
    capture? comm scopedCommBindingSpec ambient 0 .left [1, 1]
      [("p", bodyValue ambient body), ("n", rootValue ambient channel)] "q" payload =
      some [("q", rootValue ambient payload), ("p", bodyValue ambient body),
        ("n", rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_q, output_q_arguments, Option.bind_some, recover_root safe]
  rfl

private theorem rest_capture {ambient : Nat} {channel body payload : Pattern} {rest : List Pattern}
    (safe : Pattern.isWellScopedListAt ambient rest = true) :
    captureRest? comm scopedCommBindingSpec ambient 0 .left [2]
      [("q", rootValue ambient payload), ("p", bodyValue ambient body),
        ("n", rootValue ambient channel)] "rest" .hashBag rest =
      some (captured ambient channel body payload rest) := by
  have restSafe : (Pattern.collection .hashBag rest none).isWellScopedAt ambient = true := safe
  simp only [Option.bind_eq_bind, captureRest?, capture?, dependencies_rest, source_rest_arguments,
    Option.bind_some, recover_root restSafe]
  rfl

private theorem input_matching {ambient : Nat} {channel body : Pattern}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (bodySafe : body.isWellScopedAt (ambient + 1) = true) :
    TracedMatches comm scopedCommBindingSpec ambient .left [0] 0 []
      (.apply "PInput" [.fvar "n", .lambda none (.fvar "p")]) (input channel body) []
      [("p", bodyValue ambient body), ("n", rootValue ambient channel)] :=
  .constructor (.cons (.capture (input_n_capture channelSafe))
    (.cons (.binder (.capture (input_p_capture bodySafe))) .nil))

private theorem output_matching {ambient : Nat} {channel body payload : Pattern}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (payloadSafe : payload.isWellScopedAt ambient = true) :
    TracedMatches comm scopedCommBindingSpec ambient .left [1] 0
      [("p", bodyValue ambient body), ("n", rootValue ambient channel)]
      (.apply "POutput" [.fvar "n", .fvar "q"]) (output channel payload) []
      [("q", rootValue ambient payload), ("p", bodyValue ambient body),
        ("n", rootValue ambient channel)] :=
  .constructor (.cons (.capture (output_n_capture channelSafe))
    (.cons (.capture (output_q_capture payloadSafe)) .nil))

/-- The actual original LHS captures any scoped body, including arbitrary
nested constructors and binders, without rebuilding or decoding the body. -/
theorem source_matching {ambient : Nat} {channel body payload : Pattern} {rest : List Pattern}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true)
    (restSafe : Pattern.isWellScopedListAt ambient rest = true) :
    TracedMatches comm scopedCommBindingSpec ambient .left [] 0 [] comm.left
      (source channel body payload rest) commTrace (captured ambient channel body payload rest) := by
  apply TracedMatches.bag (by decide)
  apply TracedBag.cons (headTrace := []) (tailTrace := [{ path := [1], selected := 0 }]) 0 (by simp)
  · exact input_matching channelSafe bodySafe
  · apply TracedBag.cons (headTrace := []) (tailTrace := []) 0 (by simp)
    · exact output_matching channelSafe payloadSafe
    · exact .rest (rest_capture restSafe)

theorem capture_readout (ambient : Nat) (channel body payload : Pattern) (rest : List Pattern) :
    lookup (captured ambient channel body payload rest) "p" = some (bodyValue ambient body) ∧
    lookup (captured ambient channel body payload rest) "n" = some (rootValue ambient channel) ∧
    lookup (captured ambient channel body payload rest) "rest" =
      some (rootValue ambient (.collection .hashBag rest none)) := by
  exact ⟨rfl, rfl, rfl⟩

/-- This readout also isolates ordinary binder elimination as a distinct
operation; the RHS schema and its contextual captures remain identical. -/
theorem reduct_readout (operation : Pattern → Pattern → Pattern)
    {ambient : Nat} {channel body payload : Pattern} {rest : List Pattern}
    (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true)
    (restSafe : Pattern.isWellScopedListAt ambient rest = true) :
    reductWith? operation comm scopedCommBindingSpec ambient
      (captured ambient channel body payload rest) =
      some (.collection .hashBag (operation (.apply "NQuote" [payload]) body :: rest) none) := by
  have restScoped : (Pattern.collection .hashBag rest none).isWellScopedAt ambient = true := restSafe
  have bodyFound : lookup (captured ambient channel body payload rest) "p" = some (bodyValue ambient body) := rfl
  have payloadFound : lookup (captured ambient channel body payload rest) "q" = some (rootValue ambient payload) := rfl
  have restFound : lookup (captured ambient channel body payload rest) "rest" =
      some (rootValue ambient (.collection .hashBag rest none)) := rfl
  unfold reductWith?
  change instantiateWith? operation comm scopedCommBindingSpec ambient .right [] 0
    (captured ambient channel body payload rest)
    (.collection .hashBag [.subst (.fvar "p") (.apply "NQuote" [.fvar "q"])] (some "rest")) = _
  simp only [instantiateWith?, instantiateArgsWith?, Option.bind_eq_bind,
    List.nil_append, List.cons_append, bodyFound, payloadFound, restFound,
    target_p_arguments, target_q_arguments, target_rest_arguments,
    instantiate_body bodySafe, instantiate_root payloadSafe, instantiate_root restScoped,
    Option.bind_some, Nat.zero_add, List.length_singleton]
  rfl

/-- Every source-family occurrence is eventually emitted by the actual
interruptible matcher, with its original contextual assignment and origins. -/
theorem matching_eventually {ambient : Nat} {channel body payload : Pattern} {rest : List Pattern}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true)
    (restSafe : Pattern.isWellScopedListAt ambient rest = true) :
    ∃ fuel, complete (run (request ambient channel body payload rest) fuel
        (start (request ambient channel body payload rest))) = true ∧
      { assignment := captured ambient channel body payload rest, trace := commTrace } ∈
        (run (request ambient channel body payload rest) fuel
          (start (request ambient channel body payload rest))).answers := by
  obtain ⟨fuel, finished, exactAnswers⟩ := completedEventually (request ambient channel body payload rest)
  exact ⟨fuel, finished, (exactAnswers _).mpr (source_matching channelSafe bodySafe payloadSafe restSafe)⟩

/-- Equal input terms at distinct collection positions induce distinct
physical match origins even though the retained capture and reduct agree. -/
theorem duplicate_input_origins {ambient : Nat} {channel body payload : Pattern}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true) :
    let actualSource := Pattern.collection .hashBag
      [input channel body, input channel body, output channel payload] none
    let actualCapture := captured ambient channel body payload [input channel body]
    let firstTrace : List BagChoice := [{ path := [0], selected := 0 }, { path := [1], selected := 1 }]
    let secondTrace : List BagChoice := [{ path := [0], selected := 1 }, { path := [1], selected := 1 }]
    TracedMatches comm scopedCommBindingSpec ambient .left [] 0 [] comm.left
      actualSource firstTrace actualCapture ∧
    TracedMatches comm scopedCommBindingSpec ambient .left [] 0 [] comm.left
      actualSource secondTrace actualCapture ∧ firstTrace ≠ secondTrace := by
  have residualSafe : Pattern.isWellScopedListAt ambient [input channel body] = true := by
    simp [input, Pattern.isWellScopedListAt, Pattern.isWellScopedAt, channelSafe, bodySafe]
  refine ⟨?_, ?_, by decide⟩
  · apply TracedMatches.bag (by decide)
    apply TracedBag.cons (headTrace := []) (tailTrace := [{ path := [1], selected := 1 }]) 0 (by simp)
    · exact input_matching channelSafe bodySafe
    · apply TracedBag.cons (headTrace := []) (tailTrace := []) 1 (by simp)
      · exact output_matching channelSafe payloadSafe
      · exact .rest (rest_capture residualSafe)
  · apply TracedMatches.bag (by decide)
    apply TracedBag.cons (headTrace := []) (tailTrace := [{ path := [1], selected := 1 }]) 1 (by simp)
    · exact input_matching channelSafe bodySafe
    · apply TracedBag.cons (headTrace := []) (tailTrace := []) 1 (by simp)
      · exact output_matching channelSafe payloadSafe
      · exact .rest (rest_capture residualSafe)

end Mettapedia.OSLF.MeTTaIL.GeneralRho
