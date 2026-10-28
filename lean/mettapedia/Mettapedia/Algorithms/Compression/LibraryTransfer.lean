import Mettapedia.Algorithms.Compression.LayeredSource

/-!
# Recovering and replaying a fixed layered source library

Recovery reads a definition before applying each existing decoder. Replaying
the recovered entries in reverse order installs the fixed definitions on a
different receiving source. Local checked inverses yield reconstruction of
that receiving source by the complete newest-first decoder sequence.

The source-profile reader, matcher and fixed-prefix check are separate from
these algorithm laws. In particular this development does not infer source
equivalence from examples or certify native evaluator execution.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.LibraryTransfer

open LayeredSource

universe u

structure Stage (Definition : Type*) where
  layer : Layer
  definition : Definition
  deriving DecidableEq, Repr

section Recovery

variable {Source Definition : Type u}

def recover (extract : Layer → Source → Option Definition)
    (undo : Layer → Source → Option Source) : List Layer → Source → Option (List (Stage Definition))
  | [], _ => some []
  | layer :: rest, source =>
      match extract layer source with
      | none => none
      | some definition =>
          match undo layer source with
          | none => none
          | some previous =>
              (recover extract undo rest previous).map fun later => ⟨layer, definition⟩ :: later

theorem recover_cons_iff (extract : Layer → Source → Option Definition)
    (undo : Layer → Source → Option Source) (layer : Layer) (rest : List Layer)
    (source : Source) (stages : List (Stage Definition)) :
    recover extract undo (layer :: rest) source = some stages ↔
      ∃ definition previous later, extract layer source = some definition ∧
        undo layer source = some previous ∧ recover extract undo rest previous = some later ∧
        stages = ⟨layer, definition⟩ :: later := by
  cases extracted : extract layer source with
  | none => simp [recover, extracted]
  | some definition =>
      cases decoded : undo layer source with
      | none => simp [recover, extracted, decoded]
      | some previous =>
          cases recovered : recover extract undo rest previous with
          | none => simp [recover, extracted, decoded, recovered]
          | some later => simp [recover, extracted, decoded, recovered, eq_comm]

theorem recovered_layers (extract : Layer → Source → Option Definition)
    (undo : Layer → Source → Option Source) (layers : List Layer)
    (source : Source) (stages : List (Stage Definition))
    (found : recover extract undo layers source = some stages) :
    stages.map Stage.layer = layers := by
  induction layers generalizing source stages with
  | nil => cases Option.some.inj found; rfl
  | cons layer rest ih =>
      obtain ⟨definition, previous, later, _, _, recovered, rfl⟩ :=
        (recover_cons_iff extract undo layer rest source stages).mp found
      simp only [List.map_cons, ih previous later recovered]

theorem recovered_length (extract : Layer → Source → Option Definition)
    (undo : Layer → Source → Option Source) (layers : List Layer)
    (source : Source) (stages : List (Stage Definition))
    (found : recover extract undo layers source = some stages) : stages.length = layers.length := by
  have same := congrArg List.length (recovered_layers extract undo layers source stages found)
  simpa using same

theorem recovery_checks_all_decoders (extract : Layer → Source → Option Definition)
    (undo : Layer → Source → Option Source) (layers : List Layer)
    (source : Source) (stages : List (Stage Definition))
    (found : recover extract undo layers source = some stages) :
    ∃ original, expand undo layers source = some original := by
  induction layers generalizing source stages with
  | nil => exact ⟨source, rfl⟩
  | cons layer rest ih =>
      obtain ⟨definition, previous, later, _, decoded, recovered, _⟩ :=
        (recover_cons_iff extract undo layer rest source stages).mp found
      obtain ⟨original, restored⟩ := ih previous later recovered
      exact ⟨original, by simp only [expand, decoded, Option.bind_some, restored]⟩

end Recovery

section Replay

variable {Source Entry : Type u}

def replay (install : Entry → Source → Option Source) : List Entry → Source → Option Source
  | [], source => some source
  | entry :: rest, source => (install entry source).bind (replay install rest)

theorem replay_append (install : Entry → Source → Option Source)
    (first second : List Entry) (source : Source) :
    replay install (first ++ second) source =
      (replay install first source).bind (replay install second) := by
  induction first generalizing source with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.cons_append, replay]
      cases next : install entry source <;> simp [ih]

theorem failed_stage_rejects_publication (install : Entry → Source → Option Source)
    (first second : List Entry) (source : Source) (failed : replay install first source = none) :
    replay install (first ++ second) source = none := by rw [replay_append, failed]; rfl

/-- Inverting every admitted installation is sufficient for whole receiving
source reconstruction. The conclusion is not assumed as a task invariant. -/
theorem replay_reconstructs (install : Entry → Source → Option Source)
    (descriptor : Entry → Layer) (undo : Layer → Source → Option Source)
    (localInverse : ∀ entry before after, install entry before = some after →
      undo (descriptor entry) after = some before)
    (entries : List Entry) (original result : Source)
    (finished : replay install entries original = some result) :
    expand undo (entries.map descriptor).reverse result = some original := by
  induction entries generalizing original result with
  | nil => cases Option.some.inj finished; rfl
  | cons entry rest ih =>
      simp only [replay, Option.bind_eq_some_iff] at finished
      obtain ⟨middle, installed, tail⟩ := finished
      have restored := ih middle result tail
      simp only [List.map_cons, List.reverse_cons, expand_append, restored, Option.bind_some]
      simp only [expand, localInverse entry original middle installed, Option.bind_some]

end Replay

def installedLayer {Definition : Type*} (codec : KolmogorovComplexity.BinString)
    (stage : Stage Definition) : Layer := ⟨codec, stage.layer.name⟩

theorem installed_names_preserved {Source Definition : Type u}
    (extract : Layer → Source → Option Definition) (undo : Layer → Source → Option Source)
    (codec : KolmogorovComplexity.BinString) (layers : List Layer) (source : Source)
    (stages : List (Stage Definition)) (found : recover extract undo layers source = some stages) :
    (stages.map (installedLayer codec)).map Layer.name = layers.map Layer.name := by
  have same := congrArg (List.map Layer.name) (recovered_layers extract undo layers source stages found)
  simpa [List.map_map, Function.comp_def, installedLayer] using same

theorem recovered_replay_reconstructs {Source Definition : Type u}
    (install : Stage Definition → Source → Option Source)
    (undo : Layer → Source → Option Source) (codec : KolmogorovComplexity.BinString)
    (localInverse : ∀ entry before after, install entry before = some after →
      undo (installedLayer codec entry) after = some before)
    (stages : List (Stage Definition)) (original result : Source)
    (finished : replay install stages.reverse original = some result) :
    expand undo (stages.map (installedLayer codec)) result = some original := by
  have restored := replay_reconstructs install (installedLayer codec) undo localInverse
    stages.reverse original result finished
  simpa only [List.map_reverse, List.reverse_reverse] using restored

/-- Cost acceptance uses the complete LM1 envelope, not the size of a pattern
or an uncharged helper table. The observer is the task's original criterion. -/
theorem accepted_complete_bits_decrease {Observation : Type*} [DecidableEq Observation]
    (observe : Payload → Option Observation) (original : Observation)
    (current candidate result : Payload)
    (checked : CostedArtifact.accept
      (fun payload => decide (observe payload = some original)) byteCost current candidate = some result) :
    observe result = some original ∧ (write result).length < (write current).length := by
  obtain ⟨rfl, _, observed, smaller⟩ :=
    (CostedArtifact.accept_iff (fun payload => decide (observe payload = some original))
      byteCost current candidate result).mp checked
  constructor
  · exact of_decide_eq_true observed
  · rw [serialized_length, serialized_length]
    omega

end Mettapedia.Algorithms.Compression.LibraryTransfer
