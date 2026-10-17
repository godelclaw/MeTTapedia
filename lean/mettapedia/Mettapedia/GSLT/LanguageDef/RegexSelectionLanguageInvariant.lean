import Mettapedia.GSLT.LanguageDef.RegexSelectionLowering

/-!
# Residual-language invariants for emitted regex instructions

The annotation is computed from source-language meanings and symbolic address
ownership. It is a semantic certificate for the existing emitted program, not a
different compiler or an executable implementation-selection policy.
-/

set_option autoImplicit false
open scoped Computability

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.Recognition

open Mettapedia.Computability.RegularLanguages

private noncomputable instance : DecidableRel Within := fun _ _ => Classical.propDecidable _

/-- This value is used only with a successful context-free language witness.
It does not assign assertions a context-independent meaning. -/
noncomputable def sourceLanguage (pattern : Pattern) : Language Nat := (language? pattern).getD 0

theorem sourceLanguage_of_erased (pattern : Pattern) (regex : Regex Nat)
    (erased : erase? pattern = some regex) : sourceLanguage pattern = language regex := by
  have equal : language? pattern = some (language regex) := by
    simpa [erased] using (erase_language pattern).symm
  simp [sourceLanguage, equal]

noncomputable def annotation (pattern : Pattern) (continuation : Language Nat)
    (address target : Address) : Language Nat :=
  if target = address then sourceLanguage pattern * continuation else
    match pattern with
    | .seq first second =>
        if Within (.left address) target then
          annotation first (sourceLanguage second * continuation) (.left address) target
        else annotation second continuation (.right address) target
    | .alt first second =>
        if Within (.left address) target then annotation first continuation (.left address) target
        else annotation second continuation (.right address) target
    | .star body greedy =>
        if target = .loop address then sourceLanguage (.star body greedy) * continuation
        else annotation body (sourceLanguage (.star body greedy) * continuation) (.body address) target
    | .optional body _ => annotation body continuation (.body address) target
    | .plus body greedy =>
        if target = .loop address then sourceLanguage (.star body greedy) * continuation
        else annotation body (sourceLanguage (.star body greedy) * continuation) (.body address) target
    | .capture _ body =>
        if target = .close address then continuation
        else annotation body continuation (.body address) target
    | _ => 0

@[simp] theorem annotation_entry (pattern : Pattern) (continuation : Language Nat) (address : Address) :
    annotation pattern continuation address address = sourceLanguage pattern * continuation := by
  cases pattern <;> simp [annotation]

theorem annotation_outside (pattern : Pattern) (continuation : Language Nat) (address target : Address)
    (outside : ¬ Within address target) : annotation pattern continuation address target = 0 := by
  have different : target ≠ address := by rintro rfl; exact outside (.refl _)
  induction pattern generalizing continuation address with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ => simp [annotation, different]
  | seq first second ihFirst ihSecond =>
      have notLeft : ¬ Within (.left address) target := fun inside => outside ((Within.left (.refl _)).trans inside)
      have notRight : ¬ Within (.right address) target := fun inside => outside ((Within.right (.refl _)).trans inside)
      simp only [annotation, if_neg different, if_neg notLeft]
      exact ihSecond continuation address.right notRight (by rintro rfl; exact notRight (.refl _))
  | alt first second ihFirst ihSecond =>
      have notLeft : ¬ Within (.left address) target := fun inside => outside ((Within.left (.refl _)).trans inside)
      have notRight : ¬ Within (.right address) target := fun inside => outside ((Within.right (.refl _)).trans inside)
      simp only [annotation, if_neg different, if_neg notLeft]
      exact ihSecond continuation address.right notRight (by rintro rfl; exact notRight (.refl _))
  | star body greedy ih =>
      have notLoop : target ≠ .loop address := by rintro rfl; exact outside (.loop (.refl _))
      have notBody : ¬ Within (.body address) target := fun inside => outside ((Within.body (.refl _)).trans inside)
      simp only [annotation, if_neg different, if_neg notLoop]
      exact ih _ address.body notBody (by rintro rfl; exact notBody (.refl _))
  | optional body greedy ih =>
      have notBody : ¬ Within (.body address) target := fun inside => outside ((Within.body (.refl _)).trans inside)
      simp only [annotation, if_neg different]
      exact ih continuation address.body notBody (by rintro rfl; exact notBody (.refl _))
  | plus body greedy ih =>
      have notLoop : target ≠ .loop address := by rintro rfl; exact outside (.loop (.refl _))
      have notBody : ¬ Within (.body address) target := fun inside => outside ((Within.body (.refl _)).trans inside)
      simp only [annotation, if_neg different, if_neg notLoop]
      exact ih _ address.body notBody (by rintro rfl; exact notBody (.refl _))
  | capture group body ih =>
      have notClose : target ≠ .close address := by rintro rfl; exact outside (.close (.refl _))
      have notBody : ¬ Within (.body address) target := fun inside => outside ((Within.body (.refl _)).trans inside)
      simp only [annotation, if_neg different, if_neg notClose]
      exact ih continuation address.body notBody (by rintro rfl; exact notBody (.refl _))

noncomputable def meaning (pattern : Pattern) (continuation : Language Nat)
    (address exit target : Address) : Language Nat :=
  if target = exit then continuation else annotation pattern continuation address target

@[simp] theorem meaning_ending (pattern : Pattern) (continuation : Language Nat) (address exit : Address) :
    meaning pattern continuation address exit exit = continuation := by simp [meaning]

theorem meaning_owned (pattern : Pattern) (continuation : Language Nat) (address exit target : Address)
    (outside : ¬ Within address exit) (owned : Within address target) :
    meaning pattern continuation address exit target = annotation pattern continuation address target := by
  have different : target ≠ exit := by rintro rfl; exact outside owned
  simp [meaning, different]

@[simp] theorem meaning_entry (pattern : Pattern) (continuation : Language Nat) (address exit : Address)
    (outside : ¬ Within address exit) :
    meaning pattern continuation address exit address = sourceLanguage pattern * continuation := by
  rw [meaning_owned pattern continuation address exit address outside (.refl _), annotation_entry]

private theorem descendant_not_parent (address target : Address) (branch : Branch)
    (inside : Within (address.child branch) target) : target ≠ address := by
  intro same
  exact no_child_within_parent address branch (same ▸ inside)

theorem annotation_seq_left (first second : Pattern) (continuation : Language Nat) (address target : Address)
    (inside : Within (.left address) target) :
    annotation (.seq first second) continuation address target =
      annotation first (sourceLanguage second * continuation) (.left address) target := by
  have different := descendant_not_parent address target .left inside
  simp [annotation, different, inside]

theorem annotation_seq_right (first second : Pattern) (continuation : Language Nat) (address target : Address)
    (inside : Within (.right address) target) :
    annotation (.seq first second) continuation address target = annotation second continuation (.right address) target := by
  have different := descendant_not_parent address target .right inside
  have notLeft : ¬ Within (.left address) target := fun other =>
    sibling_subtrees_disjoint address target .left .right (by decide) other inside
  simp [annotation, different, notLeft]

theorem annotation_alt_left (first second : Pattern) (continuation : Language Nat) (address target : Address)
    (inside : Within (.left address) target) :
    annotation (.alt first second) continuation address target = annotation first continuation (.left address) target := by
  have different := descendant_not_parent address target .left inside
  simp [annotation, different, inside]

theorem annotation_alt_right (first second : Pattern) (continuation : Language Nat) (address target : Address)
    (inside : Within (.right address) target) :
    annotation (.alt first second) continuation address target = annotation second continuation (.right address) target := by
  have different := descendant_not_parent address target .right inside
  have notLeft : ¬ Within (.left address) target := fun other =>
    sibling_subtrees_disjoint address target .left .right (by decide) other inside
  simp [annotation, different, notLeft]

theorem annotation_star_body (body : Pattern) (greedy : Bool) (continuation : Language Nat)
    (address target : Address) (inside : Within (.body address) target) :
    annotation (.star body greedy) continuation address target =
      annotation body (sourceLanguage (.star body greedy) * continuation) (.body address) target := by
  have different := descendant_not_parent address target .body inside
  have notLoop : target ≠ .loop address := by
    rintro rfl
    exact distinct_children_incomparable address .body .loop (by decide) inside
  simp [annotation, different, notLoop]

theorem annotation_capture_body (group : Nat) (body : Pattern) (continuation : Language Nat)
    (address target : Address) (inside : Within (.body address) target) :
    annotation (.capture group body) continuation address target = annotation body continuation (.body address) target := by
  have different := descendant_not_parent address target .body inside
  have notClose : target ≠ .close address := by
    rintro rfl
    exact distinct_children_incomparable address .body .close (by decide) inside
  simp [annotation, different, notClose]

theorem annotation_optional_body (body : Pattern) (greedy : Bool) (continuation : Language Nat)
    (address target : Address) (inside : Within (.body address) target) :
    annotation (.optional body greedy) continuation address target =
      annotation body continuation (.body address) target := by
  have different := descendant_not_parent address target .body inside
  simp [annotation, different]

theorem annotation_plus_body (body : Pattern) (greedy : Bool) (continuation : Language Nat)
    (address target : Address) (inside : Within (.body address) target) :
    annotation (.plus body greedy) continuation address target =
      annotation body (sourceLanguage (.star body greedy) * continuation) (.body address) target := by
  have different := descendant_not_parent address target .body inside
  have notLoop : target ≠ .loop address := by
    rintro rfl
    exact distinct_children_incomparable address .body .loop (by decide) inside
  simp [annotation, different, notLoop]

inductive Edge : Instruction → List Nat → Address → Prop
  | jump (address next) : Edge (.jump address next) [] next
  | save (address group boundary next) : Edge (.save address group boundary next) [] next
  | scalar (address value next) : Edge (.scalar address value next) [value] next
  | any (address value next) : Edge (.any address next) [value] next
  | class_ (address ranges value next) : value ∈ classLetters ranges → Edge (.class_ address ranges next) [value] next
  | left (address first second) : Edge (.split address first second) [] first
  | right (address first second) : Edge (.split address first second) [] second

theorem Edge.target {instruction : Instruction} {word : List Nat} {target : Address}
    (edge : Edge instruction word target) : target ∈ instruction.targets := by
  cases edge <;> simp [Instruction.targets]

def RowSound (environment : Address → Language Nat) (instruction : Instruction) : Prop :=
  ∀ prefixWord target, Edge instruction prefixWord target →
    ∀ suffixWord ∈ environment target, prefixWord ++ suffixWord ∈ environment instruction.address

theorem RowSound.transport {before after : Address → Language Nat} {instruction : Instruction}
    (sound : RowSound before instruction) (source : before instruction.address = after instruction.address)
    (targets : ∀ target ∈ instruction.targets, before target = after target) : RowSound after instruction := by
  intro prefixWord target edge suffixWord accepted
  rw [← source]
  apply sound prefixWord target edge suffixWord
  rwa [targets target edge.target]

theorem transfer_fragment (pattern : Pattern) (continuation address : Address)
    (before after : Address → Language Nat)
    (agrees : ∀ target, Within address target ∨ target = continuation → before target = after target)
    (sound : ∀ instruction ∈ emit pattern continuation address, RowSound before instruction) :
    ∀ instruction ∈ emit pattern continuation address, RowSound after instruction := by
  intro instruction member
  apply (sound instruction member).transport
  · exact agrees instruction.address (.inl (emit_owned pattern continuation address instruction member))
  · intro target targetMember
    exact agrees target (emit_targets_owned_or_continuation pattern continuation address instruction member target targetMember)

theorem meaning_seq_first (first second : Pattern) (K : Language Nat) (address exit target : Address)
    (outside : ¬ Within address exit) (inside : Within (.left address) target ∨ target = .right address) :
    meaning first (sourceLanguage second * K) (.left address) (.right address) target =
      meaning (.seq first second) K address exit target := by
  rcases inside with inside | rfl
  · have childOutside : ¬ Within (.left address) (.right address) :=
      distinct_children_incomparable address .left .right (by decide)
    rw [meaning_owned _ _ _ _ _ childOutside inside,
      meaning_owned _ _ _ _ _ outside ((Within.left (.refl _)).trans inside), annotation_seq_left _ _ _ _ _ inside]
  · rw [meaning_ending, meaning_owned _ _ _ _ _ outside (.right (.refl _)),
      annotation_seq_right _ _ _ _ _ (.refl _), annotation_entry]

theorem meaning_seq_second (first second : Pattern) (K : Language Nat) (address exit target : Address)
    (outside : ¬ Within address exit) (inside : Within (.right address) target ∨ target = exit) :
    meaning second K (.right address) exit target = meaning (.seq first second) K address exit target := by
  rcases inside with inside | rfl
  · have childOutside : ¬ Within (.right address) exit := fun h => outside ((Within.right (.refl _)).trans h)
    rw [meaning_owned _ _ _ _ _ childOutside inside,
      meaning_owned _ _ _ _ _ outside ((Within.right (.refl _)).trans inside), annotation_seq_right _ _ _ _ _ inside]
  · simp

theorem meaning_alt_first (first second : Pattern) (K : Language Nat) (address exit target : Address)
    (outside : ¬ Within address exit) (inside : Within (.left address) target ∨ target = exit) :
    meaning first K (.left address) exit target = meaning (.alt first second) K address exit target := by
  rcases inside with inside | rfl
  · have childOutside : ¬ Within (.left address) exit := fun h => outside ((Within.left (.refl _)).trans h)
    rw [meaning_owned _ _ _ _ _ childOutside inside,
      meaning_owned _ _ _ _ _ outside ((Within.left (.refl _)).trans inside), annotation_alt_left _ _ _ _ _ inside]
  · simp

theorem meaning_alt_second (first second : Pattern) (K : Language Nat) (address exit target : Address)
    (outside : ¬ Within address exit) (inside : Within (.right address) target ∨ target = exit) :
    meaning second K (.right address) exit target = meaning (.alt first second) K address exit target := by
  rcases inside with inside | rfl
  · have childOutside : ¬ Within (.right address) exit := fun h => outside ((Within.right (.refl _)).trans h)
    rw [meaning_owned _ _ _ _ _ childOutside inside,
      meaning_owned _ _ _ _ _ outside ((Within.right (.refl _)).trans inside), annotation_alt_right _ _ _ _ _ inside]
  · simp

theorem meaning_star_repeat (body : Pattern) (greedy : Bool) (K : Language Nat) (address exit : Address)
    (outside : ¬ Within address exit) :
    meaning (.star body greedy) K address exit (.loop address) = sourceLanguage (.star body greedy) * K := by
  rw [meaning_owned _ _ _ _ _ outside (.loop (.refl _))]
  have different : Address.loop address ≠ address := by
    intro same
    have depths := congrArg Address.depth same
    simp [Address.depth] at depths
  simp [annotation, different]

theorem meaning_star_body (body : Pattern) (greedy : Bool) (K : Language Nat) (address exit target : Address)
    (outside : ¬ Within address exit) (inside : Within (.body address) target ∨ target = .loop address) :
    meaning body (sourceLanguage (.star body greedy) * K) (.body address) (.loop address) target =
      meaning (.star body greedy) K address exit target := by
  rcases inside with inside | rfl
  · have childOutside : ¬ Within (.body address) (.loop address) :=
      distinct_children_incomparable address .body .loop (by decide)
    rw [meaning_owned _ _ _ _ _ childOutside inside,
      meaning_owned _ _ _ _ _ outside ((Within.body (.refl _)).trans inside), annotation_star_body _ _ _ _ _ inside]
  · rw [meaning_ending, meaning_star_repeat _ _ _ _ _ outside]

theorem meaning_capture_close (group : Nat) (body : Pattern) (K : Language Nat) (address exit : Address)
    (outside : ¬ Within address exit) : meaning (.capture group body) K address exit (.close address) = K := by
  rw [meaning_owned _ _ _ _ _ outside (.close (.refl _))]
  have different : Address.close address ≠ address := by
    intro same
    have depths := congrArg Address.depth same
    simp [Address.depth] at depths
  simp [annotation, different]

theorem meaning_capture_body (group : Nat) (body : Pattern) (K : Language Nat) (address exit target : Address)
    (outside : ¬ Within address exit) (inside : Within (.body address) target ∨ target = .close address) :
    meaning body K (.body address) (.close address) target = meaning (.capture group body) K address exit target := by
  rcases inside with inside | rfl
  · have childOutside : ¬ Within (.body address) (.close address) :=
      distinct_children_incomparable address .body .close (by decide)
    rw [meaning_owned _ _ _ _ _ childOutside inside,
      meaning_owned _ _ _ _ _ outside ((Within.body (.refl _)).trans inside), annotation_capture_body _ _ _ _ _ inside]
  · rw [meaning_ending, meaning_capture_close _ _ _ _ _ outside]

theorem meaning_optional_body (body : Pattern) (greedy : Bool) (K : Language Nat) (address exit target : Address)
    (outside : ¬ Within address exit) (inside : Within (.body address) target ∨ target = exit) :
    meaning body K (.body address) exit target = meaning (.optional body greedy) K address exit target := by
  rcases inside with inside | rfl
  · have childOutside : ¬ Within (.body address) exit := fun h => outside ((Within.body (.refl _)).trans h)
    rw [meaning_owned _ _ _ _ _ childOutside inside,
      meaning_owned _ _ _ _ _ outside ((Within.body (.refl _)).trans inside), annotation_optional_body _ _ _ _ _ inside]
  · simp

theorem meaning_plus_repeat (body : Pattern) (greedy : Bool) (K : Language Nat) (address exit : Address)
    (outside : ¬ Within address exit) :
    meaning (.plus body greedy) K address exit (.loop address) = sourceLanguage (.star body greedy) * K := by
  rw [meaning_owned _ _ _ _ _ outside (.loop (.refl _))]
  have different : Address.loop address ≠ address := by
    intro same
    have depths := congrArg Address.depth same
    simp [Address.depth] at depths
  simp [annotation, different]

theorem meaning_plus_body (body : Pattern) (greedy : Bool) (K : Language Nat) (address exit target : Address)
    (outside : ¬ Within address exit) (inside : Within (.body address) target ∨ target = .loop address) :
    meaning body (sourceLanguage (.star body greedy) * K) (.body address) (.loop address) target =
      meaning (.plus body greedy) K address exit target := by
  rcases inside with inside | rfl
  · have childOutside : ¬ Within (.body address) (.loop address) :=
      distinct_children_incomparable address .body .loop (by decide)
    rw [meaning_owned _ _ _ _ _ childOutside inside,
      meaning_owned _ _ _ _ _ outside ((Within.body (.refl _)).trans inside), annotation_plus_body _ _ _ _ _ inside]
  · rw [meaning_ending, meaning_plus_repeat _ _ _ _ _ outside]

theorem sourceLanguage_seq (first second : Pattern) (left right : Regex Nat)
    (leftErase : erase? first = some left) (rightErase : erase? second = some right) :
    sourceLanguage (.seq first second) = sourceLanguage first * sourceLanguage second := by
  rw [sourceLanguage_of_erased _ (left * right) (by simp [erase?, leftErase, rightErase]),
    sourceLanguage_of_erased _ left leftErase, sourceLanguage_of_erased _ right rightErase]
  rfl

theorem sourceLanguage_alt (first second : Pattern) (left right : Regex Nat)
    (leftErase : erase? first = some left) (rightErase : erase? second = some right) :
    sourceLanguage (.alt first second) = sourceLanguage first + sourceLanguage second := by
  rw [sourceLanguage_of_erased _ (left + right) (by simp [erase?, leftErase, rightErase]),
    sourceLanguage_of_erased _ left leftErase, sourceLanguage_of_erased _ right rightErase]
  rfl

theorem sourceLanguage_star (body : Pattern) (greedy : Bool) (regex : Regex Nat)
    (bodyErase : erase? body = some regex) :
    sourceLanguage (.star body greedy) = (sourceLanguage body)∗ := by
  rw [sourceLanguage_of_erased _ regex.star (by simp [erase?, bodyErase]),
    sourceLanguage_of_erased _ regex bodyErase]
  rfl

theorem sourceLanguage_optional (body : Pattern) (greedy : Bool) (regex : Regex Nat)
    (bodyErase : erase? body = some regex) :
    sourceLanguage (.optional body greedy) = sourceLanguage body + 1 := by
  rw [sourceLanguage_of_erased _ (regex + 1) (by simp [erase?, bodyErase]),
    sourceLanguage_of_erased _ regex bodyErase]
  rfl

theorem sourceLanguage_plus (body : Pattern) (greedy : Bool) (regex : Regex Nat)
    (bodyErase : erase? body = some regex) :
    sourceLanguage (.plus body greedy) = sourceLanguage body * sourceLanguage (.star body greedy) := by
  rw [sourceLanguage_of_erased _ (regex * regex.star) (by simp [erase?, bodyErase]),
    sourceLanguage_star _ _ _ bodyErase, sourceLanguage_of_erased _ regex bodyErase]
  rfl

@[simp] theorem sourceLanguage_capture (group : Nat) (body : Pattern) :
    sourceLanguage (.capture group body) = sourceLanguage body := rfl

theorem prepend_star (L K : Language Nat) (word : List Nat) (accepted : word ∈ L * (L∗ * K)) :
    word ∈ L∗ * K := by
  obtain ⟨first, firstMem, rest, restMem, rfl⟩ := Language.mem_mul.mp accepted
  obtain ⟨middle, middleMem, last, lastMem, rfl⟩ := Language.mem_mul.mp restMem
  obtain ⟨parts, rfl, allParts⟩ := Language.mem_kstar.mp middleMem
  have all : ∀ part ∈ first :: parts, part ∈ L := by
    intro part member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstMem
    · exact allParts part member
  have joined : first ++ parts.flatten ∈ L∗ := Language.mem_kstar.mpr ⟨first :: parts, rfl, all⟩
  simpa only [List.append_assoc] using Language.append_mem_mul joined lastMem

theorem zero_iterations (L K : Language Nat) (word : List Nat) (member : word ∈ K) : word ∈ L∗ * K := by
  exact Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, word, member, rfl⟩

/-- The computed annotation validates every actual emitted instruction.
Its construction is independent of the graph path relation. -/
theorem emit_rows_sound (pattern : Pattern) (regex : Regex Nat) (erased : erase? pattern = some regex)
    (K : Language Nat) (exit address : Address) (outside : ¬ Within address exit) :
    ∀ instruction ∈ emit pattern exit address, RowSound (meaning pattern K address exit) instruction := by
  induction pattern generalizing regex K exit address with
  | zero =>
      intro instruction member prefixWord target edge
      simp only [emit, List.mem_singleton] at member
      subst instruction
      cases edge
  | epsilon =>
      intro instruction member prefixWord target edge suffixWord accepted
      simp only [emit, List.mem_singleton] at member
      subst instruction
      cases edge
      simpa [Instruction.address, meaning_entry _ _ _ _ outside, sourceLanguage, language?] using accepted
  | literal scalar =>
      intro instruction member prefixWord target edge suffixWord accepted
      simp only [emit, List.mem_singleton] at member
      subst instruction
      cases edge
      rw [meaning_ending] at accepted
      change scalar :: suffixWord ∈ meaning (.literal scalar) K address exit address
      rw [meaning_entry _ _ _ _ outside]
      exact Language.append_mem_mul (show [scalar] ∈ sourceLanguage (.literal scalar) from rfl) accepted
  | any =>
      intro instruction member prefixWord target edge suffixWord accepted
      simp only [emit, List.mem_singleton] at member
      subst instruction
      cases edge with
      | any _ value _ =>
          rw [meaning_ending] at accepted
          change value :: suffixWord ∈ meaning .any K address exit address
          rw [meaning_entry _ _ _ _ outside]
          exact Language.append_mem_mul (show [value] ∈ sourceLanguage .any from ⟨value, rfl⟩) accepted
  | class_ ranges =>
      intro instruction member prefixWord target edge suffixWord accepted
      simp only [emit, List.mem_singleton] at member
      subst instruction
      cases edge with
      | class_ _ _ value _ inClass =>
          rw [meaning_ending] at accepted
          change value :: suffixWord ∈ meaning (.class_ ranges) K address exit address
          rw [meaning_entry _ _ _ _ outside]
          exact Language.append_mem_mul (show [value] ∈ sourceLanguage (.class_ ranges) from
            ⟨value, inClass, rfl⟩) accepted
  | assertion name => simp [erase?] at erased
  | seq first second ihFirst ihSecond =>
      cases leftErase : erase? first with
      | none => simp [erase?, leftErase] at erased
      | some left =>
          cases rightErase : erase? second with
          | none => simp [erase?, leftErase, rightErase] at erased
          | some right =>
              have leftRightOutside : ¬ Within (.left address) (.right address) :=
                distinct_children_incomparable address .left .right (by decide)
              intro instruction member
              simp only [emit, List.mem_cons, List.mem_append] at member
              rcases member with same | leftMember | rightMember
              · subst instruction
                intro prefixWord target edge suffixWord accepted
                cases edge
                rw [← meaning_seq_first first second K address exit address.left outside (.inl (.refl _)),
                  meaning_entry _ _ _ _ leftRightOutside] at accepted
                change suffixWord ∈ meaning (.seq first second) K address exit address
                rw [meaning_entry _ _ _ _ outside, sourceLanguage_seq _ _ _ _ leftErase rightErase, mul_assoc]
                exact accepted
              · exact transfer_fragment first (.right address) (.left address)
                  (meaning first (sourceLanguage second * K) (.left address) (.right address))
                  (meaning (.seq first second) K address exit)
                  (fun target inside => meaning_seq_first first second K address exit target outside inside)
                  (ihFirst left leftErase _ _ _ leftRightOutside)
                  instruction leftMember
              · have rightOutside : ¬ Within (.right address) exit := fun h => outside ((Within.right (.refl _)).trans h)
                exact transfer_fragment second exit (.right address)
                  (meaning second K (.right address) exit) (meaning (.seq first second) K address exit)
                  (fun target inside => meaning_seq_second first second K address exit target outside inside)
                  (ihSecond right rightErase _ _ _ rightOutside) instruction rightMember
  | alt first second ihFirst ihSecond =>
      cases leftErase : erase? first with
      | none => simp [erase?, leftErase] at erased
      | some left =>
          cases rightErase : erase? second with
          | none => simp [erase?, leftErase, rightErase] at erased
          | some right =>
              have leftOutside : ¬ Within (.left address) exit := fun h => outside ((Within.left (.refl _)).trans h)
              have rightOutside : ¬ Within (.right address) exit := fun h => outside ((Within.right (.refl _)).trans h)
              intro instruction member
              simp only [emit, List.mem_cons, List.mem_append] at member
              rcases member with same | leftMember | rightMember
              · subst instruction
                intro prefixWord target edge suffixWord accepted
                cases edge with
                | left =>
                    rw [← meaning_alt_first first second K address exit address.left outside (.inl (.refl _)),
                      meaning_entry _ _ _ _ leftOutside] at accepted
                    change suffixWord ∈ meaning (.alt first second) K address exit address
                    rw [meaning_entry _ _ _ _ outside, sourceLanguage_alt _ _ _ _ leftErase rightErase, add_mul]
                    exact Or.inl accepted
                | right =>
                    rw [← meaning_alt_second first second K address exit address.right outside (.inl (.refl _)),
                      meaning_entry _ _ _ _ rightOutside] at accepted
                    change suffixWord ∈ meaning (.alt first second) K address exit address
                    rw [meaning_entry _ _ _ _ outside, sourceLanguage_alt _ _ _ _ leftErase rightErase, add_mul]
                    exact Or.inr accepted
              · exact transfer_fragment first exit (.left address)
                  (meaning first K (.left address) exit) (meaning (.alt first second) K address exit)
                  (fun target inside => meaning_alt_first first second K address exit target outside inside)
                  (ihFirst left leftErase _ _ _ leftOutside) instruction leftMember
              · exact transfer_fragment second exit (.right address)
                  (meaning second K (.right address) exit) (meaning (.alt first second) K address exit)
                  (fun target inside => meaning_alt_second first second K address exit target outside inside)
                  (ihSecond right rightErase _ _ _ rightOutside) instruction rightMember
  | star body greedy ih =>
      cases bodyErase : erase? body with
      | none => simp [erase?, bodyErase] at erased
      | some bodyRegex =>
          have bodyOutside : ¬ Within (.body address) (.loop address) :=
            distinct_children_incomparable address .body .loop (by decide)
          have bodyEntry : meaning (.star body greedy) K address exit (.body address) =
              sourceLanguage body * (sourceLanguage (.star body greedy) * K) := by
            rw [← meaning_star_body body greedy K address exit (.body address) outside (.inl (.refl _)),
              meaning_entry _ _ _ _ bodyOutside]
          have same : sourceLanguage (.star body greedy) = (sourceLanguage body)∗ :=
            sourceLanguage_star body greedy bodyRegex bodyErase
          have rootSound : RowSound (meaning (.star body greedy) K address exit)
              (choice address (.body address) exit greedy) := by
            intro prefixWord target edge suffixWord accepted
            cases greedy <;> simp only [choice, Bool.false_eq_true, ↓reduceIte] at edge
            all_goals cases edge
            all_goals change suffixWord ∈ meaning (.star body _) K address exit address
            all_goals rw [meaning_entry _ _ _ _ outside, same]
            all_goals first
              | exact zero_iterations _ K suffixWord (by simpa using accepted)
              | exact prepend_star _ K suffixWord (by simpa [bodyEntry, same] using accepted)
          have loopSound : RowSound (meaning (.star body greedy) K address exit)
              (choice (.loop address) (.body address) exit greedy) := by
            intro prefixWord target edge suffixWord accepted
            cases greedy <;> simp only [choice, Bool.false_eq_true, ↓reduceIte] at edge
            all_goals cases edge
            all_goals change suffixWord ∈ meaning (.star body _) K address exit (.loop address)
            all_goals rw [meaning_star_repeat _ _ _ _ _ outside, same]
            all_goals first
              | exact zero_iterations _ K suffixWord (by simpa using accepted)
              | exact prepend_star _ K suffixWord (by simpa [bodyEntry, same] using accepted)
          intro instruction member
          simp only [emit, List.mem_cons] at member
          rcases member with sameRow | sameRow | bodyMember
          · subst instruction; exact rootSound
          · subst instruction; exact loopSound
          · exact transfer_fragment body (.loop address) (.body address)
              (meaning body (sourceLanguage (.star body greedy) * K) (.body address) (.loop address))
              (meaning (.star body greedy) K address exit)
              (fun target inside => meaning_star_body body greedy K address exit target outside inside)
              (ih bodyRegex bodyErase _ _ _ bodyOutside) instruction bodyMember
  | optional body greedy ih =>
      cases bodyErase : erase? body with
      | none => simp [erase?, bodyErase] at erased
      | some bodyRegex =>
          have bodyOutside : ¬ Within (.body address) exit := fun h => outside ((Within.body (.refl _)).trans h)
          have bodyEntry : meaning (.optional body greedy) K address exit (.body address) = sourceLanguage body * K := by
            rw [← meaning_optional_body body greedy K address exit (.body address) outside (.inl (.refl _)),
              meaning_entry _ _ _ _ bodyOutside]
          intro instruction member
          simp only [emit, List.mem_cons] at member
          rcases member with sameRow | bodyMember
          · subst instruction
            intro prefixWord target edge suffixWord accepted
            cases greedy <;> simp only [choice, Bool.false_eq_true, ↓reduceIte] at edge
            all_goals cases edge
            all_goals change suffixWord ∈ meaning (.optional body _) K address exit address
            all_goals rw [meaning_entry _ _ _ _ outside, sourceLanguage_optional _ _ _ bodyErase, add_mul, one_mul]
            all_goals change suffixWord ∈ sourceLanguage body * K ∨ suffixWord ∈ K
            all_goals first
              | (rw [bodyEntry] at accepted; exact Or.inl accepted)
              | (rw [meaning_ending] at accepted; exact Or.inr accepted)
          · exact transfer_fragment body exit (.body address)
              (meaning body K (.body address) exit) (meaning (.optional body greedy) K address exit)
              (fun target inside => meaning_optional_body body greedy K address exit target outside inside)
              (ih bodyRegex bodyErase _ _ _ bodyOutside) instruction bodyMember
  | plus body greedy ih =>
      cases bodyErase : erase? body with
      | none => simp [erase?, bodyErase] at erased
      | some bodyRegex =>
          have bodyOutside : ¬ Within (.body address) (.loop address) :=
            distinct_children_incomparable address .body .loop (by decide)
          have bodyEntry : meaning (.plus body greedy) K address exit (.body address) =
              sourceLanguage body * (sourceLanguage (.star body greedy) * K) := by
            rw [← meaning_plus_body body greedy K address exit (.body address) outside (.inl (.refl _)),
              meaning_entry _ _ _ _ bodyOutside]
          have same : sourceLanguage (.star body greedy) = (sourceLanguage body)∗ :=
            sourceLanguage_star body greedy bodyRegex bodyErase
          have loopSound : RowSound (meaning (.plus body greedy) K address exit)
              (choice (.loop address) (.body address) exit greedy) := by
            intro prefixWord target edge suffixWord accepted
            cases greedy <;> simp only [choice, Bool.false_eq_true, ↓reduceIte] at edge
            all_goals cases edge
            all_goals change suffixWord ∈ meaning (.plus body _) K address exit (.loop address)
            all_goals rw [meaning_plus_repeat _ _ _ _ _ outside, same]
            all_goals first
              | exact zero_iterations _ K suffixWord (by simpa using accepted)
              | exact prepend_star _ K suffixWord (by simpa [bodyEntry, same] using accepted)
          intro instruction member
          simp only [emit, List.mem_cons] at member
          rcases member with sameRow | sameRow | bodyMember
          · subst instruction
            intro prefixWord target edge suffixWord accepted
            cases edge
            rw [bodyEntry] at accepted
            change suffixWord ∈ meaning (.plus body greedy) K address exit address
            rwa [meaning_entry _ _ _ _ outside, sourceLanguage_plus _ _ _ bodyErase, mul_assoc]
          · subst instruction; exact loopSound
          · exact transfer_fragment body (.loop address) (.body address)
              (meaning body (sourceLanguage (.star body greedy) * K) (.body address) (.loop address))
              (meaning (.plus body greedy) K address exit)
              (fun target inside => meaning_plus_body body greedy K address exit target outside inside)
              (ih bodyRegex bodyErase _ _ _ bodyOutside) instruction bodyMember
  | capture group body ih =>
      have bodyOutside : ¬ Within (.body address) (.close address) :=
        distinct_children_incomparable address .body .close (by decide)
      intro instruction member
      simp only [emit, List.mem_cons] at member
      rcases member with same | same | bodyMember
      · subst instruction
        intro prefixWord target edge suffixWord accepted
        cases edge
        rw [← meaning_capture_body group body K address exit (.body address) outside (.inl (.refl _)),
          meaning_entry _ _ _ _ bodyOutside] at accepted
        change suffixWord ∈ meaning (.capture group body) K address exit address
        simpa [meaning_entry _ _ _ _ outside] using accepted
      · subst instruction
        intro prefixWord target edge suffixWord accepted
        cases edge
        simpa [Instruction.address, meaning_capture_close _ _ _ _ _ outside] using accepted
      · exact transfer_fragment body (.close address) (.body address)
          (meaning body K (.body address) (.close address)) (meaning (.capture group body) K address exit)
          (fun target inside => meaning_capture_body group body K address exit target outside inside)
          (ih regex erased _ _ _ bodyOutside) instruction bodyMember

end Mettapedia.GSLT.LanguageDef.RegexSelection.Recognition
