import Mettapedia.GSLT.LanguageDef.RegexSelectionLanguageInvariant

/-!
# Recognition paths of the actual symbolic-address regex compiler

`Path` independently interprets the emitted instruction rows. Its observations
are consumed scalar words, not instruction counts or selected capture histories.
Capture saves are real epsilon edges; assertions have no context-free rule here.
The construction below uses the existing `emit`, not a second compiler.
-/

set_option autoImplicit false
open scoped Computability

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.Recognition

open Mettapedia.Computability.RegularLanguages

/-- A word-labelled path in a concrete instruction list. An instruction must
actually occur in that list before it can authorize any edge. -/
inductive Path (rows : List Instruction) : Address → List Nat → Address → Prop
  | refl (address : Address) : Path rows address [] address
  | jump {address next final word} : .jump address next ∈ rows →
      Path rows next word final → Path rows address word final
  | save {address next final word group boundary} : .save address group boundary next ∈ rows →
      Path rows next word final → Path rows address word final
  | scalar {address next final word value} : .scalar address value next ∈ rows →
      Path rows next word final → Path rows address (value :: word) final
  | any {address next final word value} : .any address next ∈ rows →
      Path rows next word final → Path rows address (value :: word) final
  | class_ {address next final word value ranges} : .class_ address ranges next ∈ rows →
      value ∈ classLetters ranges →
      Path rows next word final → Path rows address (value :: word) final
  | left {address first second final word} : .split address first second ∈ rows →
      Path rows first word final → Path rows address word final
  | right {address first second final word} : .split address first second ∈ rows →
      Path rows second word final → Path rows address word final

theorem Path.weaken {before after : List Instruction} (included : before ⊆ after)
    {address final : Address} {word : List Nat} (path : Path before address word final) :
    Path after address word final := by
  induction path with
  | refl address => exact .refl address
  | jump member _ ih => exact .jump (included member) ih
  | save member _ ih => exact .save (included member) ih
  | scalar member _ ih => exact .scalar (included member) ih
  | any member _ ih => exact .any (included member) ih
  | class_ member letter _ ih => exact .class_ (included member) letter ih
  | left member _ ih => exact .left (included member) ih
  | right member _ ih => exact .right (included member) ih

theorem Path.append {rows : List Instruction} {address middle final : Address}
    {first second : List Nat} (before : Path rows address first middle)
    (after : Path rows middle second final) : Path rows address (first ++ second) final := by
  induction before with
  | refl => exact after
  | jump member _ ih => exact .jump member (ih after)
  | save member _ ih => exact .save member (ih after)
  | scalar member _ ih => exact .scalar member (ih after)
  | any member _ ih => exact .any member (ih after)
  | class_ member letter _ ih => exact .class_ member letter (ih after)
  | left member _ ih => exact .left member (ih after)
  | right member _ ih => exact .right member (ih after)

/-- A compiler continuation can be prefixed by either priority of a split.
This theorem concerns recognition only and deliberately retains both edges. -/
theorem choice_left {rows : List Instruction} (address first second final : Address)
    (word : List Nat) (greedy : Bool)
    (member : (if greedy then Instruction.split address first second else .split address second first) ∈ rows)
    (path : Path rows first word final) : Path rows address word final := by
  cases greedy
  · exact .right member path
  · exact .left member path

theorem choice_right {rows : List Instruction} (address first second final : Address)
    (word : List Nat) (greedy : Bool)
    (member : (if greedy then Instruction.split address first second else .split address second first) ∈ rows)
    (path : Path rows second word final) : Path rows address word final := by
  cases greedy
  · exact .left member path
  · exact .right member path

/-- A repeated body can share one graph while traversing it any finite number
of times. Nullable body traversals are not dropped at recognition level. -/
theorem repetition_paths (rows : List Instruction) (repeatAt body exit : Address) (greedy : Bool)
    (L : Language Nat) (splitRow : choice repeatAt body exit greedy ∈ rows)
    (bodyPaths : ∀ word ∈ L, Path rows body word repeatAt)
    (parts : List (List Nat)) (allParts : ∀ part ∈ parts, part ∈ L) :
    Path rows repeatAt parts.flatten exit := by
  induction parts with
  | nil =>
      exact choice_right repeatAt body exit exit [] greedy splitRow (.refl _)
  | cons part rest ih =>
      have first := bodyPaths part (allParts part (by simp))
      have after := ih (fun word member => allParts word (by simp [member]))
      exact choice_left repeatAt body exit exit _ greedy splitRow (first.append after)

/-- Every word in the independently interpreted regular language traverses
the actual emitted rows to their declared continuation. This includes nested
nullable stars, priorities and captures; it makes no claim about selection. -/
theorem emit_preserves (pattern : Pattern) (regex : Regex Nat)
    (erased : erase? pattern = some regex) (word : List Nat) (accepted : word ∈ language regex)
    (continuation address : Address) : Path (emit pattern continuation address) address word continuation := by
  induction pattern generalizing regex word continuation address with
  | zero => simp [erase?] at erased; subst regex; simp [language] at accepted
  | epsilon =>
      simp only [erase?, Option.some.injEq] at erased
      subst regex
      have empty : word = [] := by simpa [language] using accepted
      subst word
      exact .jump (by simp [emit]) (.refl _)
  | literal scalar =>
      simp only [erase?, Option.some.injEq] at erased
      subst regex
      have single : word = [scalar] := accepted
      subst word
      exact .scalar (by simp [emit]) (.refl _)
  | any =>
      simp only [erase?, Option.some.injEq] at erased
      subst regex
      obtain ⟨value, rfl⟩ := accepted
      exact .any (by simp [emit]) (.refl _)
  | class_ ranges =>
      simp only [erase?, Option.some.injEq] at erased
      subst regex
      obtain ⟨value, member, rfl⟩ := (mem_language_oneOf _ _).mp accepted
      exact .class_ (by simp [emit]) member (.refl _)
  | assertion name => simp [erase?] at erased
  | seq first second ihFirst ihSecond =>
      cases left : erase? first with
      | none => simp [erase?, left] at erased
      | some leftRegex =>
          cases right : erase? second with
          | none => simp [erase?, left, right] at erased
          | some rightRegex =>
              simp [erase?, left, right] at erased
              subst regex
              obtain ⟨prefixWord, prefixMem, suffixWord, suffixMem, rfl⟩ := Language.mem_mul.mp accepted
              have before := ihFirst leftRegex left prefixWord prefixMem (.right address) (.left address)
              have after := ihSecond rightRegex right suffixWord suffixMem continuation (.right address)
              have before' : Path (emit (.seq first second) continuation address)
                  (.left address) prefixWord (.right address) :=
                before.weaken (by intro instruction member; simp [emit, member])
              have after' : Path (emit (.seq first second) continuation address)
                  (.right address) suffixWord continuation :=
                after.weaken (by intro instruction member; simp [emit, member])
              exact .jump (by simp [emit]) (before'.append after')
  | alt first second ihFirst ihSecond =>
      cases left : erase? first with
      | none => simp [erase?, left] at erased
      | some leftRegex =>
          cases right : erase? second with
          | none => simp [erase?, left, right] at erased
          | some rightRegex =>
              simp [erase?, left, right] at erased
              subst regex
              change word ∈ language leftRegex ∨ word ∈ language rightRegex at accepted
              rcases accepted with inLeft | inRight
              · exact .left (second := .right address) (by simp [emit])
                  ((ihFirst leftRegex left word inLeft continuation (.left address)).weaken
                    (by intro instruction member; simp [emit, member]))
              · exact .right (first := .left address) (by simp [emit])
                  ((ihSecond rightRegex right word inRight continuation (.right address)).weaken
                    (by intro instruction member; simp [emit, member]))
  | star body greedy ih =>
      cases bodyErase : erase? body with
      | none => simp [erase?, bodyErase] at erased
      | some bodyRegex =>
          simp [erase?, bodyErase] at erased
          subst regex
          obtain ⟨parts, rfl, partMem⟩ := Language.mem_kstar.mp accepted
          have repeatPath : ∀ parts : List (List Nat), (∀ part ∈ parts, part ∈ language bodyRegex) →
              Path (emit (.star body greedy) continuation address)
                (.loop address) parts.flatten continuation := by
            intro parts allParts
            apply repetition_paths _ (.loop address) (.body address) continuation greedy (language bodyRegex)
              (by cases greedy <;> simp [emit, choice]) ?_ parts allParts
            intro part member
            exact (ih bodyRegex bodyErase part member (.loop address) (.body address)).weaken
              (by intro instruction member; simp [emit, member])
          cases parts with
          | nil =>
              apply choice_right address (.body address) continuation continuation [] greedy
              · cases greedy <;> simp [emit, choice]
              · exact .refl _
          | cons part rest =>
              have firstPath := ih bodyRegex bodyErase part (partMem part (by simp))
                (.loop address) (.body address)
              have firstPath' : Path (emit (.star body greedy) continuation address)
                  (.body address) part (.loop address) :=
                firstPath.weaken (by intro instruction member; simp [emit, member])
              have restPath := repeatPath rest (fun part member => partMem part (by simp [member]))
              apply choice_left address (.body address) continuation continuation _ greedy
              · cases greedy <;> simp [emit, choice]
              · exact firstPath'.append restPath
  | optional body greedy ih =>
      cases bodyErase : erase? body with
      | none => simp [erase?, bodyErase] at erased
      | some bodyRegex =>
          simp [erase?, bodyErase] at erased
          subst regex
          change word ∈ language bodyRegex ∨ word ∈ (1 : Language Nat) at accepted
          rcases accepted with bodyWord | emptyWord
          · apply choice_left address (.body address) continuation continuation word greedy
            · cases greedy <;> simp [emit, choice]
            · exact (ih bodyRegex bodyErase word bodyWord continuation (.body address)).weaken
                (by intro instruction member; simp [emit, member])
          · have empty : word = [] := emptyWord
            subst word
            apply choice_right address (.body address) continuation continuation [] greedy
            · cases greedy <;> simp [emit, choice]
            · exact .refl _
  | plus body greedy ih =>
      cases bodyErase : erase? body with
      | none => simp [erase?, bodyErase] at erased
      | some bodyRegex =>
          simp [erase?, bodyErase] at erased
          subst regex
          obtain ⟨firstWord, firstMem, repeatWord, repeatMem, rfl⟩ := Language.mem_mul.mp accepted
          obtain ⟨parts, rfl, allParts⟩ := Language.mem_kstar.mp repeatMem
          have bodyPaths : ∀ word ∈ language bodyRegex,
              Path (emit (.plus body greedy) continuation address) (.body address) word (.loop address) := by
            intro part member
            exact (ih bodyRegex bodyErase part member (.loop address) (.body address)).weaken
              (by intro instruction member; simp [emit, member])
          have restPath := repetition_paths (emit (.plus body greedy) continuation address)
            (.loop address) (.body address) continuation greedy (language bodyRegex)
            (by cases greedy <;> simp [emit, choice]) bodyPaths parts allParts
          exact .jump (by simp [emit]) ((bodyPaths firstWord firstMem).append restPath)
  | capture group body ih =>
      have bodyPath := ih regex erased word accepted (.close address) (.body address)
      have bodyPath' : Path (emit (.capture group body) continuation address)
          (.body address) word (.close address) :=
        bodyPath.weaken (by intro instruction member; simp [emit, member])
      simpa using Path.save (group := group) (boundary := .start) (next := .body address) (by simp [emit])
        (bodyPath'.append (.save (group := group) (boundary := .finish)
          (next := continuation) (by simp [emit]) (.refl _)))

theorem compile_preserves (pattern : Pattern) (regex : Regex Nat)
    (erased : erase? pattern = some regex) (word : List Nat) (accepted : word ∈ language regex) :
    Path (compile pattern).rows (compile pattern).entry word .ending :=
  (emit_preserves pattern regex erased word accepted .ending .root).weaken
    (by intro instruction member; simp [compile, member])

/-- A path cannot invent a word outside an independently supplied language
invariant that is established for every instruction it actually traverses. -/
theorem Path.sound {rows : List Instruction} {environment : Address → Language Nat}
    (instructions : ∀ instruction ∈ rows, RowSound environment instruction)
    {address final : Address} {word : List Nat} (path : Path rows address word final)
    (terminalWord : [] ∈ environment final) : word ∈ environment address := by
  induction path with
  | refl address => exact terminalWord
  | jump member _ ih => exact instructions _ member [] _ (.jump _ _) _ (ih terminalWord)
  | save member _ ih => exact instructions _ member [] _ (.save _ _ _ _) _ (ih terminalWord)
  | scalar member _ ih => exact instructions _ member [_] _ (.scalar _ _ _) _ (ih terminalWord)
  | any member _ ih => exact instructions _ member [_] _ (.any _ _ _) _ (ih terminalWord)
  | class_ member letter _ ih => exact instructions _ member [_] _ (.class_ _ _ _ _ letter) _ (ih terminalWord)
  | left member _ ih => exact instructions _ member [] _ (.left _ _ _) _ (ih terminalWord)
  | right member _ ih => exact instructions _ member [] _ (.right _ _ _) _ (ih terminalWord)

/-- Every complete path of an emitted fragment reflects to the independent
source recognition language. The continuation is outside the fragment's owned
address subtree, as guaranteed by all recursive calls of `compile`. -/
theorem emit_reflects (pattern : Pattern) (regex : Regex Nat)
    (erased : erase? pattern = some regex) (word : List Nat) (continuation address : Address)
    (outside : ¬ Within address continuation)
    (path : Path (emit pattern continuation address) address word continuation) : word ∈ language regex := by
  have accepted := path.sound (emit_rows_sound pattern regex erased 1 continuation address outside)
    (by simp)
  rw [meaning_entry _ _ _ _ outside, sourceLanguage_of_erased pattern regex erased, mul_one] at accepted
  exact accepted

theorem emit_recognition_iff (pattern : Pattern) (regex : Regex Nat)
    (erased : erase? pattern = some regex) (word : List Nat) (continuation address : Address)
    (outside : ¬ Within address continuation) :
    Path (emit pattern continuation address) address word continuation ↔ word ∈ language regex :=
  ⟨emit_reflects pattern regex erased word continuation address outside,
    fun accepted => emit_preserves pattern regex erased word accepted continuation address⟩

theorem compile_reflects (pattern : Pattern) (regex : Regex Nat)
    (erased : erase? pattern = some regex) (word : List Nat)
    (path : Path (compile pattern).rows (compile pattern).entry word .ending) : word ∈ language regex := by
  have outside : ¬ Within .root .ending := by intro inside; cases inside
  have invariant : ∀ instruction ∈ (compile pattern).rows,
      RowSound (meaning pattern 1 .root .ending) instruction := by
    intro instruction member
    simp only [compile, List.mem_cons] at member
    rcases member with rfl | member
    · intro prefixWord target edge
      cases edge
    · exact emit_rows_sound pattern regex erased 1 .ending .root outside instruction member
  have accepted := path.sound invariant (by simp)
  change word ∈ meaning pattern 1 .root .ending .root at accepted
  rw [meaning_entry _ _ _ _ outside, sourceLanguage_of_erased pattern regex erased, mul_one] at accepted
  exact accepted

/-- General two-sided recognition adequacy of the actual symbolic-address
compiler, for every source pattern with an assertion-free regular erasure. -/
theorem compile_recognition_iff (pattern : Pattern) (regex : Regex Nat)
    (erased : erase? pattern = some regex) (word : List Nat) :
    Path (compile pattern).rows (compile pattern).entry word .ending ↔ word ∈ language regex :=
  ⟨compile_reflects pattern regex erased word, compile_preserves pattern regex erased word⟩

theorem compile_matches_derivative (pattern : Pattern) (regex : Regex Nat)
    (erased : erase? pattern = some regex) (word : List Nat) :
    Path (compile pattern).rows (compile pattern).entry word .ending ↔ fullMatch regex word = true :=
  (compile_recognition_iff pattern regex erased word).trans (fullMatch_correct regex word).symm

/-- Introducing a capture changes graph rows and capture observations, but not
recognition of the enclosed assertion-free language. -/
theorem capture_conservative_for_recognition (group : Nat) (body : Pattern) (regex : Regex Nat)
    (erased : erase? body = some regex) (word : List Nat) :
    Path (compile (.capture group body)).rows .root word .ending ↔
      Path (compile body).rows .root word .ending :=
  (compile_recognition_iff (.capture group body) regex erased word).trans
    (compile_recognition_iff body regex erased word).symm

theorem repetition_preference_conservative_for_recognition (body : Pattern) (regex : Regex Nat)
    (erased : erase? body = some regex) (greedy : Bool) (word : List Nat) :
    Path (compile (.star body greedy)).rows .root word .ending ↔
      Path (compile (.star body (!greedy))).rows .root word .ending :=
  (compile_recognition_iff (.star body greedy) regex.star (by simp [erase?, erased]) word).trans
    (compile_recognition_iff (.star body (!greedy)) regex.star (by simp [erase?, erased]) word).symm

/-- Alternative order is irrelevant only at this stated recognition
observation. It is not a selected-span or capture congruence. -/
theorem alternative_order_conservative_for_recognition (first second : Pattern) (left right : Regex Nat)
    (leftErase : erase? first = some left) (rightErase : erase? second = some right) (word : List Nat) :
    Path (compile (.alt first second)).rows .root word .ending ↔
      Path (compile (.alt second first)).rows .root word .ending := by
  have before := compile_recognition_iff (.alt first second) (left + right)
    (by simp [erase?, leftErase, rightErase]) word
  have after := compile_recognition_iff (.alt second first) (right + left)
    (by simp [erase?, leftErase, rightErase]) word
  have commutes : word ∈ language (left + right) ↔ word ∈ language (right + left) := by
    change (word ∈ language left ∨ word ∈ language right) ↔ (word ∈ language right ∨ word ∈ language left)
    exact or_comm
  exact before.trans (commutes.trans after.symm)

theorem duplicate_alternative_conservative_for_recognition (body : Pattern) (regex : Regex Nat)
    (erased : erase? body = some regex) (word : List Nat) :
    Path (compile (.alt body body)).rows .root word .ending ↔ Path (compile body).rows .root word .ending := by
  have before := compile_recognition_iff (.alt body body) (regex + regex) (by simp [erase?, erased]) word
  have idempotent : word ∈ language (regex + regex) ↔ word ∈ language regex := by
    change (word ∈ language regex ∨ word ∈ language regex) ↔ word ∈ language regex
    simp
  exact before.trans (idempotent.trans (compile_recognition_iff body regex erased word).symm)

/-- Optional has a derived recognition meaning, although its native graph
keeps a direct body/exit split instead of compiling an alternative subtree. -/
theorem optional_recognition_elaboration (body : Pattern) (greedy : Bool) (regex : Regex Nat)
    (erased : erase? body = some regex) (word : List Nat) :
    Path (compile (.optional body greedy)).rows .root word .ending ↔
      Path (compile (.alt body .epsilon)).rows .root word .ending :=
  (compile_recognition_iff (.optional body greedy) (regex + 1) (by simp [erase?, erased]) word).trans
    (compile_recognition_iff (.alt body .epsilon) (regex + 1) (by simp [erase?, erased]) word).symm

/-- Plus shares a single body in its actual graph; its recognized language
is the same as body followed by star. No capture-selection equivalence is
inferred from this recognition-only elaboration. -/
theorem plus_recognition_elaboration (body : Pattern) (greedy : Bool) (regex : Regex Nat)
    (erased : erase? body = some regex) (word : List Nat) :
    Path (compile (.plus body greedy)).rows .root word .ending ↔
      Path (compile (.seq body (.star body greedy))).rows .root word .ending :=
  (compile_recognition_iff (.plus body greedy) (regex * regex.star) (by simp [erase?, erased]) word).trans
    (compile_recognition_iff (.seq body (.star body greedy)) (regex * regex.star) (by simp [erase?, erased]) word).symm

/-- The pre-existing recognition expressions embed into canonical authored
pattern values. This is an authoring adapter, not another graph compiler. -/
def ofRecognition : Regex Nat → Pattern
  | .zero => .zero
  | .epsilon => .epsilon
  | .char (.literal scalar) => .literal scalar
  | .char .any => .any
  | .plus first second => .alt (ofRecognition first) (ofRecognition second)
  | .comp first second => .seq (ofRecognition first) (ofRecognition second)
  | .star body => .star (ofRecognition body) true

theorem erase_ofRecognition (regex : Regex Nat) : erase? (ofRecognition regex) = some regex := by
  induction regex with
  | zero | epsilon => rfl
  | char atom => cases atom <;> rfl
  | plus first second ihFirst ihSecond => simp [ofRecognition, erase?, ihFirst, ihSecond]
  | comp first second ihFirst ihSecond => simp [ofRecognition, erase?, ihFirst, ihSecond]
  | star body ih => simp [ofRecognition, erase?, ih]

/-- Every old recognition expression has an actual emitted graph with exactly
the same language. This does not assert capture-history or C-code equivalence. -/
theorem recognition_embedding_conservative (regex : Regex Nat) (word : List Nat) :
    Path (compile (ofRecognition regex)).rows .root word .ending ↔ word ∈ language regex :=
  compile_recognition_iff (ofRecognition regex) regex (erase_ofRecognition regex) word

namespace Controls

theorem nested_nullable_capture_accepts :
    Path (compile (.star (.capture 1 (.alt (.literal 97) .epsilon)) true)).rows .root [97, 97] .ending := by
  apply compile_preserves _ ((literal 97 + 1).star) rfl
  exact (fullMatch_correct _ _).mp (by decide)

theorem nested_nullable_capture_does_not_invent_letter :
    ¬ Path (compile (.star (.capture 1 (.alt (.literal 97) .epsilon)) true)).rows .root [98] .ending := by
  intro path
  have impossible := (compile_matches_derivative _ ((literal 97 + 1).star) rfl [98]).mp path
  contradiction

theorem sequence_and_reversed_priority_both_recognize :
    let source := Pattern.seq (.capture 4 (.alt (.literal 97) (.literal 98))) (.star (.literal 99) false)
    Path (compile source).rows .root [98, 99, 99] .ending := by
  apply compile_preserves _ ((literal 97 + literal 98) * (literal 99).star) rfl
  exact (fullMatch_correct _ _).mp (by decide)

theorem nested_dedicated_plus_optional_capture_accepts :
    let source := Pattern.plus (.optional (.capture 3 (.alt (.literal 97) .epsilon)) false) true
    Path (compile source).rows .root [97, 97] .ending := by
  apply compile_preserves _ (((literal 97 + 1) + 1) * ((literal 97 + 1) + 1).star) rfl
  exact (fullMatch_correct _ _).mp (by decide)

theorem dedicated_optional_of_plus_accepts :
    let source := Pattern.optional (.plus (.capture 2 (.literal 98)) false) true
    Path (compile source).rows .root [98, 98] .ending := by
  apply compile_preserves _ (literal 98 * (literal 98).star + 1) rfl
  exact (fullMatch_correct _ _).mp (by decide)

theorem nested_dedicated_plus_optional_does_not_invent_letter :
    let source := Pattern.plus (.optional (.capture 3 (.alt (.literal 97) .epsilon)) false) true
    ¬ Path (compile source).rows .root [98] .ending := by
  dsimp only
  intro path
  have impossible := (compile_matches_derivative _
    (((literal 97 + 1) + 1) * ((literal 97 + 1) + 1).star) rfl [98]).mp path
  contradiction

theorem dedicated_plus_of_nonnullable_body_rejects_empty :
    ¬ Path (compile (.plus (.literal 97) true)).rows .root [] .ending := by
  intro path
  have impossible := (compile_matches_derivative _ (literal 97 * (literal 97).star) rfl []).mp path
  contradiction

/-- The fragment's freshness condition is earned by the actual compiler, not
an extra restriction on user patterns. Aliasing its exit with its entry would
allow a zero-step path even for the empty language. -/
theorem aliased_fragment_exit_would_invent_empty_word :
    Path (emit .zero .root .root) .root [] .root ∧ [] ∉ language (0 : Regex Nat) :=
  ⟨.refl _, by simp [language]⟩

/-- Forward realizability alone does not exclude a corrupt extra row. -/
theorem extra_instruction_keeps_old_word_but_invents_new :
    let rows := (compile (.literal 97)).rows ++ [.scalar .root 98 .ending]
    Path rows .root [97] .ending ∧ Path rows .root [98] .ending ∧ [98] ∉ language (literal 97) := by
  refine ⟨.scalar (by decide) (.refl _), .scalar (by decide) (.refl _), ?_⟩
  decide

theorem capture_lowering_changes_steps_not_recognition (group : Nat) (word : List Nat) :
    (compile (.capture group (.literal 97))).rows.length = 4 ∧
    (compile (.literal 97)).rows.length = 2 ∧
    (Path (compile (.capture group (.literal 97))).rows .root word .ending ↔
      Path (compile (.literal 97)).rows .root word .ending) :=
  ⟨rfl, rfl, capture_conservative_for_recognition group (.literal 97) (literal 97) rfl word⟩

end Controls

#print axioms emit_preserves
#print axioms emit_rows_sound
#print axioms emit_reflects
#print axioms compile_recognition_iff
#print axioms compile_matches_derivative
#print axioms capture_conservative_for_recognition
#print axioms repetition_preference_conservative_for_recognition
#print axioms alternative_order_conservative_for_recognition
#print axioms duplicate_alternative_conservative_for_recognition
#print axioms recognition_embedding_conservative
#print axioms optional_recognition_elaboration
#print axioms plus_recognition_elaboration

end Mettapedia.GSLT.LanguageDef.RegexSelection.Recognition
