import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBProofRunSoundness
import Mettapedia.Languages.MM0.Formats.MMB.MachineCost

/-!
# Complete MMB assertion runs and original kernel derivability

The retained binary machine's command soundness is composed across complete
runs, including stored evidence and conversion obligations. A successful
statement match fixes both the conclusion and the ordered hypotheses.

The declarations below concern `Formats.MMB.run`, `checkAssertion` and their
shared retained assertion trajectory.
Correspondence of the authored MeTTa proof runner with this machine is a
separate execution obligation; successful lexical or command decoding alone
does not establish it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ExecutedSoundness

open Formats.MMB Kernel
open MMBMachineSoundness MMBDependencySoundness MMBStateScopeSoundness
open MMBInitializationSoundness MMBRunSoundness MMBUnificationSoundness

/-- The actual decoded table declarations agree with an independently
supplied kernel environment. Definition bodies also earn their original
kernel typing judgment in the complete parameter-and-dummy context. -/
structure KernelDeclarations (signature : TermSignature)
    (definitions : Definition.Signature) (theorems : TheoremSignature)
    (tables : Tables) : Prop where
  terms : ∀ (term : Nat) (entry : TermEntry), tables.terms[term]? = some entry →
    ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, body) ∧
      signature term = some declaration
  definitions : ∀ (term : Nat) (entry : TermEntry) (commands : List UnifyCmd),
    tables.terms[term]? = some entry → entry.value = some commands →
    ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, some body) ∧
      signature term = some declaration ∧ definitions term = some body ∧
      Preterm.HasType signature (declaration.arguments ++ body.dummies.map Binder.bound)
        body.expression [] declaration.resultSort
  theorems : ∀ (index : Nat) (entry : ThmEntry), tables.thms[index]? = some entry →
    ∃ declaration, Statements.theoremDecl tables.terms entry = some declaration ∧
      theorems index = some declaration
  arities : ∀ term declaration, signature term = some declaration →
    Statements.arityOf tables.terms term = some declaration.arguments.length

section Soundness

variable {signature : TermSignature} {definitions : Definition.Signature}
  {theorems : TheoremSignature} {tables : Tables}

/-- Complete runs preserve the original kernel evidence, while all commands
share the statement's complete dummy context. No pending conversion goal
becomes completed evidence merely because its command was executed. -/
theorem run_preserves_evidence
    (declarations : KernelDeclarations signature definitions theorems tables)
    (hypotheses : List Preterm) (args : List ExprType) (seen : List Nat)
    (commands : List ProofCmd) (before after : Formats.MMB.State)
    (boundCounter : before.nextBound = (Statements.boundPositions args).length + seen.length)
    (variableCounter : before.varCount = args.length + seen.length)
    (typed : TypedStore signature
      (Statements.context args ++ (seen ++ dummySorts commands).map Binder.bound) before.store)
    (ranked : RankedStore
      (Statements.context args ++ (seen ++ dummySorts commands).map Binder.bound) before.store)
    (stack : StackSound signature definitions theorems
      (Statements.context args ++ (seen ++ dummySorts commands).map Binder.bound)
      hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems
      (Statements.context args ++ (seen ++ dummySorts commands).map Binder.bound)
      hypotheses before.store before.heap)
    (executed : run tables .assertion before commands = some after)
    (original : after.hyps.reverse.mapM (Soundness.decode after.store) = some hypotheses) :
    let context := Statements.context args ++ (seen ++ dummySorts commands).map Binder.bound
    TypedStore signature context after.store ∧ RankedStore context after.store ∧
      StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  dsimp only
  induction commands generalizing seen before with
  | nil =>
      cases Option.some.inj executed
      exact ⟨typed, ranked, stack, heap⟩
  | cons command commands ih =>
      obtain ⟨middle, advanced, continued⟩ := Option.bind_eq_some_iff.mp executed
      have preserved := MMBProofRunSoundness.step_preserves_evidence
        signature definitions theorems hypotheses tables declarations.terms
        declarations.definitions declarations.theorems declarations.arities
        args seen commands command before middle after boundCounter variableCounter
        typed ranked stack heap advanced continued original
      have counters := step_counters tables .assertion before middle command advanced
      have nextBound : middle.nextBound = (Statements.boundPositions args).length +
          (seen ++ dummySorts [command]).length := by
        rw [counters.1, boundCounter, List.length_append, Nat.add_assoc]
      have varCount : middle.varCount = args.length + (seen ++ dummySorts [command]).length := by
        rw [counters.2, variableCounter, List.length_append, Nat.add_assoc]
      have sameContext : Statements.context args ++ (seen ++ dummySorts (command :: commands)).map Binder.bound =
          Statements.context args ++ ((seen ++ dummySorts [command]) ++ dummySorts commands).map Binder.bound := by
        rw [dummySorts_cons, List.append_assoc]
      rw [sameContext] at preserved ⊢
      exact ih (seen ++ dummySorts [command]) middle nextBound varCount
        preserved.1 preserved.2.1 preserved.2.2.1 preserved.2.2.2 continued

/-- Argument loading supplies completed typed heap entries and no proof or
conversion assumptions. -/
theorem initialized_evidence (hypotheses : List Preterm) (args : List ExprType)
    (dummies : List Nat) (loaded : Formats.MMB.State)
    (initialized : loadArgs tables.sorts args = some loaded) :
    let context := Statements.context args ++ dummies.map Binder.bound
    TypedStore signature context loaded.store ∧ RankedStore context loaded.store ∧
      StackSound signature definitions theorems context hypotheses loaded.store loaded.stack ∧
      HeapSound signature definitions theorems context hypotheses loaded.store loaded.heap := by
  dsimp only
  obtain ⟨_, heapShape, stackShape, _, _, _⟩ :=
    MMBExecution.loadArgs_variable_shape tables.sorts args loaded initialized
  have initial := loadArgs_initial_fixed_context signature tables.sorts args dummies loaded initialized
  refine ⟨initial.1, initial.2, ?_, ?_⟩
  · rw [stackShape]
    exact .empty
  · intro element member
    rw [heapShape] at member
    obtain ⟨position, inside, rfl⟩ := List.mem_map.mp member
    have positionBound : position < args.length := List.mem_range.mp inside
    obtain ⟨storeShape, _, _, _, _, _⟩ :=
      MMBExecution.loadArgs_variable_shape tables.sorts args loaded initialized
    have allocation : loaded.store[position]? = some (⟨.var position, args[position]'positionBound⟩ : Alloc) := by
      rw [storeShape, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem positionBound]
      simp
    obtain ⟨expression, decoded, typed, _⟩ := initial.1.expression position _ allocation
    exact ⟨expression, _, decoded, typed⟩

/-- Successful statement matching fixes the original decoded conclusion,
not merely a well-sorted expression at the final proof pointer. -/
theorem unify_statement_original_conclusion
    (context : Context) (store : List Alloc) (typed : TypedStore signature context store)
    (entry : ThmEntry) (declaration : TheoremDecl)
    (arities : ∀ term termDeclaration, signature term = some termDeclaration →
      Statements.arityOf tables.terms term = some termDeclaration.arguments.length)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (roots : ∀ position < entry.args.length, Soundness.decode store position = some (.var position))
    (position : Nat) (hyps : List Nat) (after : Unifier)
    (accepted : unifyRun store .statement
      ⟨[position], (List.range entry.args.length).map (·, false), [], hyps⟩ entry.unify = some after) :
    Soundness.decode store position = some declaration.conclusion := by
  let fuel := 2 * entry.unify.length + 2
  obtain ⟨value, conclusion, sourceDecl⟩ := Option.bind_eq_some_iff.mp declared
  rcases value with ⟨source, middleSource, remaining⟩
  change (if middleSource.dummies ≠ [] then none else
    (Statements.decodeHyps (Statements.arityOf tables.terms) entry.args.length fuel middleSource remaining).bind
      (fun hypotheses => some (⟨Statements.context entry.args, hypotheses, source⟩ : TheoremDecl))) =
        some declaration at sourceDecl
  split at sourceDecl
  · cases sourceDecl
  · obtain ⟨sources, _, sameDeclaration⟩ := Option.bind_eq_some_iff.mp sourceDecl
    have declarationSame : (⟨Statements.context entry.args, sources, source⟩ : TheoremDecl) = declaration :=
      Option.some.inj sameDeclaration
    obtain ⟨_, commandsBefore, _, consumedRead, _⟩ :=
      Soundness.decodeExpr_source_order (Statements.arityOf tables.terms) entry.args.length fuel
        (Statements.initial entry.args.length) middleSource entry.unify remaining source conclusion
    have expressionAccepted : unifyRun store .statement
        ⟨[position], (List.range entry.args.length).map (·, false), [], hyps⟩
        (commandsBefore ++ remaining) = some after := by rw [← consumedRead]; exact accepted
    obtain ⟨middle, expressionSteps, _⟩ :=
      unifyRun_prefix store .statement _ after commandsBefore remaining expressionAccepted
    have expressionRead : Statements.decodeExpr (Statements.arityOf tables.terms) entry.args.length fuel
        (Statements.initial entry.args.length) (commandsBefore ++ remaining) = some (source, middleSource, remaining) := by
      rw [← consumedRead]
      exact conclusion
    obtain ⟨image, decoded, substituted, _⟩ :=
      decodeExpr_unifies signature context store typed (Statements.arityOf tables.terms) arities Substitution.identity
        .statement (by decide) entry.args.length fuel (Statements.initial entry.args.length) middleSource
        commandsBefore remaining source _ middle position [] expressionRead expressionSteps rfl
        (initial_identity_slots store entry.args.length roots)
    have same := identity_substitution_reflects source image substituted
    simpa only [← declarationSame, same] using decoded

/-- A complete accepted assertion stream supplies a derivation under exactly
its source hypotheses and complete formal-and-dummy context. -/
theorem initialized_run_derives
    (declarations : KernelDeclarations signature definitions theorems tables)
    (entry : ThmEntry) (declaration : TheoremDecl) (commands : List ProofCmd)
    (loaded after : Formats.MMB.State) (position : Nat) (unified : Unifier)
    (initialized : loadArgs tables.sorts entry.args = some loaded)
    (executed : run tables .assertion loaded commands = some after)
    (stackShape : after.stack = [.proof position])
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (matched : unifyRun after.store .statement
      ⟨[position], (List.range entry.args.length).map (·, false), [], after.hyps⟩ entry.unify = some unified) :
    Derives signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound)
      declaration.hypotheses declaration.conclusion := by
  have initial := initialized_evidence (signature := signature) (definitions := definitions)
    (theorems := theorems) declaration.hypotheses entry.args (dummySorts commands) loaded initialized
  have original := statement_original_hypotheses_of_run signature tables declarations.terms
    entry declaration commands loaded after position unified initialized executed declarations.arities declared matched
  obtain ⟨_, _, _, _, variableCounter, boundCounter⟩ :=
    MMBExecution.loadArgs_variable_shape tables.sorts entry.args loaded initialized
  have preserved := run_preserves_evidence declarations declaration.hypotheses entry.args [] commands loaded after
    (by simpa using boundCounter) (by simpa using variableCounter)
    initial.1 initial.2.1 initial.2.2.1 initial.2.2.2 executed original
  simp only [List.nil_append] at preserved
  rw [stackShape] at preserved
  obtain ⟨expression, decoded, derived⟩ := preserved.2.2.1.final_proof
  have conclusionRead := unify_statement_original_conclusion _ after.store preserved.1
    entry declaration declarations.arities declared
    (run_initialized_public_roots tables .assertion entry.args loaded after commands initialized executed)
    position after.hyps unified matched
  have same : expression = declaration.conclusion := Option.some.inj (decoded.symm.trans conclusionRead)
  simpa only [same] using derived

/-- Successful theorem acceptance exposes the original initialized run,
completed singleton proof stack, and successful statement unification. -/
theorem checkAssertion_theorem_witnesses (entry : ThmEntry) (commands : List ProofCmd)
    (accepted : checkAssertion tables entry commands false = true) :
    ∃ loaded after position unified,
      loadArgs tables.sorts entry.args = some loaded ∧
      run tables .assertion loaded commands = some after ∧
      after.stack = [.proof position] ∧
      unifyRun after.store .statement
        ⟨[position], (List.range entry.args.length).map (·, false), [], after.hyps⟩ entry.unify = some unified := by
  cases initialized : loadArgs tables.sorts entry.args with
  | none => simp [checkAssertion, initialized] at accepted
  | some loaded =>
      cases executed : run tables .assertion loaded commands with
      | none => simp [checkAssertion, initialized, executed] at accepted
      | some after =>
          cases stackShape : after.stack with
          | nil => simp [checkAssertion, finishAssertion, initialized, executed, stackShape] at accepted
          | cons element rest =>
              cases rest with
              | cons next rest => simp [checkAssertion, finishAssertion, initialized, executed, stackShape] at accepted
              | nil =>
                  cases element with
                  | expr position | conv left right | goal left right =>
                      simp [checkAssertion, finishAssertion, initialized, executed, stackShape] at accepted
                  | proof position =>
                      have matched : (unifyRun after.store .statement
                          ⟨[position], (List.range entry.args.length).map (·, false), [], after.hyps⟩ entry.unify).isSome = true := by
                        simp only [checkAssertion, finishAssertion, initialized, executed, Option.bind_some,
                          stackShape, Bool.and_eq_true] at accepted
                        exact accepted.2
                      obtain ⟨unified, unifiedRead⟩ := Option.isSome_iff_exists.mp matched
                      exact ⟨loaded, after, position, unified, rfl, executed, stackShape, unifiedRead⟩

/-- Original theorem acceptance proves precisely the decoded source
conclusion under its original ordered hypotheses. No new acceptance gate is
inserted and no incomplete proof or conversion obligation is accepted. -/
theorem checkAssertion_derives
    (declarations : KernelDeclarations signature definitions theorems tables)
    (entry : ThmEntry) (declaration : TheoremDecl) (commands : List ProofCmd)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (accepted : checkAssertion tables entry commands false = true) :
    Derives signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound)
      declaration.hypotheses declaration.conclusion := by
  obtain ⟨loaded, after, position, unified, initialized, executed, stackShape, matched⟩ :=
    checkAssertion_theorem_witnesses entry commands accepted
  exact initialized_run_derives declarations entry declaration commands loaded after position unified
    initialized executed stackShape declared matched

/-- Acceptance supplies a certificate for the existing kernel checker.
The existence statement does not identify that certificate with the proof
term emitted by a separate MeTTa binary frontend. -/
theorem checkAssertion_kernel_certificate
    (declarations : KernelDeclarations signature definitions theorems tables)
    (entry : ThmEntry) (declaration : TheoremDecl) (commands : List ProofCmd)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (accepted : checkAssertion tables entry commands false = true) :
    ∃ witness, ProofWitness.check signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound)
      declaration.hypotheses witness declaration.conclusion = true := by
  obtain ⟨witness, checked⟩ := (checkAssertion_derives declarations entry declaration commands declared accepted).certificate_exists
  exact ⟨witness, (ProofWitness.check_iff _ _ _ _ _ _ _).mpr checked⟩

/-- A theorem stream cannot accept an underivable decoded claim. This uses
the unchanged acceptance predicate, including all of its refusal cases. -/
theorem checkAssertion_refuses_of_not_derivable
    (declarations : KernelDeclarations signature definitions theorems tables)
    (entry : ThmEntry) (declaration : TheoremDecl) (commands : List ProofCmd)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (notDerived : ¬ Derives signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound)
      declaration.hypotheses declaration.conclusion) :
    checkAssertion tables entry commands false = false := by
  cases accepted : checkAssertion tables entry commands false with
  | false => rfl
  | true => exact False.elim (notDerived (checkAssertion_derives declarations entry declaration commands declared accepted))

/-- An accepted retained execution derives the exact independently decoded
source claim, with its original hypotheses and formal-and-dummy context. The
common trajectory does not change the kernel theory or its declaration tables. -/
theorem retained_assertion_derives
    (declarations : KernelDeclarations signature definitions theorems tables)
    (entry : ThmEntry) (declaration : TheoremDecl) (commands : List ProofCmd)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (fuel : Nat)
    (accepted : assertionVerdict tables entry false
      ((assertionTrajectory tables entry commands).observation fuel).2 = some true) :
    Derives signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound)
      declaration.hypotheses declaration.conclusion :=
  checkAssertion_derives declarations entry declaration commands declared
    (assertionTrajectory_verdict_sound tables entry commands false fuel true accepted)

/-- The same derivability theorem applies directly to continuing a retained
checkpoint, including one stopped inside a unification command. -/
theorem resumed_assertion_derives
    (declarations : KernelDeclarations signature definitions theorems tables)
    (entry : ThmEntry) (declaration : TheoremDecl) (commands : List ProofCmd)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (first extra : Nat)
    (accepted : assertionVerdict tables entry false
      ((eventMachine tables .assertion).continueRun extra
        ((assertionTrajectory tables entry commands).observation first)).2 = some true) :
    Derives signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound)
      declaration.hypotheses declaration.conclusion := by
  rw [← assertionTrajectory_resume] at accepted
  exact retained_assertion_derives declarations entry declaration commands declared (first + extra) accepted

/-- A retained accepted assertion supplies evidence for the original MM0
kernel checker, without installing a shared host logic or an extra axiom. -/
theorem retained_assertion_kernel_certificate
    (declarations : KernelDeclarations signature definitions theorems tables)
    (entry : ThmEntry) (declaration : TheoremDecl) (commands : List ProofCmd)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (fuel : Nat)
    (accepted : assertionVerdict tables entry false
      ((assertionTrajectory tables entry commands).observation fuel).2 = some true) :
    ∃ witness, ProofWitness.check signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound)
      declaration.hypotheses witness declaration.conclusion = true :=
  checkAssertion_kernel_certificate declarations entry declaration commands declared
    (assertionTrajectory_verdict_sound tables entry commands false fuel true accepted)

/-- No amount of resumption accepts an underivable claim. Budget exhaustion
remains inconclusive, so this statement does not turn it into a refusal. -/
theorem retained_assertion_never_accepts_underivable
    (declarations : KernelDeclarations signature definitions theorems tables)
    (entry : ThmEntry) (declaration : TheoremDecl) (commands : List ProofCmd)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (notDerived : ¬ Derives signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound)
      declaration.hypotheses declaration.conclusion)
    (fuel : Nat) :
    assertionVerdict tables entry false
      ((assertionTrajectory tables entry commands).observation fuel).2 ≠ some true := by
  intro accepted
  exact notDerived (retained_assertion_derives declarations entry declaration commands declared fuel accepted)

/-- Counts in the source statement prefix select the exact tables available
before the next declaration. The prefix is physical declaration order. -/
def precedingTables (source : Tables) (preceding : List Statement) : Tables :=
  ⟨source.sorts.take (preceding.countP fun statement => statement.kind == .sort),
    source.terms.take (preceding.countP fun statement => statement.kind == .term),
    source.thms.take (preceding.countP fun statement =>
      statement.kind == .axiomDecl || statement.kind == .theoremDecl)⟩

/-- Whole verification retains the actual verification of every suffix,
with precisely the counters advanced by its original preceding. -/
theorem verifyFrom_after_prefix (source : Tables) (sorts terms theorems : Nat)
    (preceding suffix : List Statement)
    (accepted : verifyFrom source sorts terms theorems (preceding ++ suffix) = true) :
    verifyFrom source
      (sorts + preceding.countP fun statement => statement.kind == .sort)
      (terms + preceding.countP fun statement => statement.kind == .term)
      (theorems + preceding.countP fun statement =>
        statement.kind == .axiomDecl || statement.kind == .theoremDecl) suffix = true := by
  induction preceding generalizing sorts terms theorems with
  | nil => simpa using accepted
  | cons statement preceding ih =>
      cases kind : statement.kind with
      | sort =>
          have continued : verifyFrom source (sorts + 1) terms theorems (preceding ++ suffix) = true := by
            simp only [List.cons_append, verifyFrom, kind, Bool.and_eq_true] at accepted
            exact accepted.2
          simpa [List.countP_cons, kind, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (sorts + 1) terms theorems continued
      | term =>
          cases read : source.terms[terms]? with
          | none => simp [List.cons_append, verifyFrom, kind, read] at accepted
          | some entry =>
              have continued : verifyFrom source sorts (terms + 1) theorems (preceding ++ suffix) = true := by
                simp only [List.cons_append, verifyFrom, kind, read, Bool.and_eq_true] at accepted
                exact accepted.2
              simpa [List.countP_cons, kind, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih sorts (terms + 1) theorems continued
      | axiomDecl | theoremDecl =>
          cases read : source.thms[theorems]? with
          | none => simp [List.cons_append, verifyFrom, kind, read] at accepted
          | some entry =>
              have continued : verifyFrom source sorts terms (theorems + 1) (preceding ++ suffix) = true := by
                simp only [List.cons_append, verifyFrom, kind, read, Bool.and_eq_true] at accepted
                exact accepted.2
              simpa [List.countP_cons, kind, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih sorts terms (theorems + 1) continued

/-- A theorem in a fully verified source file derives its exact source
claim using the declarations available before it. Later table entries cannot
be used to supply this theorem's premise or definition environment. -/
theorem verified_theorem_derives (source : Tables) (preceding suffix : List Statement)
    (statement : Statement) (entry : ThmEntry) (declaration : TheoremDecl)
    (kind : statement.kind = .theoremDecl)
    (read : source.thms[preceding.countP fun row => row.kind == .axiomDecl || row.kind == .theoremDecl]? = some entry)
    (declarations : KernelDeclarations signature definitions theorems (precedingTables source preceding))
    (decoded : Statements.theoremDecl (precedingTables source preceding).terms entry = some declaration)
    (accepted : verify source (preceding ++ statement :: suffix) = true) :
    Derives signature definitions theorems
      (Statements.context entry.args ++ (dummySorts statement.proof).map Binder.bound)
      declaration.hypotheses declaration.conclusion := by
  have continued := verifyFrom_after_prefix source 0 0 0 preceding (statement :: suffix) accepted
  simp only [Nat.zero_add, verifyFrom, kind, read, Bool.and_eq_true] at continued
  have assertion : checkAssertion (precedingTables source preceding) entry statement.proof false = true := by
    exact continued.1
  exact checkAssertion_derives declarations entry declaration statement.proof decoded assertion

end Soundness

namespace Controls

private def type : ExprType := ⟨0, false, ∅⟩
private def termEntry : TermEntry := ⟨0, [], type, none⟩
private def termDeclaration : TermDecl := ⟨[], 0, ∅⟩
private def theoremEntry : ThmEntry := ⟨[], [.term 0]⟩
private def theoremDeclaration : TheoremDecl := ⟨[], [], .term 0⟩
private def tables : Tables := ⟨[⟨false, false, true, false⟩], [termEntry], [theoremEntry]⟩
private def signature : TermSignature := fun index => if index = 0 then some termDeclaration else none
private def theoremSignature : TheoremSignature := fun index => if index = 0 then some theoremDeclaration else none

private theorem declarations : KernelDeclarations signature (fun _ => none) theoremSignature tables := by
  constructor
  · intro index entry read
    cases index with
    | zero =>
        have same : entry = termEntry := by simpa [tables] using read.symm
        subst entry
        exact ⟨termDeclaration, none, by decide, by simp [signature]⟩
    | succ index => simp [tables] at read
  · intro index entry commands read defined
    cases index with
    | zero =>
        have same : entry = termEntry := by simpa [tables] using read.symm
        subst entry
        simp [termEntry] at defined
    | succ index => simp [tables] at read
  · intro index entry read
    cases index with
    | zero =>
        have same : entry = theoremEntry := by simpa [tables] using read.symm
        subst entry
        exact ⟨theoremDeclaration, by decide, by simp [theoremSignature]⟩
    | succ index => simp [tables] at read
  · intro index declaration read
    simp only [signature] at read
    split at read
    · rename_i known
      subst index
      cases Option.some.inj read
      rfl
    · cases read

private def savedCommands : List ProofCmd := [.termSave 0, .ref 0, .thmSave 0, .conv, .refl, .save]
private def convertedCommands : List ProofCmd := [.termSave 0, .ref 0, .thm 0, .conv, .convCut, .refl, .convSave]

theorem theorem_save_and_reference_accepted :
    checkAssertion tables theoremEntry savedCommands false = true := by decide

theorem theorem_save_and_reference_derives :
    Derives signature (fun _ => none) theoremSignature [] [] (.term 0) := by
  simpa [theoremEntry, theoremDeclaration, savedCommands, dummySorts, Statements.context] using
    checkAssertion_derives declarations theoremEntry theoremDeclaration savedCommands
      (by decide) theorem_save_and_reference_accepted

/-- The shared retained interface checks this actual stream across a pause
inside theorem unification, then yields the independently specified MM0 claim. -/
theorem resumed_saved_theorem_derives :
    Derives signature (fun _ => none) theoremSignature [] [] (.term 0) := by
  simpa [theoremEntry, theoremDeclaration, savedCommands, dummySorts, Statements.context] using
    resumed_assertion_derives declarations theoremEntry theoremDeclaration savedCommands
      (by decide) 3 7 (by decide)

theorem completed_conversion_and_saved_evidence_accepted :
    checkAssertion tables theoremEntry convertedCommands false = true := by decide

theorem completed_conversion_and_saved_evidence_derives :
    Derives signature (fun _ => none) theoremSignature [] [] (.term 0) := by
  simpa [theoremEntry, theoremDeclaration, convertedCommands, dummySorts, Statements.context] using
    checkAssertion_derives declarations theoremEntry theoremDeclaration convertedCommands
      (by decide) completed_conversion_and_saved_evidence_accepted

theorem unfinished_conversion_has_a_run_but_is_refused :
    (run tables .assertion ⟨[], [], [], [], 0, 0⟩
      [.termSave 0, .ref 0, .thm 0, .conv]).isSome = true ∧
    checkAssertion tables theoremEntry [.termSave 0, .ref 0, .thm 0, .conv] false = false := by decide

theorem future_heap_reference_refused :
    checkAssertion tables theoremEntry [.term 0, .thmSave 0, .save, .ref 2] false = false := by decide

theorem unavailable_theorem_refused :
    checkAssertion tables theoremEntry [.term 0, .thm 1] false = false := by decide

theorem extra_final_stack_entry_refused :
    checkAssertion tables theoremEntry [.term 0, .thm 0, .term 0] false = false := by decide

theorem expression_is_not_a_theorem_proof :
    checkAssertion tables theoremEntry [.term 0] true = true ∧
    checkAssertion tables theoremEntry [.term 0] false = false := by decide

private def repeatedEntry : ThmEntry := ⟨[], [.term 0, .hyp, .term 0, .hyp, .term 0]⟩
private def repeatedDeclaration : TheoremDecl := ⟨[], [.term 0, .term 0], .term 0⟩
private def repeatedCommands : List ProofCmd := [.term 0, .hyp, .term 0, .hyp, .ref 0]

theorem repeated_source_hypotheses_accepted :
    checkAssertion tables repeatedEntry repeatedCommands false = true := by decide

theorem repeated_source_hypotheses_derive_exact_claim :
    Derives signature (fun _ => none) theoremSignature [] [.term 0, .term 0] (.term 0) := by
  simpa [repeatedEntry, repeatedDeclaration, repeatedCommands, dummySorts, Statements.context] using
    checkAssertion_derives declarations repeatedEntry repeatedDeclaration repeatedCommands
      (by decide) repeated_source_hypotheses_accepted

theorem omitted_repeated_hypothesis_refused :
    checkAssertion tables repeatedEntry [.term 0, .hyp, .ref 0] false = false := by decide

theorem recorded_hypothesis_cannot_forge_empty_original_scope :
    checkAssertion tables theoremEntry [.term 0, .hyp, .ref 0] false = false := by decide

private def boundType : ExprType := ⟨0, true, {0}⟩
private def boundEntry : ThmEntry := ⟨[boundType], [.ref 0]⟩
private def boundDeclaration : TheoremDecl := ⟨[.bound 0], [], .var 0⟩
private def boundTables : Tables := ⟨[⟨false, false, true, false⟩], [], [boundEntry]⟩
private def boundSignature : TheoremSignature := fun index => if index = 0 then some boundDeclaration else none

private theorem boundDeclarations : KernelDeclarations (fun _ => none) (fun _ => none) boundSignature boundTables := by
  constructor
  · intro index entry read
    simp [boundTables] at read
  · intro index entry commands read _
    simp [boundTables] at read
  · intro index entry read
    cases index with
    | zero =>
        have same : entry = boundEntry := by simpa [boundTables] using read.symm
        subst entry
        exact ⟨boundDeclaration, by decide, by simp [boundSignature]⟩
    | succ index => simp [boundTables] at read
  · intro index declaration read
    cases read

private def dummyEntry : ThmEntry := ⟨[], [.ref 0]⟩
private def boundCommands : List ProofCmd := [.dummy 0, .ref 0, .thm 0]

theorem bound_parameter_application_accepted :
    checkAssertion boundTables boundEntry [.ref 0, .ref 0, .thm 0] false = true := by decide

theorem bound_parameter_application_derives :
    Derives (fun _ => none) (fun _ => none) boundSignature [.bound 0] [] (.var 0) := by
  simpa [boundEntry, boundDeclaration, boundType, dummySorts, Statements.context,
    Statements.binder, Statements.boundPositions] using
    checkAssertion_derives boundDeclarations boundEntry boundDeclaration [.ref 0, .ref 0, .thm 0]
      (by decide) bound_parameter_application_accepted

/-- Retained execution preserves the original bound-parameter scope. -/
theorem retained_bound_parameter_derives :
    Derives (fun _ => none) (fun _ => none) boundSignature [.bound 0] [] (.var 0) := by
  simpa [boundEntry, boundDeclaration, boundType, dummySorts, Statements.context,
    Statements.binder, Statements.boundPositions] using
    retained_assertion_derives boundDeclarations boundEntry boundDeclaration
      [.ref 0, .ref 0, .thm 0] (by decide) 7 (by decide)

/-- A complete stream cannot publish a dummy as an undeclared public argument. -/
theorem retained_escaping_dummy_refused :
    assertionVerdict boundTables dummyEntry false
      ((assertionTrajectory boundTables dummyEntry boundCommands).observation 7).2 = some false := by
  decide

theorem escaping_dummy_is_not_a_source_argument :
    run boundTables .assertion ⟨[], [], [], [], 0, 0⟩ boundCommands =
      some ⟨[⟨.var 0, boundType⟩], [.proof 0], [.expr 0], [], 1, 1⟩ ∧
    checkAssertion boundTables dummyEntry boundCommands false = false := by decide

private def fileTables : Tables := { tables with thms := [theoremEntry, theoremEntry] }
private def precedingStatements : List Statement := [⟨.sort, []⟩, ⟨.term, []⟩, ⟨.axiomDecl, [.term 0]⟩]
private def theoremStatement : Statement := ⟨.theoremDecl, savedCommands⟩

theorem whole_file_with_prior_axiom_accepted :
    verify fileTables (precedingStatements ++ [theoremStatement]) = true := by decide

theorem whole_file_theorem_derives_from_exact_prefix :
    Derives signature (fun _ => none) theoremSignature [] [] (.term 0) := by
  simpa [theoremEntry, theoremDeclaration, theoremStatement, savedCommands, dummySorts, Statements.context] using
    verified_theorem_derives fileTables precedingStatements [] theoremStatement theoremEntry theoremDeclaration
      rfl rfl (by simpa [precedingTables, precedingStatements, fileTables, tables] using declarations)
      (by decide) whole_file_with_prior_axiom_accepted

theorem whole_file_future_theorem_reference_refused :
    verify fileTables (precedingStatements ++ [⟨.theoremDecl, [.term 0, .thm 1]⟩]) = false := by decide

theorem whole_file_unused_bad_theorem_refused :
    verify { fileTables with thms := [theoremEntry, theoremEntry, theoremEntry] }
      (precedingStatements ++ [⟨.theoremDecl, [.term 0, .thm 1]⟩, theoremStatement]) = false := by decide

theorem whole_file_undeclared_unused_table_entry_refused :
    verify { fileTables with thms := [theoremEntry, theoremEntry, theoremEntry] }
      (precedingStatements ++ [theoremStatement]) = false := by decide

end Controls

end Mettapedia.Languages.MM0.MeTTa.ExecutedSoundness
