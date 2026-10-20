import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaMatching

/-!
# Bidirectional production of finite dependent checking evidence

The producer synthesizes types for eliminations and checks introductions
against an expected type. Its head choices, normalization hints and proposed
conversion recipes are untrusted. Publication replays the entire result with
the existing formation-sensitive checker, including the ambient telescope.

The input here is the existing scoped core syntax. Text parsing, insertion
of implicit arguments and compilation of pattern matching are separate
elaboration stages. Fuel bounds evidence production, not the source judgment;
failure does not establish that the term has no typing derivation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveElaboration

variable {Head : Type} {RootCode : Nat → Type}

abbrev ConversionCode (Head : Type) (RootCode : Nat → Type) (n : Nat) :=
  StructuralConversionCode.Code Head RootCode n

abbrev Code (Head : Type) (RootCode : Nat → Type) (n : Nat) :=
  StructuralTypingReplay.Code Head (ConversionCode Head RootCode) n

/-- Search choices contain no typing proofs. A misleading choice can waste
the producer's budget but cannot bypass the independent final replay. -/
structure Choices (Head : Type) (RootCode : Nat → Type) where
  headType : Head → Option Head
  join : Head → Head → Option Head
  cumulative : Head → Head → Bool
  normalize : {n : Nat} → Nat → Tm Head n → Tm Head n
  conversion : {n : Nat} → Nat → Tm Head n → Tm Head n →
    Option (ConversionCode Head RootCode n)

structure Inferred (Head : Type) (RootCode : Nat → Type) (n : Nat) where
  type : Tm Head n
  evidence : Code Head RootCode n

variable (R : Rules Head) (choices : Choices Head RootCode) [DecidableEq Head]

mutual

/-- Synthesis uses the declarations' actual types, with fresh evidence for
their formation. Cyclic declaration lookup consumes fuel. -/
def synth : Nat → {n : Nat} → Ctx Head n → Tm Head n →
    Option (Inferred Head RootCode n)
  | 0, _, _, _ => none
  | fuel + 1, _, context, term => match term with
    | .var index => some ⟨Ctx.lookup context index, .var⟩
    | .head head => do
        let type ← choices.headType head
        return ⟨.head type, .headType⟩
    | .const name => do
        let type ← R.constantType name
        let formation ← synth fuel .nil type
        match formation.type with
        | .head level => return ⟨liftClosed type, .const level formation.evidence⟩
        | _ => none
    | .pi domain body => do
        let first ← synth fuel context domain
        let second ← synth fuel (.snoc context domain) body
        match first.type, second.type with
        | .head u, .head v => do
            let joined ← choices.join u v
            return ⟨.head joined, .piForm u v first.evidence second.evidence⟩
        | _, _ => none
    | .sigma domain body => do
        let first ← synth fuel context domain
        let second ← synth fuel (.snoc context domain) body
        match first.type, second.type with
        | .head u, .head v => do
            let joined ← choices.join u v
            return ⟨.head joined, .sigmaForm u v first.evidence second.evidence⟩
        | _, _ => none
    | .id carrier left right => do
        let formation ← synth fuel context carrier
        match formation.type with
        | .head level => do
            let first ← check fuel context left carrier
            let second ← check fuel context right carrier
            return ⟨.head level, .idForm level formation.evidence first second⟩
        | _ => none
    | .refl subject => do
        let inferred ← synth fuel context subject
        return ⟨.id inferred.type subject subject, .reflIntro inferred.type inferred.evidence⟩
    | .app (.lam body) argument => do
        let argumentType ← synth fuel context argument
        let bodyType ← synth fuel (.snoc context argumentType.type) body
        let formation ← synth fuel context (.pi argumentType.type bodyType.type)
        match formation.type with
        | .head level =>
            return ⟨inst0 argument bodyType.type,
              .appElim argumentType.type bodyType.type
                (.lamIntro level formation.evidence bodyType.evidence) argumentType.evidence⟩
        | _ => none
    | .app function argument => do
        let inferred ← synth fuel context function
        let viewed := choices.normalize fuel inferred.type
        match viewed with
        | .pi domain body => do
            let functionCode ← align fuel context function inferred.type viewed inferred.evidence
            let argumentCode ← check fuel context argument domain
            return ⟨inst0 argument body, .appElim domain body functionCode argumentCode⟩
        | _ => none
    | .fst pair => do
        let inferred ← synth fuel context pair
        let viewed := choices.normalize fuel inferred.type
        match viewed with
        | .sigma domain body => do
            let pairCode ← align fuel context pair inferred.type viewed inferred.evidence
            return ⟨domain, .fstElim body pairCode⟩
        | _ => none
    | .snd pair => do
        let inferred ← synth fuel context pair
        let viewed := choices.normalize fuel inferred.type
        match viewed with
        | .sigma domain body => do
            let pairCode ← align fuel context pair inferred.type viewed inferred.evidence
            return ⟨inst0 (.fst pair) body, .sndElim domain body pairCode⟩
        | _ => none
    | .lam _ | .pair _ _ => none

/-- An introduction is guided by its expected dependent type. Every changed
type is retained in an explicit conversion node for subsequent replay. -/
def check : Nat → {n : Nat} → Ctx Head n → Tm Head n → Tm Head n →
    Option (Code Head RootCode n)
  | 0, _, _, _, _ => none
  | fuel + 1, _, context, term, expected =>
      let viewed := choices.normalize fuel expected
      match term, viewed with
      | .lam body, .pi domain codomain => do
          let formation ← synth fuel context viewed
          match formation.type with
          | .head level => do
              let bodyCode ← check fuel (.snoc context domain) body codomain
              align fuel context term viewed expected (.lamIntro level formation.evidence bodyCode)
          | _ => none
      | .pair first second, .sigma domain codomain => do
          let formation ← synth fuel context viewed
          match formation.type with
          | .head level => do
              let firstCode ← check fuel context first domain
              let secondCode ← check fuel context second (inst0 first codomain)
              align fuel context term viewed expected
                (.pairIntro level formation.evidence firstCode secondCode)
          | _ => none
      | .refl subject, .id carrier _ _ => do
          let point ← check fuel context subject carrier
          align fuel context term (.id carrier subject subject) expected (.reflIntro carrier point)
      | _, _ => do
          let inferred ← synth fuel context term
          align fuel context term inferred.type expected inferred.evidence

/-- Proposed conversion never changes the subject. The target's formation
is produced independently of the proposed equality recipe. -/
def align : Nat → {n : Nat} → Ctx Head n → Tm Head n → Tm Head n → Tm Head n →
    Code Head RootCode n → Option (Code Head RootCode n)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, _, context, _term, source, target, evidence =>
      if source = target then some evidence
      else
        let cumulative := match source, target with
          | .head first, .head second =>
              if choices.cumulative first second then some (.cumul first evidence) else none
          | _, _ => none
        match cumulative with
        | some lifted => some lifted
        | none => do
            let formation ← synth fuel context target
            match formation.type with
            | .head level => do
                let conversion ← choices.conversion fuel source target
                return .convert source level evidence formation.evidence conversion
            | _ => none

end

/-- Each ambient assumption is checked, including assumptions unused by the
subject. Empty substitutions cannot make malformed contexts disappear. -/
def context : (fuel : Nat) → {n : Nat} → Ctx Head n →
    Option (StructuralTypingReplay.ContextCode Head (ConversionCode Head RootCode) n)
  | _, _, .nil => some .nil
  | fuel, _, .snoc prior type => do
      let earlier ← context fuel prior
      let formation ← synth R choices fuel prior type
      match formation.type with
      | .head level => return .snoc earlier level formation.evidence
      | _ => none

structure Submission (Head : Type) (RootCode : Nat → Type) (n : Nat) where
  context : StructuralTypingReplay.ContextCode Head (ConversionCode Head RootCode) n
  term : Code Head RootCode n

section Publication

variable [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]

variable (decoder : StructuralConversionCode.RootDecoder R.computation)
variable (choices : Choices Head decoder.Code)

def replay {n : Nat} (context : Ctx Head n) (term type : Tm Head n)
    (submission : Submission Head decoder.Code n) : Bool :=
  StructuralTypingReplay.checkJudgment R
    (fun code left right => code.check R.headEq decoder.decode left right)
    context term type submission.context submission.term

/-- The public elaboration boundary retains a submission only after the
existing checker accepts it against the original request. -/
def elaborate {n : Nat} (fuel : Nat) (ambient : Ctx Head n) (term type : Tm Head n) :
    Option (Submission Head decoder.Code n) := do
  let contextCode ← context R choices fuel ambient
  let termCode ← check R choices fuel ambient term type
  let submission := Submission.mk contextCode termCode
  if replay R decoder ambient term type submission then some submission else none

theorem replay_sound {n : Nat} {ambient : Ctx Head n} {term type : Tm Head n}
    {submission : Submission Head decoder.Code n}
    (accepted : replay R decoder ambient term type submission = true) :
    FormationSensitive.Judgment R ambient term type :=
  StructuralTypingReplay.checkJudgment_sound R _
    (fun checked => StructuralConversionCode.Code.check_sound decoder checked) accepted

/-- Soundness is independent of every producer choice, including dishonest
normalization hints or fabricated conversion recipes. -/
theorem elaborate_sound {n : Nat} (fuel : Nat) (ambient : Ctx Head n) (term type : Tm Head n)
    (submission : Submission Head decoder.Code n)
    (produced : elaborate R decoder choices fuel ambient term type = some submission) :
    FormationSensitive.Judgment R ambient term type := by
  cases contextProduced : context R choices fuel ambient with
  | none => simp [elaborate, contextProduced] at produced
  | some contextCode =>
      cases termProduced : check R choices fuel ambient term type with
      | none => simp [elaborate, contextProduced, termProduced] at produced
      | some termCode =>
          by_cases accepted : replay R decoder ambient term type
              (Submission.mk contextCode termCode) = true
          · have same : Submission.mk contextCode termCode = submission := by
              simpa [elaborate, contextProduced, termProduced, accepted] using produced
            subst submission
            exact replay_sound R decoder accepted
          · simp [elaborate, contextProduced, termProduced, accepted] at produced

end Publication

namespace Implicit

open TypedEquality.Normalization.ExecutableSchemaMatching

variable {slots ambient : Nat}

/-- All omitted parameters must have a value. Unlike schema matching's
materialization, elaboration never fills an unresolved slot with a default. -/
def complete : {slots : Nat} → Assignment Head slots ambient → Option (Sub Head slots ambient)
  | 0, _ => some Fin.elim0
  | slots + 1, assignment => do
      let newest ← assignment 0
      let earlier ← complete (fun i : Fin slots => assignment i.succ)
      return Fin.cases newest earlier

omit [DecidableEq Head] in
theorem complete_sound {assignment : Assignment Head slots ambient}
    {substitution : Sub Head slots ambient}
    (filled : complete assignment = some substitution) :
    ∀ index, assignment index = some (substitution index) := by
  induction slots with
  | zero => exact fun index => index.elim0
  | succ slots ih =>
      cases first : assignment 0 with
      | none => simp [complete, first] at filled
      | some newest =>
          cases rest : complete (fun i : Fin slots => assignment i.succ) with
          | none => simp [complete, first, rest] at filled
          | some earlier =>
              have same : Fin.cases newest earlier = substitution := by
                simpa [complete, first, rest] using filled
              subst substitution
              intro index
              refine Fin.cases first (fun prior => ih rest prior) index

/-- Infer from all explicit argument types in order, sharing the existing
matcher's assignment. Repeated parameters must agree. Unsupported patterns,
missing arguments and extra arguments are refused by this producer. -/
def inferArguments (R : Rules Head) (choices : Choices Head RootCode)
    (fuel : Nat) (context : Ctx Head ambient) :
    List (Tm Head slots) → List (Tm Head ambient) → Assignment Head slots ambient →
      Option (Assignment Head slots ambient)
  | [], [], assignment => some assignment
  | pattern :: patterns, argument :: arguments, assignment => do
      let inferred ← synth R choices fuel context argument
      let updated ← run pattern inferred.type assignment
      inferArguments R choices fuel context patterns arguments updated
  | _, _, _ => none

def infer (R : Rules Head) (choices : Choices Head RootCode)
    (fuel : Nat) (context : Ctx Head ambient) (patterns : List (Tm Head slots))
    (arguments : List (Tm Head ambient)) : Option (Sub Head slots ambient) := do
  let assignment ← inferArguments R choices fuel context patterns arguments (fun _ => none)
  complete assignment

/-- The existing telescope application fixes implicit argument order; the
written explicit argument order is then retained by ordinary application. -/
def render (telescope : Ctx Head slots) (substitution : Sub Head slots ambient)
    (function : Tm Head ambient) (arguments : List (Tm Head ambient)) : Tm Head ambient :=
  arguments.foldl Tm.app (TelescopeAbstraction.applyClosed telescope substitution function)

section Publication

variable (R : Rules Head)
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : Choices Head decoder.Code)

structure Result (Head : Type) (RootCode : Nat → Type) (slots ambient : Nat) where
  substitution : Sub Head slots ambient
  submission : Submission Head RootCode ambient

/-- Pattern inference is a producer hint, never a replacement declaration.
The rendered application is checked against the actual function and rules. -/
def elaborate (fuel : Nat) (context : Ctx Head ambient) (telescope : Ctx Head slots)
    (patterns : List (Tm Head slots)) (function : Tm Head ambient)
    (arguments : List (Tm Head ambient)) (expected : Tm Head ambient) :
    Option (Result Head decoder.Code slots ambient) := do
  let substitution ← infer R choices fuel context patterns arguments
  let submission ← FormationSensitiveElaboration.elaborate R decoder choices fuel context
    (render telescope substitution function arguments) expected
  return ⟨substitution, submission⟩

theorem elaborate_sound (fuel : Nat) (context : Ctx Head ambient) (telescope : Ctx Head slots)
    (patterns : List (Tm Head slots)) (function : Tm Head ambient)
    (arguments : List (Tm Head ambient)) (expected : Tm Head ambient)
    (result : Result Head decoder.Code slots ambient)
    (produced : elaborate R decoder choices fuel context telescope patterns function arguments expected =
      some result) :
    FormationSensitive.Judgment R context
      (render telescope result.substitution function arguments) expected := by
  cases inferred : infer R choices fuel context patterns arguments with
  | none => simp [elaborate, inferred] at produced
  | some substitution =>
      cases checked : FormationSensitiveElaboration.elaborate R decoder choices fuel context
          (render telescope substitution function arguments) expected with
      | none => simp [elaborate, inferred, checked] at produced
      | some submission =>
          have same : Result.mk substitution submission = result := by
            simpa [elaborate, inferred, checked] using produced
          subst result
          exact FormationSensitiveElaboration.elaborate_sound R decoder choices fuel context _ _ _ checked

end Publication
end Implicit
end FormationSensitiveElaboration
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
