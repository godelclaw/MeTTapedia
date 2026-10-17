import Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeFormation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeEvidence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitutionEvidence

/-!
# Source-native rho proof admission

Raw proof validity and authored source formation are checked separately.
Contexts, endpoint sorts and the requested judgment remain literal request
fields. The independent meaning is the original rho relation together with
its source endpoint formation; structural congruence is not presumed to
preserve arbitrary raw sorting.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeKernel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open NativeEvidence

inductive SourceSort where
  | proc
  | name
  deriving DecidableEq, Repr

def SourceSort.label : SourceSort → String
  | .proc => "Proc"
  | .name => "Name"

/-- A finite, literal source context. Free-name lookup uses the first matching
entry, so the request does not purport to serialize an arbitrary function. -/
structure Context where
  free : List (String × SourceSort)
  bound : List SourceSort
  deriving DecidableEq, Repr

def Context.freeSort (context : Context) (name : String) : Option String :=
  ((context.free.find? (fun entry => entry.1 == name)).map Prod.snd).map SourceSort.label

def Context.boundSorts (context : Context) : List String := context.bound.map SourceSort.label

/-- Formation uses the original declaration-derived source judgment. -/
def Formed (context : Context) (sort : SourceSort) (p : Pattern) : Prop :=
  (match sort with
   | .proc => NativeFormation.Proc context.freeSort context.boundSorts p
   | .name => NativeFormation.Name context.freeSort context.boundSorts p) ∧
  binderSafeAt "NQuote" context.bound.length p = true

def checkFormed (context : Context) (sort : SourceSort) (p : Pattern) : Bool :=
  (match sort with
   | .proc => NativeFormation.checkProc context.freeSort context.boundSorts p
   | .name => NativeFormation.checkName context.freeSort context.boundSorts p) &&
  binderSafeAt "NQuote" context.bound.length p

theorem checkFormed_exact (context : Context) (sort : SourceSort) (p : Pattern) :
    checkFormed context sort p = true ↔ Formed context sort p := by
  cases sort <;> simp only [checkFormed, Formed, Bool.and_eq_true,
    NativeFormation.checkProc_exact, NativeFormation.checkName_exact]

theorem formed_canonical {context : Context} {sort : SourceSort} {p : Pattern}
    (typed : Formed context sort p) : p.hasCanonicalBinderMetadata = true := by
  cases sort with
  | proc => exact NativeFormation.proc_canonical typed.1
  | name => exact NativeFormation.name_canonical typed.1

/-- Alpha-equivalence on admitted endpoints needs only literal locally
nameless syntax equality, while display syntax has the erasure observer. -/
theorem formed_alpha_iff_eq {context : Context} {sort : SourceSort} {first second : Pattern}
    (firstTyped : Formed context sort first) (secondTyped : Formed context sort second) :
    NativeFormation.checkAlpha first second = true ↔ first = second :=
  (NativeFormation.checkAlpha_exact first second).trans
    (Pattern.alphaEquiv_iff_eq_of_canonical (formed_canonical firstTyped) (formed_canonical secondTyped))

/-- Endpoint roles are part of the request. In particular a process step is
not admitted as a name judgment, even if its raw certificate is valid. -/
def Admission (context : Context) (sort : SourceSort) : Judgment → Prop
  | .structural first second => Formed context sort first ∧ Formed context sort second
  | .name first second => sort = .name ∧ Formed context .name first ∧ Formed context .name second
  | .step first second | .steps first second =>
      sort = .proc ∧ Formed context .proc first ∧ Formed context .proc second
  | .permutation first second =>
      sort = .proc ∧ (∀ p ∈ first, Formed context .proc p) ∧
        (∀ p ∈ second, Formed context .proc p)

def checkAdmission (context : Context) (sort : SourceSort) : Judgment → Bool
  | .structural first second => checkFormed context sort first && checkFormed context sort second
  | .name first second =>
      (sort == .name) && checkFormed context .name first && checkFormed context .name second
  | .step first second | .steps first second =>
      (sort == .proc) && checkFormed context .proc first && checkFormed context .proc second
  | .permutation first second =>
      (sort == .proc) && first.all (checkFormed context .proc) &&
        second.all (checkFormed context .proc)

theorem checkAdmission_exact (context : Context) (sort : SourceSort) (claim : Judgment) :
    checkAdmission context sort claim = true ↔ Admission context sort claim := by
  cases claim <;> simp only [checkAdmission, Admission, Bool.and_eq_true, beq_iff_eq,
    checkFormed_exact, List.all_eq_true, and_assoc]

structure Claim where
  context : Context
  sort : SourceSort
  judgment : Judgment
  deriving DecidableEq, Repr

/-- This statement does not mention the Boolean proof checker. -/
def Meaning (claim : Claim) : Prop :=
  Admission claim.context claim.sort claim.judgment ∧ NativeEvidence.Meaning claim.judgment

/-- This compatibility entry checks the original raw33 article plus admitted
endpoints. COMM in that article still performs the original syntactic routine;
the separately explicit article path supplies its computation witnesses. -/
def checkRaw (claim : Claim) (wire : Wire) : Bool :=
  checkAdmission claim.context claim.sort claim.judgment && checkWire claim.judgment wire

theorem checkRaw_exact (claim : Claim) (wire : Wire) :
    checkRaw claim wire = true ↔
      Admission claim.context claim.sort claim.judgment ∧
        ∃ derivation : NativeEvidence.Derivation claim.judgment,
          Mettapedia.OSLF.NativeTypes.Certificates.Tree.encodeDerivation derivation = wire := by
  simp only [checkRaw, Bool.and_eq_true, checkAdmission_exact, checkWire_exact]

theorem checkRaw_sound (claim : Claim) (wire : Wire)
    (accepted : checkRaw claim wire = true) : Meaning claim := by
  obtain ⟨admitted, derivation, _⟩ := (checkRaw_exact claim wire).mp accepted
  exact ⟨admitted, NativeEvidence.derivation_sound derivation⟩

theorem checkRaw_complete (claim : Claim) :
    Meaning claim ↔ ∃ wire : Wire, checkRaw claim wire = true := by
  constructor
  · rintro ⟨admitted, source⟩
    obtain ⟨wire, accepted⟩ := (checkWire_complete claim.judgment).mp source
    exact ⟨wire, by simp only [checkRaw, Bool.and_eq_true, checkAdmission_exact]; exact ⟨admitted, accepted⟩⟩
  · rintro ⟨wire, accepted⟩
    exact checkRaw_sound claim wire accepted

namespace Explicit

open Mettapedia.OSLF.NativeTypes.Certificates

structure CommReceipt where
  result : Pattern
  computation : SemanticSubstitutionEvidence.Certificate

abbrev Label := Rule × Option CommReceipt
abbrev Evidence := Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.Wire Label

/-- Inspect one original rule. COMM takes its literal result from a checked
rho computation article; no original substitution routine is called here. -/
def readConclusion : Label → Option Judgment
  | (.comm channel payload body rest, some receipt) =>
      if SemanticSubstitutionEvidence.check body payload receipt.result receipt.computation then
        some (conclusionWithComm (fun _ _ => receipt.result) (.comm channel payload body rest))
      else none
  | (.comm _ _ _ _, none) => none
  | (rule, none) => some (conclusionWithComm (fun body _ => body) rule)
  | (_, some _) => none

theorem readConclusion_exact (label : Label) (claim : Judgment)
    (accepted : readConclusion label = some claim) : conclusion label.1 = claim := by
  rcases label with ⟨rule, receipt⟩
  cases rule <;> cases receipt <;>
    simp only [readConclusion, Option.some.injEq] at accepted
  all_goals try contradiction
  all_goals try exact accepted
  rename_i channel payload body rest receipt
  split at accepted
  · have computed := SemanticSubstitutionEvidence.check_sound body payload receipt.result receipt.computation (by assumption)
    simpa only [conclusion, conclusionWithComm, computed] using Option.some.inj accepted
  · contradiction

/-- Local source computation authority, independent of the replay Boolean.
Non-COMM nodes have no computation annotation to authorize. -/
def AnnotationValid (label : Label) : Prop :=
  match label.1 with
  | .comm _ payload body _ => ∃ receipt : CommReceipt,
      label.2 = some receipt ∧ receipt.computation.Valid (.comm body payload) ∧
        receipt.computation.result = .pattern receipt.result
  | _ => label.2 = none

theorem readConclusion_annotation (label : Label) (claim : Judgment)
    (accepted : readConclusion label = some claim) : AnnotationValid label := by
  rcases label with ⟨rule, receipt⟩
  cases rule <;> cases receipt <;> simp only [readConclusion] at accepted
  all_goals try contradiction
  all_goals try exact rfl
  rename_i channel payload body rest receipt
  split at accepted
  · exact ⟨receipt, rfl, (SemanticSubstitutionEvidence.check_exact body payload receipt.result receipt.computation).mp (by assumption)⟩
  · contradiction

theorem readConclusion_of_annotation (label : Label) (claim : Judgment)
    (root : conclusion label.1 = claim) (valid : AnnotationValid label) :
    readConclusion label = some claim := by
  rcases label with ⟨rule, receipt⟩
  cases rule
  all_goals try
    change receipt = none at valid
    cases valid
    simpa only [readConclusion, conclusion, conclusionWithComm] using congrArg some root
  rename_i channel payload body rest
  obtain ⟨receipt, same, valid, result⟩ := valid
  cases same
  have checked := (SemanticSubstitutionEvidence.check_exact body payload receipt.result receipt.computation).mpr ⟨valid, result⟩
  have computed := SemanticSubstitutionEvidence.check_sound body payload receipt.result receipt.computation checked
  simp only [conclusion, conclusionWithComm, computed] at root
  simpa only [readConclusion, checked, ite_true, conclusionWithComm] using congrArg some root

/-- Source-native explicit articles: original rho inference instances and
premise occurrences, together with independent source computation witnesses. -/
inductive Valid : Evidence → Judgment → Prop where
  | node (label : Label) (children : List Evidence) (claim : Judgment)
      (root : conclusion label.1 = claim) (annotation : AnnotationValid label)
      (premises : List.Forall₂ Valid children (NativeEvidence.premises label.1)) :
      Valid (.node label children) claim

mutual
  def read : Evidence → Option Judgment
    | .node label children => do
        let claim ← readConclusion label
        if checkChildren children (premises label.1) then some claim else none

  def checkChildren : List Evidence → List Judgment → Bool
    | [], [] => true
    | child :: children, claim :: claims =>
        (read child == some claim) && checkChildren children claims
    | _, _ => false
end

theorem read_node_exact (label : Label) (children : List Evidence) (claim : Judgment) :
    read (.node label children) = some claim ↔
      readConclusion label = some claim ∧ checkChildren children (premises label.1) = true := by
  cases head : readConclusion label <;> cases checked : checkChildren children (premises label.1) <;>
    simp only [read, head, Bind.bind, Option.bind, checked, Bool.false_eq_true,
      ite_false, ite_true, Option.some.injEq, reduceCtorEq, and_false, and_true]

mutual
  theorem read_sound (evidence : Evidence) (claim : Judgment)
      (accepted : read evidence = some claim) : NativeEvidence.Meaning claim := by
    cases evidence with
    | node label children =>
        obtain ⟨head, checked⟩ := (read_node_exact label children claim).mp accepted
        rw [← readConclusion_exact label claim head]
        exact rule_sound label.1 (checkChildren_sound children (premises label.1) checked)

  theorem checkChildren_sound (children : List Evidence) (claims : List Judgment)
      (accepted : checkChildren children claims = true) :
      ∀ claim ∈ claims, NativeEvidence.Meaning claim := by
    cases children with
    | nil =>
        cases claims with
        | nil => intro claim member; cases member
        | cons claim claims => contradiction
    | cons child children =>
        cases claims with
        | nil => contradiction
        | cons first claims =>
            change ((read child == some first) && checkChildren children claims) = true at accepted
            simp only [Bool.and_eq_true, beq_iff_eq] at accepted
            intro claim member
            rcases List.mem_cons.mp member with same | later
            · cases same
              exact read_sound child first accepted.1
            · exact checkChildren_sound children claims accepted.2 claim later
end

mutual
  theorem read_valid (evidence : Evidence) (claim : Judgment)
      (accepted : read evidence = some claim) : Valid evidence claim := by
    cases evidence with
    | node label children =>
        obtain ⟨head, checked⟩ := (read_node_exact label children claim).mp accepted
        exact .node label children claim (readConclusion_exact label claim head)
          (readConclusion_annotation label claim head)
          (checkChildren_valid children (premises label.1) checked)

  theorem checkChildren_valid (children : List Evidence) (claims : List Judgment)
      (accepted : checkChildren children claims = true) : List.Forall₂ Valid children claims := by
    cases children with
    | nil => cases claims with
      | nil => exact .nil
      | cons claim claims => contradiction
    | cons child children => cases claims with
      | nil => contradiction
      | cons claim claims =>
          change ((read child == some claim) && checkChildren children claims) = true at accepted
          simp only [Bool.and_eq_true, beq_iff_eq] at accepted
          exact .cons (read_valid child claim accepted.1) (checkChildren_valid children claims accepted.2)
end

mutual
  theorem valid_read (evidence : Evidence) (claim : Judgment)
      (valid : Valid evidence claim) : read evidence = some claim := by
    cases valid with
    | node label children claim root annotation premises =>
        apply (read_node_exact label children claim).mpr
        exact ⟨readConclusion_of_annotation label claim root annotation,
          validChildren_checked children (NativeEvidence.premises label.1) premises⟩

  theorem validChildren_checked (children : List Evidence) (claims : List Judgment)
      (valid : List.Forall₂ Valid children claims) : checkChildren children claims = true := by
    cases valid with
    | nil => rfl
    | @cons child claim children claims head tail =>
        change ((read child == some claim) && checkChildren children claims) = true
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨valid_read child claim head, validChildren_checked children claims tail⟩
end

def check (claim : Judgment) (evidence : Evidence) : Bool := read evidence == some claim

/-- Exactness is for the very article supplied by the caller, including its
computation histories and every repeated premise occurrence. -/
theorem check_exact (claim : Judgment) (evidence : Evidence) :
    check claim evidence = true ↔ Valid evidence claim := by
  simp only [check, beq_iff_eq]
  exact ⟨read_valid evidence claim, valid_read evidence claim⟩

theorem check_sound (claim : Judgment) (evidence : Evidence)
    (accepted : check claim evidence = true) : NativeEvidence.Meaning claim :=
  read_sound evidence claim (by simpa only [check, beq_iff_eq] using accepted)

/-- Generating computation evidence belongs to the producer. The checker
above only validates supplied local results. -/
def annotateRule (rule : Rule) : Label :=
  (rule, match rule with
    | .comm _ payload body _ => some ⟨semanticCommSubst body payload, SemanticSubstitutionEvidence.certificate body payload⟩
    | _ => none)

theorem readConclusion_annotateRule (rule : Rule) :
    readConclusion (annotateRule rule) = some (conclusion rule) := by
  cases rule <;> simp only [annotateRule, readConclusion, conclusion, conclusionWithComm]
  exact if_pos (SemanticSubstitutionEvidence.check_certificate _ _)

/-- Every original finite proof tree supplies a literal computation witness
at each COMM occurrence, preserving the source child positions. -/
def fromTree : Proof → Evidence
  | .node rule children =>
      .node (annotateRule rule) (List.ofFn (fun position => fromTree (children position)))

theorem checkChildren_ofFn (claims : List Judgment)
    (children : Fin claims.length → Evidence)
    (accepted : ∀ position, read (children position) = some (claims.get position)) :
    checkChildren (List.ofFn children) claims = true := by
  induction claims with
  | nil => simp only [List.ofFn_zero, checkChildren]
  | cons claim claims ih =>
      rw [List.ofFn_succ]
      change ((read (children 0) == some claim) &&
        checkChildren (List.ofFn (fun position => children position.succ)) claims) = true
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · exact accepted 0
      · exact ih (fun position => children position.succ) (fun position => accepted position.succ)

theorem read_fromTree (tree : Proof) (claim : Judgment)
    (accepted : NativeEvidence.check claim tree = true) : read (fromTree tree) = some claim := by
  induction tree generalizing claim with
  | node rule children ih =>
      change Rule at rule
      change Fin (premises rule).length → Proof at children
      change (decide (conclusion rule = claim) &&
        decide (∀ position, NativeEvidence.check ((premises rule).get position) (children position) = true)) = true at accepted
      simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
      rcases accepted with ⟨root, accepted⟩
      change read (.node (annotateRule rule)
        (List.ofFn (fun position => fromTree (children position)))) = some claim
      rw [read, readConclusion_annotateRule]
      simp only [Bind.bind, Option.bind]
      have ready : checkChildren (List.ofFn (fun position => fromTree (children position))) (premises rule) = true :=
        checkChildren_ofFn (premises rule) _ (fun position => ih position _ (accepted position))
      change (if checkChildren (List.ofFn (fun position => fromTree (children position))) (premises rule) then
        some (conclusion rule) else none) = some claim
      rw [ready, if_pos rfl, root]

theorem check_complete (claim : Judgment) :
    NativeEvidence.Meaning claim ↔ ∃ evidence : Evidence, check claim evidence = true := by
  constructor
  · intro source
    obtain ⟨tree, accepted⟩ := (NativeEvidence.check_complete claim).mp source
    exact ⟨fromTree tree, by simp only [check, beq_iff_eq]; exact read_fromTree tree claim accepted⟩
  · rintro ⟨evidence, accepted⟩
    exact check_sound claim evidence accepted

end Explicit

/-- Raw source proof validity and formed endpoint checking remain distinct
request modes rather than silently narrowing the original raw calculus. -/
inductive RequestGoal where
  | raw (judgment : Judgment)
  | formed (claim : Claim)
  deriving DecidableEq, Repr

def RequestGoal.meaning : RequestGoal → Prop
  | .raw judgment => NativeEvidence.Meaning judgment
  | .formed claim => Meaning claim

def checkExplicit : RequestGoal → Explicit.Evidence → Bool
  | .raw judgment, evidence => Explicit.check judgment evidence
  | .formed claim, evidence =>
      checkAdmission claim.context claim.sort claim.judgment && Explicit.check claim.judgment evidence

theorem checkExplicit_sound (goal : RequestGoal) (evidence : Explicit.Evidence)
    (accepted : checkExplicit goal evidence = true) : goal.meaning := by
  cases goal with
  | raw judgment => exact Explicit.check_sound judgment evidence accepted
  | formed claim =>
      simp only [checkExplicit, Bool.and_eq_true, checkAdmission_exact] at accepted
      exact ⟨accepted.1, Explicit.check_sound claim.judgment evidence accepted.2⟩

theorem checkExplicit_complete (goal : RequestGoal) :
    goal.meaning ↔ ∃ evidence : Explicit.Evidence, checkExplicit goal evidence = true := by
  cases goal with
  | raw judgment => exact Explicit.check_complete judgment
  | formed claim =>
      constructor
      · rintro ⟨admitted, source⟩
        obtain ⟨evidence, checked⟩ := (Explicit.check_complete claim.judgment).mp source
        exact ⟨evidence, by
          simp only [checkExplicit, Bool.and_eq_true, checkAdmission_exact]
          exact ⟨admitted, checked⟩⟩
      · rintro ⟨evidence, checked⟩
        exact checkExplicit_sound (.formed claim) evidence checked

namespace Storage

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary

def sort : Codec SourceSort := Codec.nat.mapped
  (fun s => match s with | .proc => 0 | .name => 1)
  (fun n => match n with | 0 => some .proc | 1 => some .name | _ => none)
  (by intro s; cases s <;> rfl)

def context : Codec Context :=
  (Codec.prod (Codec.list (Codec.prod Codec.string sort)) (Codec.list sort)).mapped
    (fun value => (value.free, value.bound))
    (fun value => some ⟨value.1, value.2⟩) (by intro value; rfl)

def claim : Codec Claim :=
  (Codec.prod context (Codec.prod sort NativeEvidence.Storage.judgment)).mapped
    (fun value => (value.context, value.sort, value.judgment))
    (fun value => some ⟨value.1, value.2.1, value.2.2⟩) (by intro value; rfl)

/-- Rho-native call results retain their constructor, literal syntax and match
bit. A list result is not interchangeable with a single process result. -/
def computationResult : Codec SemanticSubstitutionEvidence.Result where
  put
    | .pattern value => .pair (.atom 0) (Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec.put value)
    | .patterns values => .pair (.atom 1)
        ((Codec.list Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec).put values)
    | .marked name matched => .pair (.atom 2) (.pair
        (Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec.put name)
        (.atom (if matched then 1 else 0)))
  get
    | .pair (.atom 0) value =>
        (Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec.get value).map .pattern
    | .pair (.atom 1) values =>
        ((Codec.list Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec).get values).map .patterns
    | .pair (.atom 2) (.pair name (.atom matched)) => do
        let value ← Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec.get name
        match matched with
        | 0 => some (.marked value false)
        | 1 => some (.marked value true)
        | _ => none
    | _ => none
  get_put value := by
    cases value with
    | pattern value => simp only [Codec.get_put, Option.map_some]
    | patterns values => simp only [Codec.get_put, Option.map_some]
    | marked name matched =>
        cases matched <;> simp
        all_goals rw [Codec.get_put]
        all_goals rfl

mutual
  private def computationToWire : SemanticSubstitutionEvidence.Certificate →
      Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.Wire SemanticSubstitutionEvidence.Result
    | .node result children => .node result (computationChildrenToWire children)
  private def computationChildrenToWire : List SemanticSubstitutionEvidence.Certificate →
      List (Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.Wire SemanticSubstitutionEvidence.Result)
    | [] => []
    | child :: children => computationToWire child :: computationChildrenToWire children
end

mutual
  private def computationFromWire :
      Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.Wire SemanticSubstitutionEvidence.Result →
      SemanticSubstitutionEvidence.Certificate
    | .node result children => .node result (computationChildrenFromWire children)
  private def computationChildrenFromWire :
      List (Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.Wire SemanticSubstitutionEvidence.Result) →
      List SemanticSubstitutionEvidence.Certificate
    | [] => []
    | child :: children => computationFromWire child :: computationChildrenFromWire children
end

mutual
  private theorem computationFromTo (evidence : SemanticSubstitutionEvidence.Certificate) :
      computationFromWire (computationToWire evidence) = evidence := by
    cases evidence with
    | node result children =>
        simp only [computationToWire, computationFromWire, computationChildrenFromTo children]

  private theorem computationChildrenFromTo : ∀ children : List SemanticSubstitutionEvidence.Certificate,
      computationChildrenFromWire (computationChildrenToWire children) = children
    | [] => rfl
    | child :: children => by
        simp only [computationChildrenToWire, computationChildrenFromWire,
          computationFromTo child, computationChildrenFromTo children]
end

/-- Reuse the existing wire/Data recursion; only the native call-tree
container is transported across its literal constructor isomorphism. -/
def computation : Codec SemanticSubstitutionEvidence.Certificate :=
  (Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.wireCodec computationResult).mapped
    computationToWire (some ∘ computationFromWire)
    (fun value => congrArg some (computationFromTo value))

def commReceipt : Codec Explicit.CommReceipt :=
  (Codec.prod Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec computation).mapped
    (fun value => (value.result, value.computation))
    (fun value => some ⟨value.1, value.2⟩) (by intro value; rfl)

private def optionalCommReceipt : Codec (Option Explicit.CommReceipt) where
  put | none => .atom 0 | some receipt => .pair (.atom 1) (commReceipt.put receipt)
  get | .atom 0 => some none
      | .pair (.atom 1) raw => (commReceipt.get raw).map some
      | _ => none
  get_put value := by cases value <;> simp only [Codec.get_put, Option.map_some]

def explicitProof : Codec Explicit.Evidence :=
  Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.wireCodec
    (Codec.prod NativeEvidence.Storage.rule optionalCommReceipt)

private def header : String := "rho-kernel-formed-v1"

def rawRequest : Codec (Claim × Wire) :=
  (Codec.prod Codec.string (Codec.prod claim NativeEvidence.Storage.proof)).mapped
    (fun value => (header, value))
    (fun value => if value.1 = header then some value.2 else none)
    (by intro value; simp)

def encodeRawRequest (goal : Claim) (wire : Wire) : List Alphabet :=
  encodeWith rawRequest (goal, wire)

def checkRawRequest (word : List Alphabet) : Option Claim := do
  let (goal, wire) ← decodeWith rawRequest word
  if encodeRawRequest goal wire = word ∧ checkRaw goal wire = true then some goal else none

theorem checkRawRequest_exact (goal : Claim) (word : List Alphabet) :
    checkRawRequest word = some goal ↔
      ∃ wire : Wire, encodeRawRequest goal wire = word ∧ checkRaw goal wire = true := by
  cases decoded : decodeWith rawRequest word with
  | none =>
      constructor
      · intro impossible
        simp only [checkRawRequest, decoded, Bind.bind, Option.bind] at impossible
        cases impossible
      · rintro ⟨wire, exactInput, _⟩
        have recovered := decodeWith_encodeWith rawRequest (goal, wire)
        change decodeWith rawRequest (encodeRawRequest goal wire) = _ at recovered
        rw [exactInput, decoded] at recovered
        cases recovered
  | some packet =>
      rcases packet with ⟨found, wire⟩
      by_cases valid : encodeRawRequest found wire = word ∧ checkRaw found wire = true
      · simp only [checkRawRequest, decoded, Bind.bind, Option.bind, if_pos valid, Option.some.injEq]
        constructor
        · intro same
          cases same
          exact ⟨wire, valid⟩
        · rintro ⟨original, exactInput, _⟩
          have recovered := decodeWith_encodeWith rawRequest (goal, original)
          change decodeWith rawRequest (encodeRawRequest goal original) = _ at recovered
          rw [exactInput, decoded] at recovered
          exact congrArg Prod.fst (Option.some.inj recovered)
      · simp only [checkRawRequest, decoded, Bind.bind, Option.bind, if_neg valid]
        constructor
        · intro impossible; cases impossible
        · rintro ⟨original, exactInput, accepted⟩
          exfalso
          apply valid
          have recovered := decodeWith_encodeWith rawRequest (goal, original)
          change decodeWith rawRequest (encodeRawRequest goal original) = _ at recovered
          rw [exactInput, decoded] at recovered
          have same := Option.some.inj recovered
          cases same
          exact ⟨exactInput, accepted⟩

theorem checkRawRequest_sound (word : List Alphabet) (goal : Claim)
    (accepted : checkRawRequest word = some goal) : Meaning goal := by
  obtain ⟨wire, _, accepted⟩ := (checkRawRequest_exact goal word).mp accepted
  exact checkRaw_sound goal wire accepted

theorem checkRawRequest_complete (goal : Claim) :
    Meaning goal ↔ ∃ word, checkRawRequest word = some goal := by
  constructor
  · intro source
    obtain ⟨wire, accepted⟩ := checkRaw_complete goal |>.mp source
    exact ⟨encodeRawRequest goal wire, (checkRawRequest_exact goal _).mpr ⟨wire, rfl, accepted⟩⟩
  · rintro ⟨word, accepted⟩
    exact checkRawRequest_sound word goal accepted

def requestGoal : Codec RequestGoal where
  put
    | .raw judgment => .pair (.atom 0) (NativeEvidence.Storage.judgment.put judgment)
    | .formed goal => .pair (.atom 1) (claim.put goal)
  get
    | .pair (.atom 0) raw => (NativeEvidence.Storage.judgment.get raw).map .raw
    | .pair (.atom 1) raw => (claim.get raw).map .formed
    | _ => none
  get_put goal := by cases goal <;> simp only [Codec.get_put, Option.map_some]

private def explicitHeader : String := "rho-kernel-explicit-v1"

def explicitRequest : Codec (RequestGoal × Explicit.Evidence) :=
  (Codec.prod Codec.string (Codec.prod requestGoal explicitProof)).mapped
    (fun value => (explicitHeader, value))
    (fun value => if value.1 = explicitHeader then some value.2 else none)
    (by intro value; simp)

def encodeExplicitRequest (goal : RequestGoal) (evidence : Explicit.Evidence) : List Alphabet :=
  encodeWith explicitRequest (goal, evidence)

def checkExplicitRequest (word : List Alphabet) : Option RequestGoal := do
  let (goal, evidence) ← decodeWith explicitRequest word
  if encodeExplicitRequest goal evidence = word ∧ checkExplicit goal evidence = true then some goal else none

theorem checkExplicitRequest_exact (goal : RequestGoal) (word : List Alphabet) :
    checkExplicitRequest word = some goal ↔
      ∃ evidence : Explicit.Evidence,
        encodeExplicitRequest goal evidence = word ∧ checkExplicit goal evidence = true := by
  cases decoded : decodeWith explicitRequest word with
  | none =>
      constructor
      · intro impossible
        simp only [checkExplicitRequest, decoded, Bind.bind, Option.bind] at impossible
        cases impossible
      · rintro ⟨evidence, exactInput, _⟩
        have recovered := decodeWith_encodeWith explicitRequest (goal, evidence)
        change decodeWith explicitRequest (encodeExplicitRequest goal evidence) = _ at recovered
        rw [exactInput, decoded] at recovered
        cases recovered
  | some packet =>
      rcases packet with ⟨found, evidence⟩
      by_cases valid : encodeExplicitRequest found evidence = word ∧ checkExplicit found evidence = true
      · simp only [checkExplicitRequest, decoded, Bind.bind, Option.bind, if_pos valid, Option.some.injEq]
        constructor
        · intro same
          cases same
          exact ⟨evidence, valid⟩
        · rintro ⟨original, exactInput, _⟩
          have recovered := decodeWith_encodeWith explicitRequest (goal, original)
          change decodeWith explicitRequest (encodeExplicitRequest goal original) = _ at recovered
          rw [exactInput, decoded] at recovered
          exact congrArg Prod.fst (Option.some.inj recovered)
      · simp only [checkExplicitRequest, decoded, Bind.bind, Option.bind, if_neg valid]
        constructor
        · intro impossible; cases impossible
        · rintro ⟨original, exactInput, accepted⟩
          exfalso
          apply valid
          have recovered := decodeWith_encodeWith explicitRequest (goal, original)
          change decodeWith explicitRequest (encodeExplicitRequest goal original) = _ at recovered
          rw [exactInput, decoded] at recovered
          have same := Option.some.inj recovered
          cases same
          exact ⟨exactInput, accepted⟩

theorem checkExplicitRequest_sound (word : List Alphabet) (goal : RequestGoal)
    (accepted : checkExplicitRequest word = some goal) : goal.meaning := by
  obtain ⟨evidence, _, accepted⟩ := (checkExplicitRequest_exact goal word).mp accepted
  exact checkExplicit_sound goal evidence accepted

theorem checkExplicitRequest_complete (goal : RequestGoal) :
    goal.meaning ↔ ∃ word, checkExplicitRequest word = some goal := by
  constructor
  · intro source
    obtain ⟨evidence, checked⟩ := (checkExplicit_complete goal).mp source
    exact ⟨encodeExplicitRequest goal evidence,
      (checkExplicitRequest_exact goal _).mpr ⟨evidence, rfl, checked⟩⟩
  · rintro ⟨word, accepted⟩
    exact checkExplicitRequest_sound word goal accepted

theorem explicit_trailing_refused (goal : RequestGoal) (evidence : Explicit.Evidence)
    (tail : List Alphabet) (nonempty : tail.isEmpty = false) :
    checkExplicitRequest (encodeExplicitRequest goal evidence ++ tail) = none := by
  simp only [checkExplicitRequest, encodeExplicitRequest,
    decodeWith_trailing_refused explicitRequest (goal, evidence) tail nonempty,
    Bind.bind, Option.bind]

end Storage
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeKernel
