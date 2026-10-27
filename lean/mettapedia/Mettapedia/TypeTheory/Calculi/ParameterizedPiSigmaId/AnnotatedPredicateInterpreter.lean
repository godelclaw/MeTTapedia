import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateEquality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ContextChecking
import Mettapedia.Logic.DerivationList

/-!
# Shared certificate-directed contextual interpretation

The traversal handles the structural equality rules once. Every evidence
implementation exposes an actual retained HOL proof and its source readings;
extra instance evidence, such as extensionality freedom, may be retained.
The standard implementation uses the shared equality constructors directly.
Root interpretation is an explicit input over the source decoder's code type.
Full source-judgment and context checks remain the admission gate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
namespace Interpreter
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
  {lex : LexicalReading Head Base Const} {closed : List (HOL.ClosedFormula Const)}

/-- Evidence implementations must expose a proof at their exact interpreted
endpoints. No separate proof-soundness premise is accepted by the traversal. -/
structure EvidenceOps (lex : LexicalReading Head Base Const) (closed : List (HOL.ClosedFormula Const)) where
  Evidence : (Γ : HOL.Ctx Base) → CTm Head Γ.length → CTm Head Γ.length → HOL.Ty Base → Type (max u v)
  view : ∀ {Γ source target carrier}, Evidence Γ source target carrier → EqualityAt lex closed Γ source target carrier
  refl : ∀ {Γ source carrier} {code : HOL.Term Const Γ carrier}, Reads lex source code → Evidence Γ source source carrier
  symm : ∀ {Γ source target carrier}, Evidence Γ source target carrier → Evidence Γ target source carrier
  trans : ∀ {Γ source middle target},
    ((carrier : HOL.Ty Base) × Evidence Γ source middle carrier) →
    ((carrier : HOL.Ty Base) × Evidence Γ middle target carrier) →
    ((carrier : HOL.Ty Base) × Evidence Γ source target carrier)
  app : ∀ {Γ f g a b domain codomain}, Evidence Γ f g (.arr domain codomain) → Evidence Γ a b domain →
    Evidence Γ (.app f a) (.app g b) codomain
  lam : ∀ {Γ A A' domain codomain} {body body' : CTm Head (Γ.length + 1)},
    Evidence Γ A A' (.arr domain .prop) → Evidence (domain :: Γ) body body' codomain →
    Evidence Γ (.lam A body) (.lam A' body') (.arr domain codomain)
  pi : ∀ {Γ A A' domain codomain} {B B' : CTm Head (Γ.length + 1)},
    Evidence Γ A A' (.arr domain .prop) → Evidence (domain :: Γ) B B' (.arr codomain .prop) →
    Evidence Γ (.pi A B) (.pi A' B') (.arr (.arr domain codomain) .prop)
  beta : ∀ {Γ A domain codomain} {body : CTm Head (Γ.length + 1)} {argument : CTm Head Γ.length}
    {domainCode : HOL.Term Const Γ (.arr domain .prop)} {bodyCode : HOL.Term Const (domain :: Γ) codomain}
    {argumentCode : HOL.Term Const Γ domain},
    Reads lex A domainCode → Reads lex (Γ := domain :: Γ) body bodyCode → Reads lex argument argumentCode →
    Evidence Γ (.app (.lam A body) argument) (CTm.inst0 argument body) codomain

variable [DecidableEq Base]

def standard : EvidenceOps lex closed where
  Evidence := EqualityAt lex closed
  view := fun evidence => evidence
  refl := EqualityAt.refl
  symm := EqualityAt.symm
  trans := EqualityReading.trans
  app := EqualityAt.app
  lam := EqualityAt.lam
  pi := EqualityAt.pi
  beta := EqualityAt.beta

def beta? (ops : EvidenceOps lex closed) (Γ : HOL.Ctx Base)
    (domain : CTm Head Γ.length) (body : CTm Head (Γ.length + 1)) (argument : CTm Head Γ.length) :
    Option ((carrier : HOL.Ty Base) × ops.Evidence Γ (.app (.lam domain body) argument)
      (CTm.inst0 argument body) carrier) := do
  let ⟨⟨.arr carrier .prop, domainCode⟩, domainRead⟩ ← Reader.read? lex Γ domain | none
  let ⟨⟨result, bodyCode⟩, bodyRead⟩ ← Reader.read? lex (carrier :: Γ) body
  let ⟨⟨argumentType, argumentCode⟩, argumentRead⟩ ← Reader.read? lex Γ argument
  if same : argumentType = carrier then
    pure (by cases same; exact ⟨result, ops.beta domainRead bodyRead argumentRead⟩)
  else none

theorem beta?_complete (ops : EvidenceOps lex closed) {Γ : HOL.Ctx Base}
    {A : CTm Head Γ.length} {body : CTm Head (Γ.length + 1)} {argument : CTm Head Γ.length}
    {domain codomain : HOL.Ty Base} {domainCode : HOL.Term Const Γ (.arr domain .prop)}
    {bodyCode : HOL.Term Const (domain :: Γ) codomain} {argumentCode : HOL.Term Const Γ domain}
    (domainRead : Reads lex A domainCode) (bodyRead : Reads lex (Γ := domain :: Γ) body bodyCode)
    (argumentRead : Reads lex argument argumentCode) :
    beta? ops Γ A body argument = some ⟨codomain, ops.beta domainRead bodyRead argumentRead⟩ := by
  simp [beta?, Reader.read?_complete domainRead, Reader.read?_complete bodyRead, Reader.read?_complete argumentRead]

abbrev Witness (Head : Type) (Root : Nat → Type) :=
  (statement : CStatement Head) × Checking.Code Head Root statement
abbrev Certificate (Root : Nat → Type) := Logic.Derivation (CStatement Head) (Witness Head Root)
variable {Root : Nat → Type} [DecidableEq Head]

def readEquality? (ops : EvidenceOps lex closed)
    (roots : (Γ : HOL.Ctx Base) → (source target : CTm Head Γ.length) → Root Γ.length →
      Option ((carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier)) :
    Certificate (Head := Head) Root → (Γ : HOL.Ctx Base) →
    (context : CCtx Head Γ.length) → (source target type : CTm Head Γ.length) →
    Option (((carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier))
  | .node _ witness count children, Γ, context, source, target, type =>
      if same : witness.1 = .equality context source target type then
        match (same ▸ witness.2 : Checking.Code Head Root
            (.equality context source target type)) with
        | @Checking.Code.refl _ _ _ _ term _ =>
            (Reader.read? lex Γ term).map fun read => ⟨read.val.1, ops.refl read.property⟩
        | @Checking.Code.symm _ _ _ context left right type =>
            if bound : 0 < count then
              (readEquality? ops roots (children ⟨0, bound⟩) Γ context left right type).map
                fun read => ⟨read.1, ops.symm read.2⟩
            else none
        | @Checking.Code.trans _ _ _ context left middle right type =>
            if bound : 1 < count then do
              let first ← readEquality? ops roots (children ⟨0, by omega⟩) Γ context left middle type
              let second ← readEquality? ops roots (children ⟨1, bound⟩) Γ context middle right type
              some (ops.trans first second)
            else none
        | @Checking.Code.appCong _ _ _ context f g a b A B =>
            if bound : 1 < count then do
              let ⟨.arr domain codomain, function⟩ ←
                readEquality? ops roots (children ⟨0, by omega⟩) Γ context f g (.pi A B) | none
              let ⟨argumentType, argument⟩ ←
                readEquality? ops roots (children ⟨1, bound⟩) Γ context a b A
              if same : argumentType = domain then
                some ⟨codomain, ops.app function (same ▸ argument)⟩
              else none
            else none
        | @Checking.Code.lamCong _ _ _ context A A' body body' B _u w =>
            if bound : 2 < count then do
              let ⟨.arr domain .prop, domains⟩ ←
                readEquality? ops roots (children ⟨0, by omega⟩) Γ context A A' (.head w) | none
              let ⟨codomain, bodies⟩ ←
                readEquality? ops roots (children ⟨2, bound⟩) (domain :: Γ) (.snoc context A) body body' B
              some ⟨.arr domain codomain, ops.lam domains bodies⟩
            else none
        | @Checking.Code.piCong _ _ _ context A A' B B' u v _w =>
            if bound : 1 < count then do
              let ⟨.arr domain .prop, domains⟩ ←
                readEquality? ops roots (children ⟨0, by omega⟩) Γ context A A' (.head u) | none
              let ⟨.arr codomain .prop, families⟩ ←
                readEquality? ops roots (children ⟨1, bound⟩) (domain :: Γ) (.snoc context A) B B' (.head v) | none
              some ⟨.arr (.arr domain codomain) .prop, ops.pi domains families⟩
            else none
        | @Checking.Code.betaPi _ _ _ _ A argument body _B _u => beta? ops Γ A body argument
        | .root code => roots Γ source target code
        | @Checking.Code.convEq _ _ _ context left right A _B _u =>
            if bound : 0 < count then
              readEquality? ops roots (children ⟨0, bound⟩) Γ context left right A
            else none
        | @Checking.Code.subEq _ _ _ context left right A _B =>
            if bound : 0 < count then
              readEquality? ops roots (children ⟨0, bound⟩) Γ context left right A
            else none
        | _ => none
      else none

section Coverage
variable (ops : EvidenceOps lex closed)
  (roots : (Γ : HOL.Ctx Base) → (source target : CTm Head Γ.length) → Root Γ.length →
    Option ((carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier))
  {Γ : HOL.Ctx Base} {context : CCtx Head Γ.length}

def equationNode {n : Nat}
    {context : CCtx Head n} {source target type : CTm Head n}
    (code : Checking.Code Head Root (.equality context source target type))
    (children : List (Certificate (Head := Head) Root)) : Certificate (Head := Head) Root :=
  Logic.Derivation.fromChildren (.equality context source target type)
    ⟨.equality context source target type, code⟩ children

theorem read_root (source target type : CTm Head Γ.length)
    (code : Root Γ.length) (children : List (Certificate (Head := Head) Root)) :
    readEquality? ops roots
      (equationNode (.root (Γ := context) (left := source) (right := target) (A := type) code) children)
      Γ context source target type = roots Γ source target code := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?]

theorem read_beta (A argument : CTm Head Γ.length) (body B : CTm Head (Γ.length + 1))
    (u : Head) (children : List (Certificate (Head := Head) Root)) :
    readEquality? ops roots
      (equationNode (.betaPi (Γ := context) (A := A) (a := argument) (body := body) (B := B) (u := u)) children)
      Γ context (.app (.lam A body) argument) (CTm.inst0 argument body) (CTm.inst0 argument B) =
      beta? ops Γ A body argument := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?]

theorem read_refl (source type : CTm Head Γ.length) (typing : Certificate (Head := Head) Root)
    {carrier : HOL.Ty Base} {code : HOL.Term Const Γ carrier}
    (reading : Reads lex source code) :
    readEquality? ops roots (equationNode (.refl (Γ := context) (a := source) (A := type)) [typing])
      Γ context source source type = some ⟨carrier, ops.refl reading⟩ := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?, Reader.read?_complete reading]

theorem read_symm (source target type : CTm Head Γ.length)
    (child : Certificate (Head := Head) Root) (reading : ((carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier))
    (accepted : readEquality? ops roots child Γ context source target type = some reading) :
    readEquality? ops roots (equationNode (.symm (Γ := context) (a := source) (b := target) (A := type)) [child])
      Γ context target source type = some ⟨reading.1, ops.symm reading.2⟩ := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?, accepted]

theorem read_trans (source middle target type : CTm Head Γ.length)
    (first second : Certificate (Head := Head) Root)
    (left : ((carrier : HOL.Ty Base) × ops.Evidence Γ source middle carrier)) (right : ((carrier : HOL.Ty Base) × ops.Evidence Γ middle target carrier))
    (acceptedLeft : readEquality? ops roots first Γ context source middle type = some left)
    (acceptedRight : readEquality? ops roots second Γ context middle target type = some right) :
    readEquality? ops roots
      (equationNode (.trans (Γ := context) (a := source) (b := middle) (c := target) (A := type)) [first, second])
      Γ context source target type = some (ops.trans left right) := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?, acceptedLeft, acceptedRight]

theorem read_app (f g a b A : CTm Head Γ.length) (B : CTm Head (Γ.length + 1))
    (first second : Certificate (Head := Head) Root) {domain codomain : HOL.Ty Base}
    (function : ops.Evidence Γ f g (.arr domain codomain)) (argument : ops.Evidence Γ a b domain)
    (acceptedFunction : readEquality? ops roots first Γ context f g (.pi A B) = some ⟨_, function⟩)
    (acceptedArgument : readEquality? ops roots second Γ context a b A = some ⟨_, argument⟩) :
    readEquality? ops roots
      (equationNode (.appCong (Γ := context) (f := f) (g := g) (a := a) (b := b) (A := A) (B := B)) [first, second])
      Γ context (.app f a) (.app g b) (CTm.inst0 a B) = some ⟨codomain, ops.app function argument⟩ := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?, acceptedFunction, acceptedArgument]

theorem read_lam (A A' : CTm Head Γ.length) (body body' B : CTm Head (Γ.length + 1)) (u w : Head)
    (domainCertificate formation bodyCertificate : Certificate (Head := Head) Root) {domain codomain : HOL.Ty Base}
    (domains : ops.Evidence Γ A A' (.arr domain .prop))
    (bodies : ops.Evidence (domain :: Γ) body body' codomain)
    (acceptedDomain : readEquality? ops roots domainCertificate Γ context A A' (.head w) = some ⟨_, domains⟩)
    (acceptedBody : readEquality? ops roots bodyCertificate (domain :: Γ) (.snoc context A) body body' B = some ⟨_, bodies⟩) :
    readEquality? ops roots
      (equationNode (.lamCong (Γ := context) (A := A) (A' := A') (body := body) (body' := body') (B := B) (u := u) (w := w))
        [domainCertificate, formation, bodyCertificate])
      Γ context (.lam A body) (.lam A' body') (.pi A B) = some ⟨.arr domain codomain, ops.lam domains bodies⟩ := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?, acceptedDomain, acceptedBody]

theorem read_pi (A A' : CTm Head Γ.length) (B B' : CTm Head (Γ.length + 1)) (u v w : Head)
    (domainCertificate familyCertificate : Certificate (Head := Head) Root) {domain codomain : HOL.Ty Base}
    (domains : ops.Evidence Γ A A' (.arr domain .prop))
    (families : ops.Evidence (domain :: Γ) B B' (.arr codomain .prop))
    (acceptedDomain : readEquality? ops roots domainCertificate Γ context A A' (.head u) = some ⟨_, domains⟩)
    (acceptedFamily : readEquality? ops roots familyCertificate (domain :: Γ) (.snoc context A) B B' (.head v) = some ⟨_, families⟩) :
    readEquality? ops roots
      (equationNode (.piCong (Γ := context) (A := A) (A' := A') (B := B) (B' := B') (u := u) (v := v) (w := w))
        [domainCertificate, familyCertificate])
      Γ context (.pi A B) (.pi A' B') (.head w) = some ⟨.arr (.arr domain codomain) .prop, ops.pi domains families⟩ := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?, acceptedDomain, acceptedFamily]

theorem read_convEq (source target A B : CTm Head Γ.length) (u : Head)
    (child conversion : Certificate (Head := Head) Root) :
    readEquality? ops roots
      (equationNode (.convEq (Γ := context) (a := source) (b := target) (A := A) (B := B) (u := u)) [child, conversion])
      Γ context source target B = readEquality? ops roots child Γ context source target A := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?]

theorem read_subEq (source target A B : CTm Head Γ.length)
    (child subtyping : Certificate (Head := Head) Root) :
    readEquality? ops roots
      (equationNode (.subEq (Γ := context) (a := source) (b := target) (A := A) (B := B)) [child, subtyping])
      Γ context source target B = readEquality? ops roots child Γ context source target A := by
  simp [equationNode, Logic.Derivation.fromChildren, readEquality?]

end Coverage

section Admission
variable {R : Rules Head} (P : ChurchRules R)
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
    (decoder : Checking.RootDecoder P.computation)

def checkJudgment (certificate : Certificate (Head := Head) decoder.Code) (statement : CStatement Head) : Bool :=
  certificate.valid (Checking.interface P decoder) && decide (certificate.concl = statement)

theorem checkJudgment_sound {certificate : Certificate (Head := Head) decoder.Code} {statement : CStatement Head}
    (accepted : checkJudgment P decoder certificate statement = true) : CDerivable P statement := by
  have parts : certificate.valid (Checking.interface P decoder) = true ∧ certificate.concl = statement := by
    simpa only [checkJudgment, Bool.and_eq_true, decide_eq_true_eq] using accepted
  rw [← parts.2]
  exact Checking.derives_sound P decoder (certificate.valid_sound (Checking.interface P decoder) parts.1)

structure CheckedEquality (ops : EvidenceOps lex closed) (Γ : HOL.Ctx Base)
    (context : CCtx Head Γ.length) (source target type : CTm Head Γ.length) where
  contextFormed : CCtxFormed P context
  sourceEqual : CEqual P context source target type
  carrier : HOL.Ty Base
  evidence : ops.Evidence Γ source target carrier

def check? (ops : EvidenceOps lex closed)
    (roots : (Γ : HOL.Ctx Base) → (source target : CTm Head Γ.length) → decoder.Code Γ.length →
      Option ((carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier))
    (Γ : HOL.Ctx Base) (context : CCtx Head Γ.length) (source target type : CTm Head Γ.length)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code) :
    Option (CheckedEquality P ops Γ context source target type) :=
  if formed : Checking.checkContext P decoder context contextCertificate = true then
    if accepted : checkJudgment P decoder certificate (.equality context source target type) = true then
      (readEquality? ops roots certificate Γ context source target type).map fun evidence =>
        ⟨Checking.checkContext_sound P decoder contextCertificate formed,
          checkJudgment_sound P decoder accepted,
          evidence.1, evidence.2⟩
    else none
  else none

theorem admit_reading (ops : EvidenceOps lex closed)
    (roots : (Γ : HOL.Ctx Base) → (source target : CTm Head Γ.length) → decoder.Code Γ.length →
      Option ((carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier))
    (Γ : HOL.Ctx Base) (context : CCtx Head Γ.length) (source target type : CTm Head Γ.length)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code)
    (evidence : (carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier)
    (formed : Checking.checkContext P decoder context contextCertificate = true)
    (accepted : checkJudgment P decoder certificate (.equality context source target type) = true)
    (interpreted : readEquality? ops roots certificate Γ context source target type = some evidence) :
    check? P decoder ops roots Γ context source target type contextCertificate certificate =
      some ⟨Checking.checkContext_sound P decoder contextCertificate formed,
        checkJudgment_sound P decoder accepted, evidence.1, evidence.2⟩ := by
  simp [check?, formed, accepted, interpreted]

theorem check?_refuses_source (ops : EvidenceOps lex closed)
    (roots : (Γ : HOL.Ctx Base) → (source target : CTm Head Γ.length) → decoder.Code Γ.length →
      Option ((carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier))
    (Γ : HOL.Ctx Base) (context : CCtx Head Γ.length) (source target type : CTm Head Γ.length)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code)
    (refused : checkJudgment P decoder certificate (.equality context source target type) = false) :
    check? P decoder ops roots Γ context source target type contextCertificate certificate = none := by
  simp [check?, refused]

theorem check?_refuses_context (ops : EvidenceOps lex closed)
    (roots : (Γ : HOL.Ctx Base) → (source target : CTm Head Γ.length) → decoder.Code Γ.length →
      Option ((carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier))
    (Γ : HOL.Ctx Base) (context : CCtx Head Γ.length) (source target type : CTm Head Γ.length)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code)
    (refused : Checking.checkContext P decoder context contextCertificate = false) :
    check? P decoder ops roots Γ context source target type contextCertificate certificate = none := by
  simp [check?, refused]

def CheckedEquality.reading {ops : EvidenceOps lex closed} {Γ : HOL.Ctx Base}
    {context : CCtx Head Γ.length} {source target type : CTm Head Γ.length}
    (received : CheckedEquality P ops Γ context source target type) : EqualityReading lex closed Γ source target :=
  ⟨received.carrier, ops.view received.evidence⟩

end Admission

#print axioms readEquality?
#print axioms check?
#print axioms CheckedEquality.reading
end Interpreter
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
