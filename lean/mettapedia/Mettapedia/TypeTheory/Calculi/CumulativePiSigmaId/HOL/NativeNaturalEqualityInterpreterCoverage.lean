import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalEqualityInterpreter
import Mettapedia.Logic.DerivationList

/-!
# Compositional coverage of annotated equality instructions

These equations concern the actual incoming certificate nodes. Their
recursive premises are successful readings of the indicated child
certificates; source formation and local-rule validity are separately checked
by the admission program. Natural and beta leaves use their proved readers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.CertificateInterpretation

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies Programs.Annotated

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} [DecidableEq Base]
    {operations : Operations Base Const} {profile : Programs.ComputationProfiles.Selection}
    {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}

def equationNode {n : Nat} (profile : Programs.ComputationProfiles.Selection)
    {context : CCtx Tower.Head n} {source target type : CTm Tower.Head n}
    (code : Checking.Code Tower.Head (JudgmentReplay.decoder profile).Code (.equality context source target type))
    (children : List (JudgmentReplay.Certificate profile)) : JudgmentReplay.Certificate profile :=
  Logic.Derivation.fromChildren (.equality context source target type)
    ⟨.equality context source target type, code⟩ children

theorem read_root (source target type : CTm Tower.Head Γ.length)
    (code : SchemaJudgmentCode.Code Tower.Head Γ.length) (children : List (JudgmentReplay.Certificate profile)) :
    readEquality? operations profile
      (equationNode profile (.root (Γ := context) (left := source) (right := target) (A := type) code) children)
      Γ context source target type = EqualityCode.natural? operations profile Γ source target code := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode] using
    (AnnotatedPredicateReading.Interpreter.read_root (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) source target type code children)

theorem read_beta (A argument : CTm Tower.Head Γ.length) (body B : CTm Tower.Head (Γ.length + 1))
    (u : Tower.Head) (children : List (JudgmentReplay.Certificate profile)) :
    readEquality? operations profile
      (equationNode profile (.betaPi (Γ := context) (A := A) (a := argument) (body := body) (B := B) (u := u)) children)
      Γ context (.app (.lam A body) argument) (CTm.inst0 argument body) (CTm.inst0 argument B) =
      EqualityCode.beta? operations Γ A body argument := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode, EqualityCode.beta?] using
    (AnnotatedPredicateReading.Interpreter.read_beta (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) A argument body B u children)

theorem read_refl (source type : CTm Tower.Head Γ.length) (typing : JudgmentReplay.Certificate profile)
    {carrier : HOL.Ty Base} {code : HOL.Term Const Γ carrier}
    (reading : AnnotatedReads operations source code) :
    readEquality? operations profile (equationNode profile (.refl (Γ := context) (a := source) (A := type)) [typing])
      Γ context source source type = some ⟨carrier, EqualityAt.refl reading⟩ := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode, evidenceOps] using
    (AnnotatedPredicateReading.Interpreter.read_refl (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) source type typing reading.toGeneric)

theorem read_symm (source target type : CTm Tower.Head Γ.length)
    (child : JudgmentReplay.Certificate profile) (reading : EqualityReading operations Γ source target)
    (accepted : readEquality? operations profile child Γ context source target type = some reading) :
    readEquality? operations profile (equationNode profile (.symm (Γ := context) (a := source) (b := target) (A := type)) [child])
      Γ context target source type = some ⟨reading.1, reading.2.symm⟩ := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode, evidenceOps] using
    (AnnotatedPredicateReading.Interpreter.read_symm (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) source target type child reading accepted)

theorem read_trans (source middle target type : CTm Tower.Head Γ.length)
    (first second : JudgmentReplay.Certificate profile)
    (left : EqualityReading operations Γ source middle) (right : EqualityReading operations Γ middle target)
    (acceptedLeft : readEquality? operations profile first Γ context source middle type = some left)
    (acceptedRight : readEquality? operations profile second Γ context middle target type = some right) :
    readEquality? operations profile
      (equationNode profile (.trans (Γ := context) (a := source) (b := middle) (c := target) (A := type)) [first, second])
      Γ context source target type = some (EqualityReading.trans left right) := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode, evidenceOps] using
    (AnnotatedPredicateReading.Interpreter.read_trans (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) source middle target type first second left right acceptedLeft acceptedRight)

theorem read_app (f g a b A : CTm Tower.Head Γ.length) (B : CTm Tower.Head (Γ.length + 1))
    (first second : JudgmentReplay.Certificate profile) {domain codomain : HOL.Ty Base}
    (function : EqualityAt operations Γ f g (.arr domain codomain)) (argument : EqualityAt operations Γ a b domain)
    (acceptedFunction : readEquality? operations profile first Γ context f g (.pi A B) = some ⟨_, function⟩)
    (acceptedArgument : readEquality? operations profile second Γ context a b A = some ⟨_, argument⟩) :
    readEquality? operations profile
      (equationNode profile (.appCong (Γ := context) (f := f) (g := g) (a := a) (b := b) (A := A) (B := B)) [first, second])
      Γ context (.app f a) (.app g b) (CTm.inst0 a B) = some ⟨codomain, EqualityAt.app function argument⟩ := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode, evidenceOps] using
    (AnnotatedPredicateReading.Interpreter.read_app (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) f g a b A B first second function argument acceptedFunction acceptedArgument)

theorem read_lam (A A' : CTm Tower.Head Γ.length) (body body' B : CTm Tower.Head (Γ.length + 1)) (u w : Tower.Head)
    (domainCertificate formation bodyCertificate : JudgmentReplay.Certificate profile) {domain codomain : HOL.Ty Base}
    (domains : EqualityAt operations Γ A A' (.arr domain .prop))
    (bodies : EqualityAt operations (domain :: Γ) body body' codomain)
    (acceptedDomain : readEquality? operations profile domainCertificate Γ context A A' (.head w) = some ⟨_, domains⟩)
    (acceptedBody : readEquality? operations profile bodyCertificate (domain :: Γ) (.snoc context A) body body' B = some ⟨_, bodies⟩) :
    readEquality? operations profile
      (equationNode profile (.lamCong (Γ := context) (A := A) (A' := A') (body := body) (body' := body') (B := B) (u := u) (w := w))
        [domainCertificate, formation, bodyCertificate])
      Γ context (.lam A body) (.lam A' body') (.pi A B) = some ⟨.arr domain codomain, EqualityAt.lam domains bodies⟩ := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode, evidenceOps] using
    (AnnotatedPredicateReading.Interpreter.read_lam (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) A A' body body' B u w domainCertificate formation bodyCertificate domains bodies acceptedDomain acceptedBody)

theorem read_pi (A A' : CTm Tower.Head Γ.length) (B B' : CTm Tower.Head (Γ.length + 1)) (u v w : Tower.Head)
    (domainCertificate familyCertificate : JudgmentReplay.Certificate profile) {domain codomain : HOL.Ty Base}
    (domains : EqualityAt operations Γ A A' (.arr domain .prop))
    (families : EqualityAt operations (domain :: Γ) B B' (.arr codomain .prop))
    (acceptedDomain : readEquality? operations profile domainCertificate Γ context A A' (.head u) = some ⟨_, domains⟩)
    (acceptedFamily : readEquality? operations profile familyCertificate (domain :: Γ) (.snoc context A) B B' (.head v) = some ⟨_, families⟩) :
    readEquality? operations profile
      (equationNode profile (.piCong (Γ := context) (A := A) (A' := A') (B := B) (B' := B') (u := u) (v := v) (w := w))
        [domainCertificate, familyCertificate])
      Γ context (.pi A B) (.pi A' B') (.head w) = some ⟨.arr (.arr domain codomain) .prop, EqualityAt.pi domains families⟩ := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode, evidenceOps] using
    (AnnotatedPredicateReading.Interpreter.read_pi (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) A A' B B' u v w domainCertificate familyCertificate domains families acceptedDomain acceptedFamily)

theorem read_convEq (source target A B : CTm Tower.Head Γ.length) (u : Tower.Head)
    (child conversion : JudgmentReplay.Certificate profile) :
    readEquality? operations profile
      (equationNode profile (.convEq (Γ := context) (a := source) (b := target) (A := A) (B := B) (u := u)) [child, conversion])
      Γ context source target B = readEquality? operations profile child Γ context source target A := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode] using
    (AnnotatedPredicateReading.Interpreter.read_convEq (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) source target A B u child conversion)

theorem read_subEq (source target A B : CTm Tower.Head Γ.length)
    (child subtyping : JudgmentReplay.Certificate profile) :
    readEquality? operations profile
      (equationNode profile (.subEq (Γ := context) (a := source) (b := target) (A := A) (B := B)) [child, subtyping])
      Γ context source target B = readEquality? operations profile child Γ context source target A := by
  simpa only [readEquality?, equationNode, AnnotatedPredicateReading.Interpreter.equationNode] using
    (AnnotatedPredicateReading.Interpreter.read_subEq (evidenceOps operations)
      (EqualityCode.natural? operations profile) (Γ := Γ) (context := context) source target A B child subtyping)

theorem admit_reading (source target type : CTm Tower.Head Γ.length)
    (contextCertificate : JudgmentReplay.ContextCertificate profile Γ.length)
    (certificate : JudgmentReplay.Certificate profile) (reading : EqualityReading operations Γ source target)
    (formed : JudgmentReplay.checkContext profile context contextCertificate = true)
    (accepted : JudgmentReplay.check profile certificate (.equality context source target type) = true)
    (interpreted : readEquality? operations profile certificate Γ context source target type = some reading) :
    check? operations profile Γ context source target type contextCertificate certificate =
      some ⟨JudgmentReplay.context_sound profile formed, JudgmentReplay.check_sound profile accepted, reading⟩ := by
  have admitted := AnnotatedPredicateReading.Interpreter.admit_reading
    (church profile) (JudgmentReplay.decoder profile) (evidenceOps operations)
    (EqualityCode.natural? operations profile) Γ context source target type
    contextCertificate certificate reading formed accepted interpreted
  simp only [check?, admitted, Option.map_some]

#print axioms read_root
#print axioms read_beta
#print axioms read_refl
#print axioms read_symm
#print axioms read_trans
#print axioms read_app
#print axioms read_lam
#print axioms read_pi
#print axioms admit_reading

end AnnotatedConversion.CertificateInterpretation
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
