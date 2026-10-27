import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalContextualConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateInterpreter

/-!
# Retained equality readings for incoming annotated derivations

Each value contains the two annotated endpoint readings and an actual retained
HOL proof at one simple carrier. Composition computes carrier and midpoint
agreement from reading coherence. The constructors use the existing primitive
beta proof, natural row proofs and contextual congruence programs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated
open FormationSensitiveHOLInterface (variableIndex)

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    {operations : Operations Base Const} {Γ : HOL.Ctx Base}

structure EqualityAt (operations : Operations Base Const) (Γ : HOL.Ctx Base)
    (source target : CTm Tower.Head Γ.length) (carrier : HOL.Ty Base) where
  left : HOL.Term Const Γ carrier
  right : HOL.Term Const Γ carrier
  leftRead : AnnotatedReads operations source left
  rightRead : AnnotatedReads operations target right
  proof : HOL.ProofSyntax Const (assumptions operations Γ) (.eq left right)
  free : proof.FunctionExtensionalityFree

abbrev EqualityReading (operations : Operations Base Const) (Γ : HOL.Ctx Base)
    (source target : CTm Tower.Head Γ.length) :=
  (carrier : HOL.Ty Base) × EqualityAt operations Γ source target carrier

namespace EqualityAt

def refl {source : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {term : HOL.Term Const Γ carrier} (reading : AnnotatedReads operations source term) :
    EqualityAt operations Γ source source carrier :=
  ⟨term, term, reading, reading, .eqRefl term, True.intro⟩

def symm {source target : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    (reading : EqualityAt operations Γ source target carrier) : EqualityAt operations Γ target source carrier :=
  ⟨reading.right, reading.left, reading.rightRead, reading.leftRead, .eqSymm reading.proof, reading.free⟩

def app {f g a b : CTm Tower.Head Γ.length} {domain codomain : HOL.Ty Base}
    (function : EqualityAt operations Γ f g (.arr domain codomain))
    (argument : EqualityAt operations Γ a b domain) :
    EqualityAt operations Γ (.app f a) (.app g b) codomain :=
  ⟨.app function.left argument.left, .app function.right argument.right,
    .application function.leftRead argument.leftRead, .application function.rightRead argument.rightRead,
    HOL.ProofSyntax.appCongr function.proof argument.proof, ⟨function.free, argument.free⟩⟩

def lam {A A' : CTm Tower.Head Γ.length} {body body' : CTm Tower.Head (Γ.length + 1)}
    {domain codomain : HOL.Ty Base}
    (domains : EqualityAt operations Γ A A' (.arr domain .prop))
    (bodies : EqualityAt operations (domain :: Γ) body body' codomain) :
    EqualityAt operations Γ (.lam A body) (.lam A' body') (.arr domain codomain) where
  left := .lam bodies.left
  right := .lam bodies.right
  leftRead := .abstraction domains.leftRead bodies.leftRead
  rightRead := .abstraction domains.rightRead bodies.rightRead
  proof := .eqLam (HOL.ProofSyntax.castIndices (Contextual.assumptions_weaken operations Γ domain).symm rfl bodies.proof)
  free := by simpa only [HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.ProofSyntax.functionExtensionalityFree_castIndices] using bodies.free

def pi {A A' : CTm Tower.Head Γ.length} {B B' : CTm Tower.Head (Γ.length + 1)}
    {domain codomain : HOL.Ty Base}
    (domains : EqualityAt operations Γ A A' (.arr domain .prop))
    (families : EqualityAt operations (domain :: Γ) B B' (.arr codomain .prop)) :
    EqualityAt operations Γ (.pi A B) (.pi A' B') (.arr (.arr domain codomain) .prop) where
  left := HOL.PredicateProducts.pi domains.left families.left
  right := HOL.PredicateProducts.pi domains.right families.right
  leftRead := .product domains.leftRead families.leftRead
  rightRead := .product domains.rightRead families.rightRead
  proof := HOL.PredicateProducts.congruence domains.proof
    (HOL.ProofSyntax.castIndices (Contextual.assumptions_weaken operations Γ domain).symm rfl families.proof)
  free := HOL.PredicateProducts.congruence_free _ _ domains.free (by
    simpa only [HOL.ProofSyntax.functionExtensionalityFree_castIndices] using families.free)

def beta {A : CTm Tower.Head Γ.length} {body : CTm Tower.Head (Γ.length + 1)}
    {argument : CTm Tower.Head Γ.length} {domain codomain : HOL.Ty Base}
    {domainCode : HOL.Term Const Γ (.arr domain .prop)}
    {bodyCode : HOL.Term Const (domain :: Γ) codomain} {argumentCode : HOL.Term Const Γ domain}
    (domainRead : AnnotatedReads operations A domainCode)
    (bodyRead : AnnotatedReads operations (Γ := domain :: Γ) body bodyCode)
    (argumentRead : AnnotatedReads operations argument argumentCode) :
    EqualityAt operations Γ (.app (.lam A body) argument) (CTm.inst0 argument body) codomain :=
  ⟨.app (.lam bodyCode) argumentCode, HOL.instantiate argumentCode bodyCode,
    .application (.abstraction domainRead bodyRead) argumentRead,
    bodyRead.instantiate argumentRead, .beta argumentCode bodyCode, True.intro⟩

def row (row : Row) (raw : CSub Tower.Head (row.parameters operations).length Γ.length)
    (assignment : HOL.Subst Const (row.parameters operations) Γ)
    (represented : ∀ {type} (index : HOL.Var (row.parameters operations) type),
      AnnotatedReads operations (raw (variableIndex index)) (assignment index)) :
    EqualityAt operations Γ ((row.left operations).subst raw) ((row.right operations).subst raw) operations.result where
  left := HOL.subst assignment (row.leftCode operations)
  right := HOL.subst assignment (row.rightCode operations)
  leftRead := (row.left_reads operations).substitute assignment raw represented
  rightRead := (row.right_reads operations).substitute assignment raw represented
  proof := HOL.ProofSyntax.castIndices (assumptions_substitute operations assignment) rfl
    (HOL.ProofSyntax.subst assignment (row.proof operations))
  free := by simpa only [HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    HOL.ProofSyntax.functionExtensionalityFree_subst] using row.proof_free operations

end EqualityAt

namespace EqualityReading

variable [DecidableEq Base]

def trans {source middle target : CTm Tower.Head Γ.length}
    (first : EqualityReading operations Γ source middle)
    (second : EqualityReading operations Γ middle target) : EqualityReading operations Γ source target := by
  obtain ⟨carrier, first⟩ := first
  obtain ⟨carrier', second⟩ := second
  have same : carrier = carrier' := congrArg Sigma.fst (AnnotatedReading.coherent first.rightRead second.leftRead)
  cases same
  exact ⟨carrier, first.left, second.right, first.leftRead, second.rightRead,
    AnnotatedReading.compose first.rightRead second.leftRead first.proof second.proof,
    AnnotatedReading.compose_free _ _ _ _ first.free second.free⟩

end EqualityReading

/-- Nat retains its extensionality-free evidence while using the shared
traversal. The view supplies the actual proof under the common closed premises. -/
def evidenceOps [DecidableEq Base] (operations : Operations Base Const) :
    AnnotatedPredicateReading.Interpreter.EvidenceOps (lexicalReading operations) (closedAssumptions operations) where
  Evidence := EqualityAt operations
  view := fun evidence => ⟨evidence.left, evidence.right, evidence.leftRead.toGeneric, evidence.rightRead.toGeneric,
    HOL.ProofSyntax.castIndices (assumptions_eq_closed operations _) rfl evidence.proof⟩
  refl := fun reading => EqualityAt.refl (AnnotatedReads.ofGeneric reading)
  symm := EqualityAt.symm
  trans := EqualityReading.trans
  app := EqualityAt.app
  lam := EqualityAt.lam
  pi := EqualityAt.pi
  beta := fun domain body argument => EqualityAt.beta
    (AnnotatedReads.ofGeneric domain) (AnnotatedReads.ofGeneric body) (AnnotatedReads.ofGeneric argument)

#print axioms evidenceOps

#print axioms EqualityAt.row
#print axioms EqualityAt.pi
#print axioms EqualityReading.trans

end AnnotatedConversion
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
