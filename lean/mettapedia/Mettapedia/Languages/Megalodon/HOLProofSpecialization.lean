import Mettapedia.Languages.Megalodon.HOLProofInference
import Mettapedia.Logic.HOL.Syntax.SubstitutionExtension

/-!
# Native universal specialization by simultaneous substitution

Successive source arguments extend one substitution. These constructions keep
the actual nested native applications while exposing a single source
substitution, so concrete proof schemas share the same binding calculation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLProofSpecialization

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLProofInference

variable {environment : Environment} {gamma : Ctx Base} {firstType secondType thirdType : Ty Base}
variable {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}

theorem allE2 {program : Pf}
    {body : Formula (Constant environment) (secondType :: firstType :: gamma)}
    (first : Term (Constant environment) gamma firstType)
    (second : Term (Constant environment) gamma secondType)
    (firstFormed : plainAnnotations depth (native first) = true)
    (secondFormed : plainAnnotations depth (native second) = true)
    (firstNormal : DeltaNormalInvariant.Normal environment (native first))
    (secondNormal : DeltaNormalInvariant.Normal environment (native second))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.all (.all body))) :
    Infers depth assumptions (.termApp (.termApp program (native first)) (native second))
      (subst (Subst.cons second (Subst.single first)) body) := by
  have one := HOLProofInference.allE first firstFormed firstNormal contextNormal inferred
  change Infers depth assumptions _ (.all (subst (Subst.lift (Subst.single first)) body)) at one
  have two := HOLProofInference.allE second secondFormed secondNormal contextNormal one
  simpa only [instantiate_subst_lift] using two

theorem allE3 {program : Pf}
    {body : Formula (Constant environment) (thirdType :: secondType :: firstType :: gamma)}
    (first : Term (Constant environment) gamma firstType)
    (second : Term (Constant environment) gamma secondType)
    (third : Term (Constant environment) gamma thirdType)
    (firstFormed : plainAnnotations depth (native first) = true)
    (secondFormed : plainAnnotations depth (native second) = true)
    (thirdFormed : plainAnnotations depth (native third) = true)
    (firstNormal : DeltaNormalInvariant.Normal environment (native first))
    (secondNormal : DeltaNormalInvariant.Normal environment (native second))
    (thirdNormal : DeltaNormalInvariant.Normal environment (native third))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.all (.all (.all body)))) :
    Infers depth assumptions
      (.termApp (.termApp (.termApp program (native first)) (native second)) (native third))
      (subst (Subst.cons third (Subst.cons second (Subst.single first))) body) := by
  have two := allE2 first second firstFormed secondFormed firstNormal secondNormal contextNormal inferred
  change Infers depth assumptions _
    (.all (subst (Subst.lift (Subst.cons second (Subst.single first))) body)) at two
  have three := HOLProofInference.allE third thirdFormed thirdNormal contextNormal two
  simpa only [instantiate_subst_lift] using three

#print axioms allE2
#print axioms allE3

end Mettapedia.Languages.Megalodon.HOLProofSpecialization
