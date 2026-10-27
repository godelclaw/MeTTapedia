import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalPredicateReading

/-!
# The original natural telescope and computation rows in the predicate reading

These are the declared `natEliminateType` and its original zero/successor
rows, not independently invented copies of the dependent signature. The
target products retain all guards, and the four parameter roles keep their
source order. The reading witnesses compose with the generic simultaneous
substitution law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation NativeNaturalVectorFamilies

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

namespace Operations

def motiveCode (operations : Operations Base Const) :
    HOL.ClosedTerm Const (.arr operations.motiveType .prop) :=
  HOL.PredicateProducts.pi (HOL.PredicateProducts.full operations.number)
    (HOL.PredicateProducts.full (.arr operations.result .prop))

def zeroCode (operations : Operations Base Const) :
    HOL.Term Const [operations.motiveType] (.arr operations.result .prop) :=
  .app (.var .vz) (HOL.weakenCtx _ operations.zero)

def methodPredicate (operations : Operations Base Const) {Γ : HOL.Ctx Base}
    (family : HOL.Term Const Γ operations.motiveType) :
    HOL.Term Const Γ (.arr operations.methodType .prop) :=
  HOL.PredicateProducts.pi (HOL.PredicateProducts.full operations.number)
    (HOL.PredicateProducts.pi (.app (HOL.weaken family) (.var .vz))
      (.app (HOL.weaken (HOL.weaken family))
        (.app (HOL.weakenCtx _ operations.successor) (.var (.vs .vz)))))

def resultPredicate (operations : Operations Base Const) {Γ : HOL.Ctx Base}
    (family : HOL.Term Const Γ operations.motiveType) :
    HOL.Term Const Γ (.arr (.arr operations.number operations.result) .prop) :=
  HOL.PredicateProducts.pi (HOL.PredicateProducts.full operations.number)
    (.app (HOL.weaken family) (.var .vz))

def stepCode (operations : Operations Base Const) :
    HOL.Term Const [operations.result, operations.motiveType] (.arr operations.methodType .prop) :=
  operations.methodPredicate (.var (.vs .vz))

def resultCode (operations : Operations Base Const) :
    HOL.Term Const [operations.methodType, operations.result, operations.motiveType]
      (.arr (.arr operations.number operations.result) .prop) :=
  operations.resultPredicate (.var (.vs (.vs .vz)))

def eliminatorCode (operations : Operations Base Const) :
    HOL.ClosedTerm Const (.arr operations.eliminatorType .prop) :=
  HOL.PredicateProducts.pi operations.motiveCode
    (HOL.PredicateProducts.pi operations.zeroCode
      (HOL.PredicateProducts.pi operations.stepCode operations.resultCode))

@[simp] theorem rename_methodPredicate (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}
    (ρ : HOL.Rename Base Γ Ξ) (family : HOL.Term Const Γ operations.motiveType) :
    HOL.rename ρ (operations.methodPredicate family) =
      operations.methodPredicate (HOL.rename ρ family) := by
  simp only [methodPredicate, HOL.PredicateProducts.rename_pi, HOL.PredicateProducts.rename_full,
    HOL.rename, HOL.rename_weakenCtx]
  simp only [HOL.weaken, HOL.rename_comp, HOL.Rename.lift, HOL.Rename.weaken]

@[simp] theorem rename_resultPredicate (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}
    (ρ : HOL.Rename Base Γ Ξ) (family : HOL.Term Const Γ operations.motiveType) :
    HOL.rename ρ (operations.resultPredicate family) =
      operations.resultPredicate (HOL.rename ρ family) := by
  simp [resultPredicate, HOL.rename, HOL.weaken, HOL.rename_comp,
    HOL.Rename.lift, HOL.Rename.weaken]

theorem motiveCode_reads (operations : Operations Base Const) :
    Reads operations (Γ := []) natMotiveType operations.motiveCode :=
  .product .natural .motiveUniverse

theorem zeroCode_reads (operations : Operations Base Const) :
    Reads operations (Γ := [operations.motiveType]) natZeroCaseType operations.zeroCode :=
  .application (Reads.var (operations := operations) (Γ := [operations.motiveType]) .vz) .zero

theorem stepCode_reads (operations : Operations Base Const) :
    Reads operations (Γ := [operations.result, operations.motiveType]) natSuccCaseType operations.stepCode :=
  .product .natural (.product
    (.application
      (Reads.var (operations := operations) (Γ := [operations.number, operations.result, operations.motiveType]) (.vs (.vs .vz)))
      (Reads.var (operations := operations) (Γ := [operations.number, operations.result, operations.motiveType]) .vz))
    (.application
      (Reads.var (operations := operations) (Γ := [operations.result, operations.number, operations.result, operations.motiveType]) (.vs (.vs (.vs .vz))))
      (.application .successor
        (Reads.var (operations := operations) (Γ := [operations.result, operations.number, operations.result, operations.motiveType]) (.vs .vz)))))

theorem resultCode_reads (operations : Operations Base Const) :
    Reads operations (Γ := [operations.methodType, operations.result, operations.motiveType]) natEliminateResultType operations.resultCode :=
  .product .natural (.application (Reads.var (operations := operations) (Γ := [operations.number, operations.methodType, operations.result, operations.motiveType]) (.vs (.vs (.vs .vz)))) (Reads.var (operations := operations) (Γ := [operations.number, operations.methodType, operations.result, operations.motiveType]) .vz))

/-- Structural translation of the independently declared eliminator type. -/
theorem eliminatorCode_reads (operations : Operations Base Const) :
    Reads operations (Γ := []) natEliminateType operations.eliminatorCode :=
  .product operations.motiveCode_reads (.product operations.zeroCode_reads
    (.product operations.stepCode_reads operations.resultCode_reads))

abbrev parameters (operations : Operations Base Const) : HOL.Ctx Base :=
  [operations.methodType, operations.result, operations.motiveType]

abbrev successorParameters (operations : Operations Base Const) : HOL.Ctx Base :=
  operations.number :: operations.parameters

def atParameters (operations : Operations Base Const) :
    HOL.Term Const operations.parameters (.arr operations.number operations.result) :=
  .app (.app (.app operations.eliminator
    (.var (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz)

def zeroLeft (operations : Operations Base Const) :
    HOL.Term Const operations.parameters operations.result :=
  .app operations.atParameters (HOL.weakenCtx _ operations.zero)

def zeroRight (operations : Operations Base Const) :
    HOL.Term Const operations.parameters operations.result := .var (.vs .vz)

def successorLeft (operations : Operations Base Const) :
    HOL.Term Const operations.successorParameters operations.result :=
  .app (HOL.weaken operations.atParameters)
    (.app (HOL.weakenCtx _ operations.successor) (.var .vz))

def successorRight (operations : Operations Base Const) :
    HOL.Term Const operations.successorParameters operations.result :=
  .app (.app (.var (.vs .vz)) (.var .vz))
    (.app (HOL.weaken operations.atParameters) (.var .vz))

theorem atParameters_reads (operations : Operations Base Const) :
    Reads operations (Γ := operations.parameters) natEliminateAtParameters operations.atParameters :=
  .application (.application (.application .eliminator (Reads.var (operations := operations) (Γ := operations.parameters) (.vs (.vs .vz))))
    (Reads.var (operations := operations) (Γ := operations.parameters) (.vs .vz))) (Reads.var (operations := operations) (Γ := operations.parameters) .vz)

theorem zeroLeft_reads (operations : Operations Base Const) :
    Reads operations (Γ := operations.parameters) natZeroIotaLeft operations.zeroLeft :=
  .application operations.atParameters_reads .zero

theorem zeroRight_reads (operations : Operations Base Const) :
    Reads operations (Γ := operations.parameters) natZeroIotaRight operations.zeroRight := Reads.var (operations := operations) (Γ := operations.parameters) (.vs .vz)

theorem successorLeft_reads (operations : Operations Base Const) :
    Reads operations (Γ := operations.successorParameters) natSuccIotaLeft operations.successorLeft :=
  .application
    (operations.atParameters_reads.rename HOL.Rename.weaken wk (fun _ => rfl))
    (.application .successor (Reads.var (operations := operations) (Γ := operations.successorParameters) .vz))

theorem successorRight_reads (operations : Operations Base Const) :
    Reads operations (Γ := operations.successorParameters) natSuccIotaRight operations.successorRight :=
  .application (.application (Reads.var (operations := operations) (Γ := operations.successorParameters) (.vs .vz)) (Reads.var (operations := operations) (Γ := operations.successorParameters) .vz))
    (.application
      (operations.atParameters_reads.rename HOL.Rename.weaken wk (fun _ => rfl))
      (Reads.var (operations := operations) (Γ := operations.successorParameters) .vz))

/-- The actual source row is transported by the same substitutions used in
the source calculus and the target HOL context. -/
theorem zeroLeft_substituted (operations : Operations Base Const)
    {Γ : HOL.Ctx Base} (θ : HOL.Subst Const operations.parameters Γ)
    (raw : Sub Tower.Head operations.parameters.length Γ.length)
    (components : ∀ {type} (index : HOL.Var operations.parameters type),
      Reads operations (raw (FormationSensitiveHOLInterface.variableIndex index)) (θ index)) :
    Reads operations (Presentation.subst raw natZeroIotaLeft) (HOL.subst θ operations.zeroLeft) :=
  operations.zeroLeft_reads.substitute θ raw components

theorem successorRight_substituted (operations : Operations Base Const)
    {Γ : HOL.Ctx Base} (θ : HOL.Subst Const operations.successorParameters Γ)
    (raw : Sub Tower.Head operations.successorParameters.length Γ.length)
    (components : ∀ {type} (index : HOL.Var operations.successorParameters type),
      Reads operations (raw (FormationSensitiveHOLInterface.variableIndex index)) (θ index)) :
    Reads operations (Presentation.subst raw natSuccIotaRight) (HOL.subst θ operations.successorRight) :=
  operations.successorRight_reads.substitute θ raw components

end Operations

#print axioms Operations.eliminatorCode_reads
#print axioms Operations.zeroLeft_reads
#print axioms Operations.successorRight_reads
#print axioms Operations.zeroLeft_substituted
#print axioms Operations.successorRight_substituted

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
