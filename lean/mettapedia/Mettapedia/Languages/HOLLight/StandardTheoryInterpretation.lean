import Mettapedia.Languages.HOLLight.SourceProfile

/-!
# Registered source Boolean definitions and their interpretation

The source bodies retain the names, type annotations and declaration identities
of HOL Light revision `924faf0c3471a04174ffdeb8576ce7cabcb92d64`.
Each body enters through the existing declaration checker. Model construction
uses the admitted polymorphic extension rather than assigning Boolean meanings
by theorem names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.StandardTheoryInterpretation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open DefinitionAdapters SignatureFormation ModelInterpretation

universe w

namespace Source

@[irreducible] def truthBody : SourceTerm :=
  (.app (.app (.const Const.equality (Ty.function (Ty.function Ty.bool Ty.bool) (Ty.function (Ty.function Ty.bool Ty.bool) Ty.bool))) (.abs (Name.global "p") Ty.bool (.var (Name.global "p") Ty.bool))) (.abs (Name.global "p") Ty.bool (.var (Name.global "p") Ty.bool)))

def truthConstant : Const :=
  .mk (Name.global "T") (.defined truthBody)

def truthSchema : Ty := Ty.bool

theorem truthAdmission :
    (admitConstantInTheory SourceProfile.primitiveContext
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
      (Name.global "T") truthBody).isSome = true := by decide +kernel

@[irreducible] def truthResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory SourceProfile.primitiveContext
    (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
    (Name.global "T") truthBody).get truthAdmission

theorem truthAdmitted :
    admitConstantInTheory SourceProfile.primitiveContext
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
      (Name.global "T") truthBody = some truthResult := by
  unfold truthResult
  exact (Option.some_get truthAdmission).symm

theorem truthIdentity : truthResult.output.constant = truthConstant :=
  (ConstantAdmission.source_equation truthAdmitted).1

theorem truthType : truthResult.definition.ty = truthSchema :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

@[irreducible] def truthContext : TheoryContext := truthResult.context

@[irreducible] def conjunctionBody : SourceTerm :=
  (.abs (Name.global "p") Ty.bool (.abs (Name.global "q") Ty.bool (.app (.app (.const Const.equality (Ty.function (Ty.function (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) Ty.bool) (Ty.function (Ty.function (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) Ty.bool) Ty.bool))) (.abs (Name.global "f") (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (.app (.app (.var (Name.global "f") (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.var (Name.global "p") Ty.bool)) (.var (Name.global "q") Ty.bool)))) (.abs (Name.global "f") (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (.app (.app (.var (Name.global "f") (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.const truthConstant Ty.bool)) (.const truthConstant Ty.bool))))))

def conjunctionConstant : Const :=
  .mk (Name.global "/\\") (.defined conjunctionBody)

def conjunctionSchema : Ty := (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))

theorem conjunctionAdmission :
    (admitConstantInTheory truthContext
      (ExportReplay.instanceCertificates truthContext.signature)
      (Name.global "/\\") conjunctionBody).isSome = true := by decide +kernel

@[irreducible] def conjunctionResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory truthContext
    (ExportReplay.instanceCertificates truthContext.signature)
    (Name.global "/\\") conjunctionBody).get conjunctionAdmission

theorem conjunctionAdmitted :
    admitConstantInTheory truthContext
      (ExportReplay.instanceCertificates truthContext.signature)
      (Name.global "/\\") conjunctionBody = some conjunctionResult := by
  unfold conjunctionResult
  exact (Option.some_get conjunctionAdmission).symm

theorem conjunctionIdentity : conjunctionResult.output.constant = conjunctionConstant :=
  (ConstantAdmission.source_equation conjunctionAdmitted).1

theorem conjunctionType : conjunctionResult.definition.ty = conjunctionSchema :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

@[irreducible] def conjunctionContext : TheoryContext := conjunctionResult.context

@[irreducible] def implicationBody : SourceTerm :=
  (.abs (Name.global "p") Ty.bool (.abs (Name.global "q") Ty.bool (.app (.app (.const Const.equality (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.app (.const conjunctionConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.var (Name.global "p") Ty.bool)) (.var (Name.global "q") Ty.bool))) (.var (Name.global "p") Ty.bool))))

def implicationConstant : Const :=
  .mk (Name.global "==>") (.defined implicationBody)

def implicationSchema : Ty := (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))

theorem implicationAdmission :
    (admitConstantInTheory conjunctionContext
      (ExportReplay.instanceCertificates conjunctionContext.signature)
      (Name.global "==>") implicationBody).isSome = true := by decide +kernel

@[irreducible] def implicationResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory conjunctionContext
    (ExportReplay.instanceCertificates conjunctionContext.signature)
    (Name.global "==>") implicationBody).get implicationAdmission

theorem implicationAdmitted :
    admitConstantInTheory conjunctionContext
      (ExportReplay.instanceCertificates conjunctionContext.signature)
      (Name.global "==>") implicationBody = some implicationResult := by
  unfold implicationResult
  exact (Option.some_get implicationAdmission).symm

theorem implicationIdentity : implicationResult.output.constant = implicationConstant :=
  (ConstantAdmission.source_equation implicationAdmitted).1

theorem implicationType : implicationResult.definition.ty = implicationSchema :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

@[irreducible] def implicationContext : TheoryContext := implicationResult.context

@[irreducible] def universalBody : SourceTerm :=
  (.abs (Name.global "P") (Ty.function (.var (Name.global "A")) Ty.bool) (.app (.app (.const Const.equality (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool))) (.var (Name.global "P") (Ty.function (.var (Name.global "A")) Ty.bool))) (.abs (Name.global "x") (.var (Name.global "A")) (.const truthConstant Ty.bool))))

def universalConstant : Const :=
  .mk (Name.global "!") (.defined universalBody)

def universalSchema : Ty := (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)

theorem universalAdmission :
    (admitConstantInTheory implicationContext
      (ExportReplay.instanceCertificates implicationContext.signature)
      (Name.global "!") universalBody).isSome = true := by decide +kernel

@[irreducible] def universalResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory implicationContext
    (ExportReplay.instanceCertificates implicationContext.signature)
    (Name.global "!") universalBody).get universalAdmission

theorem universalAdmitted :
    admitConstantInTheory implicationContext
      (ExportReplay.instanceCertificates implicationContext.signature)
      (Name.global "!") universalBody = some universalResult := by
  unfold universalResult
  exact (Option.some_get universalAdmission).symm

theorem universalIdentity : universalResult.output.constant = universalConstant :=
  (ConstantAdmission.source_equation universalAdmitted).1

theorem universalType : universalResult.definition.ty = universalSchema :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

@[irreducible] def universalContext : TheoryContext := universalResult.context

@[irreducible] def existentialBody : SourceTerm :=
  (.abs (Name.global "P") (Ty.function (.var (Name.global "A")) Ty.bool) (.app (.const universalConstant (Ty.function (Ty.function Ty.bool Ty.bool) Ty.bool)) (.abs (Name.global "q") Ty.bool (.app (.app (.const implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.const universalConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (Name.global "x") (.var (Name.global "A")) (.app (.app (.const implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.var (Name.global "P") (Ty.function (.var (Name.global "A")) Ty.bool)) (.var (Name.global "x") (.var (Name.global "A"))))) (.var (Name.global "q") Ty.bool))))) (.var (Name.global "q") Ty.bool)))))

def existentialConstant : Const :=
  .mk (Name.global "?") (.defined existentialBody)

def existentialSchema : Ty := (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)

theorem existentialAdmission :
    (admitConstantInTheory universalContext
      (ExportReplay.instanceCertificates universalContext.signature)
      (Name.global "?") existentialBody).isSome = true := by decide +kernel

@[irreducible] def existentialResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory universalContext
    (ExportReplay.instanceCertificates universalContext.signature)
    (Name.global "?") existentialBody).get existentialAdmission

theorem existentialAdmitted :
    admitConstantInTheory universalContext
      (ExportReplay.instanceCertificates universalContext.signature)
      (Name.global "?") existentialBody = some existentialResult := by
  unfold existentialResult
  exact (Option.some_get existentialAdmission).symm

theorem existentialIdentity : existentialResult.output.constant = existentialConstant :=
  (ConstantAdmission.source_equation existentialAdmitted).1

theorem existentialType : existentialResult.definition.ty = existentialSchema :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

@[irreducible] def existentialContext : TheoryContext := existentialResult.context

@[irreducible] def falsityBody : SourceTerm :=
  (.app (.const universalConstant (Ty.function (Ty.function Ty.bool Ty.bool) Ty.bool)) (.abs (Name.global "p") Ty.bool (.var (Name.global "p") Ty.bool)))

def falsityConstant : Const :=
  .mk (Name.global "F") (.defined falsityBody)

def falsitySchema : Ty := Ty.bool

theorem falsityAdmission :
    (admitConstantInTheory existentialContext
      (ExportReplay.instanceCertificates existentialContext.signature)
      (Name.global "F") falsityBody).isSome = true := by decide +kernel

@[irreducible] def falsityResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory existentialContext
    (ExportReplay.instanceCertificates existentialContext.signature)
    (Name.global "F") falsityBody).get falsityAdmission

theorem falsityAdmitted :
    admitConstantInTheory existentialContext
      (ExportReplay.instanceCertificates existentialContext.signature)
      (Name.global "F") falsityBody = some falsityResult := by
  unfold falsityResult
  exact (Option.some_get falsityAdmission).symm

theorem falsityIdentity : falsityResult.output.constant = falsityConstant :=
  (ConstantAdmission.source_equation falsityAdmitted).1

theorem falsityType : falsityResult.definition.ty = falsitySchema :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

@[irreducible] def falsityContext : TheoryContext := falsityResult.context

@[irreducible] def negationBody : SourceTerm :=
  (.abs (Name.global "p") Ty.bool (.app (.app (.const implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.var (Name.global "p") Ty.bool)) (.const falsityConstant Ty.bool)))

def negationConstant : Const :=
  .mk (Name.global "~") (.defined negationBody)

def negationSchema : Ty := (Ty.function Ty.bool Ty.bool)

theorem negationAdmission :
    (admitConstantInTheory falsityContext
      (ExportReplay.instanceCertificates falsityContext.signature)
      (Name.global "~") negationBody).isSome = true := by decide +kernel

@[irreducible] def negationResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory falsityContext
    (ExportReplay.instanceCertificates falsityContext.signature)
    (Name.global "~") negationBody).get negationAdmission

theorem negationAdmitted :
    admitConstantInTheory falsityContext
      (ExportReplay.instanceCertificates falsityContext.signature)
      (Name.global "~") negationBody = some negationResult := by
  unfold negationResult
  exact (Option.some_get negationAdmission).symm

theorem negationIdentity : negationResult.output.constant = negationConstant :=
  (ConstantAdmission.source_equation negationAdmitted).1

theorem negationType : negationResult.definition.ty = negationSchema :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

@[irreducible] def negationContext : TheoryContext := negationResult.context

@[irreducible] def oneOneBody : SourceTerm :=
  (.abs (Name.global "_2064") (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) (.app (.const universalConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (Name.global "x1") (.var (Name.global "A")) (.app (.const universalConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (Name.global "x2") (.var (Name.global "A")) (.app (.app (.const implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.app (.const Const.equality (Ty.function (.var (Name.global "B")) (Ty.function (.var (Name.global "B")) Ty.bool))) (.app (.var (Name.global "_2064") (Ty.function (.var (Name.global "A")) (.var (Name.global "B")))) (.var (Name.global "x1") (.var (Name.global "A"))))) (.app (.var (Name.global "_2064") (Ty.function (.var (Name.global "A")) (.var (Name.global "B")))) (.var (Name.global "x2") (.var (Name.global "A")))))) (.app (.app (.const Const.equality (Ty.function (.var (Name.global "A")) (Ty.function (.var (Name.global "A")) Ty.bool))) (.var (Name.global "x1") (.var (Name.global "A")))) (.var (Name.global "x2") (.var (Name.global "A"))))))))))

def oneOneConstant : Const :=
  .mk (Name.global "ONE_ONE") (.defined oneOneBody)

def oneOneSchema : Ty := (Ty.function (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) Ty.bool)

theorem oneOneAdmission :
    (admitConstantInTheory negationContext
      (ExportReplay.instanceCertificates negationContext.signature)
      (Name.global "ONE_ONE") oneOneBody).isSome = true := by decide +kernel

@[irreducible] def oneOneResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory negationContext
    (ExportReplay.instanceCertificates negationContext.signature)
    (Name.global "ONE_ONE") oneOneBody).get oneOneAdmission

theorem oneOneAdmitted :
    admitConstantInTheory negationContext
      (ExportReplay.instanceCertificates negationContext.signature)
      (Name.global "ONE_ONE") oneOneBody = some oneOneResult := by
  unfold oneOneResult
  exact (Option.some_get oneOneAdmission).symm

theorem oneOneIdentity : oneOneResult.output.constant = oneOneConstant :=
  (ConstantAdmission.source_equation oneOneAdmitted).1

theorem oneOneType : oneOneResult.definition.ty = oneOneSchema :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

@[irreducible] def oneOneContext : TheoryContext := oneOneResult.context

@[irreducible] def ontoBody : SourceTerm :=
  (.abs (Name.global "_2069") (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) (.app (.const universalConstant (Ty.function (Ty.function (.var (Name.global "B")) Ty.bool) Ty.bool)) (.abs (Name.global "y") (.var (Name.global "B")) (.app (.const existentialConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (Name.global "x") (.var (Name.global "A")) (.app (.app (.const Const.equality (Ty.function (.var (Name.global "B")) (Ty.function (.var (Name.global "B")) Ty.bool))) (.var (Name.global "y") (.var (Name.global "B")))) (.app (.var (Name.global "_2069") (Ty.function (.var (Name.global "A")) (.var (Name.global "B")))) (.var (Name.global "x") (.var (Name.global "A"))))))))))

def ontoConstant : Const :=
  .mk (Name.global "ONTO") (.defined ontoBody)

def ontoSchema : Ty := (Ty.function (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) Ty.bool)

theorem ontoAdmission :
    (admitConstantInTheory oneOneContext
      (ExportReplay.instanceCertificates oneOneContext.signature)
      (Name.global "ONTO") ontoBody).isSome = true := by decide +kernel

@[irreducible] def ontoResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory oneOneContext
    (ExportReplay.instanceCertificates oneOneContext.signature)
    (Name.global "ONTO") ontoBody).get ontoAdmission

theorem ontoAdmitted :
    admitConstantInTheory oneOneContext
      (ExportReplay.instanceCertificates oneOneContext.signature)
      (Name.global "ONTO") ontoBody = some ontoResult := by
  unfold ontoResult
  exact (Option.some_get ontoAdmission).symm

theorem ontoIdentity : ontoResult.output.constant = ontoConstant :=
  (ConstantAdmission.source_equation ontoAdmitted).1

theorem ontoType : ontoResult.definition.ty = ontoSchema :=
  (Ty.same_eq_true_iff _ _).mp (by decide +kernel)

@[irreducible] def ontoContext : TheoryContext := ontoResult.context

def etaAxiom : SourceTerm :=
  (.app (.const universalConstant (Ty.function (Ty.function (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) Ty.bool) Ty.bool)) (.abs (Name.global "t") (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) (.app (.app (.const Const.equality (Ty.function (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) (Ty.function (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) Ty.bool))) (.abs (Name.global "x") (.var (Name.global "A")) (.app (.var (Name.global "t") (Ty.function (.var (Name.global "A")) (.var (Name.global "B")))) (.var (Name.global "x") (.var (Name.global "A")))))) (.var (Name.global "t") (Ty.function (.var (Name.global "A")) (.var (Name.global "B")))))))

def selectionAxiom : SourceTerm :=
  (.app (.const universalConstant (Ty.function (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool) Ty.bool)) (.abs (Name.global "P") (Ty.function (.var (Name.global "A")) Ty.bool) (.app (.const universalConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (Name.global "x") (.var (Name.global "A")) (.app (.app (.const implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.var (Name.global "P") (Ty.function (.var (Name.global "A")) Ty.bool)) (.var (Name.global "x") (.var (Name.global "A"))))) (.app (.var (Name.global "P") (Ty.function (.var (Name.global "A")) Ty.bool)) (.app (.const ModelInterpretation.selectionConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) (.var (Name.global "A")))) (.var (Name.global "P") (Ty.function (.var (Name.global "A")) Ty.bool)))))))))

def infinityAxiom : SourceTerm :=
  (.app (.const existentialConstant (Ty.function (Ty.function (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator [])) Ty.bool) Ty.bool)) (.abs (Name.global "f") (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator [])) (.app (.app (.const conjunctionConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.const oneOneConstant (Ty.function (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator [])) Ty.bool)) (.var (Name.global "f") (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator []))))) (.app (.const negationConstant (Ty.function Ty.bool Ty.bool)) (.app (.const ontoConstant (Ty.function (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator [])) Ty.bool)) (.var (Name.global "f") (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator []))))))))

end Source

namespace Raw

private theorem defined_not_equality (name : Name) (body : SourceTerm) (annotation : Ty) :
    equalityOperand? (.mk name (.defined body)) annotation = none := by
  have different : Const.mk name (.defined body) ≠ Const.equality := by
    intro equal
    cases equal
  simp [equalityOperand?, Const.same_eq_true_iff, different]

private theorem truth_sourceDB : Source.truthBody.toDB [] =
    (.app (.app (.const Const.equality (Ty.function (Ty.function Ty.bool Ty.bool) (Ty.function (Ty.function Ty.bool Ty.bool) Ty.bool))) (.abs Ty.bool (.bound 0))) (.abs Ty.bool (.bound 0))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def truth :
    HOL.ClosedTerm Symbol HOL.Ty.prop :=
  (.eq ((.lam (.var .vz)) : HOL.Term Symbol [] (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)) (.lam (.var .vz)))

theorem truth_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.truthBody.toDB [])) HOL.Ty.prop
      (truth) := by
  rw [truth_sourceDB]
  simp only [TermSubst.applyDB, truth, TypeSubst.apply_function, TypeSubst.apply_bool]
  refine Translates.equalityApp (σ := (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))
    (by simpa [Ty.equality] using equalityOperand?_equality (substitution.apply (Ty.function Ty.bool Ty.bool))) (by simp) ?_ ?_
  · refine Translates.abs (σ := HOL.Ty.prop) (by simp) ?_
    exact Translates.bound .vz
  · refine Translates.abs (σ := HOL.Ty.prop) (by simp) ?_
    exact Translates.bound .vz

private theorem conjunction_sourceDB : Source.conjunctionBody.toDB [] =
    (.abs Ty.bool (.abs Ty.bool (.app (.app (.const Const.equality (Ty.function (Ty.function (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) Ty.bool) (Ty.function (Ty.function (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) Ty.bool) Ty.bool))) (.abs (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (.app (.app (.bound 0) (.bound 2)) (.bound 1)))) (.abs (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (.app (.app (.bound 0) (.const Source.truthConstant Ty.bool)) (.const Source.truthConstant Ty.bool)))))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def conjunction :
    HOL.ClosedTerm Symbol (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)) :=
  (.lam (.lam (.eq ((.lam (.app (.app (.var .vz) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))) : HOL.Term Symbol [HOL.Ty.prop, HOL.Ty.prop] (HOL.Ty.arr (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)) HOL.Ty.prop)) (.lam (.app (.app (.var .vz) ((.const (.constant Source.truthConstant Ty.bool (by simp))) : HOL.Term Symbol [(HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)), HOL.Ty.prop, HOL.Ty.prop] HOL.Ty.prop)) ((.const (.constant Source.truthConstant Ty.bool (by simp))) : HOL.Term Symbol [(HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)), HOL.Ty.prop, HOL.Ty.prop] HOL.Ty.prop))))))

theorem conjunction_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.conjunctionBody.toDB [])) (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))
      (conjunction) := by
  rw [conjunction_sourceDB]
  simp only [TermSubst.applyDB, conjunction, TypeSubst.apply_function, TypeSubst.apply_bool]
  refine Translates.abs (σ := HOL.Ty.prop) (by simp) ?_
  refine Translates.abs (σ := HOL.Ty.prop) (by simp) ?_
  refine Translates.equalityApp (σ := (HOL.Ty.arr (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)) HOL.Ty.prop))
    (by simpa [Ty.equality] using equalityOperand?_equality (substitution.apply (Ty.function (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) Ty.bool))) (by simp) ?_ ?_
  · refine Translates.abs (σ := (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))) (by simp) ?_
    refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
    · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
      · exact Translates.bound .vz
      · exact Translates.bound (.vs (.vs .vz))
    · exact Translates.bound (.vs .vz)
  · refine Translates.abs (σ := (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))) (by simp) ?_
    refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
    · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
      · exact Translates.bound .vz
      · exact Translates.constant (by apply defined_not_equality) (by simp)
    · exact Translates.constant (by apply defined_not_equality) (by simp)

private theorem implication_sourceDB : Source.implicationBody.toDB [] =
    (.abs Ty.bool (.abs Ty.bool (.app (.app (.const Const.equality (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.app (.const Source.conjunctionConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.bound 1)) (.bound 0))) (.bound 1)))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def implication :
    HOL.ClosedTerm Symbol (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)) :=
  (.lam (.lam (.eq ((.app (.app ((.const (.constant Source.conjunctionConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (by simp))) : HOL.Term Symbol [HOL.Ty.prop, HOL.Ty.prop] (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))) (.var (.vs .vz))) (.var .vz)) : HOL.Term Symbol [HOL.Ty.prop, HOL.Ty.prop] HOL.Ty.prop) (.var (.vs .vz)))))

theorem implication_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.implicationBody.toDB [])) (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))
      (implication) := by
  rw [implication_sourceDB]
  simp only [TermSubst.applyDB, implication, TypeSubst.apply_function, TypeSubst.apply_bool]
  refine Translates.abs (σ := HOL.Ty.prop) (by simp) ?_
  refine Translates.abs (σ := HOL.Ty.prop) (by simp) ?_
  refine Translates.equalityApp (σ := HOL.Ty.prop)
    (by simpa [Ty.equality] using equalityOperand?_equality (substitution.apply Ty.bool)) (by simp) ?_ ?_
  · refine Translates.app (σ := HOL.Ty.prop) (by simp only [DBTerm.equalityHeadOperand?]; apply defined_not_equality) ?_ ?_
    · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
      · exact Translates.constant (by apply defined_not_equality) (by simp)
      · exact Translates.bound (.vs .vz)
    · exact Translates.bound .vz
  · exact Translates.bound (.vs .vz)

private theorem universal_sourceDB : Source.universalBody.toDB [] =
    (.abs (Ty.function (.var (Name.global "A")) Ty.bool) (.app (.app (.const Const.equality (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool))) (.bound 0)) (.abs (.var (Name.global "A")) (.const Source.truthConstant Ty.bool)))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def universal (operand : HOL.Ty AtomicTy) :
    HOL.ClosedTerm Symbol (HOL.Ty.arr (HOL.Ty.arr operand HOL.Ty.prop) HOL.Ty.prop) :=
  (.lam (.eq ((.var .vz) : HOL.Term Symbol [(HOL.Ty.arr operand HOL.Ty.prop)] (HOL.Ty.arr operand HOL.Ty.prop)) (.lam ((.const (.constant Source.truthConstant Ty.bool (by simp))) : HOL.Term Symbol [operand, (HOL.Ty.arr operand HOL.Ty.prop)] HOL.Ty.prop))))

theorem universal_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.universalBody.toDB [])) (HOL.Ty.arr (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop) HOL.Ty.prop)
      (universal ((substitution.apply (.var (Name.global "A"))).toHOL)) := by
  rw [universal_sourceDB]
  simp only [TermSubst.applyDB, universal, TypeSubst.apply_function, TypeSubst.apply_bool]
  refine Translates.abs (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop)) (by simp) ?_
  refine Translates.equalityApp (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop))
    (by simpa [Ty.equality] using equalityOperand?_equality (substitution.apply (Ty.function (.var (Name.global "A")) Ty.bool))) (by simp) ?_ ?_
  · exact Translates.bound .vz
  · refine Translates.abs (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by simp) ?_
    exact Translates.constant (by apply defined_not_equality) (by simp)

private theorem existential_sourceDB : Source.existentialBody.toDB [] =
    (.abs (Ty.function (.var (Name.global "A")) Ty.bool) (.app (.const Source.universalConstant (Ty.function (Ty.function Ty.bool Ty.bool) Ty.bool)) (.abs Ty.bool (.app (.app (.const Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.const Source.universalConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (.var (Name.global "A")) (.app (.app (.const Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.bound 2) (.bound 0))) (.bound 1))))) (.bound 0))))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def existential (operand : HOL.Ty AtomicTy) :
    HOL.ClosedTerm Symbol (HOL.Ty.arr (HOL.Ty.arr operand HOL.Ty.prop) HOL.Ty.prop) :=
  (.lam (.app ((.const (.constant Source.universalConstant (Ty.function (Ty.function Ty.bool Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [(HOL.Ty.arr operand HOL.Ty.prop)] (HOL.Ty.arr (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop) HOL.Ty.prop)) (.lam (.app (.app ((.const (.constant Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (by simp))) : HOL.Term Symbol [HOL.Ty.prop, (HOL.Ty.arr operand HOL.Ty.prop)] (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))) (.app ((.const (.constant Source.universalConstant (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [HOL.Ty.prop, (HOL.Ty.arr operand HOL.Ty.prop)] (HOL.Ty.arr (HOL.Ty.arr operand HOL.Ty.prop) HOL.Ty.prop)) (.lam (.app (.app ((.const (.constant Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (by simp))) : HOL.Term Symbol [operand, HOL.Ty.prop, (HOL.Ty.arr operand HOL.Ty.prop)] (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))) (.app (.var (.vs (.vs .vz))) (.var .vz))) (.var (.vs .vz)))))) (.var .vz)))))

theorem existential_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.existentialBody.toDB [])) (HOL.Ty.arr (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop) HOL.Ty.prop)
      (existential ((substitution.apply (.var (Name.global "A"))).toHOL)) := by
  rw [existential_sourceDB]
  simp only [TermSubst.applyDB, existential, TypeSubst.apply_function, TypeSubst.apply_bool, Ty.fromHOL_toHOL]
  refine Translates.abs (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop)) (by simp) ?_
  refine Translates.app (σ := (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)) (by rfl) ?_ ?_
  · exact Translates.constant (by apply defined_not_equality) (by simp)
  · refine Translates.abs (σ := HOL.Ty.prop) (by simp) ?_
    refine Translates.app (σ := HOL.Ty.prop) (by simp only [DBTerm.equalityHeadOperand?]; apply defined_not_equality) ?_ ?_
    · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
      · exact Translates.constant (by apply defined_not_equality) (by simp)
      · refine Translates.app (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop)) (by rfl) ?_ ?_
        · exact Translates.constant (by apply defined_not_equality) (by simp)
        · refine Translates.abs (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by simp) ?_
          refine Translates.app (σ := HOL.Ty.prop) (by simp only [DBTerm.equalityHeadOperand?]; apply defined_not_equality) ?_ ?_
          · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
            · exact Translates.constant (by apply defined_not_equality) (by simp)
            · refine Translates.app (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by rfl) ?_ ?_
              · exact Translates.bound (.vs (.vs .vz))
              · exact Translates.bound .vz
          · exact Translates.bound (.vs .vz)
    · exact Translates.bound .vz

private theorem falsity_sourceDB : Source.falsityBody.toDB [] =
    (.app (.const Source.universalConstant (Ty.function (Ty.function Ty.bool Ty.bool) Ty.bool)) (.abs Ty.bool (.bound 0))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def falsity :
    HOL.ClosedTerm Symbol HOL.Ty.prop :=
  (.app ((.const (.constant Source.universalConstant (Ty.function (Ty.function Ty.bool Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [] (HOL.Ty.arr (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop) HOL.Ty.prop)) (.lam (.var .vz)))

theorem falsity_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.falsityBody.toDB [])) HOL.Ty.prop
      (falsity) := by
  rw [falsity_sourceDB]
  simp only [TermSubst.applyDB, falsity, TypeSubst.apply_function, TypeSubst.apply_bool]
  refine Translates.app (σ := (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)) (by rfl) ?_ ?_
  · exact Translates.constant (by apply defined_not_equality) (by simp)
  · refine Translates.abs (σ := HOL.Ty.prop) (by simp) ?_
    exact Translates.bound .vz

private theorem negation_sourceDB : Source.negationBody.toDB [] =
    (.abs Ty.bool (.app (.app (.const Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.bound 0)) (.const Source.falsityConstant Ty.bool))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def negation :
    HOL.ClosedTerm Symbol (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop) :=
  (.lam (.app (.app ((.const (.constant Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (by simp))) : HOL.Term Symbol [HOL.Ty.prop] (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))) (.var .vz)) ((.const (.constant Source.falsityConstant Ty.bool (by simp))) : HOL.Term Symbol [HOL.Ty.prop] HOL.Ty.prop)))

theorem negation_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.negationBody.toDB [])) (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)
      (negation) := by
  rw [negation_sourceDB]
  simp only [TermSubst.applyDB, negation, TypeSubst.apply_function, TypeSubst.apply_bool]
  refine Translates.abs (σ := HOL.Ty.prop) (by simp) ?_
  refine Translates.app (σ := HOL.Ty.prop) (by simp only [DBTerm.equalityHeadOperand?]; apply defined_not_equality) ?_ ?_
  · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
    · exact Translates.constant (by apply defined_not_equality) (by simp)
    · exact Translates.bound .vz
  · exact Translates.constant (by apply defined_not_equality) (by simp)

private theorem oneOne_sourceDB : Source.oneOneBody.toDB [] =
    (.abs (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) (.app (.const Source.universalConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (.var (Name.global "A")) (.app (.const Source.universalConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (.var (Name.global "A")) (.app (.app (.const Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.app (.const Const.equality (Ty.function (.var (Name.global "B")) (Ty.function (.var (Name.global "B")) Ty.bool))) (.app (.bound 2) (.bound 1))) (.app (.bound 2) (.bound 0)))) (.app (.app (.const Const.equality (Ty.function (.var (Name.global "A")) (Ty.function (.var (Name.global "A")) Ty.bool))) (.bound 1)) (.bound 0)))))))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def oneOne (domain : HOL.Ty AtomicTy) (codomain : HOL.Ty AtomicTy) :
    HOL.ClosedTerm Symbol (HOL.Ty.arr (HOL.Ty.arr domain codomain) HOL.Ty.prop) :=
  (.lam (.app ((.const (.constant Source.universalConstant (Ty.function (Ty.function (Ty.fromHOL domain) Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [(HOL.Ty.arr domain codomain)] (HOL.Ty.arr (HOL.Ty.arr domain HOL.Ty.prop) HOL.Ty.prop)) (.lam (.app ((.const (.constant Source.universalConstant (Ty.function (Ty.function (Ty.fromHOL domain) Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [domain, (HOL.Ty.arr domain codomain)] (HOL.Ty.arr (HOL.Ty.arr domain HOL.Ty.prop) HOL.Ty.prop)) (.lam (.app (.app ((.const (.constant Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (by simp))) : HOL.Term Symbol [domain, domain, (HOL.Ty.arr domain codomain)] (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))) (.eq ((.app (.var (.vs (.vs .vz))) (.var (.vs .vz))) : HOL.Term Symbol [domain, domain, (HOL.Ty.arr domain codomain)] codomain) (.app (.var (.vs (.vs .vz))) (.var .vz)))) (.eq ((.var (.vs .vz)) : HOL.Term Symbol [domain, domain, (HOL.Ty.arr domain codomain)] domain) (.var .vz))))))))

theorem oneOne_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.oneOneBody.toDB [])) (HOL.Ty.arr (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL (substitution.apply (.var (Name.global "B"))).toHOL) HOL.Ty.prop)
      (oneOne ((substitution.apply (.var (Name.global "A"))).toHOL) ((substitution.apply (.var (Name.global "B"))).toHOL)) := by
  rw [oneOne_sourceDB]
  simp only [TermSubst.applyDB, oneOne, TypeSubst.apply_function, TypeSubst.apply_bool, Ty.fromHOL_toHOL]
  refine Translates.abs (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL (substitution.apply (.var (Name.global "B"))).toHOL)) (by simp) ?_
  refine Translates.app (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop)) (by rfl) ?_ ?_
  · exact Translates.constant (by apply defined_not_equality) (by simp)
  · refine Translates.abs (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by simp) ?_
    refine Translates.app (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop)) (by rfl) ?_ ?_
    · exact Translates.constant (by apply defined_not_equality) (by simp)
    · refine Translates.abs (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by simp) ?_
      refine Translates.app (σ := HOL.Ty.prop) (by simp only [DBTerm.equalityHeadOperand?]; apply defined_not_equality) ?_ ?_
      · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
        · exact Translates.constant (by apply defined_not_equality) (by simp)
        · refine Translates.equalityApp (σ := (substitution.apply (.var (Name.global "B"))).toHOL)
            (by simpa [Ty.equality] using equalityOperand?_equality (substitution.apply (.var (Name.global "B")))) (by simp) ?_ ?_
          · refine Translates.app (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by rfl) ?_ ?_
            · exact Translates.bound (.vs (.vs .vz))
            · exact Translates.bound (.vs .vz)
          · refine Translates.app (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by rfl) ?_ ?_
            · exact Translates.bound (.vs (.vs .vz))
            · exact Translates.bound .vz
      · refine Translates.equalityApp (σ := (substitution.apply (.var (Name.global "A"))).toHOL)
          (by simpa [Ty.equality] using equalityOperand?_equality (substitution.apply (.var (Name.global "A")))) (by simp) ?_ ?_
        · exact Translates.bound (.vs .vz)
        · exact Translates.bound .vz

private theorem onto_sourceDB : Source.ontoBody.toDB [] =
    (.abs (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) (.app (.const Source.universalConstant (Ty.function (Ty.function (.var (Name.global "B")) Ty.bool) Ty.bool)) (.abs (.var (Name.global "B")) (.app (.const Source.existentialConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (.var (Name.global "A")) (.app (.app (.const Const.equality (Ty.function (.var (Name.global "B")) (Ty.function (.var (Name.global "B")) Ty.bool))) (.bound 1)) (.app (.bound 2) (.bound 0)))))))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def onto (domain : HOL.Ty AtomicTy) (codomain : HOL.Ty AtomicTy) :
    HOL.ClosedTerm Symbol (HOL.Ty.arr (HOL.Ty.arr domain codomain) HOL.Ty.prop) :=
  (.lam (.app ((.const (.constant Source.universalConstant (Ty.function (Ty.function (Ty.fromHOL codomain) Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [(HOL.Ty.arr domain codomain)] (HOL.Ty.arr (HOL.Ty.arr codomain HOL.Ty.prop) HOL.Ty.prop)) (.lam (.app ((.const (.constant Source.existentialConstant (Ty.function (Ty.function (Ty.fromHOL domain) Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [codomain, (HOL.Ty.arr domain codomain)] (HOL.Ty.arr (HOL.Ty.arr domain HOL.Ty.prop) HOL.Ty.prop)) (.lam (.eq ((.var (.vs .vz)) : HOL.Term Symbol [domain, codomain, (HOL.Ty.arr domain codomain)] codomain) (.app (.var (.vs (.vs .vz))) (.var .vz))))))))

theorem onto_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.ontoBody.toDB [])) (HOL.Ty.arr (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL (substitution.apply (.var (Name.global "B"))).toHOL) HOL.Ty.prop)
      (onto ((substitution.apply (.var (Name.global "A"))).toHOL) ((substitution.apply (.var (Name.global "B"))).toHOL)) := by
  rw [onto_sourceDB]
  simp only [TermSubst.applyDB, onto, TypeSubst.apply_function, TypeSubst.apply_bool, Ty.fromHOL_toHOL]
  refine Translates.abs (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL (substitution.apply (.var (Name.global "B"))).toHOL)) (by simp) ?_
  refine Translates.app (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "B"))).toHOL HOL.Ty.prop)) (by rfl) ?_ ?_
  · exact Translates.constant (by apply defined_not_equality) (by simp)
  · refine Translates.abs (σ := (substitution.apply (.var (Name.global "B"))).toHOL) (by simp) ?_
    refine Translates.app (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop)) (by rfl) ?_ ?_
    · exact Translates.constant (by apply defined_not_equality) (by simp)
    · refine Translates.abs (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by simp) ?_
      refine Translates.equalityApp (σ := (substitution.apply (.var (Name.global "B"))).toHOL)
        (by simpa [Ty.equality] using equalityOperand?_equality (substitution.apply (.var (Name.global "B")))) (by simp) ?_ ?_
      · exact Translates.bound (.vs .vz)
      · refine Translates.app (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by rfl) ?_ ?_
        · exact Translates.bound (.vs (.vs .vz))
        · exact Translates.bound .vz

private theorem etaAxiom_sourceDB : Source.etaAxiom.toDB [] =
    (.app (.const Source.universalConstant (Ty.function (Ty.function (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) Ty.bool) Ty.bool)) (.abs (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) (.app (.app (.const Const.equality (Ty.function (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) (Ty.function (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))) Ty.bool))) (.abs (.var (Name.global "A")) (.app (.bound 1) (.bound 0)))) (.bound 0)))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def etaAxiom (domain : HOL.Ty AtomicTy) (codomain : HOL.Ty AtomicTy) :
    HOL.ClosedTerm Symbol HOL.Ty.prop :=
  (.app ((.const (.constant Source.universalConstant (Ty.function (Ty.function (Ty.function (Ty.fromHOL domain) (Ty.fromHOL codomain)) Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [] (HOL.Ty.arr (HOL.Ty.arr (HOL.Ty.arr domain codomain) HOL.Ty.prop) HOL.Ty.prop)) (.lam (.eq ((.lam (.app (.var (.vs .vz)) (.var .vz))) : HOL.Term Symbol [(HOL.Ty.arr domain codomain)] (HOL.Ty.arr domain codomain)) (.var .vz))))

theorem etaAxiom_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.etaAxiom.toDB [])) HOL.Ty.prop
      (etaAxiom ((substitution.apply (.var (Name.global "A"))).toHOL) ((substitution.apply (.var (Name.global "B"))).toHOL)) := by
  rw [etaAxiom_sourceDB]
  simp only [TermSubst.applyDB, etaAxiom, TypeSubst.apply_function, TypeSubst.apply_bool, Ty.fromHOL_toHOL]
  refine Translates.app (σ := (HOL.Ty.arr (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL (substitution.apply (.var (Name.global "B"))).toHOL) HOL.Ty.prop)) (by rfl) ?_ ?_
  · exact Translates.constant (by apply defined_not_equality) (by simp)
  · refine Translates.abs (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL (substitution.apply (.var (Name.global "B"))).toHOL)) (by simp) ?_
    refine Translates.equalityApp (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL (substitution.apply (.var (Name.global "B"))).toHOL))
      (by simpa [Ty.equality] using equalityOperand?_equality (substitution.apply (Ty.function (.var (Name.global "A")) (.var (Name.global "B"))))) (by simp) ?_ ?_
    · refine Translates.abs (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by simp) ?_
      refine Translates.app (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by rfl) ?_ ?_
      · exact Translates.bound (.vs .vz)
      · exact Translates.bound .vz
    · exact Translates.bound .vz

private theorem selectionAxiom_sourceDB : Source.selectionAxiom.toDB [] =
    (.app (.const Source.universalConstant (Ty.function (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool) Ty.bool)) (.abs (Ty.function (.var (Name.global "A")) Ty.bool) (.app (.const Source.universalConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) Ty.bool)) (.abs (.var (Name.global "A")) (.app (.app (.const Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.bound 1) (.bound 0))) (.app (.bound 1) (.app (.const ModelInterpretation.selectionConstant (Ty.function (Ty.function (.var (Name.global "A")) Ty.bool) (.var (Name.global "A")))) (.bound 1)))))))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def selectionAxiom (operand : HOL.Ty AtomicTy) :
    HOL.ClosedTerm Symbol HOL.Ty.prop :=
  (.app ((.const (.constant Source.universalConstant (Ty.function (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [] (HOL.Ty.arr (HOL.Ty.arr (HOL.Ty.arr operand HOL.Ty.prop) HOL.Ty.prop) HOL.Ty.prop)) (.lam (.app ((.const (.constant Source.universalConstant (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [(HOL.Ty.arr operand HOL.Ty.prop)] (HOL.Ty.arr (HOL.Ty.arr operand HOL.Ty.prop) HOL.Ty.prop)) (.lam (.app (.app ((.const (.constant Source.implicationConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (by simp))) : HOL.Term Symbol [operand, (HOL.Ty.arr operand HOL.Ty.prop)] (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))) (.app (.var (.vs .vz)) (.var .vz))) (.app (.var (.vs .vz)) (.app ((.const (.constant ModelInterpretation.selectionConstant (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) (Ty.fromHOL operand)) (by simp))) : HOL.Term Symbol [operand, (HOL.Ty.arr operand HOL.Ty.prop)] (HOL.Ty.arr (HOL.Ty.arr operand HOL.Ty.prop) operand)) (.var (.vs .vz)))))))))

theorem selectionAxiom_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.selectionAxiom.toDB [])) HOL.Ty.prop
      (selectionAxiom ((substitution.apply (.var (Name.global "A"))).toHOL)) := by
  rw [selectionAxiom_sourceDB]
  simp only [TermSubst.applyDB, selectionAxiom, TypeSubst.apply_function, TypeSubst.apply_bool, Ty.fromHOL_toHOL]
  refine Translates.app (σ := (HOL.Ty.arr (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop) HOL.Ty.prop)) (by rfl) ?_ ?_
  · exact Translates.constant (by apply defined_not_equality) (by simp)
  · refine Translates.abs (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop)) (by simp) ?_
    refine Translates.app (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop)) (by rfl) ?_ ?_
    · exact Translates.constant (by apply defined_not_equality) (by simp)
    · refine Translates.abs (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by simp) ?_
      refine Translates.app (σ := HOL.Ty.prop) (by simp only [DBTerm.equalityHeadOperand?]; apply defined_not_equality) ?_ ?_
      · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
        · exact Translates.constant (by apply defined_not_equality) (by simp)
        · refine Translates.app (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by rfl) ?_ ?_
          · exact Translates.bound (.vs .vz)
          · exact Translates.bound .vz
      · refine Translates.app (σ := (substitution.apply (.var (Name.global "A"))).toHOL) (by rfl) ?_ ?_
        · exact Translates.bound (.vs .vz)
        · refine Translates.app (σ := (HOL.Ty.arr (substitution.apply (.var (Name.global "A"))).toHOL HOL.Ty.prop)) (by rfl) ?_ ?_
          · exact Translates.constant
              (by simp [equalityOperand?, Const.same_eq_true_iff, ModelInterpretation.selectionConstant, Const.equality, Name.global]) (by simp)
          · exact Translates.bound (.vs .vz)

private theorem infinityAxiom_sourceDB : Source.infinityAxiom.toDB [] =
    (.app (.const Source.existentialConstant (Ty.function (Ty.function (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator [])) Ty.bool) Ty.bool)) (.abs (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator [])) (.app (.app (.const Source.conjunctionConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool))) (.app (.const Source.oneOneConstant (Ty.function (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator [])) Ty.bool)) (.bound 0))) (.app (.const Source.negationConstant (Ty.function Ty.bool Ty.bool)) (.app (.const Source.ontoConstant (Ty.function (Ty.function (.op SourceProfile.individualOperator []) (.op SourceProfile.individualOperator [])) Ty.bool)) (.bound 0)))))) :=
  (DBTerm.same_eq_true_iff _ _).mp (by decide +kernel)

def infinityAxiom :
    HOL.ClosedTerm Symbol HOL.Ty.prop :=
  (.app ((.const (.constant Source.existentialConstant (Ty.function (Ty.function (Ty.function (Ty.op SourceProfile.individualOperator []) (Ty.op SourceProfile.individualOperator [])) Ty.bool) Ty.bool) (by simp))) : HOL.Term Symbol [] (HOL.Ty.arr (HOL.Ty.arr (HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL) HOL.Ty.prop) HOL.Ty.prop)) (.lam (.app (.app ((.const (.constant Source.conjunctionConstant (Ty.function Ty.bool (Ty.function Ty.bool Ty.bool)) (by simp))) : HOL.Term Symbol [(HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL)] (HOL.Ty.arr HOL.Ty.prop (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop))) (.app ((.const (.constant Source.oneOneConstant (Ty.function (Ty.function (Ty.op SourceProfile.individualOperator []) (Ty.op SourceProfile.individualOperator [])) Ty.bool) (by simp))) : HOL.Term Symbol [(HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL)] (HOL.Ty.arr (HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL) HOL.Ty.prop)) (.var .vz))) (.app ((.const (.constant Source.negationConstant (Ty.function Ty.bool Ty.bool) (by simp))) : HOL.Term Symbol [(HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL)] (HOL.Ty.arr HOL.Ty.prop HOL.Ty.prop)) (.app ((.const (.constant Source.ontoConstant (Ty.function (Ty.function (Ty.op SourceProfile.individualOperator []) (Ty.op SourceProfile.individualOperator [])) Ty.bool) (by simp))) : HOL.Term Symbol [(HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL)] (HOL.Ty.arr (HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL) HOL.Ty.prop)) (.var .vz))))))

theorem infinityAxiom_translated (substitution : TypeSubst) :
    Translates [] ((TypeCorrectTermSubstitution.ofTypes substitution).raw.applyDB
      (Source.infinityAxiom.toDB [])) HOL.Ty.prop
      (infinityAxiom) := by
  rw [infinityAxiom_sourceDB]
  simp only [TermSubst.applyDB, infinityAxiom, TypeSubst.apply_function, TypeSubst.apply_bool, TypeSubst.apply_op, List.map_nil]
  refine Translates.app (σ := (HOL.Ty.arr (HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL) HOL.Ty.prop)) (by rfl) ?_ ?_
  · exact Translates.constant (by apply defined_not_equality) (by simp)
  · refine Translates.abs (σ := (HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL)) (by simp) ?_
    refine Translates.app (σ := HOL.Ty.prop) (by simp only [DBTerm.equalityHeadOperand?]; apply defined_not_equality) ?_ ?_
    · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
      · exact Translates.constant (by apply defined_not_equality) (by simp)
      · refine Translates.app (σ := (HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL)) (by rfl) ?_ ?_
        · exact Translates.constant (by apply defined_not_equality) (by simp)
        · exact Translates.bound .vz
    · refine Translates.app (σ := HOL.Ty.prop) (by rfl) ?_ ?_
      · exact Translates.constant (by apply defined_not_equality) (by simp)
      · refine Translates.app (σ := (HOL.Ty.arr (Ty.op SourceProfile.individualOperator []).toHOL (Ty.op SourceProfile.individualOperator []).toHOL)) (by rfl) ?_ ?_
        · exact Translates.constant (by apply defined_not_equality) (by simp)
        · exact Translates.bound .vz

end Raw

namespace Interpretation

namespace Symbols

def truth : Symbol .prop := .constant Source.truthConstant Ty.bool (by simp)

def conjunction : Symbol (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)) :=
  .constant Source.conjunctionConstant Source.conjunctionSchema (by simp [Source.conjunctionSchema])

def implication : Symbol (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)) :=
  .constant Source.implicationConstant Source.implicationSchema (by simp [Source.implicationSchema])

def universal (operand : HOL.Ty AtomicTy) : Symbol ((operand.arr .prop).arr .prop) :=
  .constant Source.universalConstant (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (by simp)

def existential (operand : HOL.Ty AtomicTy) : Symbol ((operand.arr .prop).arr .prop) :=
  .constant Source.existentialConstant (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (by simp)

def falsity : Symbol .prop := .constant Source.falsityConstant Ty.bool (by simp)

def negation : Symbol (HOL.Ty.arr .prop .prop) :=
  .constant Source.negationConstant Source.negationSchema (by simp [Source.negationSchema])

def oneOne (domain codomain : HOL.Ty AtomicTy) : Symbol ((domain.arr codomain).arr .prop) :=
  .constant Source.oneOneConstant (Ty.function (Ty.function (Ty.fromHOL domain) (Ty.fromHOL codomain)) Ty.bool) (by simp)

def onto (domain codomain : HOL.Ty AtomicTy) : Symbol ((domain.arr codomain).arr .prop) :=
  .constant Source.ontoConstant (Ty.function (Ty.function (Ty.fromHOL domain) (Ty.fromHOL codomain)) Ty.bool) (by simp)

end Symbols

def atA (operand : Ty) : TypeSubst := ⟨[(Name.global "A", operand)]⟩

def atAB (domain codomain : Ty) : TypeSubst :=
  ⟨[(Name.global "A", domain), (Name.global "B", codomain)]⟩

@[simp] theorem atA_apply_A (operand : Ty) :
    (atA operand).apply (.var (Name.global "A")) = operand := by
  simp [atA, TypeSubst.lookup]

@[simp] theorem atAB_apply_A (domain codomain : Ty) :
    (atAB domain codomain).apply (.var (Name.global "A")) = domain := by
  simp [atAB, TypeSubst.lookup]

@[simp] theorem atAB_apply_B (domain codomain : Ty) :
    (atAB domain codomain).apply (.var (Name.global "B")) = codomain := by
  have different : (Name.global "B" == Name.global "A") = false := by decide +kernel
  simp [atAB, TypeSubst.lookup, List.lookup, different]

theorem truth_extension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) :
    (ConstantAdmission.sourceExtension Source.truthResult M).constDen Symbols.truth =
      M.denote (Raw.truth) (fun index => nomatch index) := by
  unfold Symbols.truth
  rw [← Source.truthIdentity]
  exact ConstantAdmission.sourceExtension_constant_translates Source.truthAdmitted M full
    TypeSubst.empty Ty.bool (by simp) (by simp [Source.truthType, Source.truthSchema])
    (Raw.truth_translated TypeSubst.empty)

theorem conjunction_extension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) :
    (ConstantAdmission.sourceExtension Source.conjunctionResult M).constDen Symbols.conjunction =
      M.denote (Raw.conjunction) (fun index => nomatch index) := by
  unfold Symbols.conjunction
  rw [← Source.conjunctionIdentity]
  exact ConstantAdmission.sourceExtension_constant_translates Source.conjunctionAdmitted M full
    TypeSubst.empty Source.conjunctionSchema (by simp [Source.conjunctionSchema])
    (by simp [Source.conjunctionType]) (Raw.conjunction_translated TypeSubst.empty)

theorem implication_extension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (ConstantAdmission.sourceExtension Source.implicationResult M).constDen (Symbols.implication) =
      M.denote (Raw.implication) (fun index => nomatch index) := by
  have translated := Raw.implication_translated TypeSubst.empty
  unfold Symbols.implication
  rw [← Source.implicationIdentity]
  exact ConstantAdmission.sourceExtension_constant_translates Source.implicationAdmitted M full
    TypeSubst.empty Source.implicationSchema (by simp [Source.implicationSchema])
    (by simp [Source.implicationType]) translated

theorem universal_extension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) :
    (ConstantAdmission.sourceExtension Source.universalResult M).constDen (Symbols.universal operand) =
      M.denote (Raw.universal operand) (fun index => nomatch index) := by
  have translated := Raw.universal_translated (atA (Ty.fromHOL operand))
  rw [atA_apply_A] at translated
  rw [Ty.toHOL_fromHOL] at translated
  unfold Symbols.universal
  rw [← Source.universalIdentity]
  exact ConstantAdmission.sourceExtension_constant_translates Source.universalAdmitted M full
    (atA (Ty.fromHOL operand)) (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (by simp)
    (by rw [Source.universalType]; simp only [Source.universalSchema, TypeSubst.apply_function, TypeSubst.apply_bool]; rw [atA_apply_A]) translated

theorem existential_extension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) :
    (ConstantAdmission.sourceExtension Source.existentialResult M).constDen (Symbols.existential operand) =
      M.denote (Raw.existential operand) (fun index => nomatch index) := by
  have translated := Raw.existential_translated (atA (Ty.fromHOL operand))
  rw [atA_apply_A] at translated
  rw [Ty.toHOL_fromHOL] at translated
  unfold Symbols.existential
  rw [← Source.existentialIdentity]
  exact ConstantAdmission.sourceExtension_constant_translates Source.existentialAdmitted M full
    (atA (Ty.fromHOL operand)) (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (by simp)
    (by rw [Source.existentialType]; simp only [Source.existentialSchema, TypeSubst.apply_function, TypeSubst.apply_bool]; rw [atA_apply_A]) translated

theorem falsity_extension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (ConstantAdmission.sourceExtension Source.falsityResult M).constDen (Symbols.falsity) =
      M.denote (Raw.falsity) (fun index => nomatch index) := by
  have translated := Raw.falsity_translated TypeSubst.empty
  unfold Symbols.falsity
  rw [← Source.falsityIdentity]
  exact ConstantAdmission.sourceExtension_constant_translates Source.falsityAdmitted M full
    TypeSubst.empty Source.falsitySchema (by simp [Source.falsitySchema])
    (by simp [Source.falsityType]) translated

theorem negation_extension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (ConstantAdmission.sourceExtension Source.negationResult M).constDen (Symbols.negation) =
      M.denote (Raw.negation) (fun index => nomatch index) := by
  have translated := Raw.negation_translated TypeSubst.empty
  unfold Symbols.negation
  rw [← Source.negationIdentity]
  exact ConstantAdmission.sourceExtension_constant_translates Source.negationAdmitted M full
    TypeSubst.empty Source.negationSchema (by simp [Source.negationSchema])
    (by simp [Source.negationType]) translated

theorem oneOne_extension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (domain : HOL.Ty AtomicTy) (codomain : HOL.Ty AtomicTy) :
    (ConstantAdmission.sourceExtension Source.oneOneResult M).constDen (Symbols.oneOne domain codomain) =
      M.denote (Raw.oneOne domain codomain) (fun index => nomatch index) := by
  have translated := Raw.oneOne_translated (atAB (Ty.fromHOL domain) (Ty.fromHOL codomain))
  rw [atAB_apply_A, atAB_apply_B] at translated
  rw [Ty.toHOL_fromHOL, Ty.toHOL_fromHOL] at translated
  unfold Symbols.oneOne
  rw [← Source.oneOneIdentity]
  exact ConstantAdmission.sourceExtension_constant_translates Source.oneOneAdmitted M full
    (atAB (Ty.fromHOL domain) (Ty.fromHOL codomain)) (Ty.function (Ty.function (Ty.fromHOL domain) (Ty.fromHOL codomain)) Ty.bool) (by simp)
    (by rw [Source.oneOneType]; simp only [Source.oneOneSchema, TypeSubst.apply_function, TypeSubst.apply_bool]; rw [atAB_apply_A, atAB_apply_B]) translated

theorem onto_extension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (domain : HOL.Ty AtomicTy) (codomain : HOL.Ty AtomicTy) :
    (ConstantAdmission.sourceExtension Source.ontoResult M).constDen (Symbols.onto domain codomain) =
      M.denote (Raw.onto domain codomain) (fun index => nomatch index) := by
  have translated := Raw.onto_translated (atAB (Ty.fromHOL domain) (Ty.fromHOL codomain))
  rw [atAB_apply_A, atAB_apply_B] at translated
  rw [Ty.toHOL_fromHOL, Ty.toHOL_fromHOL] at translated
  unfold Symbols.onto
  rw [← Source.ontoIdentity]
  exact ConstantAdmission.sourceExtension_constant_translates Source.ontoAdmitted M full
    (atAB (Ty.fromHOL domain) (Ty.fromHOL codomain)) (Ty.function (Ty.function (Ty.fromHOL domain) (Ty.fromHOL codomain)) Ty.bool) (by simp)
    (by rw [Source.ontoType]; simp only [Source.ontoSchema, TypeSubst.apply_function, TypeSubst.apply_bool]; rw [atAB_apply_A, atAB_apply_B]) translated

theorem raw_truth_denote (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (valuation : M.Valuation []) :
    M.denote Raw.truth valuation = ULift.up True :=
  HOL.HOLLightBooleanDefinitions.denote_truth M valuation

theorem raw_conjunction_denote (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (truthMeaning : M.constDen Symbols.truth = ULift.up True)
    (valuation : M.Valuation [])
    (left right : HOL.Ty.denote M.Carrier .prop) :
    M.denote (Raw.conjunction) valuation left right =
      ULift.up (left.down ∧ right.down) := by
  have liftedTruth {context : HOL.Ctx AtomicTy} (rho : M.Valuation context) :
      M.denote (HOL.weakenCtx context HOL.HOLLightBooleanDefinitions.truth) rho = ULift.up True :=
    (M.denote_weakenCtx context HOL.HOLLightBooleanDefinitions.truth rho).trans
      (HOL.HOLLightBooleanDefinitions.denote_truth M _)
  have same : M.denote (Raw.conjunction) valuation left right =
      M.denote HOL.HOLLightBooleanDefinitions.conjunction valuation left right := by
    simp only [Raw.conjunction, HOL.HOLLightBooleanDefinitions.conjunction,
      HOL.HenkinModel.denote, HOL.PreModel.denote,
      liftedTruth, ← truthMeaning, Symbols.truth]
    rfl
  rw [same]
  exact HOL.HOLLightBooleanDefinitions.denote_conjunction M full valuation left right

theorem raw_implication_denote (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (conjunctionMeaning : ∀ left right, M.constDen Symbols.conjunction left right =
      ULift.up (left.down ∧ right.down))
    (valuation : M.Valuation [])
    (left right : HOL.Ty.denote M.Carrier .prop) :
    M.denote (Raw.implication) valuation left right =
      ULift.up (left.down → right.down) := by
  simp only [Raw.implication,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend, HOL.PreModel.Eqv]
  change ULift.up ((M.constDen Symbols.conjunction left right).down ↔ left.down) = _
  rw [conjunctionMeaning]
  apply ULift.ext
  apply propext
  exact ⟨fun equal premise => (equal.mpr premise).2,
    fun implication => ⟨And.left, fun premise => ⟨premise, implication premise⟩⟩⟩

theorem raw_universal_denote (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (truthMeaning : M.constDen Symbols.truth = ULift.up True)
    (operand : HOL.Ty AtomicTy) (valuation : M.Valuation [])
    (predicate : HOL.Ty.denote M.Carrier
      (operand.arr .prop)) :
    M.denote (Raw.universal operand) valuation predicate =
      ULift.up (∀ value, M.adm operand value →
        (predicate value).down) := by
  have liftedTruth {context : HOL.Ctx AtomicTy} (rho : M.Valuation context) :
      M.denote (HOL.weakenCtx context HOL.HOLLightBooleanDefinitions.truth) rho = ULift.up True :=
    (M.denote_weakenCtx context HOL.HOLLightBooleanDefinitions.truth rho).trans
      (HOL.HOLLightBooleanDefinitions.denote_truth M _)
  have same : M.denote (Raw.universal operand) valuation predicate =
      M.denote (HOL.HOLLightBooleanDefinitions.universal
        operand) valuation predicate := by
    simp only [Raw.universal, HOL.HOLLightBooleanDefinitions.universal,
      HOL.HenkinModel.denote, HOL.PreModel.denote,
      liftedTruth, ← truthMeaning, Symbols.truth]
    rfl
  rw [same]
  exact HOL.HOLLightBooleanDefinitions.denote_universal M valuation predicate

theorem raw_existential_denote (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)
    (universalMeaning : ∀ operand predicate, M.constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down))
    (implicationMeaning : ∀ left right, M.constDen Symbols.implication left right =
      ULift.up (left.down → right.down))
    (operand : HOL.Ty AtomicTy) (valuation : M.Valuation [])
    (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    M.denote (Raw.existential operand) valuation predicate =
      ULift.up (∃ value, M.adm operand value ∧ (predicate value).down) := by
  have universalFunction (operand : HOL.Ty AtomicTy) :
      M.constDen (Symbols.universal operand) =
        fun predicate => ULift.up (∀ value, M.adm operand value → (predicate value).down) :=
    funext (universalMeaning operand)
  have implicationFunction : M.constDen Symbols.implication =
      fun left right => ULift.up (left.down → right.down) :=
    funext fun left => funext (implicationMeaning left)
  have universalBoolFunction := universalFunction HOL.Ty.prop
  simp only [Symbols.universal] at universalFunction
  simp only [Symbols.universal, Ty.fromHOL] at universalBoolFunction
  simp only [Symbols.implication, Source.implicationSchema] at implicationFunction
  have same : M.denote (Raw.existential operand) valuation predicate =
      M.denote (HOL.HOLLightBooleanDefinitions.existential operand) valuation predicate := by
    simp only [Raw.existential, HOL.HOLLightBooleanDefinitions.existential,
      HOL.HenkinModel.denote, HOL.PreModel.denote,
      universalBoolFunction, universalFunction operand, implicationFunction,
      HOL.HOLLightBooleanDefinitions.denote_all,
      HOL.HOLLightBooleanDefinitions.denote_imp M full, HOL.PreModel.extend]
    rfl
  rw [same]
  exact HOL.HOLLightBooleanDefinitions.denote_existential M full valuation predicate

theorem raw_falsity_denote (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (universalMeaning : ∀ operand predicate, M.constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down))
    (valuation : M.Valuation []) : M.denote Raw.falsity valuation = ULift.up False := by
  change M.constDen (Symbols.universal .prop) (fun value => value) = ULift.up False
  refine Eq.trans (universalMeaning HOL.Ty.prop (fun value => value)) ?_
  apply ULift.ext
  apply propext
  exact ⟨fun holds => holds (ULift.up False) (M.prop_mem _), False.elim⟩

theorem raw_negation_denote (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (implicationMeaning : ∀ left right, M.constDen Symbols.implication left right =
      ULift.up (left.down → right.down))
    (falsityMeaning : M.constDen Symbols.falsity = ULift.up False)
    (valuation : M.Valuation []) (proposition : HOL.Ty.denote M.Carrier .prop) :
    M.denote Raw.negation valuation proposition = ULift.up (¬ proposition.down) := by
  simp only [Symbols.implication, Source.implicationSchema] at implicationMeaning
  simp only [Symbols.falsity] at falsityMeaning
  simp only [Raw.negation, HOL.HenkinModel.denote, HOL.PreModel.denote,
    falsityMeaning, HOL.PreModel.extend]
  exact implicationMeaning proposition (ULift.up False)

theorem raw_oneOne_denote (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (universalMeaning : ∀ operand predicate, M.constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down))
    (implicationMeaning : ∀ left right, M.constDen Symbols.implication left right =
      ULift.up (left.down → right.down))
    (domain codomain : HOL.Ty AtomicTy) (valuation : M.Valuation [])
    (function : HOL.Ty.denote M.Carrier (domain.arr codomain)) :
    M.denote (Raw.oneOne domain codomain) valuation function =
      ULift.up (∀ left, M.adm domain left → ∀ right, M.adm domain right →
        M.Eqv codomain (function left) (function right) → M.Eqv domain left right) := by
  have universalFunction : M.constDen (Symbols.universal domain) =
      fun predicate => ULift.up (∀ value, M.adm domain value → (predicate value).down) :=
    funext (universalMeaning domain)
  have implicationFunction : M.constDen Symbols.implication =
      fun left right => ULift.up (left.down → right.down) :=
    funext fun left => funext (implicationMeaning left)
  simp only [Symbols.universal] at universalFunction
  simp only [Symbols.implication, Source.implicationSchema] at implicationFunction
  simp only [Raw.oneOne, HOL.HenkinModel.denote, HOL.PreModel.denote, universalFunction,
    implicationFunction, HOL.PreModel.extend]
  rfl

theorem raw_onto_denote (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (universalMeaning : ∀ operand predicate, M.constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down))
    (existentialMeaning : ∀ operand predicate, M.constDen (Symbols.existential operand) predicate =
      ULift.up (∃ value, M.adm operand value ∧ (predicate value).down))
    (domain codomain : HOL.Ty AtomicTy) (valuation : M.Valuation [])
    (function : HOL.Ty.denote M.Carrier (domain.arr codomain)) :
    M.denote (Raw.onto domain codomain) valuation function =
      ULift.up (∀ value, M.adm codomain value →
        ∃ preimage, M.adm domain preimage ∧ M.Eqv codomain value (function preimage)) := by
  have universalFunction : M.constDen (Symbols.universal codomain) =
      fun predicate => ULift.up (∀ value, M.adm codomain value → (predicate value).down) :=
    funext (universalMeaning codomain)
  have existentialFunction : M.constDen (Symbols.existential domain) =
      fun predicate => ULift.up (∃ value, M.adm domain value ∧ (predicate value).down) :=
    funext (existentialMeaning domain)
  simp only [Symbols.universal] at universalFunction
  simp only [Symbols.existential] at existentialFunction
  simp only [Raw.onto, HOL.HenkinModel.denote, HOL.PreModel.denote, universalFunction,
    existentialFunction, HOL.PreModel.extend]
  rfl

attribute [local irreducible] ConstantAdmission.sourceExpansion

set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[reducible] noncomputable def truthModel
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard M.Carrier
    (ConstantAdmission.sourceMeanings Source.truthResult M)

@[reducible] noncomputable def conjunctionModel
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard M.Carrier
    (ConstantAdmission.standardSourceMeanings Source.conjunctionResult M.Carrier (truthModel M).constDen)

@[simp] theorem truthModel_carrier
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (truthModel M).Carrier = M.Carrier := rfl

theorem truthModel_fullDomains (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (_full : M.FullDomains) : (truthModel M).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem truthModel_eq_sourceExtension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) :
    truthModel M = ConstantAdmission.sourceExtension Source.truthResult M :=
  HOL.HenkinModel.standard_eq_of_fullDomains
    (ConstantAdmission.sourceExtension Source.truthResult M)
    (ConstantAdmission.sourceExtension_fullDomains _ _ full)

theorem truthModel_truth (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) : (truthModel M).constDen Symbols.truth = ULift.up True := by
  have body := truth_extension M full
  exact body.trans (raw_truth_denote M _)

@[simp] theorem conjunctionModel_carrier
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (conjunctionModel M).Carrier = M.Carrier := rfl

theorem conjunctionModel_fullDomains (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (_full : M.FullDomains) : (conjunctionModel M).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem conjunctionModel_eq_sourceExtension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) :
    conjunctionModel M = ConstantAdmission.sourceExtension Source.conjunctionResult (truthModel M) :=
  ConstantAdmission.standardSourceModel_eq_sourceExtension Source.conjunctionResult (truthModel M)
    (truthModel_fullDomains M full)

theorem conjunctionModel_truth (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) : (conjunctionModel M).constDen Symbols.truth = ULift.up True := by
  rw [conjunctionModel_eq_sourceExtension M full]
  unfold Symbols.truth
  rw [ConstantAdmission.sourceExtension_constant_other]
  · exact truthModel_truth M full
  · rw [Source.conjunctionIdentity]
    intro equal
    have names := congrArg constantName equal
    simp [constantName, Source.truthConstant, Source.conjunctionConstant, Name.global] at names

theorem conjunctionModel_conjunction (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (left right : HOL.Ty.denote M.Carrier .prop) :
    (conjunctionModel M).constDen Symbols.conjunction left right =
      ULift.up (left.down ∧ right.down) := by
  rw [conjunctionModel_eq_sourceExtension M full,
    conjunction_extension _ (truthModel_fullDomains M full)]
  exact raw_conjunction_denote (truthModel M) (truthModel_fullDomains M full) (truthModel_truth M full)
    _ left right

@[reducible] noncomputable def implicationModel (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard M.Carrier
    (ConstantAdmission.standardSourceMeanings Source.implicationResult M.Carrier (conjunctionModel M).constDen)

@[simp] theorem implicationModel_carrier
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (implicationModel M).Carrier = M.Carrier := rfl

theorem implicationModel_fullDomains (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (_full : M.FullDomains) :
    (implicationModel M).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem implicationModel_eq_sourceExtension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    implicationModel M = ConstantAdmission.sourceExtension Source.implicationResult (conjunctionModel M) :=
  ConstantAdmission.standardSourceModel_eq_sourceExtension Source.implicationResult (conjunctionModel M)
    (conjunctionModel_fullDomains M full)

theorem implicationModel_truth (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (implicationModel M).constDen (Symbols.truth) =
      ULift.up True := by
  have different : Source.truthConstant ≠ Source.implicationResult.output.constant := by
    rw [Source.implicationIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.truthConstant, Source.implicationConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.implicationResult M.Carrier (conjunctionModel M).constDen Source.truthConstant
    Source.truthSchema (type := HOL.Ty.prop)
    (by simp [Source.truthSchema])
    different
  exact (retained).trans
    (conjunctionModel_truth M full)

theorem implicationModel_conjunction (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (implicationModel M).constDen (Symbols.conjunction) left right =
      ULift.up (left.down ∧ right.down) := by
  have different : Source.conjunctionConstant ≠ Source.implicationResult.output.constant := by
    rw [Source.implicationIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.conjunctionConstant, Source.implicationConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.implicationResult M.Carrier (conjunctionModel M).constDen Source.conjunctionConstant
    Source.conjunctionSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.conjunctionSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (conjunctionModel_conjunction M full left right)

theorem implicationModel_implication (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (implicationModel M).constDen (Symbols.implication) left right =
      ULift.up (left.down → right.down) := by
  change ConstantAdmission.standardSourceMeanings Source.implicationResult M.Carrier
    (conjunctionModel M).constDen Symbols.implication left right = _
  have meanings : @ConstantAdmission.standardSourceMeanings Source.implicationResult M.Carrier
      (conjunctionModel M).constDen = @ConstantAdmission.sourceMeanings Source.implicationResult (conjunctionModel M) :=
    ConstantAdmission.standardSourceMeanings_eq Source.implicationResult (conjunctionModel M)
      (conjunctionModel_fullDomains M full)
  rw [meanings]
  have body := implication_extension (conjunctionModel M)
    (conjunctionModel_fullDomains M full)
  refine (congrFun (congrFun (body) left) right).trans ?_
  exact raw_implication_denote (conjunctionModel M) (conjunctionModel_conjunction M full) (fun index => nomatch index) left right

@[reducible] noncomputable def universalModel (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard M.Carrier
    (ConstantAdmission.standardSourceMeanings Source.universalResult M.Carrier (implicationModel M).constDen)

@[simp] theorem universalModel_carrier
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (universalModel M).Carrier = M.Carrier := rfl

theorem universalModel_fullDomains (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (_full : M.FullDomains) :
    (universalModel M).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem universalModel_eq_sourceExtension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    universalModel M = ConstantAdmission.sourceExtension Source.universalResult (implicationModel M) :=
  ConstantAdmission.standardSourceModel_eq_sourceExtension Source.universalResult (implicationModel M)
    (implicationModel_fullDomains M full)

theorem universalModel_truth (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (universalModel M).constDen (Symbols.truth) =
      ULift.up True := by
  have different : Source.truthConstant ≠ Source.universalResult.output.constant := by
    rw [Source.universalIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.truthConstant, Source.universalConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.universalResult M.Carrier (implicationModel M).constDen Source.truthConstant
    Source.truthSchema (type := HOL.Ty.prop)
    (by simp [Source.truthSchema])
    different
  exact (retained).trans
    (implicationModel_truth M full)

theorem universalModel_conjunction (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (universalModel M).constDen (Symbols.conjunction) left right =
      ULift.up (left.down ∧ right.down) := by
  have different : Source.conjunctionConstant ≠ Source.universalResult.output.constant := by
    rw [Source.universalIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.conjunctionConstant, Source.universalConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.universalResult M.Carrier (implicationModel M).constDen Source.conjunctionConstant
    Source.conjunctionSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.conjunctionSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (implicationModel_conjunction M full left right)

theorem universalModel_implication (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (universalModel M).constDen (Symbols.implication) left right =
      ULift.up (left.down → right.down) := by
  have different : Source.implicationConstant ≠ Source.universalResult.output.constant := by
    rw [Source.universalIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.implicationConstant, Source.universalConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.universalResult M.Carrier (implicationModel M).constDen Source.implicationConstant
    Source.implicationSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.implicationSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (implicationModel_implication M full left right)

theorem universalModel_universal (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (universalModel M).constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down) := by
  change ConstantAdmission.standardSourceMeanings Source.universalResult M.Carrier
    (implicationModel M).constDen (Symbols.universal operand) predicate = _
  have meanings : @ConstantAdmission.standardSourceMeanings Source.universalResult M.Carrier
      (implicationModel M).constDen = @ConstantAdmission.sourceMeanings Source.universalResult (implicationModel M) :=
    ConstantAdmission.standardSourceMeanings_eq Source.universalResult (implicationModel M)
      (implicationModel_fullDomains M full)
  rw [meanings]
  have inheritedDomains : ∀ type value, (implicationModel M).adm type value ↔ M.adm type value :=
    fun type value => ⟨fun _ => full type value, fun _ => implicationModel_fullDomains M full type value⟩
  have body := universal_extension (implicationModel M)
    (implicationModel_fullDomains M full) operand
  refine (congrFun (body) predicate).trans ?_
  have rawMeaning := raw_universal_denote (implicationModel M) (implicationModel_truth M full) operand (fun index => nomatch index) predicate
  simpa only [inheritedDomains, implicationModel_carrier,
    ConstantAdmission.sourceExtension_carrier] using rawMeaning

@[reducible] noncomputable def existentialModel (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard M.Carrier
    (ConstantAdmission.standardSourceMeanings Source.existentialResult M.Carrier (universalModel M).constDen)

@[simp] theorem existentialModel_carrier
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (existentialModel M).Carrier = M.Carrier := rfl

theorem existentialModel_fullDomains (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (_full : M.FullDomains) :
    (existentialModel M).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem existentialModel_eq_sourceExtension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    existentialModel M = ConstantAdmission.sourceExtension Source.existentialResult (universalModel M) :=
  ConstantAdmission.standardSourceModel_eq_sourceExtension Source.existentialResult (universalModel M)
    (universalModel_fullDomains M full)

theorem existentialModel_truth (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (existentialModel M).constDen (Symbols.truth) =
      ULift.up True := by
  have different : Source.truthConstant ≠ Source.existentialResult.output.constant := by
    rw [Source.existentialIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.truthConstant, Source.existentialConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.existentialResult M.Carrier (universalModel M).constDen Source.truthConstant
    Source.truthSchema (type := HOL.Ty.prop)
    (by simp [Source.truthSchema])
    different
  exact (retained).trans
    (universalModel_truth M full)

theorem existentialModel_conjunction (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (existentialModel M).constDen (Symbols.conjunction) left right =
      ULift.up (left.down ∧ right.down) := by
  have different : Source.conjunctionConstant ≠ Source.existentialResult.output.constant := by
    rw [Source.existentialIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.conjunctionConstant, Source.existentialConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.existentialResult M.Carrier (universalModel M).constDen Source.conjunctionConstant
    Source.conjunctionSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.conjunctionSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (universalModel_conjunction M full left right)

theorem existentialModel_implication (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (existentialModel M).constDen (Symbols.implication) left right =
      ULift.up (left.down → right.down) := by
  have different : Source.implicationConstant ≠ Source.existentialResult.output.constant := by
    rw [Source.existentialIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.implicationConstant, Source.existentialConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.existentialResult M.Carrier (universalModel M).constDen Source.implicationConstant
    Source.implicationSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.implicationSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (universalModel_implication M full left right)

theorem existentialModel_universal (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (existentialModel M).constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down) := by
  have different : Source.universalConstant ≠ Source.existentialResult.output.constant := by
    rw [Source.existentialIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.universalConstant, Source.existentialConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.existentialResult M.Carrier (universalModel M).constDen Source.universalConstant
    (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (type := ((operand.arr .prop).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) predicate).trans
    (universalModel_universal M full operand predicate)

theorem existentialModel_existential (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (existentialModel M).constDen (Symbols.existential operand) predicate =
      ULift.up (∃ value, M.adm operand value ∧ (predicate value).down) := by
  change ConstantAdmission.standardSourceMeanings Source.existentialResult M.Carrier
    (universalModel M).constDen (Symbols.existential operand) predicate = _
  have meanings : @ConstantAdmission.standardSourceMeanings Source.existentialResult M.Carrier
      (universalModel M).constDen = @ConstantAdmission.sourceMeanings Source.existentialResult (universalModel M) :=
    ConstantAdmission.standardSourceMeanings_eq Source.existentialResult (universalModel M)
      (universalModel_fullDomains M full)
  rw [meanings]
  have inheritedDomains : ∀ type value, (universalModel M).adm type value ↔ M.adm type value :=
    fun type value => ⟨fun _ => full type value, fun _ => universalModel_fullDomains M full type value⟩
  have universalMeaning : ∀ (type : HOL.Ty AtomicTy)
      (predicate : HOL.Ty.denote.{0, w + 1} M.Carrier (type.arr .prop)),
      (universalModel M).constDen (Symbols.universal type) predicate =
        ULift.up (∀ value, (universalModel M).adm type value → (predicate value).down) := by
    intro type predicate
    simpa only [inheritedDomains, universalModel_carrier] using universalModel_universal M full type predicate
  have body := existential_extension (universalModel M)
    (universalModel_fullDomains M full) operand
  refine (congrFun (body) predicate).trans ?_
  have rawMeaning := raw_existential_denote (universalModel M) (universalModel_fullDomains M full) universalMeaning (universalModel_implication M full) operand (fun index => nomatch index) predicate
  simpa only [inheritedDomains, universalModel_carrier,
    ConstantAdmission.sourceExtension_carrier] using rawMeaning

@[reducible] noncomputable def falsityModel (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard M.Carrier
    (ConstantAdmission.standardSourceMeanings Source.falsityResult M.Carrier (existentialModel M).constDen)

@[simp] theorem falsityModel_carrier
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (falsityModel M).Carrier = M.Carrier := rfl

theorem falsityModel_fullDomains (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (_full : M.FullDomains) :
    (falsityModel M).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem falsityModel_eq_sourceExtension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    falsityModel M = ConstantAdmission.sourceExtension Source.falsityResult (existentialModel M) :=
  ConstantAdmission.standardSourceModel_eq_sourceExtension Source.falsityResult (existentialModel M)
    (existentialModel_fullDomains M full)

theorem falsityModel_truth (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (falsityModel M).constDen (Symbols.truth) =
      ULift.up True := by
  have different : Source.truthConstant ≠ Source.falsityResult.output.constant := by
    rw [Source.falsityIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.truthConstant, Source.falsityConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.falsityResult M.Carrier (existentialModel M).constDen Source.truthConstant
    Source.truthSchema (type := HOL.Ty.prop)
    (by simp [Source.truthSchema])
    different
  exact (retained).trans
    (existentialModel_truth M full)

theorem falsityModel_conjunction (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (falsityModel M).constDen (Symbols.conjunction) left right =
      ULift.up (left.down ∧ right.down) := by
  have different : Source.conjunctionConstant ≠ Source.falsityResult.output.constant := by
    rw [Source.falsityIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.conjunctionConstant, Source.falsityConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.falsityResult M.Carrier (existentialModel M).constDen Source.conjunctionConstant
    Source.conjunctionSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.conjunctionSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (existentialModel_conjunction M full left right)

theorem falsityModel_implication (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (falsityModel M).constDen (Symbols.implication) left right =
      ULift.up (left.down → right.down) := by
  have different : Source.implicationConstant ≠ Source.falsityResult.output.constant := by
    rw [Source.falsityIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.implicationConstant, Source.falsityConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.falsityResult M.Carrier (existentialModel M).constDen Source.implicationConstant
    Source.implicationSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.implicationSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (existentialModel_implication M full left right)

theorem falsityModel_universal (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (falsityModel M).constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down) := by
  have different : Source.universalConstant ≠ Source.falsityResult.output.constant := by
    rw [Source.falsityIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.universalConstant, Source.falsityConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.falsityResult M.Carrier (existentialModel M).constDen Source.universalConstant
    (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (type := ((operand.arr .prop).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) predicate).trans
    (existentialModel_universal M full operand predicate)

theorem falsityModel_existential (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (falsityModel M).constDen (Symbols.existential operand) predicate =
      ULift.up (∃ value, M.adm operand value ∧ (predicate value).down) := by
  have different : Source.existentialConstant ≠ Source.falsityResult.output.constant := by
    rw [Source.falsityIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.existentialConstant, Source.falsityConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.falsityResult M.Carrier (existentialModel M).constDen Source.existentialConstant
    (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (type := ((operand.arr .prop).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) predicate).trans
    (existentialModel_existential M full operand predicate)

theorem falsityModel_falsity (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (falsityModel M).constDen (Symbols.falsity) =
      ULift.up False := by
  change ConstantAdmission.standardSourceMeanings Source.falsityResult M.Carrier
    (existentialModel M).constDen Symbols.falsity = _
  have meanings : @ConstantAdmission.standardSourceMeanings Source.falsityResult M.Carrier
      (existentialModel M).constDen = @ConstantAdmission.sourceMeanings Source.falsityResult (existentialModel M) :=
    ConstantAdmission.standardSourceMeanings_eq Source.falsityResult (existentialModel M)
      (existentialModel_fullDomains M full)
  rw [meanings]
  have inheritedDomains : ∀ type value, (existentialModel M).adm type value ↔ M.adm type value :=
    fun type value => ⟨fun _ => full type value, fun _ => existentialModel_fullDomains M full type value⟩
  have universalMeaning : ∀ (type : HOL.Ty AtomicTy)
      (predicate : HOL.Ty.denote.{0, w + 1} M.Carrier (type.arr .prop)),
      (existentialModel M).constDen (Symbols.universal type) predicate =
        ULift.up (∀ value, (existentialModel M).adm type value → (predicate value).down) := by
    intro type predicate
    simpa only [inheritedDomains, existentialModel_carrier] using existentialModel_universal M full type predicate
  have body := falsity_extension (existentialModel M)
    (existentialModel_fullDomains M full)
  refine (body).trans ?_
  exact raw_falsity_denote (existentialModel M) universalMeaning (fun index => nomatch index)

@[reducible] noncomputable def negationModel (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard M.Carrier
    (ConstantAdmission.standardSourceMeanings Source.negationResult M.Carrier (falsityModel M).constDen)

@[simp] theorem negationModel_carrier
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (negationModel M).Carrier = M.Carrier := rfl

theorem negationModel_fullDomains (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (_full : M.FullDomains) :
    (negationModel M).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem negationModel_eq_sourceExtension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    negationModel M = ConstantAdmission.sourceExtension Source.negationResult (falsityModel M) :=
  ConstantAdmission.standardSourceModel_eq_sourceExtension Source.negationResult (falsityModel M)
    (falsityModel_fullDomains M full)

theorem negationModel_truth (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (negationModel M).constDen (Symbols.truth) =
      ULift.up True := by
  have different : Source.truthConstant ≠ Source.negationResult.output.constant := by
    rw [Source.negationIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.truthConstant, Source.negationConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.negationResult M.Carrier (falsityModel M).constDen Source.truthConstant
    Source.truthSchema (type := HOL.Ty.prop)
    (by simp [Source.truthSchema])
    different
  exact (retained).trans
    (falsityModel_truth M full)

theorem negationModel_conjunction (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (negationModel M).constDen (Symbols.conjunction) left right =
      ULift.up (left.down ∧ right.down) := by
  have different : Source.conjunctionConstant ≠ Source.negationResult.output.constant := by
    rw [Source.negationIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.conjunctionConstant, Source.negationConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.negationResult M.Carrier (falsityModel M).constDen Source.conjunctionConstant
    Source.conjunctionSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.conjunctionSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (falsityModel_conjunction M full left right)

theorem negationModel_implication (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (negationModel M).constDen (Symbols.implication) left right =
      ULift.up (left.down → right.down) := by
  have different : Source.implicationConstant ≠ Source.negationResult.output.constant := by
    rw [Source.negationIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.implicationConstant, Source.negationConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.negationResult M.Carrier (falsityModel M).constDen Source.implicationConstant
    Source.implicationSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.implicationSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (falsityModel_implication M full left right)

theorem negationModel_universal (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (negationModel M).constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down) := by
  have different : Source.universalConstant ≠ Source.negationResult.output.constant := by
    rw [Source.negationIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.universalConstant, Source.negationConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.negationResult M.Carrier (falsityModel M).constDen Source.universalConstant
    (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (type := ((operand.arr .prop).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) predicate).trans
    (falsityModel_universal M full operand predicate)

theorem negationModel_existential (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (negationModel M).constDen (Symbols.existential operand) predicate =
      ULift.up (∃ value, M.adm operand value ∧ (predicate value).down) := by
  have different : Source.existentialConstant ≠ Source.negationResult.output.constant := by
    rw [Source.negationIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.existentialConstant, Source.negationConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.negationResult M.Carrier (falsityModel M).constDen Source.existentialConstant
    (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (type := ((operand.arr .prop).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) predicate).trans
    (falsityModel_existential M full operand predicate)

theorem negationModel_falsity (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (negationModel M).constDen (Symbols.falsity) =
      ULift.up False := by
  have different : Source.falsityConstant ≠ Source.negationResult.output.constant := by
    rw [Source.negationIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.falsityConstant, Source.negationConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.negationResult M.Carrier (falsityModel M).constDen Source.falsityConstant
    Source.falsitySchema (type := HOL.Ty.prop)
    (by simp [Source.falsitySchema])
    different
  exact (retained).trans
    (falsityModel_falsity M full)

theorem negationModel_negation (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (proposition : HOL.Ty.denote M.Carrier .prop) :
    (negationModel M).constDen (Symbols.negation) proposition =
      ULift.up (¬ proposition.down) := by
  change ConstantAdmission.standardSourceMeanings Source.negationResult M.Carrier
    (falsityModel M).constDen Symbols.negation proposition = _
  have meanings : @ConstantAdmission.standardSourceMeanings Source.negationResult M.Carrier
      (falsityModel M).constDen = @ConstantAdmission.sourceMeanings Source.negationResult (falsityModel M) :=
    ConstantAdmission.standardSourceMeanings_eq Source.negationResult (falsityModel M)
      (falsityModel_fullDomains M full)
  rw [meanings]
  have body := negation_extension (falsityModel M)
    (falsityModel_fullDomains M full)
  refine (congrFun (body) proposition).trans ?_
  exact raw_negation_denote (falsityModel M) (falsityModel_implication M full) (falsityModel_falsity M full) (fun index => nomatch index) proposition

@[reducible] noncomputable def oneOneModel (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard M.Carrier
    (ConstantAdmission.standardSourceMeanings Source.oneOneResult M.Carrier (negationModel M).constDen)

@[simp] theorem oneOneModel_carrier
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (oneOneModel M).Carrier = M.Carrier := rfl

theorem oneOneModel_fullDomains (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (_full : M.FullDomains) :
    (oneOneModel M).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem oneOneModel_eq_sourceExtension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    oneOneModel M = ConstantAdmission.sourceExtension Source.oneOneResult (negationModel M) :=
  ConstantAdmission.standardSourceModel_eq_sourceExtension Source.oneOneResult (negationModel M)
    (negationModel_fullDomains M full)

theorem oneOneModel_truth (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (oneOneModel M).constDen (Symbols.truth) =
      ULift.up True := by
  have different : Source.truthConstant ≠ Source.oneOneResult.output.constant := by
    rw [Source.oneOneIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.truthConstant, Source.oneOneConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.oneOneResult M.Carrier (negationModel M).constDen Source.truthConstant
    Source.truthSchema (type := HOL.Ty.prop)
    (by simp [Source.truthSchema])
    different
  exact (retained).trans
    (negationModel_truth M full)

theorem oneOneModel_conjunction (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (oneOneModel M).constDen (Symbols.conjunction) left right =
      ULift.up (left.down ∧ right.down) := by
  have different : Source.conjunctionConstant ≠ Source.oneOneResult.output.constant := by
    rw [Source.oneOneIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.conjunctionConstant, Source.oneOneConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.oneOneResult M.Carrier (negationModel M).constDen Source.conjunctionConstant
    Source.conjunctionSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.conjunctionSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (negationModel_conjunction M full left right)

theorem oneOneModel_implication (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (oneOneModel M).constDen (Symbols.implication) left right =
      ULift.up (left.down → right.down) := by
  have different : Source.implicationConstant ≠ Source.oneOneResult.output.constant := by
    rw [Source.oneOneIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.implicationConstant, Source.oneOneConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.oneOneResult M.Carrier (negationModel M).constDen Source.implicationConstant
    Source.implicationSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.implicationSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (negationModel_implication M full left right)

theorem oneOneModel_universal (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (oneOneModel M).constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down) := by
  have different : Source.universalConstant ≠ Source.oneOneResult.output.constant := by
    rw [Source.oneOneIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.universalConstant, Source.oneOneConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.oneOneResult M.Carrier (negationModel M).constDen Source.universalConstant
    (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (type := ((operand.arr .prop).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) predicate).trans
    (negationModel_universal M full operand predicate)

theorem oneOneModel_existential (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (oneOneModel M).constDen (Symbols.existential operand) predicate =
      ULift.up (∃ value, M.adm operand value ∧ (predicate value).down) := by
  have different : Source.existentialConstant ≠ Source.oneOneResult.output.constant := by
    rw [Source.oneOneIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.existentialConstant, Source.oneOneConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.oneOneResult M.Carrier (negationModel M).constDen Source.existentialConstant
    (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (type := ((operand.arr .prop).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) predicate).trans
    (negationModel_existential M full operand predicate)

theorem oneOneModel_falsity (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (oneOneModel M).constDen (Symbols.falsity) =
      ULift.up False := by
  have different : Source.falsityConstant ≠ Source.oneOneResult.output.constant := by
    rw [Source.oneOneIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.falsityConstant, Source.oneOneConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.oneOneResult M.Carrier (negationModel M).constDen Source.falsityConstant
    Source.falsitySchema (type := HOL.Ty.prop)
    (by simp [Source.falsitySchema])
    different
  exact (retained).trans
    (negationModel_falsity M full)

theorem oneOneModel_negation (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (proposition : HOL.Ty.denote M.Carrier .prop) :
    (oneOneModel M).constDen (Symbols.negation) proposition =
      ULift.up (¬ proposition.down) := by
  have different : Source.negationConstant ≠ Source.oneOneResult.output.constant := by
    rw [Source.oneOneIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.negationConstant, Source.oneOneConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.oneOneResult M.Carrier (negationModel M).constDen Source.negationConstant
    Source.negationSchema (type := (HOL.Ty.arr .prop .prop))
    (by simp [Source.negationSchema])
    different
  exact (congrFun (retained) proposition).trans
    (negationModel_negation M full proposition)

theorem oneOneModel_oneOne (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (domain : HOL.Ty AtomicTy) (codomain : HOL.Ty AtomicTy) (function : HOL.Ty.denote M.Carrier (domain.arr codomain)) :
    (oneOneModel M).constDen (Symbols.oneOne domain codomain) function =
      ULift.up (Function.Injective function) := by
  change ConstantAdmission.standardSourceMeanings Source.oneOneResult M.Carrier
    (negationModel M).constDen (Symbols.oneOne domain codomain) function = _
  have meanings : @ConstantAdmission.standardSourceMeanings Source.oneOneResult M.Carrier
      (negationModel M).constDen = @ConstantAdmission.sourceMeanings Source.oneOneResult (negationModel M) :=
    ConstantAdmission.standardSourceMeanings_eq Source.oneOneResult (negationModel M)
      (negationModel_fullDomains M full)
  rw [meanings]
  have inheritedDomains : ∀ type value, (negationModel M).adm type value ↔ M.adm type value :=
    fun type value => ⟨fun _ => full type value, fun _ => negationModel_fullDomains M full type value⟩
  have universalMeaning : ∀ (type : HOL.Ty AtomicTy)
      (predicate : HOL.Ty.denote.{0, w + 1} M.Carrier (type.arr .prop)),
      (negationModel M).constDen (Symbols.universal type) predicate =
        ULift.up (∀ value, (negationModel M).adm type value → (predicate value).down) := by
    intro type predicate
    simpa only [inheritedDomains, negationModel_carrier] using negationModel_universal M full type predicate
  have body := oneOne_extension (negationModel M)
    (negationModel_fullDomains M full) domain codomain
  refine (congrFun (body) function).trans ?_
  have rawMeaning := raw_oneOne_denote (negationModel M) universalMeaning (negationModel_implication M full) domain codomain (fun index => nomatch index) function
  have admitted : ∀ type value, (negationModel M).adm type value ↔ True :=
    fun type value => iff_true_intro (negationModel_fullDomains M full type value)
  simpa only [admitted, true_implies, true_and, negationModel_carrier,
    ConstantAdmission.sourceExtension_carrier,
    HOL.HenkinModel.eqv_iff_eq_of_fullDomains (negationModel M)
      (negationModel_fullDomains M full), Function.Injective] using rawMeaning

@[reducible] noncomputable def ontoModel (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard M.Carrier
    (ConstantAdmission.standardSourceMeanings Source.ontoResult M.Carrier (oneOneModel M).constDen)

@[simp] theorem ontoModel_carrier
    (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) :
    (ontoModel M).Carrier = M.Carrier := rfl

theorem ontoModel_fullDomains (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (_full : M.FullDomains) :
    (ontoModel M).FullDomains :=
  HOL.HenkinModel.fullDomains_standard _ _

theorem ontoModel_eq_sourceExtension (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol) (full : M.FullDomains) :
    ontoModel M = ConstantAdmission.sourceExtension Source.ontoResult (oneOneModel M) :=
  ConstantAdmission.standardSourceModel_eq_sourceExtension Source.ontoResult (oneOneModel M)
    (oneOneModel_fullDomains M full)

theorem ontoModel_truth (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (ontoModel M).constDen (Symbols.truth) =
      ULift.up True := by
  have different : Source.truthConstant ≠ Source.ontoResult.output.constant := by
    rw [Source.ontoIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.truthConstant, Source.ontoConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.ontoResult M.Carrier (oneOneModel M).constDen Source.truthConstant
    Source.truthSchema (type := HOL.Ty.prop)
    (by simp [Source.truthSchema])
    different
  exact (retained).trans
    (oneOneModel_truth M full)

theorem ontoModel_conjunction (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (ontoModel M).constDen (Symbols.conjunction) left right =
      ULift.up (left.down ∧ right.down) := by
  have different : Source.conjunctionConstant ≠ Source.ontoResult.output.constant := by
    rw [Source.ontoIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.conjunctionConstant, Source.ontoConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.ontoResult M.Carrier (oneOneModel M).constDen Source.conjunctionConstant
    Source.conjunctionSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.conjunctionSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (oneOneModel_conjunction M full left right)

theorem ontoModel_implication (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (left right : HOL.Ty.denote M.Carrier .prop) :
    (ontoModel M).constDen (Symbols.implication) left right =
      ULift.up (left.down → right.down) := by
  have different : Source.implicationConstant ≠ Source.ontoResult.output.constant := by
    rw [Source.ontoIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.implicationConstant, Source.ontoConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.ontoResult M.Carrier (oneOneModel M).constDen Source.implicationConstant
    Source.implicationSchema (type := (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop)))
    (by simp [Source.implicationSchema])
    different
  exact (congrFun (congrFun (retained) left) right).trans
    (oneOneModel_implication M full left right)

theorem ontoModel_universal (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (ontoModel M).constDen (Symbols.universal operand) predicate =
      ULift.up (∀ value, M.adm operand value → (predicate value).down) := by
  have different : Source.universalConstant ≠ Source.ontoResult.output.constant := by
    rw [Source.ontoIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.universalConstant, Source.ontoConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.ontoResult M.Carrier (oneOneModel M).constDen Source.universalConstant
    (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (type := ((operand.arr .prop).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) predicate).trans
    (oneOneModel_universal M full operand predicate)

theorem ontoModel_existential (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (operand : HOL.Ty AtomicTy) (predicate : HOL.Ty.denote M.Carrier (operand.arr .prop)) :
    (ontoModel M).constDen (Symbols.existential operand) predicate =
      ULift.up (∃ value, M.adm operand value ∧ (predicate value).down) := by
  have different : Source.existentialConstant ≠ Source.ontoResult.output.constant := by
    rw [Source.ontoIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.existentialConstant, Source.ontoConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.ontoResult M.Carrier (oneOneModel M).constDen Source.existentialConstant
    (Ty.function (Ty.function (Ty.fromHOL operand) Ty.bool) Ty.bool) (type := ((operand.arr .prop).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) predicate).trans
    (oneOneModel_existential M full operand predicate)

theorem ontoModel_falsity (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  :
    (ontoModel M).constDen (Symbols.falsity) =
      ULift.up False := by
  have different : Source.falsityConstant ≠ Source.ontoResult.output.constant := by
    rw [Source.ontoIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.falsityConstant, Source.ontoConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.ontoResult M.Carrier (oneOneModel M).constDen Source.falsityConstant
    Source.falsitySchema (type := HOL.Ty.prop)
    (by simp [Source.falsitySchema])
    different
  exact (retained).trans
    (oneOneModel_falsity M full)

theorem ontoModel_negation (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains)  (proposition : HOL.Ty.denote M.Carrier .prop) :
    (ontoModel M).constDen (Symbols.negation) proposition =
      ULift.up (¬ proposition.down) := by
  have different : Source.negationConstant ≠ Source.ontoResult.output.constant := by
    rw [Source.ontoIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.negationConstant, Source.ontoConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.ontoResult M.Carrier (oneOneModel M).constDen Source.negationConstant
    Source.negationSchema (type := (HOL.Ty.arr .prop .prop))
    (by simp [Source.negationSchema])
    different
  exact (congrFun (retained) proposition).trans
    (oneOneModel_negation M full proposition)

theorem ontoModel_oneOne (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (domain : HOL.Ty AtomicTy) (codomain : HOL.Ty AtomicTy) (function : HOL.Ty.denote M.Carrier (domain.arr codomain)) :
    (ontoModel M).constDen (Symbols.oneOne domain codomain) function =
      ULift.up (Function.Injective function) := by
  have different : Source.oneOneConstant ≠ Source.ontoResult.output.constant := by
    rw [Source.ontoIdentity]
    intro same
    have names := congrArg constantName same
    simp [constantName, Source.oneOneConstant, Source.ontoConstant, Name.global] at names
  have retained := ConstantAdmission.standardSourceMeanings_constant_other
    Source.ontoResult M.Carrier (oneOneModel M).constDen Source.oneOneConstant
    (Ty.function (Ty.function (Ty.fromHOL domain) (Ty.fromHOL codomain)) Ty.bool) (type := ((domain.arr codomain).arr .prop))
    (by simp)
    different
  exact (congrFun (retained) function).trans
    (oneOneModel_oneOne M full domain codomain function)

theorem ontoModel_onto (M : HOL.HenkinModel.{0, 0, w + 1} AtomicTy Symbol)
    (full : M.FullDomains) (domain : HOL.Ty AtomicTy) (codomain : HOL.Ty AtomicTy) (function : HOL.Ty.denote M.Carrier (domain.arr codomain)) :
    (ontoModel M).constDen (Symbols.onto domain codomain) function =
      ULift.up (Function.Surjective function) := by
  change ConstantAdmission.standardSourceMeanings Source.ontoResult M.Carrier
    (oneOneModel M).constDen (Symbols.onto domain codomain) function = _
  have meanings : @ConstantAdmission.standardSourceMeanings Source.ontoResult M.Carrier
      (oneOneModel M).constDen = @ConstantAdmission.sourceMeanings Source.ontoResult (oneOneModel M) :=
    ConstantAdmission.standardSourceMeanings_eq Source.ontoResult (oneOneModel M)
      (oneOneModel_fullDomains M full)
  rw [meanings]
  have inheritedDomains : ∀ type value, (oneOneModel M).adm type value ↔ M.adm type value :=
    fun type value => ⟨fun _ => full type value, fun _ => oneOneModel_fullDomains M full type value⟩
  have universalMeaning : ∀ (type : HOL.Ty AtomicTy)
      (predicate : HOL.Ty.denote.{0, w + 1} M.Carrier (type.arr .prop)),
      (oneOneModel M).constDen (Symbols.universal type) predicate =
        ULift.up (∀ value, (oneOneModel M).adm type value → (predicate value).down) := by
    intro type predicate
    simpa only [inheritedDomains, oneOneModel_carrier] using oneOneModel_universal M full type predicate
  have existentialMeaning : ∀ (type : HOL.Ty AtomicTy)
      (predicate : HOL.Ty.denote.{0, w + 1} M.Carrier (type.arr .prop)),
      (oneOneModel M).constDen (Symbols.existential type) predicate =
        ULift.up (∃ value, (oneOneModel M).adm type value ∧ (predicate value).down) := by
    intro type predicate
    simpa only [inheritedDomains, oneOneModel_carrier] using oneOneModel_existential M full type predicate
  have body := onto_extension (oneOneModel M)
    (oneOneModel_fullDomains M full) domain codomain
  refine (congrFun (body) function).trans ?_
  have rawMeaning := raw_onto_denote (oneOneModel M) universalMeaning existentialMeaning domain codomain (fun index => nomatch index) function
  refine rawMeaning.trans ?_
  apply congrArg ULift.up
  apply propext
  constructor
  · intro onto value
    obtain ⟨preimage, _, equivalent⟩ := onto value (oneOneModel_fullDomains M full codomain value)
    exact ⟨preimage, ((HOL.HenkinModel.eqv_iff_eq_of_fullDomains (oneOneModel M)
      (oneOneModel_fullDomains M full) _ _).mp equivalent).symm⟩
  · intro onto value _
    obtain ⟨preimage, equal⟩ := onto value
    exact ⟨preimage, oneOneModel_fullDomains M full domain preimage,
      (HOL.HenkinModel.eqv_iff_eq_of_fullDomains (oneOneModel M)
        (oneOneModel_fullDomains M full) _ _).mpr equal.symm⟩

end Interpretation





end Mettapedia.Languages.HOLLight.StandardTheoryInterpretation
