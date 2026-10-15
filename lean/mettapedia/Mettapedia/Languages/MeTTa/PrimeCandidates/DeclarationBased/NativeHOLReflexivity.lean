import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLExecution
import Mettapedia.Languages.OpenTheory.ExtensionalHOLInterpretation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerUniformList

/-!
# Authored HOL reflexivity and native dependent proof evidence

The admitted interpretation here is the constant-free Boolean lambda
fragment. It preserves arrow types and de Bruijn positions, and embeds into
the existing logical signature and proof compiler. No atomic carrier or
source constant is identified with a List carrier.

The source checker, its shared HOL conclusion, the retained reflexivity
constructor, and the compiled native inhabitant are separate parts of the
connection. The native equality is the existing predicate equality, not
dependent identity. Declaration interpretation and the remaining source
inference requests require further adapters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLReflexivity

open Mettapedia.Logic
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.FormationSensitive

namespace BooleanLambda

abbrev TargetBase := HOL.UniformListInduction.BaseSort
abbrev TargetSymbol := HOL.UniformListInduction.Symbol

/-- Only the proposition carrier and constant arrow families are admitted. -/
inductive TypeImage : HOL.Ty AtomicTy → HOL.Ty TargetBase → Prop where
  | proposition : TypeImage .prop .prop
  | arrow {a b : HOL.Ty AtomicTy} {a' b' : HOL.Ty TargetBase} :
      TypeImage a a' → TypeImage b b' → TypeImage (.arr a b) (.arr a' b')

theorem TypeImage.functional {a : HOL.Ty AtomicTy} {b c : HOL.Ty TargetBase}
    (first : TypeImage a b) (second : TypeImage a c) : b = c := by
  induction first generalizing c with
  | proposition => cases second; rfl
  | arrow ha hb ia ib =>
      cases second with
      | arrow hc hd => rw [ia hc, ib hd]

theorem TypeImage.reflects {a b : HOL.Ty AtomicTy} {c : HOL.Ty TargetBase}
    (first : TypeImage a c) (second : TypeImage b c) : a = b := by
  induction first generalizing b with
  | proposition => cases second; rfl
  | arrow ha hb ia ib =>
      cases second with
      | arrow hc hd => rw [ia hc, ib hd]

/-- Variables keep their binder position and the interpretation of their type. -/
inductive VariableImage : {gamma : HOL.Ctx AtomicTy} → {delta : HOL.Ctx TargetBase} →
    {a : HOL.Ty AtomicTy} → {b : HOL.Ty TargetBase} → HOL.Var gamma a → HOL.Var delta b → Prop where
  | zero {gamma : HOL.Ctx AtomicTy} {delta : HOL.Ctx TargetBase}
      {a : HOL.Ty AtomicTy} {b : HOL.Ty TargetBase} :
      TypeImage a b → VariableImage (gamma := a :: gamma) (delta := b :: delta) .vz .vz
  | successor {gamma : HOL.Ctx AtomicTy} {delta : HOL.Ctx TargetBase}
      {a binder : HOL.Ty AtomicTy} {b binder' : HOL.Ty TargetBase}
      {x : HOL.Var gamma a} {y : HOL.Var delta b} :
      VariableImage x y → VariableImage (.vs (σ := binder) x) (.vs (σ := binder') y)

theorem VariableImage.type {gamma : HOL.Ctx AtomicTy} {delta : HOL.Ctx TargetBase}
    {a : HOL.Ty AtomicTy} {b : HOL.Ty TargetBase} {x : HOL.Var gamma a} {y : HOL.Var delta b}
    (image : VariableImage x y) : TypeImage a b := by
  induction image with
  | zero typed => exact typed
  | successor prior ih => exact ih

/-- This relation uses the existing intrinsic term grammars. It admits no
constant, free symbol, or additional logical connective. -/
inductive Image : {gamma : HOL.Ctx AtomicTy} → {delta : HOL.Ctx TargetBase} →
    {a : HOL.Ty AtomicTy} → {b : HOL.Ty TargetBase} →
    HOL.Term Symbol gamma a → HOL.Term TargetSymbol delta b → Prop where
  | variable {gamma : HOL.Ctx AtomicTy} {delta : HOL.Ctx TargetBase}
      {a : HOL.Ty AtomicTy} {b : HOL.Ty TargetBase} {x : HOL.Var gamma a} {y : HOL.Var delta b} :
      VariableImage x y → Image (.var x) (.var y)
  | application {gamma : HOL.Ctx AtomicTy} {delta : HOL.Ctx TargetBase}
      {a c : HOL.Ty AtomicTy} {b d : HOL.Ty TargetBase}
      {f : HOL.Term Symbol gamma (.arr a c)} {g : HOL.Term TargetSymbol delta (.arr b d)}
      {x : HOL.Term Symbol gamma a} {y : HOL.Term TargetSymbol delta b} :
      Image f g → Image x y → Image (.app f x) (.app g y)
  | abstraction {gamma : HOL.Ctx AtomicTy} {delta : HOL.Ctx TargetBase}
      {a c : HOL.Ty AtomicTy} {b d : HOL.Ty TargetBase}
      {body : HOL.Term Symbol (a :: gamma) c} {body' : HOL.Term TargetSymbol (b :: delta) d} :
      TypeImage a b → Image body body' → Image (.lam body) (.lam body')

theorem Image.type {gamma : HOL.Ctx AtomicTy} {delta : HOL.Ctx TargetBase}
    {a : HOL.Ty AtomicTy} {b : HOL.Ty TargetBase}
    {term : HOL.Term Symbol gamma a} {term' : HOL.Term TargetSymbol delta b}
    (image : Image term term') : TypeImage a b := by
  induction image with
  | «variable» position => exact position.type
  | application function argument functionType argumentType =>
      cases functionType with
      | arrow domain codomain => exact codomain
  | abstraction domain body bodyType => exact .arrow domain bodyType

/-- Representation is constructed for every term in the admitted fragment,
including arbitrary nested lambdas and applications. -/
theorem Image.represented {gamma : HOL.Ctx AtomicTy} {delta : HOL.Ctx TargetBase}
    {a : HOL.Ty AtomicTy} {b : HOL.Ty TargetBase}
    {term : HOL.Term Symbol gamma a} {term' : HOL.Term TargetSymbol delta b}
    (image : Image term term') :
    ∃ code, FormationSensitiveHOLInterface.represent FormationSensitiveHOLLeibnizInterface.signature term' = some code := by
  induction image with
  | «variable» position => exact ⟨_, rfl⟩
  | application function argument functionCode argumentCode =>
      obtain ⟨f, hf⟩ := functionCode
      obtain ⟨x, hx⟩ := argumentCode
      exact ⟨.app f x, FormationSensitiveHOLInterface.represent_app _ _ _ hf hx⟩
  | abstraction domain body bodyCode =>
      obtain ⟨body, known⟩ := bodyCode
      exact ⟨.lam body, by simp [FormationSensitiveHOLInterface.represent, known]⟩

/-- An atomic source carrier cannot enter this Boolean interpretation. -/
theorem atomic_refused (atomic : AtomicTy) (type : HOL.Ty TargetBase) :
    ¬ TypeImage (.base atomic) type := by intro image; cases image

/-- An arbitrary source constant is not licensed by the lambda fragment. -/
theorem constant_refused {gamma : HOL.Ctx AtomicTy} {delta : HOL.Ctx TargetBase}
    {a : HOL.Ty AtomicTy} {b : HOL.Ty TargetBase} (constant : Symbol a)
    (target : HOL.Term TargetSymbol delta b) : ¬ Image (.const (Γ := gamma) constant) target := by
  intro image
  cases image

end BooleanLambda

namespace Native

abbrev signature := FormationSensitiveHOLLeibnizInterface.signature
abbrev proofName := HOLNativeGenericProofCompiler.UniformList.proofName
abbrev operations := HOLNativeGenericProofCompiler.UniformList.operations
abbrev reflexivity : Tower.Tm 0 := FormationSensitiveHOLLeibnizDerived.reflTerm

/-- Compilation retains the supplied reflexivity rule rather than selecting
an arbitrary proof from proposition-valued derivability. -/
theorem compile_reflexivity {type : HOL.Ty BooleanLambda.TargetBase}
    (term : HOL.Term BooleanLambda.TargetSymbol [] type) {code : Tower.Tm 0}
    (represented : FormationSensitiveHOLInterface.represent signature term = some code) :
    HOLNativeGenericProofCompiler.compile signature proofName operations
      (HOL.ProofSyntax.eqRefl (Δ := []) term) Fin.elim0 Fin.elim0 = some reflexivity := by
  simp [HOLNativeGenericProofCompiler.compile, represented, operations,
    HOLNativeGenericProofCompiler.UniformList.operations,
    HOLNativeGenericProofCompiler.UniformList.rawOperations, reflexivity]

/-- The existing compiler theorem checks the actual two-lambda proof at the
family indexed by this term's represented equality proposition. -/
theorem reflexivity_typed {type : HOL.Ty BooleanLambda.TargetBase}
    (term : HOL.Term BooleanLambda.TargetSymbol [] type) {code : Tower.Tm 0}
    (represented : FormationSensitiveHOLInterface.represent signature term = some code) :
    Typing operations.target .nil reflexivity
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (HOLNativeGenericProofCompiler.rawEquality signature type code code)) := by
  obtain ⟨formula, formulaCode, typed⟩ := HOLNativeGenericProofCompiler.GenericTyping.compile_closed
    signature proofName operations (HOL.ProofSyntax.eqRefl (Δ := []) term) (compile_reflexivity term represented)
  have equalityCode : FormationSensitiveHOLInterface.represent signature (.eq term term) =
      some (HOLNativeGenericProofCompiler.rawEquality signature type code code) := by
    exact FormationSensitiveHOLInterface.represent_eq _ _ _ represented represented
  rw [equalityCode] at formulaCode
  cases Option.some.inj formulaCode
  exact typed

end Native

/-- An actual authored REFL execution, its shared HOL conclusion, and a
constructed native proof inhabitant agree through the admitted interpretation.
No prior theorem record, axiom commitment, or assumed checker soundness is
used. The represented term and represented conclusion are both retained. -/
theorem authored_reflexivity_native
    (world : DefinitionAdapters.TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : SignatureFormation.AnnotationsFormed world.signature source.canonical.term)
    (sourceType : HOL.Ty AtomicTy) (typeImage : source.ty.toHOL = sourceType)
    (sourceImage : HOL.Term Symbol [] sourceType)
    (translated : Translates [] source.canonical.term sourceType sourceImage)
    {nativeType : HOL.Ty BooleanLambda.TargetBase}
    (nativeImage : HOL.Term BooleanLambda.TargetSymbol [] nativeType)
    (image : BooleanLambda.Image sourceImage nativeImage)
    (bindings : Subst) (state : Effects.State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "REFL", TermReading.sourceAtom source.source]) (policy : AxiomPolicy) :
    ∃ (out : Theorem) (code : Tower.Tm 0),
      InferenceRequest.Semantics (.refl source.canonical) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧
      out.axioms = ∅ ∧ out.sequent.hyp = ∅ ∧
      Translates [] out.sequent.concl.term .prop (.eq sourceImage sourceImage) ∧
      Eval.PureReturns program bindings state
        (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
        (.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .symbol "HOL:Nil",
          Representation.termAtom Representation.registeredOperatorAtom constants [] out.sequent.concl.term,
          .symbol "HOL:Nil", .symbol "REFL"]]) ∧
      FormationSensitiveHOLInterface.represent Native.signature nativeImage = some code ∧
      HOLNativeGenericProofCompiler.compile Native.signature Native.proofName Native.operations
        (HOL.ProofSyntax.eqRefl (Δ := []) nativeImage) Fin.elim0 Fin.elim0 = some Native.reflexivity ∧
      Typing Native.operations.target .nil Native.reflexivity
        (FormationSensitiveHOLGenericProofFamily.proof Native.proofName
          (HOLNativeGenericProofCompiler.rawEquality Native.signature nativeType code code)) := by
  obtain ⟨out, semantics, derived, noAxioms, noHypotheses, returned⟩ :=
    InferenceExecution.authored_refl_derivation world table origins constants equalityIdentity
      source resolved annotations bindings state axioms receipts cache stateKey requestKey stateCaptured requestCaptured policy
  obtain ⟨code, represented⟩ := image.represented
  have conclusion : Translates [] out.sequent.concl.term .prop (.eq sourceImage sourceImage) := by
    obtain ⟨equality, equalityShape, parts⟩ := semantics
    rw [parts.2.2, equalityShape.2]
    exact .equalityApp (equalityOperand?_equality source.ty) typeImage translated translated
  exact ⟨out, code, semantics, derived, noAxioms, noHypotheses, conclusion, returned,
    represented, Native.compile_reflexivity nativeImage represented, Native.reflexivity_typed nativeImage represented⟩

namespace Controls

private def identity : CheckedSourceTerm :=
  ⟨.abs (Name.global "p") Ty.bool (.var (Name.global "p") Ty.bool), .function Ty.bool Ty.bool, by
    simp [SourceTerm.inferType]⟩

private def sourceImage : HOL.Term Symbol [] (.arr .prop .prop) := .lam (.var .vz)
private def nativeImage : HOL.Term BooleanLambda.TargetSymbol [] (.arr .prop .prop) := .lam (.var .vz)

private theorem boolean_formed : SignatureFormation.TypeFormed SourceProfile.primitiveContext.signature Ty.bool :=
  DefinitionAdapters.ContextControls.boolean_formed.mono
    (DefinitionAdapters.ContextControls.core_includes.trans
      (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes))

private theorem boolean_resolved : TypeFormation.Resolved SourceProfile.primitiveContext.signature Ty.bool := by
  change TypeFormation.Resolved _ (.op TypeOp.bool [])
  apply TypeFormation.resolved_registered_operator _ _ 0 []
  · simpa [SignatureFormation.TypeFormed, Ty.bool] using boolean_formed
  · simp

private def operators : Atom := OperatorTable.tableAtom DeclarationTable.sourcePrimitive.operators
  (fun _ => .symbol "HOL:Primitive")
private def declarations : Atom := DeclarationTable.tableAtom DeclarationTable.sourcePrimitive DeclarationTable.primitiveIdentity
private def bindings : Subst :=
  [("request", .expression [.symbol "REFL", TermReading.sourceAtom identity.source]),
   ("state", ProofLookup.sourceState operators declarations (.symbol "HOL:Nil") (.symbol "HOL:Nil") [])]

/-- A concrete registered source identity request executes the authored
checker and supplies an ordinary native lambda proof of its interpreted
conclusion. The source hypotheses and axiom dependencies are both empty. -/
theorem boolean_identity_checked (state : Effects.State) :
    ∃ (out : Theorem) (code : Tower.Tm 0),
      Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) out ∧
      Translates [] out.sequent.concl.term .prop (.eq sourceImage sourceImage) ∧
      Eval.PureReturns program bindings state
        (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
        (.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .symbol "HOL:Nil",
          Representation.termAtom Representation.registeredOperatorAtom DeclarationTable.primitiveIdentity [] out.sequent.concl.term,
          .symbol "HOL:Nil", .symbol "REFL"]]) ∧
      FormationSensitiveHOLInterface.represent Native.signature nativeImage = some code ∧
      Typing Native.operations.target .nil Native.reflexivity
        (FormationSensitiveHOLGenericProofFamily.proof Native.proofName
          (HOLNativeGenericProofCompiler.rawEquality Native.signature (.arr .prop .prop) code code)) := by
  have resolved : TermReading.SourceResolved SourceProfile.primitiveContext.signature identity.source := by
    simp only [identity, TermReading.SourceResolved]
    exact ⟨rfl, boolean_resolved, rfl, boolean_resolved⟩
  have annotations : SignatureFormation.AnnotationsFormed SourceProfile.primitiveContext.signature identity.canonical.term := by
    simpa [identity, CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex] using
      (SignatureFormation.AnnotationsFormed.abs boolean_formed (.bound 0))
  have translated : Translates [] identity.canonical.term (.arr .prop .prop) sourceImage := by
    simpa [identity, CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex, sourceImage, deBruijnIndex] using
      (Translates.abs (Γ := []) Ty.toHOL_bool (Translates.bound (HOL.Var.vz : HOL.Var [.prop] .prop)))
  have image : BooleanLambda.Image sourceImage nativeImage :=
    .abstraction .proposition (.variable (.zero .proposition))
  obtain ⟨out, code, -, derived, -, -, translatedConclusion, returned, represented, -, typed⟩ :=
    authored_reflexivity_native SourceProfile.primitiveContext DeclarationTable.sourcePrimitive
      (fun _ => .symbol "HOL:Primitive") DeclarationTable.primitiveIdentity rfl identity resolved annotations
      (.arr .prop .prop) (by simp [identity]) sourceImage translated nativeImage image
      bindings state (.symbol "HOL:Nil") (.symbol "HOL:Nil") [] "state" "request"
      (by simp [bindings, operators, declarations, applySubst, Subst.lookup])
      (by simp [bindings, applySubst, Subst.lookup]) emptyAxiomPolicy
  exact ⟨out, code, derived, translatedConclusion, returned, represented, typed⟩

/-- Equal types do not authorize swapping the two binder positions. -/
theorem swapped_binders_refused :
    ¬ BooleanLambda.VariableImage
      (HOL.Var.vz : HOL.Var [(.prop : HOL.Ty AtomicTy), .prop] .prop)
      (HOL.Var.vs .vz : HOL.Var [(.prop : HOL.Ty BooleanLambda.TargetBase), .prop] .prop) := by
  intro image
  cases image

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLReflexivity
