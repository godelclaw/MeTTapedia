import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Cache
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation
import Mettapedia.OSLF.NativeTypes.Certificates.RefinementChecking
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementJudgmentControls
import Mettapedia.GSLT.LanguageDef.SemanticEvidence
import Mettapedia.OSLF.Syntax.BindingEqualityCertificates
import Mettapedia.OSLF.Syntax.PatternSubstEquation
import Mettapedia.OSLF.Syntax.BindingEqualityWire
import Mettapedia.OSLF.Syntax.BindingWireString
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion

/-!
# Native certificate execution and rejecting controls

The independent dependent-language examples supply primitive declarations and
derivation witnesses. Raw certificates are checked computationally, including
conditional refinements and higher-order quantified predicates. Damaged premise
trees and incorrect requested judgments are rejected without semantic oracles.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Controls

deriving instance DecidableEq for TypeSymbol, PredicateSymbol

instance : DecidableEq symbols.TypeSymbol := inferInstanceAs (DecidableEq TypeSymbol)
instance : DecidableEq symbols.TermSymbol := inferInstanceAs (DecidableEq Empty)
instance : DecidableEq symbols.PredicateSymbol := inferInstanceAs (DecidableEq PredicateSymbol)

def empty : Refinement.Certificate signature := Refinement.erase emptyContext

def conditional : Refinement.Certificate signature := Refinement.erase conditionalRefinement

def quantified : Refinement.Certificate signature := Refinement.erase quantifiedPredicateFunction

def reification : Refinement.Certificate signature := Refinement.erase firstClassPredicateQuote

def newest : Refinement.Certificate signature := Refinement.erase newestAssumption

def older : Refinement.Certificate signature := Refinement.erase olderAssumption

def damagedFamily : Refinement.Certificate signature :=
  .node (.typeFamily .nil .scalar Fin.elim0) (fun _ => empty)

theorem conditional_checked : Refinement.check conditional
    (.term conditionalContext (.refine (scalar 1) (positive 1) (.var 0))
      (.comprehension (scalar 1) (positive 1))) = true := by
  exact Refinement.check_erase conditionalRefinement

theorem duplicate_origin_certificates_distinct : newest ≠ older := by
  intro same
  apply assumption_trees_retain_positions
  exact Tree.erase_injective (P := Refinement.presentation signature) same

theorem damaged_family_rejected : Refinement.check damagedFamily
    (.type .nil (scalar 0)) = false := by decide

theorem wrong_context_rejected : Refinement.check empty
    (.context (.snoc .nil (scalar 0))) = false := by decide

theorem wrong_conclusion_rejected : Refinement.check conditional
    (.entails conditionalContext .falsehood) = false := by decide

#guard Refinement.check empty (.context .nil)
#guard Refinement.check conditional
  (.term conditionalContext (.refine (scalar 1) (positive 1) (.var 0))
    (.comprehension (scalar 1) (positive 1)))
#guard Refinement.check quantified
  (.entails .nil (.all (predicateFunctionAt 0)
    (.all (scalar 1) (.implies appliedPredicate appliedPredicate))))
#guard Refinement.check reification
  (.term (.snoc .nil (scalar 0)) (.quote (positive 0)) .propositions)
#guard Refinement.check newest (.entails duplicateContext (positive 0))
#guard Refinement.check older (.entails duplicateContext (positive 0))
#guard !(Refinement.check damagedFamily (.type .nil (scalar 0)))
#guard !(Refinement.check empty (.context (.snoc .nil (scalar 0))))
#guard !(Refinement.check conditional (.entails conditionalContext .falsehood))

namespace CommonRules

open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.GSLT.LanguageDef.SemanticEvidence

/-- Reuse the independent repeated-premise specimen as a native rule table. -/
def original : Presentation where
  Judgment := Bool
  Rule := Σ judgment, RepeatedPremiseControl.Shape judgment
  conclusion := Sigma.fst
  premises code := RepeatedPremiseControl.presentation.premises () code.1 code.2

def shifted : Presentation where
  Judgment := Option Bool
  Rule := original.Rule
  conclusion code := some (original.conclusion code)
  premises code := (original.premises code).map some

instance : DecidableEq original.Judgment := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq shifted.Judgment := inferInstanceAs (DecidableEq (Option Bool))

def inclusion : Presentation.Morphism original shifted where
  judgment := some
  rule := id
  conclusion _ := rfl
  premises _ := rfl

def left : Tree original := .node ⟨false, .left⟩ Fin.elim0
def right : Tree original := .node ⟨false, .right⟩ Fin.elim0
def pair : Tree original :=
  .node ⟨true, .pair⟩ (Fin.cases left (fun _ => right))

theorem original_accepted : pair.check true = true := by decide +kernel
theorem shifted_accepted : (pair.map inclusion).check (some true) = true :=
  Tree.check_map inclusion pair true original_accepted
theorem shifted_reflects (tree : Tree original) (claim : Bool) :
    (tree.map inclusion).check (some claim) = true ↔ tree.check claim = true := by
  apply Tree.check_map_iff inclusion
  intro first second same
  exact Option.some.inj same
theorem occurrences_retained : (pair.map inclusion).nodeCount = 3 := by decide +kernel
theorem absent_claim_refused : (pair.map inclusion).check none = false := by decide +kernel

def leftWire : Tree.Wire original := .node ⟨false, .left⟩ []
def rightWire : Tree.Wire original := .node ⟨false, .right⟩ []
def pairWire : Tree.Wire original := .node ⟨true, .pair⟩ [leftWire, rightWire]

theorem wire_accepted : Tree.checkWire pairWire true = true := by decide +kernel
theorem missing_occurrence_refused :
    Tree.checkWire (P := original) (.node ⟨true, .pair⟩ [leftWire]) true = false := by decide +kernel
theorem extra_occurrence_refused :
    Tree.checkWire (P := original) (.node ⟨true, .pair⟩ [leftWire, rightWire, leftWire]) true = false := by decide +kernel
theorem wrong_child_refused :
    Tree.checkWire (P := original) (.node ⟨true, .pair⟩ [pairWire, rightWire]) true = false := by decide +kernel
theorem wrong_wire_goal_refused : Tree.checkWire pairWire false = false := by decide +kernel

/-- The source admits only one leaf. Target-only rules remain extra behavior
even when the judgment map is injective and every mapped proof checks exactly. -/
def smaller : Presentation where
  Judgment := Bool
  Rule := Unit
  conclusion _ := false
  premises _ := []

instance : DecidableEq smaller.Judgment := inferInstanceAs (DecidableEq Bool)

def smallInclusion : Presentation.Morphism smaller original where
  judgment := id
  rule _ := ⟨false, .left⟩
  conclusion _ := rfl
  premises _ := rfl

theorem target_has_extra_proof :
    pair.check true = true ∧ ∀ proof : Tree smaller, proof.check true = false := by
  refine ⟨original_accepted, ?_⟩
  intro proof
  cases proof
  rfl

def collapsed : Presentation where
  Judgment := Unit
  Rule := Unit
  conclusion _ := ()
  premises _ := []

instance : DecidableEq collapsed.Judgment := inferInstanceAs (DecidableEq Unit)

def collapse : Presentation.Morphism smaller collapsed where
  judgment _ := ()
  rule := id
  conclusion _ := rfl
  premises _ := rfl

def smallLeaf : Tree smaller := .node () Fin.elim0

theorem collapsing_claims_breaks_reflection :
    smallLeaf.check true = false ∧ (smallLeaf.map collapse).check () = true := by decide +kernel

theorem generated_kernel_checks : (FiniteRuleKernel.kernel original).decide true pair = true :=
  original_accepted
theorem generated_wire_checks : (FiniteRuleKernel.wireChecker original).check true pairWire = true :=
  wire_accepted

#guard pair.check true
#guard (pair.map inclusion).check (some true)
#guard (pair.map inclusion).nodeCount == 3
#guard !(pair.map inclusion).check none
#guard Tree.checkWire pairWire true
#guard !(Tree.checkWire (P := original) (.node ⟨true, .pair⟩ [leftWire]) true)
#guard !(Tree.checkWire (P := original) (.node ⟨true, .pair⟩ [leftWire, rightWire, leftWire]) true)
#guard !(Tree.checkWire (P := original) (.node ⟨true, .pair⟩ [pairWire, rightWire]) true)
#guard !(Tree.checkWire pairWire false)
#guard !smallLeaf.check true
#guard (smallLeaf.map collapse).check ()

end CommonRules

namespace BindingEquality

open Mettapedia.OSLF.Binding
open PatternPresentation EqualityCertificates

deriving instance DecidableEq for PatOp

def substitutionAxiom : Certificate patSig PatternSubst.substMetas PatternSubst.patE [] PatSrt.pat :=
  .axiom ⟨0, by decide⟩
    (Bodies.quote _ (ContextualAssignment.ofClosed PatternSubst.bodies [])) .nil .nil

theorem authored_substitution_checked :
    check substitutionAxiom PatternSubst.redexTerm PatternSubst.contractum = true := by decide +kernel

theorem authored_substitution_reversed :
    check (.symm substitutionAxiom) PatternSubst.contractum PatternSubst.redexTerm = true := by decide +kernel

def openBody : Term patSig [PatSrt.pat, PatSrt.pat] PatSrt.pat :=
  .op (.lamOp (some "q")) (.cons (.var (.succ .zero)) .nil)

def replaceOpen : Substitution patSig [PatSrt.pat, PatSrt.pat] [PatSrt.pat] :=
  .cons (.var .zero) (.cons (.var .zero) .nil)

def lifted : Term patSig [PatSrt.pat] PatSrt.pat :=
  .op (.lamOp (some "q")) (.cons (.var (.succ .zero)) .nil)

def captured : Term patSig [PatSrt.pat] PatSrt.pat :=
  .op (.lamOp (some "q")) (.cons (.var .zero) .nil)

def substituted : Certificate patSig [] [] [PatSrt.pat] PatSrt.pat :=
  .substitute replaceOpen (.refl openBody)

theorem open_capture_avoided : check substituted lifted lifted = true := by decide +kernel

/-- Both proposed results have the same sort and a valid scope. The raw
equality evidence still distinguishes capture from capture avoidance. -/
theorem scoped_capture_refused : check substituted captured captured = false := by decide +kernel

def mismatched : Certificate patSig [] [] [PatSrt.pat] PatSrt.pat :=
  .trans (.refl lifted) (.refl captured)

theorem invalid_transitivity_refused : replay mismatched = none := by decide +kernel

def beneathBinder : Certificate patSig [] [] [] PatSrt.pat :=
  .cong (.lamOp (some "q")) (.cons (.refl (.var .zero)) .nil)

def identity : Term patSig [] PatSrt.pat :=
  .op (.lamOp (some "q")) (.cons (.var .zero) .nil)

theorem binder_congruence_checked : check beneathBinder identity identity = true := by decide +kernel

namespace Raw

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature

def sorts : Codec PatSrt := Codec.nat.mapped (fun _ => 0)
  (fun code => if code = 0 then some .pat else none) (by intro sort; cases sort; rfl)

def operators : Codec (Σ sort : PatSrt, PatOp sort) :=
  Codec.name.mapped (fun ⟨.pat, operator⟩ => operatorName operator)
    (fun name => (decodeName name).map (fun operator => ⟨.pat, operator⟩))
    (by rintro ⟨sort, operator⟩; cases sort; simp only [decodeName_operator, Option.map_some])

def substitutedWire : Data := Wire.putCertificate sorts operators [] substituted
def axiomWire : Data := Wire.putCertificate sorts operators PatternSubst.patE substitutionAxiom
def binderWire : Data := Wire.putCertificate sorts operators [] beneathBinder

theorem encoded_open_substitution_checked :
    Wire.check (metas := []) sorts operators [] substitutedWire lifted lifted = true := by decide +kernel

theorem encoded_authored_axiom_checked :
    Wire.check sorts operators PatternSubst.patE axiomWire
      PatternSubst.redexTerm PatternSubst.contractum = true := by decide +kernel

theorem encoded_capture_refused :
    Wire.check (metas := []) sorts operators [] substitutedWire captured captured = false := by decide +kernel

def dangling : Data := .pair (.atom 1)
  (.pair ((Codec.list sorts).put []) (.pair (sorts.put .pat) (.pair (.atom 0) (.atom 0))))

theorem dangling_variable_refused :
    (Wire.getCertificate sorts operators ([] : List (EqAxiom patSig [])) dangling).isNone = true := by decide +kernel

def wrongSort : Data := .pair (.atom 1)
  (.pair ((Codec.list sorts).put []) (.pair (.atom 1) (.pair (.atom 0) (.atom 0))))

theorem unknown_sort_refused :
    (Wire.getCertificate sorts operators ([] : List (EqAxiom patSig [])) wrongSort).isNone = true := by decide +kernel

def missingBinder : Data := .pair (.atom 4)
  (.pair ((Codec.list sorts).put [])
    (.pair (operators.put ⟨.pat, .lamOp (some "q")⟩) (.atom 0)))

theorem missing_binder_body_refused :
    (Wire.getCertificate sorts operators ([] : List (EqAxiom patSig [])) missingBinder).isNone = true := by decide +kernel

def outsideEquation : Data := .pair (.atom 0) (.pair (.atom 1)
  (.pair (.atom 0) (.pair (.atom 0) (.pair (.atom 0) (.pair (.atom 0) (.atom 0))))))

theorem unregistered_equation_refused :
    (Wire.getCertificate sorts operators PatternSubst.patE outsideEquation).isNone = true := by decide +kernel

#guard Wire.check (metas := []) sorts operators [] substitutedWire lifted lifted
#guard Wire.check sorts operators PatternSubst.patE axiomWire PatternSubst.redexTerm PatternSubst.contractum
#guard Wire.check (metas := []) sorts operators [] binderWire identity identity
#guard !(Wire.check (metas := []) sorts operators [] substitutedWire captured captured)
#guard (Wire.getCertificate sorts operators ([] : List (EqAxiom patSig [])) dangling).isNone
#guard (Wire.getCertificate sorts operators ([] : List (EqAxiom patSig [])) wrongSort).isNone
#guard (Wire.getCertificate sorts operators ([] : List (EqAxiom patSig [])) missingBinder).isNone
#guard (Wire.getCertificate sorts operators PatternSubst.patE outsideEquation).isNone

end Raw

#guard check substitutionAxiom PatternSubst.redexTerm PatternSubst.contractum
#guard check (.symm substitutionAxiom) PatternSubst.contractum PatternSubst.redexTerm
#guard check substituted lifted lifted
#guard !(check substituted captured captured)
#guard (replay mismatched).isNone
#guard check beneathBinder identity identity

end BindingEquality

end Mettapedia.OSLF.NativeTypes.Certificates.Controls

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.ContextualPrograms

open Mettapedia.OSLF.Binding
open PatternPresentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open BindingSignatureEmbedding
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature

abbrev nativeNames := Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature.names
abbrev nativeRules := Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature.rules

def metas : List (MetaArity patSig) := [([PatSrt.pat], PatSrt.pat)]
def metaIndex : Fin metas.length := ⟨0, by decide⟩

def sourceBody : Term patSig [PatSrt.pat, PatSrt.pat] PatSrt.pat :=
  .op (.lamOp (some "q")) (.cons
    (.op (.applyOp "pair" 2) (.cons (.var (.succ .zero))
      (.cons (.var (.succ (.succ .zero))) .nil))) .nil)

def body : ContextualAssignment patSig metas [PatSrt.pat] :=
  EqualityCertificates.Bodies.read (.cons sourceBody .nil)

def arguments : Sub patSig [PatSrt.pat] [PatSrt.pat, PatSrt.pat] :=
  fun _ position => match position with | .zero => .var (.succ .zero)

def ambient : Sub patSig [PatSrt.pat] [PatSrt.pat, PatSrt.pat] :=
  fun _ position => match position with | .zero => .var .zero

def result : Term patSig [PatSrt.pat, PatSrt.pat] PatSrt.pat :=
  .op (.lamOp (some "q")) (.cons
    (.op (.applyOp "pair" 2) (.cons (.var (.succ (.succ .zero)))
      (.cons (.var (.succ .zero)) .nil))) .nil)

def captured : Term patSig [PatSrt.pat, PatSrt.pat] PatSrt.pat :=
  .op (.lamOp (some "q")) (.cons
    (.op (.applyOp "pair" 2) (.cons (.var .zero)
      (.cons (.var (.succ .zero)) .nil))) .nil)

def sourceAction := ContextualAssignment.joinSub arguments ambient

def program := contextualApplication (Head := Tower.Head) nativeNames body metaIndex arguments ambient

def certificate := FormationCheckedTelescopePrograms.applicationCode
  (context (Head := Tower.Head) nativeNames [PatSrt.pat, PatSrt.pat])
  (encodeSub nativeNames sourceAction) (encode nativeNames sourceBody)

def nativeResult := encode (Head := Tower.Head) nativeNames result

def requested (candidate : Tm Tower.Head 2) : Bool :=
  certificate.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot program candidate

theorem original_substitution : ContextualAssignment.apply body metaIndex arguments ambient = result := by
  decide +kernel

theorem application_retains_authority :
    FormationSensitive.Judgment (nativeRules [.lamOp (some "q"), .applyOp "pair" 2])
      (context nativeNames [PatSrt.pat, PatSrt.pat]) program (sortType nativeNames PatSrt.pat) := by
  apply ((sortRealization [.lamOp (some "q"), .applyOp "pair" 2]).contextualApplication_judgments
    body metaIndex arguments ambient ?_ ?_).1
  · change Installed nativeNames _ sourceBody
    exact .op _ _ (operator_type_lookup [.lamOp (some "q"), .applyOp "pair" 2]
      (operator := .lamOp (some "q")) (by decide))
      (.cons (.op _ _ (operator_type_lookup [.lamOp (some "q"), .applyOp "pair" 2]
        (operator := .applyOp "pair" 2) (by decide))
        (.cons (.var _) (.cons (.var _) .nil))) .nil)
  · intro sort position
    cases position with
    | zero => exact .var _
    | succ position => cases position with
      | zero => exact .var _
      | succ impossible => cases impossible


def ambientMetas : List (MetaArity patSig) := [([], PatSrt.pat)]
def ambientIndex : Fin ambientMetas.length := ⟨0, by decide⟩

def ambientBody : ContextualAssignment patSig ambientMetas [PatSrt.pat] :=
  EqualityCertificates.Bodies.read (.cons (.var .zero) .nil)
def noArguments : Sub patSig [] [PatSrt.pat, PatSrt.pat] := fun _ position => nomatch position

def ambientProgram := contextualApplication (Head := Tower.Head) nativeNames
  ambientBody ambientIndex noArguments ambient

def ambientCertificate := FormationCheckedTelescopePrograms.applicationCode
  (context (Head := Tower.Head) nativeNames [PatSrt.pat])
  (encodeSub nativeNames (ContextualAssignment.joinSub noArguments ambient))
  (encode nativeNames (ambientBody ambientIndex))

#guard requested nativeResult
#guard !(requested (encode nativeNames captured))
#guard !(requested (.var 0))
#guard !(requested (.var 1))
#guard !(requested (.const `Forged))
#guard certificate.stepCount == 2
#guard program != nativeResult
#guard ambientCertificate.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
  ambientProgram (.var 0)
#guard !(ambientCertificate.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
  ambientProgram (.var 1))
#guard ambientCertificate.stepCount == 1
#guard ambientProgram != (.var 0)
#guard sourceBody != result

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.ContextualPrograms

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.DerivedBinding

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open BindingSignatureEmbedding ClosedOperators
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
open StructuralConversionCode

private def noRoot : {n : Nat} → Empty → Option (Tm Nat n × Tm Nat n) :=
  fun code => nomatch code

private def body : Tm Nat 2 := .lam (.var 1)
private def argument : Tm Nat 1 := .var 0
private def program : Tm Nat 1 :=
  .app (.app (liftClosed Derived.identity) (.lam body)) argument
private def evidence : Code Nat (fun _ => Empty) 1 := Derived.substitutionCode body argument
private def correct : Tm Nat 1 := .lam (.var 1)
private def captured : Tm Nat 1 := .lam (.var 0)

/-- The inner binder remains bound and the ambient variable shifts beneath it. -/
theorem capture_avoided : evidence.check (fun _ _ => False) noRoot program correct = true := by
  decide +kernel

theorem capture_refused : evidence.check (fun _ _ => False) noRoot program captured = false := by
  decide +kernel

private def nested : Tm Nat 2 := .lam (.lam (.var 2))
private def nestedProgram : Tm Nat 1 :=
  .app (.app (liftClosed Derived.identity) (.lam nested)) argument
private def nestedEvidence : Code Nat (fun _ => Empty) 1 := Derived.substitutionCode nested argument

/-- Altering the second selected body breaks the literal intermediate term. -/
private def damaged : Code Nat (fun _ => Empty) 1 :=
  .trans (.single (.congAppFun (.betaPi (.var 0) (.lam body)) argument))
    (.single (.betaPi (.var 0) argument))

open Mettapedia.OSLF.Binding
open ContextualPrograms

private def sourceImages : Images PatternPresentation.patSig Tower.Head := namedImages (Head := Tower.Head) nativeNames
private def sourceArgument : Term PatternPresentation.patSig [PatternPresentation.PatSrt.pat]
    PatternPresentation.PatSrt.pat := .var .zero
private def sourceInstance := Mettapedia.OSLF.Binding.inst sourceBody sourceArgument
private def sourceProgram := Tm.app (Tm.app (liftClosed (Derived.identity (Head := Tower.Head)))
  (.lam (compile sourceImages sourceBody))) (compile sourceImages sourceArgument)
private def sourceEvidence := Derived.substitutionCode (RootCode := fun _ => Empty)
  (compile sourceImages sourceBody) (compile sourceImages sourceArgument)
private def sourceResult := compile sourceImages sourceInstance

/-- Formation comes from the original finite declaration package. The derived
program is not installed as another opaque constructor. -/
theorem identity_has_function_type :
    FormationSensitive.Typing (nativeRules []) .nil (Derived.identity (Head := Tower.Head))
      (closedArrow
        (closedArrow (sortType nativeNames PatternPresentation.PatSrt.pat)
          (sortType nativeNames PatternPresentation.PatSrt.pat))
        (closedArrow (sortType nativeNames PatternPresentation.PatSrt.pat)
          (sortType nativeNames PatternPresentation.PatSrt.pat))) := by
  let formation := Formation.ofNamed (sortRealization [])
  exact Derived.identity_typing formation
    (formation.closedArrow_formed (formation.typeFormed _) (formation.typeFormed _))

#guard evidence.check (fun _ _ => False) noRoot program correct
#guard !(evidence.check (fun _ _ => False) noRoot program captured)
#guard !(evidence.check (fun _ _ => False) noRoot program (.var 0))
#guard !(evidence.check (fun _ _ => False) noRoot correct program)
#guard evidence.stepCount == 2
#guard (Derived.introductionCode (RootCode := fun _ => Empty) body).stepCount == 1
#guard (Derived.introductionCode body).check (fun _ _ => False) noRoot
  (.app (liftClosed Derived.identity) (.lam body)) (.lam body)
#guard !((Derived.introductionCode body).check (fun _ _ => False) noRoot
  (.app (liftClosed Derived.identity) (.lam body)) (.lam (.var 0)))
#guard nestedEvidence.check (fun _ _ => False) noRoot nestedProgram (.lam (.lam (.var 2)))
#guard !(nestedEvidence.check (fun _ _ => False) noRoot nestedProgram (.lam (.lam (.var 1))))
#guard !(nestedEvidence.check (fun _ _ => False) noRoot nestedProgram (.lam (.lam (.var 0))))
#guard (damaged.decode (fun _ _ => False) noRoot).isNone
#guard !(damaged.check (fun _ _ => False) noRoot program correct)
#guard sourceEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
  sourceProgram sourceResult
#guard !(sourceEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
  sourceProgram (.var 0))
#guard sourceEvidence.stepCount == 2
#guard compile sourceImages sourceBody == encode (Head := Tower.Head) nativeNames sourceBody
#guard program != correct

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.DerivedBinding

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.ConstantInterpretation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open ConstantExpansion StructuralConversionCode

private def noRoot : {n : Nat} → Empty → Option (Tm Nat n × Tm Nat n) := fun code => nomatch code
private def bodies : Bodies Nat := fun name =>
  if name = `Left ∨ name = `Right then .lam (.var 0) else .const name
private def malformed : Code Nat (fun _ => Empty) 0 :=
  .trans (.refl (.const `Left)) (.refl (.const `Right))
private def original : Tm Nat 0 := .const `Left
private def merged : Tm Nat 0 := .lam (.var 0)

/-- Distinct original middle terms are not repaired by admission, even when
an interpretation deliberately identifies their constant bodies. -/
theorem original_join_refused : malformed.decode (fun _ _ => False) noRoot = none := by decide +kernel

theorem expansion_can_merge_rejected_join :
    (malformed.expandConstants bodies (fun code => code)).check
      (fun _ _ => False) noRoot merged merged = true := by decide +kernel

theorem admitted_expansion_retains_refusal :
    malformed.expandFor? bodies (fun code => code) (fun _ _ => False) noRoot original original = none := by
  decide +kernel

private def one : Code Nat (fun _ => Empty) 0 := .refl original
private def beta : Code Nat (fun _ => Empty) 1 :=
  .single (.betaPi (.lam (.var 1)) (.const `Left))
private def betaLeft : Tm Nat 1 := .app (.lam (.lam (.var 1))) (.const `Left)
private def betaRight : Tm Nat 1 := .lam (.const `Left)
private def betaBoth : Code Nat (fun _ => Empty) 1 := .trans beta (.symm beta)

#guard malformed.decode (fun _ _ => False) noRoot == none
#guard (malformed.expandConstants bodies (fun code => code)).check
  (fun _ _ => False) noRoot merged merged
#guard (malformed.expandFor? bodies (fun code => code) (fun _ _ => False) noRoot original original).isNone
#guard (one.expandFor? bodies (fun code => code) (fun _ _ => False) noRoot original original).isSome
#guard (one.expandFor? bodies (fun code => code) (fun _ _ => False) noRoot original (.const `Right)).isNone
#guard (one.expandConstants bodies (fun code => code)).check (fun _ _ => False) noRoot merged merged
#guard !(one.check (fun _ _ => False) noRoot original (.const `Right))
#guard beta.check (fun _ _ => False) noRoot betaLeft betaRight
#guard (beta.expandConstants bodies (fun code => code)).check (fun _ _ => False) noRoot
  (expand bodies betaLeft) (expand bodies betaRight)
#guard !((beta.expandConstants bodies (fun code => code)).check (fun _ _ => False) noRoot
  (expand bodies betaLeft) (.lam (.var 0)))
#guard betaBoth.check (fun _ _ => False) noRoot betaLeft betaLeft
#guard (betaBoth.expandConstants bodies (fun code => code)).check (fun _ _ => False) noRoot
  (expand bodies betaLeft) (expand bodies betaLeft)
#guard (betaBoth.expandConstants bodies (fun code => code)).stepCount == 2

private def sourceRoot : {n : Nat} → Unit → Option (Tm Nat n × Tm Nat n) :=
  fun _ => some (.const `Left, .const `Right)
private def targetRoot : {n : Nat} → Unit → Option (Tm Nat n × Tm Nat n) :=
  fun _ => some (liftClosed merged, liftClosed merged)
private def unrelatedRoot : {n : Nat} → Unit → Option (Tm Nat n × Tm Nat n) :=
  fun _ => some (.const `Other, .const `Other)
private def root : Code Nat (fun _ => Unit) 0 := .single (.root ())

theorem root_decoder_agrees {n : Nat} (code : Unit) :
    targetRoot (n := n) code = mapEndpoints (expand bodies) (sourceRoot code) := by
  rfl

theorem changed_root_decoder_checked :
    (root.expandConstants bodies (fun code => code)).check
      (fun _ _ => False) targetRoot merged merged = true :=
  Code.check_expandConstants bodies (fun code => code) (fun _ _ => False)
    sourceRoot targetRoot root_decoder_agrees (code := root)
    (left := original) (right := .const `Right) (by decide +kernel)

#guard root.check (fun _ _ => False) sourceRoot original (.const `Right)
#guard !(root.check (fun _ _ => False) targetRoot original (.const `Right))
#guard (root.expandConstants bodies (fun code => code)).check (fun _ _ => False) targetRoot merged merged
#guard !((root.expandConstants bodies (fun code => code)).check
  (fun _ _ => False) unrelatedRoot merged merged)
#guard (root.expandFor? bodies (fun code => code) (fun _ _ => False) sourceRoot
  original (.const `Right)).isSome

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.ConstantInterpretation

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.DerivedSchemaPrograms

open Mettapedia.OSLF.Binding
open PatternPresentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open BindingSignatureEmbedding ClosedOperators
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
open ContextualPrograms

private def bodies : ConstantExpansion.Bodies Tower.Head := fun name =>
  if name = operatorName (.lamOp (some "q")) then Derived.identity else .const name
private def images : Images patSig Tower.Head := fun operator => bodies (nativeNames.operator operator)
private def valuation : Sub patSig [PatSrt.pat, PatSrt.pat] [PatSrt.pat, PatSrt.pat] :=
  fun _ position => .var position
private def schema : Term (withMetas patSig metas) [PatSrt.pat, PatSrt.pat] PatSrt.pat :=
  .op (.inr (.mk metaIndex)) (.cons (.var (.succ .zero)) .nil)
private def emitted := Schema.program bodies nativeNames body ambient valuation schema
private def evidence := Schema.evidence bodies nativeNames body ambient valuation schema
private def result := compile images ContextualPrograms.result
private def captured := compile images ContextualPrograms.captured

/-- The retained source fixture has both a dependency and a distinct ambient
value; its inner binder is preserved by the original instantiator. -/
theorem source_instance : ContextualAssignment.instantiate body ambient valuation schema =
    ContextualPrograms.result := by decide +kernel

theorem emitted_checked : evidence.check (fun _ _ => False)
    FormationCheckedTelescopePrograms.noRoot emitted result = true := by
  have actual := Schema.evidence_checked bodies nativeNames images (fun _ => rfl)
    body ambient valuation schema
  simpa only [evidence, emitted, result, source_instance] using actual

private def nested : Term (withMetas patSig metas) [PatSrt.pat, PatSrt.pat] PatSrt.pat :=
  .op (.inl (.lamOp (some "q"))) (.cons
    (.op (.inr (.mk metaIndex)) (.cons (.var (.succ (.succ .zero))) .nil)) .nil)
private def nestedProgram := Schema.program bodies nativeNames body ambient valuation nested
private def nestedEvidence := Schema.evidence bodies nativeNames body ambient valuation nested
private def nestedResult := compile images (ContextualAssignment.instantiate body ambient valuation nested)
private def action : Sub patSig [PatSrt.pat, PatSrt.pat] [PatSrt.pat] :=
  fun _ position => match position with
    | .zero => .var .zero
    | .succ .zero => .op (.fvarOp "external") .nil
private def shiftedEnvironment := fun sort position => bind action (ambient sort position)
private def shiftedValuation := fun sort position => bind action (valuation sort position)
private def reindexed := Schema.reindexedEvidence bodies nativeNames body ambient valuation nested action
private def shiftedProgram := subst (compileSub images action) nestedProgram
private def shiftedResult := compile images
  (ContextualAssignment.instantiate body shiftedEnvironment shiftedValuation nested)

#guard evidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot emitted result
#guard !(evidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot emitted captured)
#guard !(evidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot emitted (.var 0))
#guard !(evidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot result emitted)
#guard evidence.stepCount == 2
#guard emitted != result
#guard nestedEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
  nestedProgram nestedResult
#guard !(nestedEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
  nestedProgram (.var 0))
#guard reindexed.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
  shiftedProgram shiftedResult
#guard !(reindexed.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
  shiftedProgram (.var 0))
#guard (Schema.evidence bodies nativeNames body shiftedEnvironment shiftedValuation nested).check
  (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
  (Schema.program bodies nativeNames body shiftedEnvironment shiftedValuation nested) shiftedResult
#guard reindexed.stepCount == nestedEvidence.stepCount

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.DerivedSchemaPrograms

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.UniformParameters

open Mettapedia.OSLF.Binding.PatternPresentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.ClosedOperators
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
open ConstantSubstitution TelescopeAbstraction FormationCheckedTelescopePrograms Declaration

private def sourceOperator : PatOp .pat := .applyOp "K" 2
private def sourceRules := rules [sourceOperator]
private def targetRules := rules []
private def carrier : Tm Tower.Head 0 := sortType names PatSrt.pat
private def functionType : Tm Tower.Head 0 := closedArrow carrier (closedArrow carrier carrier)
private def sourceContext : Ctx Tower.Head 2 :=
  typeContext (namedTypes (Head := Tower.Head) names) [PatSrt.pat, PatSrt.pat]
private def parameters : Ctx Tower.Head 1 := .snoc .nil functionType
private def positions (name : DeclName) : Option (Fin 1) :=
  if name = operatorName sourceOperator then some 0 else none
private def sourceBody : Tm Tower.Head 2 := .app (.app (.const (operatorName sourceOperator)) (.var 1)) (.var 0)
private def sourceProgram : Tm Tower.Head 0 := .lam (.lam sourceBody)

private theorem source_program_typed :
    FormationSensitive.Typing sourceRules .nil sourceProgram functionType := by
  let formed := Formation.ofNamed (sortRealization [sourceOperator])
  have constructor : FormationSensitive.Typing sourceRules sourceContext
      (.const (operatorName sourceOperator)) (liftClosed functionType) :=
    .const (operator_type_lookup [sourceOperator] (operator := sourceOperator) (List.mem_singleton_self _))
      ((sortRealization [sourceOperator]).operatorType_formed sourceOperator)
      (sortRealization [sourceOperator]).universeIs
  have first : FormationSensitive.Typing sourceRules sourceContext (.var 1) (liftClosed carrier) := by
    change FormationSensitive.Typing sourceRules sourceContext (.var 1) (Ctx.lookup sourceContext 1)
    exact .var 1
  have second : FormationSensitive.Typing sourceRules sourceContext (.var 0) (liftClosed carrier) := by
    change FormationSensitive.Typing sourceRules sourceContext (.var 0) (Ctx.lookup sourceContext 0)
    exact .var 0
  have functionEquation : functionType = closedArrow carrier (closedArrow carrier carrier) := rfl
  rw [functionEquation, liftClosed_closedArrow] at constructor
  have applied := FormationSensitive.Typing.appElim constructor first
  simp only [inst0, subst_liftClosed] at applied
  rw [liftClosed_closedArrow] at applied
  have appliedAgain := FormationSensitive.Typing.appElim applied second
  simp only [inst0, subst_liftClosed] at appliedAgain
  have closed := formed.closeTerm_typing (gamma := [PatSrt.pat, PatSrt.pat])
    (formed.typeFormed PatSrt.pat) sourceBody appliedAgain
  exact closed

private theorem source_roots_absent : RootFree sourceRules.computation := by
  intro scope first last step
  change Declaration.RootStep Tower.rules (signature [sourceOperator]) scope first last at step
  cases step with
  | inherited impossible => exact impossible
  | delta known => simp only [value_lookup, reduceCtorEq] at known
  | declared impossible =>
      simp only [signature, Signature.computation_ofList, RootComputation.empty] at impossible

private theorem ruleMap : RulesMap sourceRules targetRules where
  headTyping := fun known => known
  isUniverse := fun known => known
  join := fun known => known
  cumulative := fun known => known
  headEquality := fun known => known
  rootFree := source_roots_absent

private theorem actual_type_cases {name : DeclName} {type : Tm Tower.Head 0}
    (known : sourceRules.constantType name = some type) :
    (name = dataName ∧ type = .head (.sort Tower.zero)) ∨
      (name = operatorName sourceOperator ∧ type = functionType) := by
  change (signature [sourceOperator]).typeOf? name = some type at known
  unfold Signature.typeOf? at known
  cases selected : (signature [sourceOperator]).entries name with
  | none => simp [selected] at known
  | some entry =>
      have typeSame : entry.type = type := by
        simpa only [selected, Option.map_some, Option.some.injEq] using known
      have membership := Signature.entries_ofList_mem (declarationList [sourceOperator]) selected
      rcases List.mem_cons.mp membership with data | constructor
      · exact .inl ⟨congrArg Prod.fst data, typeSame.symm.trans (congrArg (fun entry => entry.type) (congrArg Prod.snd data))⟩
      · obtain ⟨operator, member, same⟩ := List.mem_map.mp constructor
        have operatorSame : operator = sourceOperator := by simpa only [List.mem_singleton] using member
        subst operator
        exact .inr ⟨(congrArg Prod.fst same).symm,
          typeSame.symm.trans (congrArg (fun entry => entry.type) (congrArg Prod.snd same).symm)⟩

/-- Actual finite declaration lookup supplies the generic primitive contract;
the resulting whole-program formation theorem needs no callback for a body. -/
theorem primitive_parameters_from_declarations :
    TypedValues sourceRules targetRules parameters (parameterValues positions) := by
  apply TypedValues.ofDeclarationParameters
  · intro name type known dependency member
    rcases actual_type_cases known with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [ConstantExpansion.constantNames, List.not_mem_nil] at member
    · change dependency ∈ [dataName, dataName, dataName] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      subst dependency
      decide +kernel
  · intro name type index known chosen
    rcases actual_type_cases known with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [positions] at chosen
      contradiction
    · have indexSame : index = 0 := Fin.eq_zero index
      subst index
      rfl
  · intro name type known chosen
    rcases actual_type_cases known with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨?_, .sort (.succ Tower.zero), ?_, .sort (.succ Tower.zero)⟩
      · change (signature []).typeOf? dataName = some (.head (.sort Tower.zero))
        rw [Signature.typeOf?, data_lookup]
        rfl
      · exact .headType (.sort Tower.zero)
    · simp [positions] at chosen

private theorem primitive_parameters_typed :
    TypedValues sourceRules targetRules parameters (parameterValues positions) :=
  primitive_parameters_from_declarations

private def program := parameterProgram parameters positions sourceProgram
private def firstProjection : Tm Tower.Head 0 := .lam (.lam (.var 1))
private def secondProjection : Tm Tower.Head 0 := .lam (.lam (.var 0))
private def firstArguments : Sub Tower.Head 1 0 := fun _ => firstProjection
private def secondArguments : Sub Tower.Head 1 0 := fun _ => secondProjection
private def evidenceFirst := applicationCode parameters firstArguments (parameterTerm positions sourceProgram)
private def evidenceSecond := applicationCode parameters secondArguments (parameterTerm positions sourceProgram)
private def applicationFirst := applyClosed parameters firstArguments (liftClosed program)
private def applicationSecond := applyClosed parameters secondArguments (liftClosed program)
private def resultFirst := interpret (specializedValues positions firstArguments) Fin.elim0 sourceProgram
private def resultSecond := interpret (specializedValues positions secondArguments) Fin.elim0 sourceProgram

private theorem function_formed :
    FormationSensitive.Typing targetRules .nil functionType (.head (.sort Tower.zero)) :=
  (sortRealization []).operatorType_formed sourceOperator
private theorem parameters_formed : FormationSensitive.ContextFormation targetRules parameters :=
  .snoc .nil function_formed (.sort Tower.zero)
private theorem target_universes : FormationSensitive.UniverseRegularity targetRules :=
  FormationSensitive.towerUniverseRegularity.includeSignature (signature [])
private theorem joins {first second : Tower.Head}
    (left : targetRules.isUniverse first) (right : targetRules.isUniverse second) :
    ∃ result, targetRules.isUniverse result ∧ targetRules.join first second result := by
  cases left with
  | sort first => cases right with
    | sort second => exact ⟨_, .sort (.max first second), .sorts first second⟩

/-- The single compiled program is formed with a genuine function parameter.
No polymorphic constant or supplied whole-program correctness field is used. -/
theorem uniform_program_formed : FormationSensitive.Typing targetRules .nil program
    (closeType parameters (parameterTerm positions functionType)) :=
  parameterProgram_typing ruleMap target_universes joins parameters_formed
    source_program_typed primitive_parameters_typed

private theorem projection_typed (chooseFirst : Bool) :
    FormationSensitive.Typing targetRules .nil
      (if chooseFirst then firstProjection else secondProjection) functionType := by
  let formed := Formation.ofNamed (sortRealization [])
  have selected : FormationSensitive.Typing targetRules sourceContext
      (if chooseFirst then (.var 1) else (.var 0)) (liftClosed carrier) := by
    cases chooseFirst
    · change FormationSensitive.Typing targetRules sourceContext (.var 0) (Ctx.lookup sourceContext 0)
      exact .var 0
    · change FormationSensitive.Typing targetRules sourceContext (.var 1) (Ctx.lookup sourceContext 1)
      exact .var 1
  have closed := formed.closeTerm_typing (gamma := [PatSrt.pat, PatSrt.pat])
    (formed.typeFormed PatSrt.pat) _ selected
  cases chooseFirst <;> exact closed

private theorem first_arguments_typed :
    FormationSensitive.CtxMor targetRules parameters .nil firstArguments := by
  intro index
  have selected : index = 0 := Fin.eq_zero index
  subst index
  change FormationSensitive.Typing targetRules .nil firstProjection functionType
  exact projection_typed true

theorem uniform_first_application_formed : FormationSensitive.Judgment targetRules .nil
    applicationFirst (interpret (specializedValues positions firstArguments) Fin.elim0 functionType) :=
  parameterApplication_judgment ruleMap target_universes joins parameters_formed
    source_program_typed primitive_parameters_typed .nil firstArguments first_arguments_typed

private def normalizeFirst : StructuralConversionCode.Code Tower.Head (fun _ => Empty) 0 :=
  .trans
    (.single (.congLam (.congLam (.congAppFun (.betaPi (.lam (.var 1)) (.var 1)) (.var 0)))))
    (.single (.congLam (.congLam (.betaPi (.var 2) (.var 0)))))
private def normalizeSecond : StructuralConversionCode.Code Tower.Head (fun _ => Empty) 0 :=
  .trans
    (.single (.congLam (.congLam (.congAppFun (.betaPi (.lam (.var 0)) (.var 1)) (.var 0)))))
    (.single (.congLam (.congLam (.betaPi (.var 0) (.var 0)))))

#guard normalizeFirst.check (fun _ _ => False) noRoot resultFirst firstProjection
#guard normalizeSecond.check (fun _ _ => False) noRoot resultSecond secondProjection
#guard !(normalizeFirst.check (fun _ _ => False) noRoot resultFirst secondProjection)
#guard !(normalizeSecond.check (fun _ _ => False) noRoot resultSecond firstProjection)
#guard normalizeFirst.stepCount == 2
#guard normalizeSecond.stepCount == 2

#guard evidenceFirst.check (fun _ _ => False) noRoot applicationFirst resultFirst
#guard evidenceSecond.check (fun _ _ => False) noRoot applicationSecond resultSecond
#guard !(evidenceFirst.check (fun _ _ => False) noRoot applicationFirst resultSecond)
#guard !(evidenceSecond.check (fun _ _ => False) noRoot applicationSecond resultFirst)
#guard evidenceFirst.stepCount == 1
#guard evidenceSecond.stepCount == 1
#guard resultFirst != resultSecond
#guard firstProjection != secondProjection
#guard (targetRules.constantType (operatorName sourceOperator)).isNone
#guard parameterTerm positions (.const (operatorName sourceOperator) : Tm Tower.Head 0) == (.var 0)
#guard parameterTerm positions (.lam (.const (operatorName sourceOperator)) : Tm Tower.Head 0) == (.lam (.var 1))
#guard parameterTerm positions (.lam (.var 0) : Tm Tower.Head 0) == (.lam (.var 0))
#guard parameterTerm positions (.const dataName : Tm Tower.Head 0) == (.const dataName)

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.UniformParameters

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.UniformParameters

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
open ConstantSubstitution

#guard parameterTerm positions (.pi (.const dataName) (.const dataName) : Tm Tower.Head 0) ==
  (.pi (.const dataName) (.const dataName))
#guard parameterTerm positions (.const (operatorName sourceOperator) : Tm Tower.Head 0) !=
  (liftClosed (.const (operatorName sourceOperator) : Tm Tower.Head 0) : Tm Tower.Head 1)
#guard parameterTerm positions (.lam (.const (operatorName sourceOperator)) : Tm Tower.Head 0) ==
  (.lam (.var 1))

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.UniformParameters

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.OpenParameterEvidence

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open ConstantSubstitution StructuralConversionCode FormationCheckedTelescopePrograms

private def values : Values Nat 2 := fun name => if name = `K then .var 1 else .const name
private def sourceVariables : Sub Nat 1 2 := fun _ => .var 0
private def source : Code Nat (fun _ => Empty) 1 :=
  .single (.betaPi (.app (.const `K) (.var 0)) (.var 0))
private def sourceFirst : Tm Nat 1 := .app (.lam (.app (.const `K) (.var 0))) (.var 0)
private def sourceLast : Tm Nat 1 := .app (.const `K) (.var 0)
private def targetFirst : Tm Nat 2 := .app (.lam (.app (.var 2) (.var 0))) (.var 0)
private def targetLast : Tm Nat 2 := .app (.var 1) (.var 0)

#guard source.check (fun _ _ => False) noRoot sourceFirst sourceLast
#guard interpret values sourceVariables sourceFirst == targetFirst
#guard interpret values sourceVariables sourceLast == targetLast
#guard (source.interpretParameters values sourceVariables).check (fun _ _ => False) noRoot targetFirst targetLast
#guard !((source.interpretParameters values sourceVariables).check
  (fun _ _ => False) noRoot targetFirst (.app (.var 0) (.var 0)))
#guard (source.interpretParameters values sourceVariables).stepCount == source.stepCount
#guard (source.interpretFor? (fun _ _ => False) sourceFirst sourceLast values sourceVariables).isSome
#guard (source.interpretFor? (fun _ _ => False) sourceFirst sourceFirst values sourceVariables).isNone

private def malformed : Code Nat (fun _ => Empty) 0 :=
  .trans (.refl (.const `First)) (.refl (.const `Second))
private def merge : Values Nat 1 := fun _ => .var 0
#guard (malformed.decode (fun _ _ => False) noRoot).isNone
#guard (malformed.interpretParameters merge Fin.elim0).check (fun _ _ => False) noRoot (.var 0) (.var 0)
#guard (malformed.interpretFor? (fun _ _ => False) (.const `First) (.const `Second) merge Fin.elim0).isNone

private def closed : Code Nat (fun _ => Empty) 0 :=
  .single (.betaPi (.app (.const `K) (.var 0)) (.const `A))
private def closedFirst : Tm Nat 0 := .app (.lam (.app (.const `K) (.var 0))) (.const `A)
private def closedLast : Tm Nat 0 := .app (.const `K) (.const `A)
private def positions (name : DeclName) : Option (Fin 1) := if name = `K then some 0 else none
private def firstValues : Sub Nat 1 0 := fun _ => .lam (.var 0)
private def lastValues : Sub Nat 1 0 := fun _ => .lam (.const `B)
private def firstProgram : Tm Nat 0 := .app (.lam (.app (.lam (.var 0)) (.var 0))) (.const `A)
private def firstResult : Tm Nat 0 := .app (.lam (.var 0)) (.const `A)
private def lastProgram : Tm Nat 0 := .app (.lam (.app (.lam (.const `B)) (.var 0))) (.const `A)
private def lastResult : Tm Nat 0 := .app (.lam (.const `B)) (.const `A)

theorem first_specialization_checked :
    (closed.specializeParameters positions firstValues).check (fun _ _ => False) noRoot
      firstProgram firstResult = true :=
  Code.specializeParameters_checked (fun _ _ => False)
    (code := closed) (first := closedFirst) (last := closedLast) (by decide +kernel) positions firstValues

#guard closed.check (fun _ _ => False) noRoot closedFirst closedLast
#guard (closed.specializeParameters positions firstValues).check (fun _ _ => False) noRoot firstProgram firstResult
#guard (closed.specializeParameters positions lastValues).check (fun _ _ => False) noRoot lastProgram lastResult
#guard !((closed.specializeParameters positions firstValues).check (fun _ _ => False) noRoot firstProgram lastResult)
#guard !((closed.specializeParameters positions lastValues).check (fun _ _ => False) noRoot lastProgram firstResult)
#guard (closed.specializeParameters positions firstValues).stepCount == closed.stepCount
#guard (closed.specializeParameters positions lastValues).stepCount == closed.stepCount

open TelescopeAbstraction

private def context : Ctx Nat 1 := .snoc .nil (.pi (.head 0) (.head 0))
private def firstApplication : Tm Nat 0 :=
  applyClosed context firstValues (liftClosed (closeTerm context (parameterTerm positions closedFirst)))
private def lastApplication : Tm Nat 0 :=
  applyClosed context lastValues (liftClosed (closeTerm context (parameterTerm positions closedFirst)))

theorem first_application_checked :
    (closed.applyParameters context positions firstValues closedFirst).check (fun _ _ => False) noRoot
      firstApplication firstResult = true :=
  Code.applyParameters_checked (code := closed) (first := closedFirst) (last := closedLast)
    (by decide +kernel) context positions firstValues

#guard (closed.applyParameters context positions firstValues closedFirst).check
  (fun _ _ => False) noRoot firstApplication firstResult
#guard (closed.applyParameters context positions lastValues closedFirst).check
  (fun _ _ => False) noRoot lastApplication lastResult
#guard !((closed.applyParameters context positions firstValues closedFirst).check
  (fun _ _ => False) noRoot firstApplication lastResult)
#guard !((closed.applyParameters context positions lastValues closedFirst).check
  (fun _ _ => False) noRoot lastApplication firstResult)
#guard (closed.applyParameters context positions firstValues closedFirst).stepCount == 1 + closed.stepCount
#guard (closed.applyParameters context positions lastValues closedFirst).stepCount == 2
#guard (closed.applyParametersFor? context positions firstValues closedFirst closedLast).isSome
#guard (closed.applyParametersFor? context positions firstValues closedFirst closedFirst).isNone
#guard (malformed.applyParametersFor? context positions firstValues (.const `First) (.const `Second)).isNone

private def closedContext : Ctx Nat 0 := .nil
private def noPositions : DeclName → Option (Fin 0) := fun _ => none

#guard (closed.applyParameters closedContext noPositions Fin.elim0 closedFirst).check
  (fun _ _ => False) noRoot closedFirst closedLast
#guard (closed.applyParameters (m := 0) closedContext noPositions Fin.elim0 closedFirst).stepCount == closed.stepCount

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.OpenParameterEvidence

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.CurriedAdapters

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation BindingSignatureEmbedding FormationCheckedTelescopePrograms TelescopeAbstraction

def input : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))
    (.head (.sort Tower.zero))
def output : Tower.Ctx 3 := input

def adapters (count : Nat) : Fin 3 → Tower.Tm 0 :=
  Fin.cases (.lam (.const (.num `adapterLeft count)))
    (Fin.cases ClosedOperators.Derived.identity
      (Fin.cases (.lam (.const (.num `adapterRight (count+1)))) Fin.elim0))

def values : Sub Tower.Head 3 2 :=
  Fin.cases (.var 0) (Fin.cases (.var 1) (Fin.cases (.lam (.var 2)) Fin.elim0))

def constructor : Tower.Tm 0 := .const `Authored.constructor

def source (count : Nat) : Tower.Tm 2 :=
  applyClosed input values (liftClosed (adaptClosed input output (adapters count) constructor))

def target (count : Nat) : Tower.Tm 2 :=
  .app (.app (.app (liftClosed constructor)
    (.app (liftClosed (adapters count 2)) (values 2)))
    (.app (liftClosed (adapters count 1)) (values 1)))
    (.app (liftClosed (adapters count 0)) (values 0))

def checked (count : Nat) : Bool :=
  (adaptClosedCode input output (adapters count) constructor values).check
    (fun _ _ => False) noRoot (source count) (target count)

def wrongOrder (count : Nat) : Bool :=
  (adaptClosedCode input output (adapters count) constructor values).check
    (fun _ _ => False) noRoot (source count)
    (.app (.app (.app (liftClosed constructor)
      (.app (liftClosed (adapters count 0)) (values 0)))
      (.app (liftClosed (adapters count 1)) (values 1)))
      (.app (liftClosed (adapters count 2)) (values 2)))

def captured (count : Nat) : Bool :=
  (adaptClosedCode input output (adapters count) constructor values).check
    (fun _ _ => False) noRoot (source count)
    (.app (.app (.app (liftClosed constructor)
      (.app (liftClosed (adapters count 2)) (.lam (.var 1))))
      (.app (liftClosed (adapters count 1)) (values 1)))
      (.app (liftClosed (adapters count 0)) (values 0)))

#guard checked 0
#guard !wrongOrder 0
#guard !captured 0
#guard checked 1
#guard !wrongOrder 1
#guard !captured 1
#guard checked 2
#guard !wrongOrder 2
#guard !captured 2
#guard checked 3
#guard !wrongOrder 3
#guard !captured 3
#guard checked 4
#guard !wrongOrder 4
#guard !captured 4
#guard checked 5
#guard !wrongOrder 5
#guard !captured 5
#guard checked 6
#guard !wrongOrder 6
#guard !captured 6
#guard checked 7
#guard !wrongOrder 7
#guard !captured 7
#guard checked 8
#guard !wrongOrder 8
#guard !captured 8
#guard checked 9
#guard !wrongOrder 9
#guard !captured 9
#guard checked 10
#guard !wrongOrder 10
#guard !captured 10
#guard checked 11
#guard !wrongOrder 11
#guard !captured 11

#guard (adaptClosedCode input output (adapters 5) constructor values).stepCount = 3

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.CurriedAdapters

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.NativeBodyPrograms

open Mettapedia.OSLF.Binding PatternPresentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open BindingSignatureEmbedding ClosedOperators StructuralConversionCode
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
open ContextualPrograms

private def firstPrograms : Fin metas.length → Tm Tower.Head 0 := fun _ => .lam (.lam (.var 1))
private def lastPrograms : Fin metas.length → Tm Tower.Head 0 := fun _ => .lam (.lam (.var 0))
private def primitive : ConstantExpansion.Bodies Tower.Head := fun name => .const name
private def first := Schema.programWithPrograms primitive nativeNames firstPrograms
  ambient DerivedSchemaPrograms.valuation DerivedSchemaPrograms.schema
private def last := Schema.programWithPrograms primitive nativeNames lastPrograms
  ambient DerivedSchemaPrograms.valuation DerivedSchemaPrograms.schema
private def firstCode : Code Tower.Head (fun _ => Empty) 2 :=
  .trans (.single (.congAppFun (.betaPi (.lam (.var 1)) (.var 0)) (.var 1)))
    (.single (.betaPi (.var 1) (.var 1)))
private def lastCode : Code Tower.Head (fun _ => Empty) 2 :=
  .trans (.single (.congAppFun (.betaPi (.lam (.var 0)) (.var 0)) (.var 1)))
    (.single (.betaPi (.var 0) (.var 1)))

theorem first_function_formed :
    FormationSensitive.Typing (nativeRules []) .nil (firstPrograms metaIndex) UniformParameters.functionType :=
  UniformParameters.projection_typed true

theorem last_function_formed :
    FormationSensitive.Typing (nativeRules []) .nil (lastPrograms metaIndex) UniformParameters.functionType :=
  UniformParameters.projection_typed false

#guard first == .app (.app (liftClosed (firstPrograms metaIndex)) (.var 0)) (.var 1)
#guard last == .app (.app (liftClosed (lastPrograms metaIndex)) (.var 0)) (.var 1)
#guard first != last
#guard firstCode.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot first (.var 0)
#guard lastCode.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot last (.var 1)
#guard !(firstCode.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot first (.var 1))
#guard !(lastCode.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot last (.var 0))
#guard firstCode.stepCount == 2
#guard lastCode.stepCount == 2

private def firstNested := Schema.programWithPrograms DerivedSchemaPrograms.bodies nativeNames firstPrograms
  ambient DerivedSchemaPrograms.valuation DerivedSchemaPrograms.nested
private def lastNested := Schema.programWithPrograms DerivedSchemaPrograms.bodies nativeNames lastPrograms
  ambient DerivedSchemaPrograms.valuation DerivedSchemaPrograms.nested

#guard firstNested == .app (liftClosed Derived.identity)
  (.lam (.app (.app (liftClosed (firstPrograms metaIndex)) (.var 1)) (.var 2)))
#guard lastNested == .app (liftClosed Derived.identity)
  (.lam (.app (.app (liftClosed (lastPrograms metaIndex)) (.var 1)) (.var 2)))
#guard firstNested != lastNested

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.NativeBodyPrograms


namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.UniformAmbient

open Mettapedia.OSLF.Binding PatternPresentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open BindingSignatureEmbedding ConstantSubstitution StructuralConversionCode
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
open ContextualPrograms

private def metaNames : Fin metas.length → DeclName := fun _ => .num .anonymous 0
private def positions (name : DeclName) : Option (Fin metas.length) :=
  if name = .num .anonymous 0 then some metaIndex else none
private def templates : Fin metas.length → Tm Tower.Head 0 := fun index => .const (metaNames index)
private def identity : Sub patSig [PatSrt.pat, PatSrt.pat] [PatSrt.pat, PatSrt.pat] :=
  fun _ position => .var position
private def schema : Term (withMetas patSig metas) [PatSrt.pat, PatSrt.pat] PatSrt.pat :=
  .op (.inr (.mk metaIndex)) (.cons (.var (.succ .zero)) .nil)
private def nested : Term (withMetas patSig metas) [PatSrt.pat, PatSrt.pat] PatSrt.pat :=
  .op (.inl (.lamOp (some "q"))) (.cons
    (.op (.inr (.mk metaIndex)) (.cons (.var (.succ (.succ .zero))) .nil)) .nil)

private theorem operators_not_selected {sort : patSig.Srt} (operator : patSig.Op sort) :
    positions (nativeNames.operator operator) = none := by
  cases sort
  cases operator with
  | fvarOp => rfl
  | applyOp => rfl
  | lamOp name => cases name <;> rfl
  | multiLamOp => rfl
  | substOp => rfl
  | collOp kind => cases kind <;> rfl

private def actualValues : Values Tower.Head 2 := specializedValues positions
  (Schema.ambientFunctions nativeNames (Schema.bodyPrograms nativeNames body) ambient)
private def template := Schema.fixedTemplate nativeNames templates schema
private def nestedTemplate := Schema.fixedTemplate nativeNames templates nested
private def emitted := interpret actualValues (encodeSub nativeNames identity) template
private def original : Tm Tower.Head 2 := Schema.compile nativeNames body ambient identity schema
private def nestedEmitted := interpret actualValues (encodeSub nativeNames identity) nestedTemplate
private def nestedOriginal : Tm Tower.Head 2 := Schema.compile nativeNames body ambient identity nested

theorem original_compiler_agrees : emitted = original := by
  exact Schema.fixedTemplate_specialize nativeNames metaNames positions operators_not_selected
    (fun index => by fin_cases index; rfl) body ambient identity schema

theorem nested_original_compiler_agrees : nestedEmitted = nestedOriginal := by
  exact Schema.fixedTemplate_specialize nativeNames metaNames positions operators_not_selected
    (fun index => by fin_cases index; rfl) body ambient identity nested

private def action : Sub patSig [PatSrt.pat, PatSrt.pat] [PatSrt.pat] :=
  fun _ position => match position with
    | .zero => .var .zero
    | .succ .zero => .op (.fvarOp "external") .nil
private def nextEnvironment := fun sort position => bind action (ambient sort position)
private def nextValues : Values Tower.Head 1 := specializedValues positions
  (Schema.ambientFunctions nativeNames (Schema.bodyPrograms nativeNames body) nextEnvironment)
private def next := interpret nextValues (encodeSub nativeNames action) template
private def nextNested := interpret nextValues (encodeSub nativeNames action) nestedTemplate

theorem changed_caller_agrees : next = Schema.compile nativeNames body nextEnvironment action schema :=
  Schema.fixedTemplate_specialize nativeNames metaNames positions operators_not_selected
    (fun index => by fin_cases index; rfl) body nextEnvironment action schema

private def emptyBody : ContextualAssignment patSig metas [] :=
  EqualityCertificates.Bodies.read (.cons (.var .zero) .nil)
private def emptyValues : Values Tower.Head 2 := specializedValues positions
  (Schema.ambientFunctions nativeNames (Schema.bodyPrograms nativeNames emptyBody) (Schema.emptyEnvironment (target := [PatSrt.pat, PatSrt.pat])))
private def emptyEmitted := interpret emptyValues (encodeSub nativeNames identity) template
private def originalEvidence : Code Tower.Head (fun _ => Empty) 2 := Schema.compileEvidence nativeNames body ambient identity schema
private def nextEvidence : Code Tower.Head (fun _ => Empty) 1 := Schema.compileEvidence nativeNames body nextEnvironment action schema
private def nestedEvidence : Code Tower.Head (fun _ => Empty) 2 := Schema.compileEvidence nativeNames body ambient identity nested

theorem original_evidence_checks : originalEvidence.check (fun _ _ => False)
    FormationCheckedTelescopePrograms.noRoot emitted nativeResult = true := by
  have checked := Schema.fixedTemplate_evidence_checked (Head := Tower.Head) nativeNames metaNames positions
    operators_not_selected (fun index => by fin_cases index; rfl) body ambient identity schema
  have actualInstance : ContextualAssignment.instantiate body ambient identity schema = ContextualPrograms.result := by
    decide +kernel
  dsimp only [originalEvidence, emitted, actualValues, template, templates, ContextualPrograms.nativeResult]
  unfold templates
  simpa only [actualInstance] using checked

theorem scope_and_order_controls :
    (template == .app (.const (metaNames metaIndex)) (.var 1)) = true ∧
    (nestedTemplate == .app (.const (operatorName (.lamOp (some "q"))))
      (.lam (.app (.const (metaNames metaIndex)) (.var 2)))) = true ∧
    (emitted == original) = true ∧
    (nestedEmitted == nestedOriginal) = true ∧
    originalEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot emitted nativeResult = true ∧
    originalEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot emitted
      (encode nativeNames captured) = false ∧
    (emptyEmitted == .app (.lam (.var 0)) (.var 1)) = true ∧
    (emitted != .app (.app (liftClosed (Schema.bodyPrograms nativeNames body metaIndex)) (.var 1)) (.var 0)) = true := by
  decide +kernel

#guard template == .app (.const (metaNames metaIndex)) (.var 1)
#guard nestedTemplate == .app (.const (operatorName (.lamOp (some "q"))))
  (.lam (.app (.const (metaNames metaIndex)) (.var 2)))
#guard emitted == original
#guard nestedEmitted == nestedOriginal
#guard originalEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot emitted nativeResult
#guard !(originalEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot emitted
  (encode nativeNames captured))
#guard next == Schema.compile nativeNames body nextEnvironment action schema
#guard nextNested == Schema.compile nativeNames body nextEnvironment action nested
#guard nextEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot next
  (encode nativeNames (ContextualAssignment.instantiate body nextEnvironment action schema))
#guard nestedEvidence.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot nestedEmitted
  (encode nativeNames (ContextualAssignment.instantiate body ambient identity nested))
#guard emptyEmitted == .app (.lam (.var 0)) (.var 1)
#guard template != emitted
#guard emitted != .app (.app (liftClosed (Schema.bodyPrograms nativeNames body metaIndex)) (.var 1)) (.var 0)
#guard nextNested != .app (.const (operatorName (.lamOp (some "q"))))
  (.lam (.app (.app (liftClosed (Schema.bodyPrograms nativeNames body metaIndex)) (.var 0))
    (.const (operatorName (.fvarOp "external")))))

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.UniformAmbient

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.LiteralImages

open Mettapedia.OSLF.Binding
open PatternPresentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open BindingSignatureEmbedding ConstantSubstitution Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature

private def leftAtom : Term patSig [] PatSrt.pat := .op (.applyOp "A" 0) .nil
private def rightAtom : Term patSig [] PatSrt.pat := .op (.applyOp "B" 0) .nil
private def nested : Term patSig [] PatSrt.pat :=
  .op (.multiLamOp 2 ["x", "y"]) (.cons (.var (.succ .zero)) .nil)
private def captured : Term patSig [] PatSrt.pat :=
  .op (.multiLamOp 2 ["x", "y"]) (.cons (.var .zero) .nil)
private def originalSubstitution : Term patSig [] PatSrt.pat :=
  .op .substOp (.cons (.var .zero) (.cons leftAtom .nil))
private def inventory : List (PatOp .pat) :=
  [.applyOp "A" 0, .applyOp "B" 0, .multiLamOp 2 ["x", "y"], .substOp]
private def originalRules := rules inventory

private theorem noRoot : RootFree originalRules.computation := by
  intro scope first last step
  change RootStep Tower.rules (signature inventory) scope first last at step
  cases step with
  | inherited impossible => exact impossible
  | delta known => simp only [value_lookup, reduceCtorEq] at known
  | declared impossible =>
      simp only [signature, Signature.computation_ofList, RootComputation.empty] at impossible

private theorem operatorsUnique : ∀ {sort : PatSrt},
    Function.Injective (names.operator (sort := sort)) := by
  intro sort first last same
  cases sort
  exact operatorName_injective same

private theorem sourceAtomsDifferent : leftAtom ≠ rightAtom := by
  intro same
  have encoded := congrArg (encode (Head := Tower.Head) names) same
  have different : encode (Head := Tower.Head) names leftAtom ≠ encode names rightAtom := by decide +kernel
  exact different encoded

private theorem scopePositionsDifferent : nested ≠ captured := by
  intro same
  have encoded := congrArg (encode (Head := Tower.Head) names) same
  change Tm.app (.const _) (.lam (.lam (.var 1))) =
    Tm.app (.const _) (.lam (.lam (.var 0))) at encoded
  cases encoded

/-- The actual opaque finite declaration package reflects full native
conversion, even when intermediate native terms are outside the source image. -/
theorem original_conversion_exact (first last : Term patSig [] PatSrt.pat) :
    Conv originalRules.headEq (encode names first) (encode names last)
      originalRules.computation ↔ first = last :=
  encode_conversion_iff_eq_of_rootFree names @operatorsUnique originalRules noRoot
    LevelTower.headEq_symmetric first last

theorem different_constructors_do_not_convert :
    ¬ Conv originalRules.headEq (encode names leftAtom) (encode names rightAtom)
      originalRules.computation := by
  intro conversion
  exact sourceAtomsDifferent ((original_conversion_exact _ _).mp conversion)

theorem different_binder_positions_do_not_convert :
    ¬ Conv originalRules.headEq (encode names nested) (encode names captured)
      originalRules.computation := by
  intro conversion
  exact scopePositionsDifferent ((original_conversion_exact _ _).mp conversion)

theorem original_substitution_constructor_is_literal :
    ¬ Conv originalRules.headEq (encode names originalSubstitution) (encode names leftAtom)
      originalRules.computation := by
  intro conversion
  have same := (original_conversion_exact _ _).mp conversion
  have encoded := congrArg (encode (Head := Tower.Head) names) same
  cases encoded

private def nativeNested : Tm Tower.Head 0 := encode names nested
private def nativeCaptured : Tm Tower.Head 0 := encode names captured
private def outsideImage : Tm Tower.Head 0 := .app (.lam (.var 0)) nativeNested
private def beta : StructuralConversionCode.Code Tower.Head (fun _ => Empty) 0 :=
  .single (.betaPi (.var 0) nativeNested)
private def detour := StructuralConversionCode.Code.trans (.symm beta) beta

theorem outside_is_not_literal :
    ∀ term : Term patSig [] PatSrt.pat, encode names term ≠ outsideImage := by
  intro term same
  have reduction : Step (fun (_ _ : Tower.Head) => False) outsideImage nativeNested
      RootComputation.empty := by
    exact StepCore.betaPi (.var 0) nativeNested
  rw [← same] at reduction
  exact encode_noStep names (root := RootComputation.empty) (by intro n first last impossible; exact impossible) term reduction

#guard beta.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot outsideImage nativeNested
#guard detour.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot nativeNested nativeNested
#guard !(detour.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot nativeNested nativeCaptured)
#guard detour.stepCount == 2
#guard nativeNested != nativeCaptured
#guard encode (Head := Tower.Head) names leftAtom != encode names rightAtom
#guard encode (Head := Tower.Head) names originalSubstitution != encode names leftAtom

theorem any_checked_detour_reflects (first last : Term patSig [] PatSrt.pat)
    (code : StructuralConversionCode.Code Tower.Head (fun _ => Empty) 0)
    (checked : code.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (encode names first) (encode names last) = true) : first = last := by
  let restricted : Rules Tower.Head := { originalRules with headEq := fun _ _ => False }
  exact (encoded_checked_iff_eq names @operatorsUnique restricted noRoot.eq_empty
    ⟨fun {_ _} impossible => impossible.elim⟩ first last).mp ⟨code, checked⟩

/-- Fresh constructor identities are essential to syntax reflection. -/
private def colliding : Names patSig where
  sort := names.sort
  operator := fun _ => `Collision

theorem colliding_names_lose_injection :
    leftAtom ≠ rightAtom ∧ encode (Head := Tower.Head) colliding leftAtom = encode colliding rightAtom :=
  ⟨sourceAtomsDifferent, rfl⟩

#guard encode (Head := Tower.Head) colliding leftAtom == encode colliding rightAtom

/-- Adding an explicit constructor equation changes the conversion theory. -/
private def extraRoot : RootComputation Tower.Head where
  step := fun first last => first = .const (operatorName (.applyOp "A" 0)) ∧
    last = .const (operatorName (.applyOp "B" 0))
  rename := by
    intro n m shift first last held
    rcases held with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  substitute := by
    intro n m assignment first last held
    rcases held with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

private def withEquation : Rules Tower.Head := { originalRules with computation := extraRoot }

theorem extra_equation_loses_literal_conversion_reflection :
    leftAtom ≠ rightAtom ∧
      Conv withEquation.headEq (encode names leftAtom) (encode names rightAtom)
        withEquation.computation := by
  refine ⟨sourceAtomsDifferent, .rel _ _ (.root ?_)⟩
  exact ⟨rfl, rfl⟩


end Mettapedia.OSLF.NativeTypes.Certificates.Controls.LiteralImages

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls.SharedTransport

open Shared
open CommonRules

def reused : Certificate original where
  rows := [⟨⟨false, .left⟩, Fin.elim0⟩, ⟨⟨true, .pair⟩, fun _ => 0⟩]
  root := 1

def forward : Certificate original where
  rows := [⟨⟨false, .left⟩, Fin.elim0⟩, ⟨⟨true, .pair⟩, fun _ => 1⟩]
  root := 1

def badUnused : Certificate original where
  rows := reused.rows ++ [⟨⟨true, .pair⟩, fun _ => 99⟩]
  root := reused.root

def small : Certificate smaller where
  rows := [⟨(), Fin.elim0⟩]
  root := 0

theorem repeated_premises_retained :
    checkJudgmentsWithWork (reused.map inclusion) (some true) = (true, 2, 3) := by decide +kernel

theorem collapsing_judgments_breaks_graph_reflection :
    checkJudgments small true = false ∧ checkJudgments (small.map collapse) () = true := by decide +kernel

theorem invalid_unused_row_remains_refused :
    checkJudgments badUnused true = false ∧
      checkJudgments (badUnused.map inclusion) (some true) = false := by decide +kernel

#guard checkJudgments reused true
#guard checkJudgments (reused.map inclusion) (some true)
#guard (reused.map inclusion).rows.length == 2
#guard (reused.map inclusion).root == 1
#guard ((reused.map inclusion).rows.get ⟨1, by decide⟩).references ⟨0, by decide +kernel⟩ == 0
#guard ((reused.map inclusion).rows.get ⟨1, by decide⟩).references ⟨1, by decide +kernel⟩ == 0
#guard checkJudgmentsWithWork (reused.map inclusion) (some true) == (true, 2, 3)
#guard !checkJudgments reused false
#guard !checkJudgments (reused.map inclusion) (some false)
#guard !checkJudgments forward true
#guard !checkJudgments (forward.map inclusion) (some true)
#guard !checkJudgments badUnused true
#guard !checkJudgments (badUnused.map inclusion) (some true)
#guard !checkJudgments small true
#guard checkJudgments (small.map collapse) ()
#guard checkJudgments (small.map smallInclusion) false
#guard checkJudgments ((small.map smallInclusion).map inclusion) (some false)

#print axioms repeated_premises_retained
#print axioms collapsing_judgments_breaks_graph_reflection
#print axioms invalid_unused_row_remains_refused

end Mettapedia.OSLF.NativeTypes.Certificates.Controls.SharedTransport
