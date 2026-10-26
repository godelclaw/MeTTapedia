import Mettapedia.GSLT.LanguageDef.BindingSignatureSubstitution
import Mettapedia.GSLT.LanguageDef.BindingSignatureWire

/-!
# Controls for declaration-derived scoped syntax

The input control reads the actual rho constructor declarations, with both
Name and Proc variables and a binding argument. The multi-abstraction control
keeps two different binder counts in one authored parameter family.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

private def dropRule : GrammarRule := rhoCalc.terms.get ⟨1, by decide⟩
private def parallelRule : GrammarRule := rhoCalc.terms.get ⟨3, by decide⟩
private def inputRule : GrammarRule := rhoCalc.terms.get ⟨5, by decide⟩
private def zeroRule : GrammarRule := rhoCalc.terms.get ⟨0, by decide⟩
private def quoteRule : GrammarRule := rhoCalc.terms.get ⟨2, by decide⟩

private def zero {bound : List TypeExpr} : Term (signatureOf rhoCalc) bound TypeExpr.proc :=
  .op (.constructor zeroRule (List.get_mem _ _) (by
    simp [UsesBareCollection, zeroRule, rhoCalc]) .nil) .nil

private def quotedZero {bound : List TypeExpr} :
    Term (signatureOf rhoCalc) bound TypeExpr.name := by
  apply Term.op (Operator.constructor quoteRule (List.get_mem _ _) (by
    simp [UsesBareCollection, quoteRule, rhoCalc, TypeExpr.proc, TypeExpr.baseType])
    (.cons (.simple "p" TypeExpr.proc) .nil))
  change Args (signatureOf rhoCalc) [([], TypeExpr.proc)] bound
  exact .cons zero .nil

private def drop {bound : List TypeExpr}
    (name : Term (signatureOf rhoCalc) bound TypeExpr.name) :
    Term (signatureOf rhoCalc) bound TypeExpr.proc :=
  .op (.constructor dropRule (List.get_mem _ _) (by
    simp [UsesBareCollection, dropRule, rhoCalc, TypeExpr.name, TypeExpr.baseType])
    (.cons (.simple "n" TypeExpr.name) .nil)) (.cons name .nil)

/-- Both the newly bound name and an enclosing name occur in the body. -/
def inputBody : Term (signatureOf rhoCalc)
    [TypeExpr.name, TypeExpr.name, TypeExpr.proc] TypeExpr.proc :=
  .op (.collectionConstructor parallelRule (List.get_mem _ _) "ps" .hashBag TypeExpr.proc rfl 3)
    (show Args (signatureOf rhoCalc) (List.replicate 3 ([], TypeExpr.proc))
      [TypeExpr.name, TypeExpr.name, TypeExpr.proc] from
    .cons (drop (.var .zero))
      (.cons (drop (.var (.succ .zero)))
        (.cons (.var (.succ (.succ .zero))) .nil)))

def input : Term (signatureOf rhoCalc) [TypeExpr.name, TypeExpr.proc] TypeExpr.proc :=
  .op (.constructor inputRule (List.get_mem _ _) (by
    simp [UsesBareCollection, inputRule, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.funType])
    (.cons (.simple "n" TypeExpr.name)
      (.cons (.abstraction none "p" TypeExpr.name TypeExpr.proc) .nil)))
    (.cons (.var .zero) (.cons inputBody .nil))

theorem input_erases : erase input =
    .apply "PInput" [.bvar 0, .lambda none
      (.collection .hashBag [.apply "PDrop" [.bvar 0],
        .apply "PDrop" [.bvar 1], .bvar 2] none)] := rfl

theorem input_typed : HasType rhoCalc FreeTypeContext.empty
    [TypeExpr.name, TypeExpr.proc] (erase input) TypeExpr.proc := erase_typed input

theorem input_weakened_erases : erase (weaken (t := TypeExpr.proc) input) =
    .apply "PInput" [.bvar 1, .lambda none
      (.collection .hashBag [.apply "PDrop" [.bvar 0],
        .apply "PDrop" [.bvar 2], .bvar 3] none)] := by
  rw [erase_weaken, input_erases]
  rfl

/-- A well-scoped alternative still captures the enclosing Name variable. -/
def captured : Pattern := .apply "PInput" [.bvar 1, .lambda none
  (.collection .hashBag [.apply "PDrop" [.bvar 0],
    .apply "PDrop" [.bvar 0], .bvar 3] none)]

theorem captured_is_wellScoped : captured.isWellScopedAt 3 = true := by decide

theorem weakening_does_not_capture :
    erase (weaken (t := TypeExpr.proc) input) ≠ captured := by
  rw [input_weakened_erases]
  decide

/-- Binder elimination is exercised on the actual collection constructor body,
with both a newly bound Name and an enclosing Name in its ordered context. -/
theorem input_instantiation :
    erase (bind (extend (Term.var (S := signatureOf rhoCalc) (Var.zero
      (Γ := [TypeExpr.proc]) (s := TypeExpr.name)))) inputBody) =
    instantiateBVar (.bvar 0) (erase inputBody) :=
  erase_bind_extend _ inputBody

/-- Replacing the enclosing Name traverses an actual Name-binding argument;
the local Name remains bound and the older Proc shifts down. -/
theorem input_closed_instantiation :
    erase (bind (extend (quotedZero (bound := [TypeExpr.proc]))) input) =
    .apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none
      (.collection .hashBag [.apply "PDrop" [.bvar 0],
        .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]], .bvar 1] none)] := by
  rw [erase_bind_extend, input_erases]
  simp [instantiateBVar, instantiateBVarAt, erase,
    eraseConstructorArguments, ParameterScope.wrap,
    quotedZero, zero, quoteRule, zeroRule, rhoCalc, liftBVars]

private def multiRule : GrammarRule where
  label := "BindMany"
  category := "Proc"
  params := [.multiAbstraction "p" (.arrow (.multiBinder TypeExpr.name) TypeExpr.proc)]
  syntaxPattern := [.nonTerminal "p"]

private def multiLanguage : LanguageDef :=
  LanguageDef.ofCore "ManyBinders" ["Name", "Proc"] [multiRule] [] []

theorem multiLanguage_valid : multiLanguage.validate = [] := by decide +kernel

def threeBinders : Term (signatureOf multiLanguage) [TypeExpr.proc] TypeExpr.proc :=
  .op (.constructor multiRule (by simp [multiLanguage, LanguageDef.ofCore]) (by
    simp [UsesBareCollection, multiRule, TermParam.multiAbstraction])
    (.cons (.multiAbstraction [] "p" TypeExpr.name TypeExpr.proc 3) .nil))
    (.cons (.var (.succ (.succ (.succ .zero)))) .nil)

def zeroBinders : Term (signatureOf multiLanguage) [TypeExpr.proc] TypeExpr.proc :=
  .op (.constructor multiRule (by simp [multiLanguage, LanguageDef.ofCore]) (by
    simp [UsesBareCollection, multiRule, TermParam.multiAbstraction])
    (.cons (.multiAbstraction [] "p" TypeExpr.name TypeExpr.proc 0) .nil))
    (.cons (.var .zero) .nil)

theorem multiple_counts_preserved :
    erase threeBinders = .apply "BindMany" [.multiLambda 3 [] (.bvar 3)] ∧
    erase zeroBinders = .apply "BindMany" [.multiLambda 0 [] (.bvar 0)] := ⟨rfl, rfl⟩

theorem illShaped_abstraction_has_no_scope
    (binder : Option String) (name : String) (kind : CollType) (element : TypeExpr)
    (binders : List TypeExpr) (body : TypeExpr) :
    IsEmpty (ParameterScope (.abstractionNamed binder name (.collection kind element))
      binders body) := ⟨fun scope => nomatch scope⟩

theorem no_dangling_variable (type : TypeExpr) : IsEmpty (Var ([] : List TypeExpr) type) :=
  ⟨fun position => nomatch position⟩

theorem undeclared_constructor_not_available :
    ¬ ({ label := "Invented", category := "Proc", params := [], syntaxPattern := [] } :
      GrammarRule) ∈ rhoCalc.terms := by decide

end Mettapedia.GSLT.LanguageDef.BindingSyntax.Controls

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.Controls.SourceReceipt
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.NamedFreeContext
set_option autoImplicit false

/-- The real rho input retains its declared Name-binding slot. -/
theorem input_readback : SourceReadback.check input (erase input) = true := SourceReadback.check_erase input

theorem named_binding_slot_refused : SourceReadback.check input
    (.apply "PInput" [.bvar 0,.lambda (some "display")
      (.collection .hashBag [.apply "PDrop" [.bvar 0],.apply "PDrop" [.bvar 1],.bvar 2] none)]) = false := by
  decide +kernel

theorem wrong_constructor_refused : SourceReadback.check input
    (.apply "Invented" [.bvar 0,.lambda none
      (.collection .hashBag [.apply "PDrop" [.bvar 0],.apply "PDrop" [.bvar 1],.bvar 2] none)]) = false := by
  decide +kernel

def displayedLambda : Term (signatureOf rhoCalc) [] (.arrow TypeExpr.proc TypeExpr.proc) :=
  .op (.lambda TypeExpr.proc TypeExpr.proc) (.cons (.var .zero) .nil)

theorem ordinary_lambda_display_retained : SourceReadback.check displayedLambda
    (.lambda (some "visible") (.bvar 0)) = true := rfl

theorem ordinary_lambda_display_typed : HasType rhoCalc FreeTypeContext.empty []
    (.lambda (some "visible") (.bvar 0)) (.arrow TypeExpr.proc TypeExpr.proc) :=
  SourceReadback.typed displayedLambda _ ordinary_lambda_display_retained

def restData : Term (signatureOf rhoCalc) [TypeExpr.proc] (.collection .hashSet TypeExpr.proc) :=
  .op (.collection .hashSet TypeExpr.proc 1) (.cons (.var .zero) .nil)

theorem collection_tail_retained : (SourceReceiptData.ofTerm restData).accepts
    (.collection .hashSet [.bvar 0] (some "unassignedRest")) = true := by decide +kernel

theorem collection_tail_typed_without_lookup : HasType rhoCalc FreeTypeContext.empty [TypeExpr.proc]
    (.collection .hashSet [.bvar 0] (some "unassignedRest")) (.collection .hashSet TypeExpr.proc) :=
  (SourceReceiptData.ofTerm restData).sound _ collection_tail_retained

theorem wrong_collection_kind_refused : (SourceReceiptData.ofTerm restData).accepts
    (.collection .hashBag [.bvar 0] (some "unassignedRest")) = false := by decide +kernel

def rawSubstitution : Term (signatureOf rhoCalc) [TypeExpr.proc] TypeExpr.proc :=
  .op (.subst TypeExpr.proc TypeExpr.proc) (.cons (.var .zero) (.cons (.var .zero) .nil))

theorem raw_substitution_readback : (SourceReceiptData.ofTerm rawSubstitution).accepts
    (.subst (.bvar 0) (.bvar 0)) = true := by decide +kernel

theorem raw_substitution_typed : HasType rhoCalc FreeTypeContext.empty [TypeExpr.proc]
    (.subst (.bvar 0) (.bvar 0)) TypeExpr.proc :=
  (SourceReceiptData.ofTerm rawSubstitution).sound _ raw_substitution_readback

def freeData : SourceReceiptData rhoCalc [] (.arrow TypeExpr.proc (.collection .hashSet TypeExpr.proc)) where
  entries := [("outside",TypeExpr.proc)]
  term := .op (.lambda TypeExpr.proc (.collection .hashSet TypeExpr.proc))
    (.cons (.op (.collection .hashSet TypeExpr.proc 1) (.cons (.var (.succ .zero)) .nil)) .nil)

def freeSource : Pattern := .lambda (some "visible")
  (.collection .hashSet [.fvar "outside"] (some "unassignedRest"))

theorem free_names_binders_and_tail_retained : freeData.accepts freeSource = true := by decide +kernel

theorem free_source_typed : HasType rhoCalc (FreeTypeContext.ofList freeData.entries) [] freeSource
    (.arrow TypeExpr.proc (.collection .hashSet TypeExpr.proc)) :=
  freeData.sound _ free_names_binders_and_tail_retained

def leakedIndex : SourceReceiptData rhoCalc [] TypeExpr.proc where
  entries := [("outside",TypeExpr.proc)]
  term := .var .zero

/-- Reading the closed term alone would see index zero. Exact source
restoration prevents treating that dangling index as a named free slot. -/
theorem bound_index_cannot_use_free_suffix : leakedIndex.accepts (.bvar 0) = false := by decide +kernel

def conflictingHeader : SourceReceiptData rhoCalc [] TypeExpr.proc where
  entries := [("outside",TypeExpr.proc),("outside",TypeExpr.name)]
  term := .var .zero

theorem conflicting_header_refused : conflictingHeader.accepts (.fvar "outside") = false := by decide +kernel

def freeReceipt : Wire.SourceReceipt rhoCalc []
    (.arrow TypeExpr.proc (.collection .hashSet TypeExpr.proc)) freeSource :=
  ⟨freeData,free_names_binders_and_tail_retained⟩

theorem checked_source_packet_roundtrip :
    (Wire.sourceReceiptCodec rhoCalc [] (.arrow TypeExpr.proc (.collection .hashSet TypeExpr.proc)) freeSource).get
      ((Wire.sourceReceiptCodec rhoCalc [] (.arrow TypeExpr.proc (.collection .hashSet TypeExpr.proc)) freeSource).put freeReceipt) =
        some freeReceipt := Codec.get_put _ _

theorem malformed_packet_refused :
    (Wire.sourceReceiptCodec rhoCalc [] TypeExpr.proc (.bvar 0)).get (.pair (.atom 0) (.atom 0)) = none := rfl

#print axioms input_readback
#print axioms named_binding_slot_refused
#print axioms wrong_constructor_refused
#print axioms ordinary_lambda_display_retained
#print axioms ordinary_lambda_display_typed
#print axioms collection_tail_retained
#print axioms collection_tail_typed_without_lookup
#print axioms wrong_collection_kind_refused
#print axioms raw_substitution_readback
#print axioms raw_substitution_typed
#print axioms free_names_binders_and_tail_retained
#print axioms free_source_typed
#print axioms bound_index_cannot_use_free_suffix
#print axioms conflicting_header_refused
#print axioms checked_source_packet_roundtrip
#print axioms malformed_packet_refused
end Mettapedia.GSLT.LanguageDef.BindingSyntax.Controls.SourceReceipt
