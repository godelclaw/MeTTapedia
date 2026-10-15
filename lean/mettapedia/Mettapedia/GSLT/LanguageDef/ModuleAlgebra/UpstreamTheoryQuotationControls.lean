import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
import Mettapedia.OSLF.Framework.GrammarDerives
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.Languages.MM0Lite.LanguageDef
import Mettapedia.Languages.MM0.Presentation.Calculus

/-!
# Upstream quotation and full-language assembly controls

The carrier quotation is the current upstream `EmptySet` body. The monoid and
rho operator fragments use current upstream rows while leaving their inherited
base to explicit assembly. HE and MM0 syntax checks compare independently
authored quotations with existing source declarations. Whole-language split
and reconstruction controls do not create parallel specifications.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotationControls

namespace SurfaceIsolation

/-- Importing the quotation does not reserve its keywords in ordinary code. -/
def Theory : Nat := 7
def name : Nat := 3
def types : Nat := 2
def Declare : Nat := 4
def Export : Nat := 5
def Assert : Nat := 6
def Rewrite : Nat := 8

end SurfaceIsolation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open UpstreamTheoryQuotation

namespace UpstreamSurfaceIsolation

/-- Opening upstream authoring alone does not enable the English keywords. -/
def Declare : Nat := 1
def Export : Nat := 2
def Assert : Nat := 3
def Rewrite : Nat := 4
def returning : Nat := 5
def taking : Nat := 6
def equals : Nat := 7

end UpstreamSurfaceIsolation

def carrier : QuotedTheory := moduleTheory! Theory EmptySet() {
  Types { Elem; }
  Exports { Elem; }
}

def monoidOperations : QuotedTheory := moduleTheory! Theory MonoidOperations() {
  Terms {
    One  . |- "1" : Elem;
    Mult . x:Elem, y:Elem |- "(" x "*" y ")" : Elem;
  }
  Equations {
    (Mult (Mult x y) z) == (Mult x (Mult y z));
    (Mult x (One)) == x;
    (Mult (One) x) == x;
  }
}

def monoid : QuotedTheory := assemble "Monoid" [carrier, monoidOperations]

theorem carrier_declaration_and_export :
    carrier.types = [TypeDecl.plain "Elem"] ∧ carrier.extension = ["Elem"] := by
  exact ⟨rfl, rfl⟩

theorem monoid_rows_exact :
    monoid.terms = [
      { label := "One", category := "Elem", params := [], syntaxPattern := [.terminal "1"] },
      { label := "Mult", category := "Elem",
        params := [.simple "x" (.base "Elem"), .simple "y" (.base "Elem")],
        syntaxPattern := [.terminal "(", .nonTerminal "x", .terminal "*",
          .nonTerminal "y", .terminal ")"] }] := by
  rfl

theorem monoid_equation_meaning_retained :
    (monoid.equations[0]?).map (fun equation => (equation.left, equation.right)) =
      some (.apply "Mult" [.apply "Mult" [.fvar "x", .fvar "y"], .fvar "z"],
        .apply "Mult" [.fvar "x", .apply "Mult" [.fvar "y", .fvar "z"]]) := by
  rfl

theorem monoid_is_admitted : (admit? monoid).isSome = true := by cbv

theorem operation_fragment_needs_its_carrier :
    (admit? monoidOperations).isSome = false := by decide +kernel

theorem monoid_consuming : ConsumingGrammar monoid.toLanguageDef :=
  consumingGrammarB_sound (by decide)

theorem monoid_complete_parse :
    enumDerives monoid.toLanguageDef 5 "Elem" ["(", "1", "*", "1", ")"] =
      [.apply "Mult" [.apply "One" [], .apply "One" []]] := by decide

theorem monoid_missing_operand_rejected :
    enumDerives monoid.toLanguageDef 4 "Elem" ["(", "1", "*", ")"] = [] := by decide

def ambiguousUnit : QuotedTheory := moduleTheory! Theory AmbiguousUnit() {
  Types { Elem; }
  Terms {
    One . |- "1" : Elem;
    OtherOne . |- "1" : Elem;
  }
}

theorem ambiguity_retains_both_constructor_trees :
    enumDerives ambiguousUnit.toLanguageDef 1 "Elem" ["1"] =
      [.apply "One" [], .apply "OtherOne" []] := by decide

def proseTokens : String ≃ String :=
  (Equiv.swap "1" "one").trans (Equiv.swap "*" "times")

theorem prose_notation_same_parse :
    Derives (changeNotation proseTokens monoid).toLanguageDef "Elem"
      ["(", "one", "times", "one", ")"]
      (.apply "Mult" [.apply "One" [], .apply "One" []]) := by
  have original : Derives monoid.toLanguageDef "Elem" ["(", "1", "*", "1", ")"]
      (.apply "Mult" [.apply "One" [], .apply "One" []]) :=
    ((mem_enumDerives_iff _ _ _ _ _).mp
      (by rw [monoid_complete_parse]; simp)).1
  change Derives (Parsing.GrammarPresentationTransport.mapLanguage proseTokens
    monoid.toLanguageDef) "Elem" ["(", "one", "times", "one", ")"] _
  have tokenLaw : ["(", "1", "*", "1", ")"].map proseTokens =
      ["(", "one", "times", "one", ")"] := by decide +kernel
  rw [← tokenLaw]
  exact Parsing.GrammarPresentationTransport.derives_map proseTokens original

/-! ## Visibility is independent data, with checked negative controls -/

def privateCarrier : QuotedTheory := ofCore carrier.toLanguageDef []

theorem visibility_not_determined_by_core :
    privateCarrier.toLanguageDef = carrier.toLanguageDef ∧ privateCarrier ≠ carrier := by
  refine ⟨rfl, ?_⟩
  intro same
  have exported := congrArg exportedNames same
  change ([] : List String) = ["Elem"] at exported
  cases exported

def inventedExport : QuotedTheory := moduleTheory! Theory InventedExport() {
  Types { Elem; }
  Exports { Missing; }
}

theorem export_does_not_declare_a_sort :
    inventedExport.typeNames = ["Elem"] ∧ exportsValid inventedExport = false := by decide

theorem invented_export_rejected : (admit? inventedExport).isSome = false := by decide +kernel

theorem repeated_base_requires_shared_join :
    (admit? (assemble "RepeatedBase" [carrier, carrier])).isSome = false := by decide +kernel

/-! ## Binder and collection rows from the current rho example -/

def rhoInteraction : QuotedTheory := moduleTheory! Theory RhoInteraction() {
  Types { Proc; Name; }
  Terms {
    PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
    POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc;
    PInput . n:Name, ^x.p:[Name -> Proc] |- n "?" x "." "{" p "}" : Proc;
    NQuote . p:Proc |- "@" "(" p ")" : Name;
  }
  Rewrites {
    RComm : (PPar {(PInput n ^x.p), (POutput n q), ...rest})
      ~> (PPar {(subst ^x.p (NQuote q)), ...rest});
  }
}

theorem rho_interaction_is_admitted : (admit? rhoInteraction).isSome = true := by cbv

theorem rho_binder_parameter_retained :
    (rhoInteraction.terms[2]?).map (·.params) =
      some [.simple "n" (.base "Name"),
        .abstractionWithBinder "x" "p" (.arrow (.base "Name") (.base "Proc"))] := rfl

theorem rho_comm_left_retained :
    (rhoInteraction.rewrites[0]?).map (·.left) =
      some (.apply "PPar" [.collection .hashBag
        [.apply "PInput" [.fvar "n", .lambda (some "x") (.fvar "p")],
         .apply "POutput" [.fvar "n", .fvar "q"]] (some "rest")]) := rfl

theorem rho_comm_right_retained :
    (rhoInteraction.rewrites[0]?).map (·.right) =
      some (.apply "PPar" [.collection .hashBag
        [Pattern.eval (.lambda (some "x") (.fvar "p"))
          (.apply "NQuote" [.fvar "q"])] (some "rest")]) := rfl

theorem authored_scope_application_is_not_implicit_binder_elimination :
    Pattern.eval (.lambda (some "x") (.bvar 0)) (.fvar "n") ≠
      .subst (.lambda (some "x") (.bvar 0)) (.fvar "n") := by decide

def nestedSubstitution : QuotedTheory := moduleTheory! Theory NestedSubstitution() {
  Rewrites {
    RNested : p ~> (subst ^x.(subst ^y.p q) r);
    RGuard : if (subst ^x.p q) ~> t then p ~> t;
  }
}

theorem nested_substitution_scope_retained :
    (nestedSubstitution.rewrites[0]?).map (·.right) =
      some (Pattern.eval
        (.lambda (some "x")
          (Pattern.eval (.lambda (some "y") (.fvar "p")) (.fvar "q")))
        (.fvar "r")) := rfl

theorem guard_substitution_scope_retained :
    (nestedSubstitution.rewrites[1]?).map (·.premises) =
      some [.congruence
        (Pattern.eval (.lambda (some "x") (.fvar "p")) (.fvar "q")) (.fvar "t")] := rfl

def guardedCongruence : QuotedTheory := moduleTheory! Theory GuardedCongruence() {
  Types { Proc; }
  Terms { Keep . p:Proc |- "keep" p : Proc; }
  Rewrites { RKeep : if S ~> T then (Keep S) ~> (Keep T); }
}

theorem guarded_premise_retained :
    (guardedCongruence.rewrites[0]?).map (·.premises) =
      some [.congruence (.fvar "S") (.fvar "T")] := rfl

def restrictionEquation : QuotedTheory := moduleTheory! Theory RestrictionEquation() {
  Equations {
    if x # Q then (PPar {(PNew ^x.P), Q}) == (PNew ^x.(PPar {P, Q}));
  }
}

theorem freshness_guard_retained :
    (restrictionEquation.equations[0]?).map (·.premises) =
      some [.freshness ⟨"x", .fvar "Q"⟩] := rfl

/-! ## Imported nullaries must be resolved in the assembled signature -/

def importedUnitEquation : QuotedTheory := moduleTheory! Theory ImportedUnitEquation() {
  Equations { (Mult x One) == x; }
}

theorem imported_unit_initially_unresolved :
    (importedUnitEquation.equations[0]?).map (·.left) =
      some (.apply "Mult" [.fvar "x", .fvar "One"]) := rfl

theorem imported_unit_resolved_after_assembly :
    ((assemble "ImportedUnit" [carrier, monoidOperations, importedUnitEquation]).equations[3]?).map
      (·.left) = some (.apply "Mult" [.fvar "x", .apply "One" []]) := rfl

/-! ## Sentence authoring reuses the same payload and module composition -/

namespace English

open EnglishAuthoring

def carrier : QuotedTheory := englishTheory! Theory EmptySet {
  Declare the sort Elem.
  Export the sort Elem.
}

def operations : QuotedTheory := englishTheory! Theory MonoidOperations {
  Declare One returning Elem with notation "1".
  Declare Mult taking x:Elem, y:Elem returning Elem
    with notation "(" x "*" y ")".
  Assert that (Mult (Mult x y) z) equals (Mult x (Mult y z)).
  Assert that (Mult x (One)) equals x.
  Assert that (Mult (One) x) equals x.
}

def monoid : QuotedTheory := assemble "Monoid" [carrier, operations]

theorem carrier_surfaces_agree :
    carrier = UpstreamTheoryQuotationControls.carrier := rfl

theorem operation_surfaces_agree :
    operations = monoidOperations := rfl

theorem composition_surfaces_agree :
    monoid = UpstreamTheoryQuotationControls.monoid := rfl

theorem mixed_surfaces_compose :
    assemble "Monoid" [carrier, monoidOperations] = monoid := rfl

theorem monoid_is_admitted : (admit? monoid).isSome = true := by cbv

theorem operations_require_the_carrier :
    (admit? operations).isSome = false := by decide +kernel

theorem english_authored_language_has_complete_parse :
    enumDerives monoid.toLanguageDef 5 "Elem" ["(", "1", "*", "1", ")"] =
      [.apply "Mult" [.apply "One" [], .apply "One" []]] := by decide

theorem english_authored_language_rejects_missing_operand :
    enumDerives monoid.toLanguageDef 4 "Elem" ["(", "1", "*", ")"] = [] := by decide

theorem notation_change_commutes_with_english_composition (tokens : String ≃ String) :
    changeNotation tokens monoid =
      assemble "Monoid" [changeNotation tokens carrier, changeNotation tokens operations] := by
  simpa only [monoid, List.map_cons, List.map_nil] using
    changeNotation_assemble tokens "Monoid" [carrier, operations]

def importedUnitEquation : QuotedTheory := englishTheory! Theory ImportedUnitEquation {
  Assert that (Mult x One) equals x.
}

theorem imported_constant_surfaces_agree :
    importedUnitEquation = UpstreamTheoryQuotationControls.importedUnitEquation := rfl

theorem imported_constant_resolves_after_composition :
    ((assemble "ImportedUnit" [carrier, operations, importedUnitEquation]).equations[3]?).map
      (·.left) = some (.apply "Mult" [.fvar "x", .apply "One" []]) := rfl

def inventedExport : QuotedTheory := englishTheory! Theory InventedExport {
  Declare the sort Elem.
  Export the sort Missing.
}

theorem exported_name_does_not_declare_its_sort :
    inventedExport.typeNames = ["Elem"] ∧ exportsValid inventedExport = false := by decide

theorem invented_export_rejected : (admit? inventedExport).isSome = false := by decide +kernel

def rhoInteraction : QuotedTheory := englishTheory! Theory RhoInteraction {
  Declare the sort Proc.
  Declare the sort Name.
  Declare PPar taking ps:HashBag(Proc) returning Proc with notation "{" ps.*sep("|") "}".
  Declare POutput taking n:Name, q:Proc returning Proc with notation n "!" "(" q ")".
  Declare PInput taking n:Name, ^x.p:[Name -> Proc] returning Proc
    with notation n "?" x "." "{" p "}".
  Declare NQuote taking p:Proc returning Name with notation "@" "(" p ")".
  Rewrite RComm : (PPar {(PInput n ^x.p), (POutput n q), ...rest})
    to (PPar {(subst ^x.p (NQuote q)), ...rest}).
}

theorem binder_and_collection_surfaces_agree :
    rhoInteraction = UpstreamTheoryQuotationControls.rhoInteraction := rfl

theorem rho_interaction_is_admitted : (admit? rhoInteraction).isSome = true := by cbv

theorem binder_parameter_cannot_be_erased :
    (rhoInteraction.terms[2]?).map (·.params) ≠
      some [.simple "n" (.base "Name"), .simple "p" (.base "Proc")] := by decide

def nestedSubstitution : QuotedTheory := englishTheory! Theory NestedSubstitution {
  Rewrite RNested : p to (subst ^x.(subst ^y.p q) r).
  Rewrite RGuard : if (subst ^x.p q) ~> t then p to t.
}

theorem scoped_substitution_surfaces_agree :
    nestedSubstitution = UpstreamTheoryQuotationControls.nestedSubstitution := rfl

def restrictionEquation : QuotedTheory := englishTheory! Theory RestrictionEquation {
  Assert that if x # Q then (PPar {(PNew ^x.P), Q}) equals (PNew ^x.(PPar {P, Q})).
}

theorem guarded_equation_surfaces_agree :
    restrictionEquation = UpstreamTheoryQuotationControls.restrictionEquation := rfl

theorem guard_cannot_be_erased :
    (restrictionEquation.equations[0]?).map (·.premises) ≠ some [] := by decide

end English

/-! ## Actual language consumers, without parallel complete specifications -/

def heReturn : QuotedTheory := moduleTheory! Theory HEReturnFragment() {
  Types { Instr; Atom; }
  Terms { Return . result:Atom |- "return" "(" result ")" : Instr; }
}

theorem he_return_matches_existing_source :
    heReturn.terms[0]? =
      Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE.terms.find? (fun row => row.label == "Return") :=
  rfl

theorem full_he_core_reconstructs :
    NativeAuthoring.assembleRaw "MeTTaHE"
      (NativeAuthoring.splitCore Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE) =
      Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE :=
  NativeAuthoring.assembleRaw_splitCore _

def mm0Formula : QuotedTheory := moduleTheory! Theory MM0FormulaFragment() {
  Types { Formula; }
  Exports { Formula; }
  Terms {
    AtomP . |- "P" : Formula;
    AtomQ . |- "Q" : Formula;
    AtomR . |- "R" : Formula;
    Implies . a:Formula, b:Formula |- "(" a "->" b ")" : Formula;
  }
}

theorem mm0_formula_is_admitted : (admit? mm0Formula).isSome = true := by cbv

theorem mm0_formula_matches_existing_source :
    mm0Formula.terms = Mettapedia.Languages.MM0Lite.LanguageDef.mm0Lite.terms.take 4 := rfl

theorem full_mm0_lite_core_reconstructs :
    NativeAuthoring.assembleRaw "MM0Lite"
      (NativeAuthoring.splitCore Mettapedia.Languages.MM0Lite.LanguageDef.mm0Lite) =
      Mettapedia.Languages.MM0Lite.LanguageDef.mm0Lite :=
  NativeAuthoring.assembleRaw_splitCore _

theorem petta_program_core_reconstructs (space : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) :
    NativeAuthoring.assembleRaw "PeTTaSpace"
      (NativeAuthoring.splitCore
        (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef space)) =
      Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef space :=
  NativeAuthoring.assembleRaw_splitCore _

theorem mm0_calculus_assembly_retains_all_rows (first second : NativeAuthoring.Document) :
    NativeAuthoring.compile Mettapedia.Languages.MM0.Presentation.Calculus.definition
      (.bundle [first, second]) =
      NativeAuthoring.compile
        (NativeAuthoring.compile Mettapedia.Languages.MM0.Presentation.Calculus.definition first) second :=
  NativeAuthoring.compile_bundle_pair _ _ _

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotationControls
