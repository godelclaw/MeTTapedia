import Mettapedia.OSLF.NativeTypes.SortProfiles.Derived
import Mettapedia.OSLF.NativeTypes.Modal.Rules
import Mettapedia.OSLF.NativeTypes.Modal.Formation
import Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers
import Mettapedia.OSLF.NativeTypes.Modal.ProgramAdmission
import Mettapedia.OSLF.NativeTypes.Structural.Logic
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceModalReadouts

open Mettapedia.OSLF.Framework

/-!
# The authored-language type-system generator

Constructor selection changes the actual term signature; rule, equation and
context selection changes the actual operational plan. Logical selection is a
separate input. The cube coordinate retains the derived modal slots and the
shared structural argument/result profiles used to form the authored laws.

The generated catalogues retain declarations, contextual addresses and actual
typing descents. Compilation diagnostics are retained beside these catalogues.
Neither a refused connective nor an unfinished execution is a negative answer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema)
open Mettapedia.OSLF.NativeTypes.Structural (ConnectiveFragment Formula Judgment Refusal)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Derived (CubeVertex)

structure LanguageFragment where
  constructorIndices : Option (List Nat) := none
  operational : Permissions := {}
  deriving DecidableEq, Repr

/-- Original constructor positions are retained in this selected catalogue. -/
def selectedConstructors (language : LanguageDef) (fragment : LanguageFragment) :
    List (GrammarRule × Nat) :=
  language.terms.zipIdx.filter fun entry => selected fragment.constructorIndices entry.2

def selectedLanguage (language : LanguageDef) (fragment : LanguageFragment) : LanguageDef :=
  {language with terms := (selectedConstructors language fragment).map Prod.fst}

def selectedSnapshot (snapshot : Snapshot) (fragment : LanguageFragment) : Snapshot :=
  {snapshot with language := selectedLanguage snapshot.language fragment}

theorem selected_constructor_iff (language : LanguageDef) (fragment : LanguageFragment)
    (entry : GrammarRule × Nat) :
    entry ∈ selectedConstructors language fragment ↔
      entry ∈ language.terms.zipIdx ∧ selected fragment.constructorIndices entry.2 = true := by
  simp [selectedConstructors]

theorem unrestricted_signature (language : LanguageDef) (operational : Permissions) :
    selectedLanguage language ⟨none, operational⟩ = language := by
  simp [selectedLanguage, selectedConstructors, selected, List.zipIdx_map_fst]

/-- Every schema is obtained from a selected authored rule and the complete
typed descent of its source. Ambient binders are read from that descent. -/
def schemas (plan : Plan) : List (Schema plan) :=
  plan.rules.zipIdx.attach.flatMap fun entry =>
    (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.sourceCandidates plan.snapshot.language entry.val.1.rule).flatMap fun carrier =>
      (Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate plan.snapshot.language
        (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree entry.val.1.rule) .all [] carrier entry.val.1.rule.left).map fun site =>
        {ordinal := entry.val.2, declaration := entry.val.1, declared := entry.property,
          position := site.address, bound := [], programCarrier := carrier,
          focusBound := site.focusBound, focusCarrier := site.focusType}

/-- The raw catalogue includes every authored position. Operational selection
does not invent a second manually listed site vocabulary. -/
def selectedSites (language : LanguageDef) (permissions : Permissions) : List Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site :=
  (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).filter fun site => selected permissions.ruleIndices site.declaration

theorem selected_sites_iff (language : LanguageDef) (permissions : Permissions)
    (site : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site) :
    site ∈ selectedSites language permissions ↔
      (site.rule, site.declaration) ∈ language.rewrites.zipIdx ∧
      Mettapedia.OSLF.MeTTaIL.DerivedContexts.Selects site.focus site.context site.rule.left ∧
      selected permissions.ruleIndices site.declaration = true := by
  simp only [selectedSites, List.mem_filter, Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate_spec, and_assoc]

abbrev Assignment := Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.Assignment

/-- Selected laws retain their original declaration positions. Equation
directions can disable conversion, without turning a directed rule into an
equation or renumbering the law catalogue. -/
def selectedEquationLaws (language : LanguageDef) (permissions : Permissions) :
    List Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law :=
  (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equationLaws language).filter fun law =>
    selected permissions.equationIndices law.declaration && !permissions.equationDirections.isEmpty

def selectedRewriteLaws (language : LanguageDef) (permissions : Permissions) :
    List Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law :=
  (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.rewriteLaws language).filter fun law =>
    selected permissions.ruleIndices law.declaration

theorem selected_equation_law_iff (language : LanguageDef) (permissions : Permissions)
    (law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law) :
    law ∈ selectedEquationLaws language permissions ↔
      law ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equationLaws language ∧
      selected permissions.equationIndices law.declaration = true ∧
      permissions.equationDirections.isEmpty = false := by
  simp [selectedEquationLaws, Bool.and_eq_true]

theorem selected_rewrite_law_iff (language : LanguageDef) (permissions : Permissions)
    (law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law) :
    law ∈ selectedRewriteLaws language permissions ↔
      law ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.rewriteLaws language ∧
      selected permissions.ruleIndices law.declaration = true := by
  simp [selectedRewriteLaws]

structure Generated where
  snapshot : Snapshot
  languageFragment : LanguageFragment
  logicFragment : ConnectiveFragment
  vertex : CubeVertex snapshot.language
  modalCatalogue : List (Schema (compile snapshot languageFragment.operational))
  structuralCatalogue : List Mettapedia.OSLF.NativeTypes.Structural.Former
  rawSites : List Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site
  sourceCarrierStatuses : List (Nat × Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers.CarrierStatus)
  programSourceCarrierStatuses : List (Nat × Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.ProgramCarrierStatus)
  sortAssignments : List Assignment
  equationAdmission : Option Bool
  rewriteAdmission : Option Bool

/-- The three inputs are selected independently. The cube's type is the actual
selected presentation's computed cube, rather than a supplied slot count. -/
def generate (snapshot : Snapshot) (language : LanguageFragment) (logic : ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language) : Generated :=
  let chosen := selectedSnapshot snapshot language
  let equationStatus := Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws chosen.language
      (selectedEquationLaws chosen.language language.operational)) vertex.2
  let admittedVertex := equationStatus != some false
  {snapshot := chosen, languageFragment := language, logicFragment := logic, vertex := vertex,
    modalCatalogue := if admittedVertex && logic.core.modal then schemas (compile chosen language.operational) else [],
    structuralCatalogue := if admittedVertex && logic.core.structural then
      Mettapedia.OSLF.NativeTypes.Structural.structuralFormers chosen.language else [],
    rawSites := selectedSites chosen.language language.operational,
    sourceCarrierStatuses := (compile chosen language.operational).rules.map fun declaration =>
      (declaration.declarationIndex,
        Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers.carrierStatus chosen.language declaration.rule),
    programSourceCarrierStatuses := (compile chosen language.operational).rules.map fun declaration =>
      (declaration.declarationIndex,
        Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.programCarrierStatus chosen.language declaration.rule),
    sortAssignments := Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.assignments chosen.language vertex,
    equationAdmission := equationStatus,
    rewriteAdmission := Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws chosen.language
        (selectedRewriteLaws chosen.language language.operational)) vertex.2}

def Generated.plan (generated : Generated) : Plan :=
  compile generated.snapshot generated.languageFragment.operational

def Generated.atomSort (generated : Generated) (index : Nat) : Option TypeExpr :=
  (generated.modalCatalogue[index]?).map Schema.focusCarrier

def Generated.elaborate (generated : Generated) (expected : TypeExpr) (formula : Formula) :
    Except Refusal Judgment :=
  Mettapedia.OSLF.NativeTypes.Structural.elaborate generated.snapshot.language generated.atomSort
    generated.logicFragment expected formula

theorem generated_formation_iff (generated : Generated) (expected : TypeExpr) (formula : Formula) :
    (generated.elaborate expected formula).isOk = true ↔
      Mettapedia.OSLF.NativeTypes.Structural.Formed generated.snapshot.language generated.atomSort
        generated.logicFragment expected formula :=
  by
    rw [← Mettapedia.OSLF.NativeTypes.Structural.elaborate_success_iff]
    cases output : generated.elaborate expected formula <;>
      simp [Generated.elaborate] at output ⊢ <;> simp [output, Except.isOk, Except.toBool]

def Generated.request (generated : Generated) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) : GeneralOccurrenceFrontier.Request :=
  GeneralOccurrenceFrontier.Request.fromSnapshot generated.snapshot
    generated.languageFragment.operational bound expected source

/-- Interruptible execution retains the actual dependent native answers. -/
def Generated.execute (generated : Generated) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (budget : Nat) :
    GeneralOccurrenceFrontier.State (generated.request bound expected source) :=
  GeneralOccurrenceFrontier.run _ budget (GeneralOccurrenceFrontier.start _)

/-- Exhaustive execution is available only after its admission and source
checks succeed. No caller supplies an exhaustive frontier oracle. -/
def Generated.executeCertified? (generated : Generated) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) :
    Option (GeneralOccurrenceFrontier.State (generated.request bound expected source)) :=
  GeneralOccurrenceFrontier.executeCertified? generated.snapshot
    generated.languageFragment.operational bound expected source

theorem generated_certified_coverage {generated : Generated} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    {state : GeneralOccurrenceFrontier.State (generated.request bound expected source)}
    (executed : generated.executeCertified? bound expected source = some state) :
    GeneralOccurrenceFrontier.complete _ state = true ∧
      GeneralOccurrenceFrontier.checkCertificate _ state = true :=
  GeneralOccurrenceFrontier.executeCertified?_complete executed

end Mettapedia.OSLF.NativeTypes.Generation
