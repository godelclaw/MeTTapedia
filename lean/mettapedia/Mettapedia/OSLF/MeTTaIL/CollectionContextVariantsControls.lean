import Mettapedia.OSLF.MeTTaIL.CollectionContextVariants
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesGenerator
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

/-!
# Typed source controls for collection contexts

All tested holes come from the existing typed occurrence generator over the
authored module. These controls exercise the context component; the broader
execution profile remains refused until the source-coverage join is proved.
-/

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

#module_file "../../../../../metta/gslt/module/CollectionNestedControl.module"

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection.ContextControls

open Syntax GeneralTypedSites

def source : LanguageDef :=
  CollectionNestedControl.language.toOption.getD
    { «name» := "", «types» := [], «terms» := [], «equations» := [], «rewrites» := [] }

def language : LanguageDef := (source.toCore.toOption.map (·.language)).getD source

theorem source_loaded : CollectionNestedControl.language = .ok source := by rfl
example : source.toCore.isOk = true := by cbv

def permissions : OperationalPermissions :=
  { enabled := true, constructorArguments := [("Wrap", 0)],
    collectionKinds := [.hashBag, .hashSet] }

def atom (label : String) : Pattern := .apply label []
def setOf (items : List Pattern) : Pattern := .collection .hashSet items none
def bagOf (items : List Pattern) : Pattern := .collection .hashBag items none

def selectedSites (term : Pattern) : List SiteData :=
  (generate language (fun _ => none) permissions [] (.base "Proc") term).filter
    (fun site => site.focus == atom "A")

def alternatives (term : Pattern) : List SiteVariant :=
  (selectedSites term).flatMap siteVariants

def targets (term : Pattern) : List Pattern :=
  (alternatives term).map (fun variant =>
    CanonicalBags.canon (variant.site.context.fill (atom "B")))

theorem set_retains_or_consumes :
    (targets (setOf [atom "A"])).Perm
      [setOf [atom "B"], setOf [atom "A", atom "B"]] := by cbv; decide

theorem bag_consumes_only : targets (bagOf [atom "A"]) = [bagOf [atom "B"]] := by cbv

theorem nested_set_retention :
    (targets (setOf [setOf [atom "A"]])).Perm
      ([setOf [setOf [atom "B"]],
        setOf [setOf [atom "A"], setOf [atom "B"]],
        setOf [setOf [atom "A", atom "B"]],
        setOf [setOf [atom "A"], setOf [atom "A", atom "B"]]].map
          CanonicalBags.canon) := by cbv; decide

theorem replacing_into_existing_set_member :
    setOf [atom "B"] ∈ targets (setOf [atom "A", atom "B"]) := by
  cbv
  exact .head _

theorem equal_bag_occurrences_keep_origins :
    let variants := alternatives (bagOf [atom "A", atom "A"])
    variants.length = 2 ∧
      (variants.map (fun variant => variant.original.address)).Nodup ∧
      targets (bagOf [atom "A", atom "A"]) =
        [bagOf [atom "A", atom "B"], bagOf [atom "A", atom "B"]] := by cbv; decide

theorem constructor_context_kept :
    (targets (.apply "Wrap" [setOf [atom "A"]])).Perm
      [.apply "Wrap" [setOf [atom "B"]],
        .apply "Wrap" [setOf [atom "A", atom "B"]]] := by cbv; decide

def plan : GeneralExecutionAdmission.Plan := GeneralExecutionAdmission.compile
  ⟨language, [], ⟨[], [], []⟩⟩
  { sites := permissions, includeDerivedEquations := false }

theorem set_context_still_requires_qualification :
    plan.obligations = [.setDecomposition] := by cbv

theorem root_certificate_does_not_authorize_contexts :
    (CollectionExecutionAdmission.admit? plan).isNone = true := by cbv

end Mettapedia.OSLF.MeTTaIL.CollectionSelection.ContextControls
