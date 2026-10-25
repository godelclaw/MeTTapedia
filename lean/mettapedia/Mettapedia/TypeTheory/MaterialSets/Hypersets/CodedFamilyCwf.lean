import Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyCwf

/-!
# Contextual dependent types on valid hyperset codes

Contexts, types and values use the existing valid well-founded codes and
their interpreted membership. The actual coded dependent sum supplies
context comprehension. Decoding compares its projections, generic variable
and pairing with the material hyperset CwF, retaining their member values.

The codes live one host universe above the hypersets they describe. Host
membership remains well-founded; it is not the interpreted membership used
by this contextual model. The existing code construction retains its
classical host dependency and the graph presentation for replacement.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilyCwf

open Mettapedia.GSLT.Core.ContextualLadder
open CategoryTheory
open CodedFamilies

universe u v w

theorem dependentFunction_heq {I : Sort v} {F G : I → Sort w}
    {first : (i : I) → F i} {second : (i : I) → G i}
    (same : ∀ i, HEq (first i) (second i)) : HEq first second := by
  have types : F = G := funext (fun i => type_eq_of_heq (same i))
  cases types
  exact heq_of_eq (funext (fun i => eq_of_heq (same i)))

abbrev Substitution (source target : Code.{u}) := CodedFamilies.Members source → CodedFamilies.Members target

def projection (presentation : HSet.Presentation.{u}) {context : Code.{u}}
    (family : Family context) : Substitution (sigmaCode presentation family) context :=
  fun point => (sigmaMembersEquiv presentation family point).1

def lastVariable (presentation : HSet.Presentation.{u}) {context : Code.{u}}
    (family : Family context) : Section (family ∘ projection presentation family) :=
  fun point => (sigmaMembersEquiv presentation family point).2

def pairSubstitution (presentation : HSet.Presentation.{u}) {source target : Code.{u}}
    (substitution : Substitution source target) (family : Family target)
    (value : Section (family ∘ substitution)) : Substitution source (sigmaCode presentation family) :=
  fun point => pairCode presentation family ⟨substitution point, value point⟩

theorem projection_pair (presentation : HSet.Presentation.{u}) {source target : Code.{u}}
    (substitution : Substitution source target) (family : Family target)
    (value : Section (family ∘ substitution)) :
    projection presentation family ∘ pairSubstitution presentation substitution family value =
      substitution := by
  funext point
  exact congrArg PSigma.fst ((sigmaMembersEquiv presentation family).apply_symm_apply
    ⟨substitution point, value point⟩)

theorem variable_pair_heq (presentation : HSet.Presentation.{u}) {source target : Code.{u}}
    (substitution : Substitution source target) (family : Family target)
    (value : Section (family ∘ substitution)) :
    HEq (fun point => lastVariable presentation family
      (pairSubstitution presentation substitution family value point)) value := by
  apply dependentFunction_heq
  intro point
  exact (PSigma.mk.inj_iff.mp ((sigmaMembersEquiv presentation family).apply_symm_apply
    ⟨substitution point, value point⟩)).2

theorem pair_eta (presentation : HSet.Presentation.{u}) {source target : Code.{u}}
    (family : Family target) (substitution : Substitution source (sigmaCode presentation family)) :
    pairSubstitution presentation (projection presentation family ∘ substitution) family
      (fun point => lastVariable presentation family (substitution point)) = substitution := by
  funext point
  exact (sigmaMembersEquiv presentation family).symm_apply_apply (substitution point)

/-- A category with families using actual host codes and interpreted membership. -/
def codedCwf (presentation : HSet.Presentation.{u}) :
    Cwf.{u + 2, u + 2, u + 2, u + 2} where
  Ctx := Code
  Sub := Substitution
  idS _ := id
  compS first second := first ∘ second
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Ty := Family
  tySub family substitution := family ∘ substitution
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm _ := Section
  tmSub value substitution := fun point => value (substitution point)
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext _ := sigmaCode presentation
  wk := projection presentation
  vz := lastVariable presentation
  pair := pairSubstitution presentation
  wk_pair := projection_pair presentation
  vz_pair substitution family value :=
    eq_of_heq ((variable_pair_heq presentation substitution family value).trans (cast_heq _ value).symm)
  pair_eta := pair_eta presentation

def terminalContext : Code.{u} := encode FamilyCwf.terminalContext

def toTerminal (context : Code.{u}) : Substitution context terminalContext :=
  fun _ => (encodedMemberEquiv FamilyCwf.terminalContext).symm ⟨∅, HSet.mem_singleton_self ∅⟩

theorem toTerminal_unique (context : Code.{u}) (substitution : Substitution context terminalContext) :
    substitution = toTerminal context := by
  funext point
  apply (encodedMemberEquiv FamilyCwf.terminalContext).injective
  apply El.ext HSet.propositional
  change (encodedMemberEquiv FamilyCwf.terminalContext (substitution point)).1 =
    ((encodedMemberEquiv FamilyCwf.terminalContext)
      ((encodedMemberEquiv FamilyCwf.terminalContext).symm ⟨∅, HSet.mem_singleton_self ∅⟩)).1
  rw [Equiv.apply_symm_apply]
  exact HSet.mem_singleton.mp (encodedMemberEquiv FamilyCwf.terminalContext (substitution point)).2

def codedCwfWithTerminal (presentation : HSet.Presentation.{u}) :
    CwfWithTerminal.{u + 2, u + 2, u + 2, u + 2} where
  toCwf := codedCwf presentation
  empty := terminalContext
  toEmpty := toTerminal
  toEmpty_unique := toTerminal_unique

/-- Decoding acts on the actual categories of contexts and substitutions. -/
def decodingFunctor (presentation : HSet.Presentation.{u}) :
    (codedCwf presentation).base.Context ⥤
      (FamilyCwf.hypersetCwf presentation).base.Context where
  obj context := ⟨decode context.val⟩
  map substitution := decodedSub substitution
  map_id context := decodedSub_id context.val
  map_comp first second := decodedSub_comp first second

/-- Every material context is represented by its actual valid code. -/
theorem decodingFunctor_surjective (presentation : HSet.Presentation.{u}) :
    Function.Surjective (decodingFunctor presentation).obj := by
  intro context
  refine ⟨⟨encode context.val⟩, ?_⟩
  exact congrArg
    (fun value : HSet.{u} => (⟨value⟩ : (FamilyCwf.hypersetCwf presentation).base.Context))
    (decode_encode context.val)

/-- No substitution is identified by the decoded context comparison. -/
theorem decodingFunctor_faithful (presentation : HSet.Presentation.{u})
    {source target : (codedCwf presentation).base.Context} :
    Function.Injective (fun substitution : source ⟶ target =>
      (decodingFunctor presentation).map substitution) := by
  intro first second same
  funext point
  apply (memberEquiv target.val).injective
  exact (decodedSub_at_member first point).symm.trans
    ((congrFun same (memberEquiv source.val point)).trans (decodedSub_at_member second point))

/-- Every material substitution between decoded contexts has an explicit preimage. -/
theorem decodingFunctor_full (presentation : HSet.Presentation.{u})
    (source target : (codedCwf presentation).base.Context) :
    Function.Surjective (fun substitution : source ⟶ target =>
      (decodingFunctor presentation).map substitution) := by
  intro substitution
  refine ⟨fun point => (memberEquiv target.val).symm (substitution (memberEquiv source.val point)), ?_⟩
  funext point
  exact ((memberEquiv target.val).apply_symm_apply _).trans
    (congrArg substitution ((memberEquiv source.val).apply_symm_apply point))

/-- Types over corresponding contexts are compared as actual code-valued
and hyperset-valued dependent families. -/
def typeEquiv (context : Code.{u}) :
    Family context ≃ FamilyCwf.Family (decode context) :=
  Equiv.arrowCongr (memberEquiv context) carrierEquiv

theorem typeEquiv_apply (context : Code.{u}) (family : Family context) :
    typeEquiv context family = decodedFamily family := rfl

/-- Coded comprehension decodes as the actual material context extension. -/
def comprehensionEquiv (presentation : HSet.Presentation.{u}) {context : Code.{u}}
    (family : Family context) :
    CodedFamilies.Members (sigmaCode presentation family) ≃
      FamilyCwf.Elements (FamilyCwf.extension presentation (decodedFamily family)) :=
  encodedMemberEquiv (materialSigma presentation family)

private theorem pairComparison (presentation : HSet.Presentation.{u}) {context : Code.{u}}
    (family : Family context) (point : CodedFamilies.Members (sigmaCode presentation family)) :
    pairEquiv family (sigmaMembersEquiv presentation family point) =
      FamilyCwf.extensionDecode presentation (decodedFamily family)
        (comprehensionEquiv presentation family point) :=
  (pairEquiv family).apply_symm_apply _

/-- Decoding the selected projection agrees with the material projection. -/
theorem projection_comparison (presentation : HSet.Presentation.{u}) {context : Code.{u}}
    (family : Family context) (point : CodedFamilies.Members (sigmaCode presentation family)) :
    FamilyCwf.projection presentation (decodedFamily family)
        (comprehensionEquiv presentation family point) =
      memberEquiv context (projection presentation family point) :=
  (congrArg PSigma.fst (pairComparison presentation family point)).symm

/-- Comprehension is preserved by a specified isomorphism of material contexts. -/
def comprehensionIso (presentation : HSet.Presentation.{u}) (context : Code.{u})
    (family : Family context) :
    (decodingFunctor presentation).obj ⟨sigmaCode presentation family⟩ ≅
      ⟨FamilyCwf.extension presentation (decodedFamily family)⟩ where
  hom := fun point => comprehensionEquiv presentation family
    ((memberEquiv (sigmaCode presentation family)).symm point)
  inv := fun point => memberEquiv (sigmaCode presentation family)
    ((comprehensionEquiv presentation family).symm point)
  hom_inv_id := by
    funext point
    exact congrArg (memberEquiv (sigmaCode presentation family))
      ((comprehensionEquiv presentation family).symm_apply_apply _)
      |>.trans ((memberEquiv (sigmaCode presentation family)).apply_symm_apply point)
  inv_hom_id := by
    funext point
    exact congrArg (comprehensionEquiv presentation family)
      ((memberEquiv (sigmaCode presentation family)).symm_apply_apply _)
      |>.trans ((comprehensionEquiv presentation family).apply_symm_apply point)

/-- The comprehension isomorphism lies over the same decoded base context. -/
theorem comprehensionIso_projection (presentation : HSet.Presentation.{u}) (context : Code.{u})
    (family : Family context) :
    (decodingFunctor presentation).map
        (show (⟨sigmaCode presentation family⟩ : (codedCwf presentation).base.Context) ⟶
          ⟨context⟩ from projection presentation family) =
      (comprehensionIso presentation context family).hom ≫
        (show (⟨FamilyCwf.extension presentation (decodedFamily family)⟩ :
          (FamilyCwf.hypersetCwf presentation).base.Context) ⟶ ⟨decode context⟩
          from FamilyCwf.projection presentation (decodedFamily family)) := by
  funext point
  exact (projection_comparison presentation family
    ((memberEquiv (sigmaCode presentation family)).symm point)).symm

/-- The generic variable retains its complete decoded material value. -/
theorem variable_comparison (presentation : HSet.Presentation.{u}) {context : Code.{u}}
    (family : Family context) (point : CodedFamilies.Members (sigmaCode presentation family)) :
    (FamilyCwf.lastVariable presentation (decodedFamily family)
        (comprehensionEquiv presentation family point)).1 =
      decode (lastVariable presentation family point).1 := by
  exact (congrArg (fun pair => pair.2.1) (pairComparison presentation family point)).symm.trans
    (pairEquiv_second_value family (sigmaMembersEquiv presentation family point))

/-- A paired substitution decodes to the actual ordered pair of its values. -/
theorem pair_comparison (presentation : HSet.Presentation.{u}) {source target : Code.{u}}
    (substitution : Substitution source target) (family : Family target)
    (value : Section (family ∘ substitution)) (point : CodedFamilies.Members source) :
    decode (pairSubstitution presentation substitution family value point).1 =
      HSet.kpair (decode (substitution point).1) (decode (value point).1) :=
  pairCode_value presentation family ⟨substitution point, value point⟩

/-- The general CwF comprehension lift is the already constructed coded-sum map. -/
theorem extensionSubstitution_eq_mapSigma (presentation : HSet.Presentation.{u})
    {source target : Code.{u}} (substitution : Substitution source target) (family : Family target) :
    TypeOver.extensionSubstitution (C := codedCwf presentation) substitution family =
      mapSigma presentation substitution family := rfl

/-- An enclosing host universe contains every actual code context and type. -/
theorem codes_bounded {bound : ZFSet.{u + 1}}
    (closed : Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed bound)
    (containsCarrier : Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift.carrierCode.{u} ∈ bound)
    (context : Code.{u}) (family : Family context) (point : CodedFamilies.Members context) :
    context.1 ∈ bound ∧ (family point).1 ∈ bound :=
  ⟨validCode_mem closed containsCarrier context, validCode_mem closed containsCarrier (family point)⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CodedFamilyCwf
