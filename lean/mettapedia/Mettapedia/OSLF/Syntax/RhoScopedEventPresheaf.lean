import Mettapedia.OSLF.Syntax.RhoScopedParallelEvents
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Original scoped rho events as a varying contextual graph

The event object retains the authored rule, full contextual assignment and
surrounding process class. Its source and target maps descend the original
source equations and commute with all actual syntactic substitutions.
Existential event support is compared with the independently authored
permitted-path transition relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedEventPresheaf

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelEvents

theorem substitute_id {context : Ctx sig} {sort : Srt}
    (value : TermQ rhoSourceE context sort) :
    bindQ (fun _ position => .var position) value = value := by
  induction value using Quotient.inductionOn with
  | _ value => exact congrArg project (bind_id value)

theorem substitute_comp {source middle target : Ctx sig} {sort : Srt}
    (earlier : Sub sig source middle) (later : Sub sig middle target)
    (value : TermQ rhoSourceE source sort) :
    bindQ later (bindQ earlier value) =
      bindQ (fun sort position => bind later (earlier sort position)) value := by
  induction value using Quotient.inductionOn with
  | _ value => exact congrArg project (bind_comp earlier later value)

theorem substitute_join {source target : Ctx sig} (change : Sub sig source target)
    (first second : Process source) :
    bindQ change (join first second) = join (bindQ change first) (bindQ change second) := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second => rfl

def terms (sort : Srt) : (Syntactic.Ctxt sig)ᵒᵖ ⥤ Type where
  obj world := TermQ rhoSourceE world.unop.vars sort
  map change := TypeCat.ofHom (bindQ change.unop)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    exact substitute_id
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    exact (substitute_comp earlier.unop later.unop value).symm

variable {admitted : SourceRule → Prop}

theorem root_map_id {context : Ctx sig} (root : Root sourceRules admitted context) :
    root.map (fun _ position => .var position) = root := by
  rcases root with ⟨selected, firing⟩
  exact congrArg (fun firing => (⟨selected, firing⟩ : Root sourceRules admitted context))
    (ContextualRootEvents.Instance.map_id firing)

theorem root_map_comp {source middle target : Ctx sig}
    (earlier : Sub sig source middle) (later : Sub sig middle target)
    (root : Root sourceRules admitted source) :
    (root.map earlier).map later =
      root.map (fun sort position => bind later (earlier sort position)) := by
  rcases root with ⟨selected, firing⟩
  exact congrArg (fun firing => (⟨selected, firing⟩ : Root sourceRules admitted target))
    (ContextualRootEvents.Instance.map_comp earlier later firing)

def events (admitted : SourceRule → Prop) : (Syntactic.Ctxt sig)ᵒᵖ ⥤ Type where
  obj world := Root sourceRules admitted world.unop.vars × Process world.unop.vars
  map change := TypeCat.ofHom (fun event => (event.1.map change.unop, bindQ change.unop event.2))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨root, surrounding⟩
    exact Prod.ext (root_map_id root) (substitute_id surrounding)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    rintro ⟨root, surrounding⟩
    exact Prod.ext (root_map_comp earlier.unop later.unop root).symm
      (substitute_comp earlier.unop later.unop surrounding).symm

def source (admitted : SourceRule → Prop) : events admitted ⟶ terms .pr where
  app _ := TypeCat.ofHom (fun event => join event.1.source event.2)
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    rintro ⟨root, surrounding⟩
    exact (congrArg (join · (bindQ change.unop surrounding))
      (Root.source_map change.unop root)).trans
        (substitute_join change.unop root.source surrounding).symm

def target (admitted : SourceRule → Prop) : events admitted ⟶ terms .pr where
  app _ := TypeCat.ofHom (fun event => join event.1.target event.2)
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    rintro ⟨root, surrounding⟩
    exact (congrArg (join · (bindQ change.unop surrounding))
      (Root.target_map change.unop root)).trans
        (substitute_join change.unop root.target surrounding).symm

theorem source_fibre_iff_step (admitted : SourceRule → Prop)
    (world : (Syntactic.Ctxt sig)ᵒᵖ) (process : Process world.unop.vars) :
    (∃ event : (events admitted).obj world, (source admitted).app world event = process) ↔
      ∃ result, RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := admitted) process result := by
  constructor
  · rintro ⟨⟨root, surrounding⟩, readout⟩
    refine ⟨join root.target surrounding, (step_iff_root_surrounding _ _).mpr ?_⟩
    exact ⟨root, surrounding, readout.symm, rfl⟩
  · rintro ⟨result, step⟩
    obtain ⟨root, surrounding, sourceReadout, _⟩ :=
      (step_iff_root_surrounding _ _).mp step
    exact ⟨⟨root, surrounding⟩, sourceReadout.symm⟩

end Mettapedia.OSLF.Binding.RhoScopedEventPresheaf
