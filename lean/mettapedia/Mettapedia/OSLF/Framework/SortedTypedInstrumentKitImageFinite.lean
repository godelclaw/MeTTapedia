import Mettapedia.OSLF.Framework.SortedTypedInstrumentReactiveFibres
import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceReactiveFibres
import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitMonotonicity

/-!
# Actual kit IPO branching and modal adequacy at every interface

The only independent branching admission is finiteness of primitive original
reacta at each fixed original redex. Complete source inclusion transports
that local condition; genuine administrative argument factors discharge it
for all admitted probes. The actual supported-category firing comparison
then bounds every kit successor. Modal completeness applies to arbitrary
supported native left and right states, including auxiliary sorts, rather
than requiring a constructor-generated left state or a finite kit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.OSLF.SortedCommutative.ReactiveFiniteness
open Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.InterfaceModalLogic

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}

def originalRulePredicate
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel)) :
    ReactionRule (.origin : SourceCategory source Parallel) → Prop :=
  fun rule => ∃ origin, originalRules origin = rule

theorem ambient_finiteReactumFibres (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (originalFibres : FiniteReactumFibres (originalRulePredicate originalRules)) :
    FiniteReactumFibres (ambientRules (NativeOrigins := NativeOrigins) originalRules opened) := by
  intro sort redex
  have oldFibres := SourceReactiveFibres.mapped_finiteReactumFibres originalFibres
  have adminFibres := ReactiveFibres.administrative_finiteReactumFibres
    (source := source) (Parallel := Parallel) (Origins := NativeOrigins)
  apply ((oldFibres sort redex).union (adminFibres sort redex)).subset
  rintro reactum ⟨declaration, read⟩
  cases declaration with
  | original origin =>
    exact Or.inl ⟨originalRules origin, ⟨origin, rfl⟩, read⟩
  | administrative occurrence permitted => exact Or.inr ⟨occurrence, read⟩

theorem ambient_imageFinite (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (originalFibres : FiniteReactumFibres (originalRulePredicate originalRules)) :
    ImageFinite (ambientRules (NativeOrigins := NativeOrigins) originalRules opened) :=
  imageFinite (ambient_finiteReactumFibres opened originalRules originalFibres)

theorem category_imageFinite (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (originalFibres : FiniteReactumFibres (originalRulePredicate originalRules)) :
    ImageFinite (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) := by
  intro before after label agent
  have finiteTargets := ambient_imageFinite (NativeOrigins := NativeOrigins) opened originalRules originalFibres
    (first := before.base) (last := after.base) label.val agent.val
  let _ := finiteTargets.fintype
  apply Finite.of_injective (fun supplied =>
    (⟨supplied.val.val, (category_step_iff opened originalRules agent label supplied.val).mp supplied.property⟩ :
      {target | ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules opened)
        label.val agent.val target}))
  intro first second same
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun supplied :
      {target : (.origin : ContextCategory source Parallel) ⟶ after.base |
        ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules opened) label.val agent.val target} =>
      supplied.val) same

theorem original_identity_label_step (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {sort : source.Srt} (redex reactum : Class source Parallel sort)
    (admitted : originalRulePredicate originalRules
      {codomain := .interface sort, redex := .value redex, reactum := .value reactum}) :
    ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (𝟙 ((sourceInclusion opened).obj (.interface sort)))
      ((sourceInclusion opened).map (RawArrow.value redex))
      ((sourceInclusion opened).map (RawArrow.value reactum)) := by
  let supplied : ReactionRule (.origin : SourceCategory source Parallel) :=
    {codomain := .interface sort, redex := .value redex, reactum := .value reactum}
  have square : supplied.redex ≫ (𝟙 (.interface sort : SourceCategory source Parallel)) = supplied.redex :=
    Category.comp_id _
  have sourceStep : ActIPO (originalRulePredicate originalRules)
      (𝟙 (.interface sort : SourceCategory source Parallel)) supplied.redex supplied.reactum :=
    ⟨supplied, admitted, 𝟙 _, square.trans (Category.comp_id supplied.redex).symm,
      raw_right_identity_isIPO _ square, (Category.comp_id supplied.reactum).symm⟩
  apply (category_step_iff opened originalRules _ _ _).mpr
  obtain ⟨rule, ⟨before, ⟨origin, beforeRead⟩, mapRead⟩, reaction, nativeSquare, minimal, resultRead⟩ :=
    Source.source_step_maps _ sourceStep
  exact ⟨rule, ⟨Declaration.original origin, (congrArg Source.mapReactionRule beforeRead).trans mapRead⟩,
    reaction, nativeSquare, minimal, resultRead⟩

theorem original_fibres_of_category_imageFinite (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (finite : ImageFinite (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)) :
    FiniteReactumFibres (originalRulePredicate originalRules) := by
  intro sort redex
  let before : origin opened ⟶ (sourceInclusion opened).obj (.interface sort) :=
    (sourceInclusion opened).map (RawArrow.value redex)
  have finiteTargets := finite (𝟙 ((sourceInclusion opened).obj (.interface sort))) before
  let _ := finiteTargets.fintype
  apply Finite.of_injective (fun supplied :
      {reactum : Class source Parallel sort |
        originalRulePredicate originalRules
          {codomain := .interface sort, redex := .value redex, reactum := .value reactum}} =>
    (⟨(sourceInclusion opened).map (RawArrow.value supplied.val),
      original_identity_label_step (NativeOrigins := NativeOrigins)
        opened originalRules redex supplied.val supplied.property⟩ :
      {target : origin opened ⟶ (sourceInclusion opened).obj (.interface sort) |
        ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
          (𝟙 ((sourceInclusion opened).obj (.interface sort))) before target}))
  intro first second same
  apply Subtype.ext
  have maps := congrArg (fun supplied :
      {target : origin opened ⟶ (sourceInclusion opened).obj (.interface sort) |
        ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
          (𝟙 ((sourceInclusion opened).obj (.interface sort))) before target} => supplied.val) same
  exact RawArrow.value.inj ((sourceInclusion opened).map_injective maps)

theorem category_imageFinite_iff_original_fibres (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel)) :
    ImageFinite (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) ↔
      FiniteReactumFibres (originalRulePredicate originalRules) :=
  ⟨original_fibres_of_category_imageFinite opened originalRules,
    category_imageFinite opened originalRules⟩

theorem arbitrary_native_ipo_iff_all_interface_modal (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (originalFibres : FiniteReactumFibres (originalRulePredicate originalRules))
    {interface : ContextCategory source Parallel}
    (first second : (.origin : ContextCategory source Parallel) ⟶ interface) :
    IPOBisimilar (ambientRules (NativeOrigins := NativeOrigins) originalRules opened) first second ↔
      LogicallyEquivalent (ambientRules (NativeOrigins := NativeOrigins) originalRules opened) first second :=
  ipoBisimilar_iff_logicallyEquivalent _ (ambient_imageFinite opened originalRules originalFibres) first second

theorem arbitrary_supported_ipo_iff_all_interface_modal (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (originalFibres : FiniteReactumFibres (originalRulePredicate originalRules))
    {interface : Object opened} (first second : origin opened ⟶ interface) :
    IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) first second ↔
      LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) first second :=
  ipoBisimilar_iff_logicallyEquivalent _ (category_imageFinite opened originalRules originalFibres) first second

theorem all_interface_modal_context_congruence (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (originalFibres : FiniteReactumFibres (originalRulePredicate originalRules))
    {before after : Object opened} {first second : origin opened ⟶ before}
    (related : LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) first second)
    (context : before ⟶ after) :
    LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (first ≫ context) (second ≫ context) :=
  (arbitrary_supported_ipo_iff_all_interface_modal opened originalRules originalFibres _ _).mp
    (bisimulation_context_congruence _
      ((arbitrary_supported_ipo_iff_all_interface_modal opened originalRules originalFibres first second).mpr related)
      context)

theorem all_interface_modal_instrument_monotonicity {first second : Policy source Parallel}
    (subkit : ∀ head, first head → second head)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (originalFibres : FiniteReactumFibres (originalRulePredicate originalRules))
    {interface : Object first} {before after : origin first ⟶ interface}
    (related : LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules second)
      ((expand subkit).map before) ((expand subkit).map after)) :
    LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules first) before after :=
  (arbitrary_supported_ipo_iff_all_interface_modal first originalRules originalFibres before after).mp
    (bisimulation_monotone subkit originalRules
      ((arbitrary_supported_ipo_iff_all_interface_modal second originalRules originalFibres _ _).mpr related))

theorem original_fibres_of_finite_rule_image
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (finiteRules : Set.Finite (Set.range originalRules)) :
    FiniteReactumFibres (originalRulePredicate originalRules) :=
  finiteReactumFibres_of_finite_rule_images finiteRules

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
