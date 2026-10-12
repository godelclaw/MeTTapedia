import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceFiringComparison
import Mettapedia.OSLF.Framework.SortedCommutativeReactiveFibreFinite

/-!
# Local original reactum finiteness survives the genuine source inclusion

An admitted mapped original rule recovers its original declared sort and
complete redex/reactum classes. Faithfulness of the independently earned
class inclusion then fixes the original redex. Its finite primitive fibre
bounds the complete native reacta; no finite origin set or finite rule set
is required. Fresh bundle and probe sorts have no original rule preimage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.SourceReactiveFibres

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.OSLF.SortedCommutative.ReactiveFiniteness
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

theorem mapped_rule_readout (supplied : ReactionRule (.origin : SourceCategory source Parallel))
    {nativeSort : Srt source Parallel}
    (nativeRedex nativeReactum : ValueClass (source := source) (Parallel := Parallel) nativeSort)
    (read : Source.mapReactionRule supplied =
      {codomain := .interface nativeSort, redex := .value nativeRedex, reactum := .value nativeReactum}) :
    ∃ originalSort : source.Srt, ∃ redex reactum : Class source Parallel originalSort,
      supplied = {codomain := .interface originalSort, redex := .value redex, reactum := .value reactum} ∧
        nativeSort = .original originalSort ∧
        HEq nativeRedex (classEmbedding redex) ∧ HEq nativeReactum (classEmbedding reactum) := by
  obtain ⟨codomain, redex, reactum⟩ := supplied
  have domains := congrArg ReactionRule.codomain read
  cases codomain with
  | origin =>
    change (RawObject.origin : ContextCategory source Parallel) = RawObject.interface nativeSort at domains
    cases domains
  | interface sort =>
    cases redex with
    | value before =>
      cases reactum with
      | value after =>
        change (RawObject.interface (Srt.original sort) : ContextCategory source Parallel) =
          RawObject.interface nativeSort at domains
        have sorts : Srt.original sort = nativeSort := RawObject.interface.inj domains
        subst nativeSort
        have redexArrows := congrArg (fun rule => (⟨rule.codomain, rule.redex⟩ :
          Σ object : ContextCategory source Parallel, (.origin : ContextCategory source Parallel) ⟶ object)) read
        have reactumArrows := congrArg (fun rule => (⟨rule.codomain, rule.reactum⟩ :
          Σ object : ContextCategory source Parallel, (.origin : ContextCategory source Parallel) ⟶ object)) read
        have beforeRead : classEmbedding before = nativeRedex :=
          RawArrow.value.inj (eq_of_heq (Sigma.mk.inj_iff.mp redexArrows).2)
        have afterRead : classEmbedding after = nativeReactum :=
          RawArrow.value.inj (eq_of_heq (Sigma.mk.inj_iff.mp reactumArrows).2)
        exact ⟨sort, before, after, rfl, rfl, heq_of_eq beforeRead.symm, heq_of_eq afterRead.symm⟩

theorem mapped_finiteReactumFibres
    {sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop}
    (fibres : FiniteReactumFibres sourceRules) :
    FiniteReactumFibres (Source.mappedRules sourceRules) := by
  intro nativeSort nativeRedex
  cases nativeSort with
  | original sort =>
    by_cases preimage : ∃ before : Class source Parallel sort, classEmbedding before = nativeRedex
    · obtain ⟨before, beforeRead⟩ := preimage
      apply ((fibres sort before).image classEmbedding).subset
      rintro after ⟨supplied, admitted, read⟩
      obtain ⟨originalSort, redex, reactum, ruleRead, sortRead, redexRead, reactumRead⟩ :=
        mapped_rule_readout supplied nativeRedex after read
      have sorts : sort = originalSort := Srt.original.inj sortRead
      subst originalSort
      have sameBefore : redex = before := classEmbedding_injective
        ((eq_of_heq redexRead).symm.trans beforeRead.symm)
      subst redex
      rw [ruleRead] at admitted
      exact ⟨reactum, admitted, (eq_of_heq reactumRead).symm⟩
    · apply Set.finite_empty.subset
      rintro after ⟨supplied, _admitted, read⟩
      obtain ⟨originalSort, redex, _reactum, _ruleRead, sortRead, redexRead, _reactumRead⟩ :=
        mapped_rule_readout supplied nativeRedex after read
      have sorts : sort = originalSort := Srt.original.inj sortRead
      subst originalSort
      exact (preimage ⟨redex, (eq_of_heq redexRead).symm⟩).elim
  | arguments head =>
    apply Set.finite_empty.subset
    rintro after ⟨supplied, _admitted, read⟩
    obtain ⟨originalSort, _redex, _reactum, _ruleRead, sortRead, _redexRead, _reactumRead⟩ :=
      mapped_rule_readout supplied nativeRedex after read
    cases sortRead
  | probe instrument =>
    apply Set.finite_empty.subset
    rintro after ⟨supplied, _admitted, read⟩
    obtain ⟨originalSort, _redex, _reactum, _ruleRead, sortRead, _redexRead, _reactumRead⟩ :=
      mapped_rule_readout supplied nativeRedex after read
    cases sortRead

end Mettapedia.OSLF.Framework.SortedTypedInstruments.SourceReactiveFibres
