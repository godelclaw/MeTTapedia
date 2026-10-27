import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNets
import Mettapedia.GSLT.Logic.BagHennessyMilner

/-!
# Context-labelled native types characterize saturated bisimilarity of a token net

A token net's markings are agents of the parallel context category, and its own contexts are the bags of its tokens
(`TokenBag`). A modal formula over parallel contexts (`BagHennessyMilner.Formula`) is a context-labelled native type of
the language (`nativeFormula`): a possibility beside the tokens `cs` is `◇` with the context label of `{cs…, ...x}`.

- **The native type says what the formula says** (`sat_nativeFormula_iff`): at a marking of the net's tokens, the
  front door's native type holds exactly when the formula holds of the marking's bag.
- **A marking beside tokens reacts to finitely many markings** (`imageFinite`): one result per rule.
- **So saturated bisimilarity of markings, against every environment of tokens, is agreement on the context-labelled
  native types** (`saturated_iff_nativeTypes`): no environment tells two markings apart exactly when no native type
  over the net's contexts does.
- **A token no rule consumes is inert** (`inert_saturated`): a marking with it is saturated bisimilar to the marking
  without it, so they have the same native types over the net's contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNets

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule)
open Mettapedia.GSLT.BagRelativePushout (Obj bag bag_injective bag_comp)
open Mettapedia.GSLT.SemiSaturated (Reacts)
open Mettapedia.GSLT.BagHennessyMilner (SaturatedBisimilarIn ImageFinite saturatedBisimilarIn_iff_agree)

/-- The modal formulas over parallel contexts of tokens. -/
abbrev NetFormula := Mettapedia.GSLT.BagHennessyMilner.Formula String

variable {language : LanguageDef} (net : TokenNet language) {relEnv : RelationEnv}

/-- **A bag of the net's tokens**: the net's own contexts. -/
def TokenBag (tokens : Multiset String) : Prop := ∀ name ∈ tokens, name ∈ net.tokens

/-- **The context-labelled native type of a formula over parallel contexts.** -/
def nativeFormula : NetFormula → Formula 0
  | .top => .top
  | .bot => .bot
  | .and left right => .and (nativeFormula left) (nativeFormula right)
  | .or left right => .or (nativeFormula left) (nativeFormula right)
  | .possibly context inner => .possibly (.context "x" (beside "x" context) .any) (nativeFormula inner)
  | .necessarily context inner => .necessarily (.context "x" (beside "x" context) .any) (nativeFormula inner)

/-- **What a marking beside tokens reacts to is a marking of tokens.** -/
theorem region_of_reacts {names context : List String} {next : Multiset String} (region : Region net names)
    (contextRegion : Region net context)
    (reacts : Reacts (reactions language) (bag (names : Multiset String) ≫ bag (context : Multiset String)) (bag next)) :
    TokenBag net next := by
  rw [bag_comp] at reacts
  obtain ⟨_, ⟨rule, member, netRule, presents, rfl⟩, l, k, redexEq, reactumEq, -, rfl⟩ :=
    Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
  obtain rfl : (netRule.consumed : Multiset String) = l := bag_injective redexEq
  obtain rfl : (netRule.produced : Multiset String) = k := bag_injective reactumEq
  intro name found
  rcases Multiset.mem_add.mp found with produced | kept
  · exact produced_region net member presents name (Multiset.mem_coe.mp produced)
  · rcases Multiset.mem_add.mp (Multiset.mem_of_le tsub_le_self kept) with inNames | inContext
    · exact region name (Multiset.mem_coe.mp inNames)
    · exact contextRegion name (Multiset.mem_coe.mp inContext)

theorem region_of_tokenBag {context : List String} (tokens : TokenBag net (context : Multiset String)) :
    Region net context :=
  fun name member => tokens name (Multiset.mem_coe.mpr member)

/-- **The native type says what the formula says**, at a marking of the net's tokens, for a formula over its
contexts. -/
theorem sat_nativeFormula_iff : ∀ (formula : NetFormula), formula.Within (TokenBag net) → ∀ {names : List String},
    Region net names →
      ((referenceStructure relEnv language).sat Env.closed (nativeFormula formula) (marking names) ↔
        formula.Holds (reactions language) (names : Multiset String))
  | .top, _, _, _ => Iff.rfl
  | .bot, _, _, _ => Iff.rfl
  | .and left right, within, _, region =>
    and_congr (sat_nativeFormula_iff left within.1 region) (sat_nativeFormula_iff right within.2 region)
  | .or left right, within, _, region =>
    or_congr (sat_nativeFormula_iff left within.1 region) (sat_nativeFormula_iff right within.2 region)
  | .possibly context inner, within, names, region => by
    have contextRegion := region_of_tokenBag net within.1
    change (∃ target, _ ∧ _) ↔ (∃ next, _ ∧ _)
    constructor
    · rintro ⟨target, step, holds⟩
      obtain ⟨targetState, others, reacts, toTarget⟩ := (contextStep_iff net "x" region contextRegion).mp step
      have othersRegion := region_of_tokenBag net (region_of_reacts net region contextRegion reacts)
      have holdsOthers := (sat_respects_equivalent relEnv language (nativeFormula inner) (state_marking others)
        targetState toTarget).mpr holds
      exact ⟨others, reacts, (sat_nativeFormula_iff inner within.2 othersRegion).mp holdsOthers⟩
    · rintro ⟨next, reacts, holds⟩
      obtain ⟨others, rfl⟩ := Quotient.exists_rep next
      have othersRegion := region_of_tokenBag net (region_of_reacts net region contextRegion reacts)
      exact ⟨marking others, (contextStep_iff net "x" region contextRegion).mpr
        ⟨state_marking others, others, reacts, Relation.EqvGen.refl _⟩,
        (sat_nativeFormula_iff inner within.2 othersRegion).mpr holds⟩
  | .necessarily context inner, within, names, region => by
    have contextRegion := region_of_tokenBag net within.1
    change (∀ target, _ → _) ↔ (∀ next, _ → _)
    constructor
    · intro every next reacts
      obtain ⟨others, rfl⟩ := Quotient.exists_rep next
      have othersRegion := region_of_tokenBag net (region_of_reacts net region contextRegion reacts)
      exact (sat_nativeFormula_iff inner within.2 othersRegion).mp (every (marking others)
        ((contextStep_iff net "x" region contextRegion).mpr
          ⟨state_marking others, others, reacts, Relation.EqvGen.refl _⟩))
    · intro every target step
      obtain ⟨targetState, others, reacts, toTarget⟩ := (contextStep_iff net "x" region contextRegion).mp step
      have othersRegion := region_of_tokenBag net (region_of_reacts net region contextRegion reacts)
      exact (sat_respects_equivalent relEnv language (nativeFormula inner) (state_marking others) targetState
        toTarget).mp ((sat_nativeFormula_iff inner within.2 othersRegion).mpr (every others reacts))

omit net in
/-- **A bag reacts to finitely many bags**: one result per rule. -/
theorem reacts_finite (agent : Multiset String) :
    {next | Reacts (reactions language) (bag agent) (bag next)}.Finite := by
  classical
  let result : RewriteRule → Multiset String := fun rule =>
    if presented : ∃ netRule : NetRule, netRule.Presents rule then
      (presented.choose.produced : Multiset String) + (agent - presented.choose.consumed)
    else 0
  refine ((List.finite_toSet language.rewrites).image result).subset ?_
  intro next reacts
  obtain ⟨_, ⟨rule, member, netRule, presents, rfl⟩, l, k, redexEq, reactumEq, -, resultEq⟩ :=
    Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
  obtain rfl : (netRule.consumed : Multiset String) = l := bag_injective redexEq
  obtain rfl : (netRule.produced : Multiset String) = k := bag_injective reactumEq
  have presented : ∃ netRule : NetRule, netRule.Presents rule := ⟨netRule, presents⟩
  refine ⟨rule, member, ?_⟩
  simp only [result, dif_pos presented]
  rw [presented.choose_spec.unique presents, resultEq]

/-- **A marking beside tokens reacts to finitely many markings.** -/
theorem imageFinite : ImageFinite (reactions language) (TokenBag net) := by
  intro agent context _
  simpa only [bag_comp] using reacts_finite (language := language) (agent + context)

/-- **Context-labelled native types characterize saturated bisimilarity**: two markings of the net's tokens are
saturated bisimilar against every environment of tokens exactly when they have the same native types over the net's
contexts. -/
theorem saturated_iff_nativeTypes {first second : List String} (firstRegion : Region net first)
    (secondRegion : Region net second) :
    SaturatedBisimilarIn (reactions language) (TokenBag net) (first : Multiset String) (second : Multiset String) ↔
      ∀ formula : NetFormula, formula.Within (TokenBag net) →
        ((referenceStructure relEnv language).sat Env.closed (nativeFormula formula) (marking first) ↔
          (referenceStructure relEnv language).sat Env.closed (nativeFormula formula) (marking second)) := by
  rw [saturatedBisimilarIn_iff_agree (imageFinite net)]
  exact forall_congr' fun formula => forall_congr' fun within => by
    rw [sat_nativeFormula_iff net formula within firstRegion, sat_nativeFormula_iff net formula within secondRegion]

/-! ## Inert tokens -/

theorem cons_sub_of_not_mem {inert : String} {agent consumed : Multiset String} (absent : inert ∉ consumed) :
    (inert ::ₘ agent) - consumed = inert ::ₘ (agent - consumed) := by
  have zero := Multiset.count_eq_zero.mpr absent
  ext name
  simp only [Multiset.count_sub, Multiset.count_cons]
  split_ifs with same
  · subst same
    omega
  · omega

omit net in
/-- **A token no rule consumes is inert**: beside any context, a marking with it reacts as the marking without it, the
token carried along. -/
theorem inert_saturated {inert : String}
    (unconsumed : ∀ rule ∈ language.rewrites, ∀ netRule : NetRule, netRule.Presents rule → inert ∉ netRule.consumed)
    (admissible : Multiset String → Prop) (agent : Multiset String) :
    SaturatedBisimilarIn (reactions language) admissible (inert ::ₘ agent) agent := by
  refine ⟨fun first second => first = inert ::ₘ second, ?_, rfl⟩
  rintro _ second rfl context -
  constructor
  · intro next reacts
    rw [bag_comp] at reacts
    obtain ⟨_, ⟨rule, member, netRule, presents, rfl⟩, l, k, redexEq, reactumEq, contained, rfl⟩ :=
      Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
    obtain rfl : (netRule.consumed : Multiset String) = l := bag_injective redexEq
    obtain rfl : (netRule.produced : Multiset String) = k := bag_injective reactumEq
    have absent : inert ∉ (netRule.consumed : Multiset String) := fun inside =>
      unconsumed rule member netRule presents (Multiset.mem_coe.mp inside)
    rw [Multiset.cons_add] at contained
    refine ⟨netRule.produced + ((second + context) - netRule.consumed), ?_, ?_⟩
    · rw [bag_comp]
      exact Mettapedia.GSLT.BagSaturated.reacts_iff.mpr ⟨_, ⟨rule, member, netRule, presents, rfl⟩, _, _, rfl, rfl,
        (Multiset.le_cons_of_notMem absent).mp contained, rfl⟩
    · rw [Multiset.cons_add, cons_sub_of_not_mem absent, Multiset.add_cons]
  · intro next reacts
    rw [bag_comp] at reacts
    obtain ⟨_, ⟨rule, member, netRule, presents, rfl⟩, l, k, redexEq, reactumEq, contained, rfl⟩ :=
      Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
    obtain rfl : (netRule.consumed : Multiset String) = l := bag_injective redexEq
    obtain rfl : (netRule.produced : Multiset String) = k := bag_injective reactumEq
    have absent : inert ∉ (netRule.consumed : Multiset String) := fun inside =>
      unconsumed rule member netRule presents (Multiset.mem_coe.mp inside)
    refine ⟨inert ::ₘ (netRule.produced + ((second + context) - netRule.consumed)), ?_, rfl⟩
    rw [bag_comp, ← Multiset.add_cons, ← cons_sub_of_not_mem absent, ← Multiset.cons_add]
    exact Mettapedia.GSLT.BagSaturated.reacts_iff.mpr ⟨_, ⟨rule, member, netRule, presents, rfl⟩, _, _, rfl, rfl,
      contained.trans (by rw [Multiset.cons_add]; exact Multiset.le_cons_self _ _), rfl⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNets
