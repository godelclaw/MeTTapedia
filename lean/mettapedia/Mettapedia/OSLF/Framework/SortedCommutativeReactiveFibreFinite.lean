import Mettapedia.OSLF.Syntax.SortedCommutativeGroundFactorAllSorts
import Mettapedia.OSLF.Framework.SortedCommutativeContextReactiveSystem
import Mettapedia.GSLT.Logic.InterfaceModalAdequacy
import Mathlib.Data.Set.Finite.Range

/-!
# Finite primitive reactum fibres earn all-interface modal completeness

The independent primitive rule condition bounds the possible complete reacta
at each fixed redex. The actual equation/context category supplies only finitely
many complete ground factorizations of an exposed value. Their dependent sum
with primitive reacta bounds every actual IPO result, including arbitrary
interface labels and original unit rules. No IPO branching or modal adequacy
is supplied as a model field. Finite authored rule images discharge the local
condition; possibly infinite administrative families need their own fibre proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative.ReactiveFiniteness

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.InterfaceModalLogic
open GroundFactors

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

abbrev Reaction := ReactionRule (.origin : RawObject signature Parallel)

def FiniteReactumFibres (rules : Reaction (signature := signature) (Parallel := Parallel) → Prop) : Prop :=
  ∀ (sort : signature.Srt) (redex : Class signature Parallel sort),
    Set.Finite {reactum : Class signature Parallel sort |
      rules {codomain := .interface sort, redex := .value redex, reactum := .value reactum}}

theorem finiteReactumFibres_of_finite_rule_images
    {rules : Reaction (signature := signature) (Parallel := Parallel) → Prop}
    (finiteRules : Set.Finite {rule | rules rule}) : FiniteReactumFibres rules := by
  intro sort redex
  let _ := finiteRules.fintype
  exact Finite.of_injective
    (fun reactum => (⟨{codomain := .interface sort, redex := .value redex, reactum := .value reactum},
      reactum.property⟩ : {rule : Reaction (signature := signature) (Parallel := Parallel) | rules rule}))
    (by
      intro first second same
      apply Subtype.ext
      have pairs := congrArg (fun supplied : {rule : Reaction (signature := signature) (Parallel := Parallel) |
          rules rule} => (⟨supplied.val.codomain, supplied.val.reactum⟩ :
            Σ object : RawObject signature Parallel, (.origin : RawObject signature Parallel) ⟶ object)) same
      have values := (Sigma.mk.inj_iff.mp pairs).2
      change HEq (RawArrow.value first.val) (RawArrow.value second.val) at values
      exact RawArrow.value.inj (eq_of_heq values))

abbrev RawFactor {target : signature.Srt} (whole : Class signature Parallel target) :=
  Σ source : signature.Srt,
    {reading : ContextClass signature Parallel source target × Class signature Parallel source //
      reading.1.fill reading.2 = whole}

def normalizeFactor {target : signature.Srt} {whole : Class signature Parallel target}
    (supplied : RawFactor whole) : TotalFactor whole :=
  ⟨supplied.1, ⟨(normalizeContext supplied.2.val.1, supplied.2.val.2),
    (ContextClass.normalize_filling supplied.2.val.1 supplied.2.val.2).trans supplied.2.property⟩⟩

theorem normalizeFactor_injective {target : signature.Srt} {whole : Class signature Parallel target} :
    Function.Injective (normalizeFactor (whole := whole)) := by
  rintro ⟨firstSort, ⟨⟨firstContext, firstInput⟩, firstRead⟩⟩
    ⟨secondSort, ⟨⟨secondContext, secondInput⟩, secondRead⟩⟩ same
  have normalized := congrArg totalReading same
  obtain ⟨sorts, readings⟩ := Sigma.mk.inj_iff.mp normalized
  change firstSort = secondSort at sorts
  subst secondSort
  have pairs : (normalizeContext firstContext, firstInput) = (normalizeContext secondContext, secondInput) :=
    eq_of_heq readings
  have contexts : firstContext = secondContext := (contextEquiv _ _).injective (congrArg Prod.fst pairs)
  have inputs : firstInput = secondInput := congrArg Prod.snd pairs
  subst secondContext
  subst secondInput
  rfl

theorem rawFactor_finite {target : signature.Srt} (whole : Class signature Parallel target) :
    Finite (RawFactor whole) := by
  let _ := totalFactor_finite whole
  exact Finite.of_injective _ normalizeFactor_injective

abbrev Emission (rules : Reaction (signature := signature) (Parallel := Parallel) → Prop)
    {target : signature.Srt} (whole : Class signature Parallel target) :=
  Σ factor : RawFactor whole,
    {reactum : Class signature Parallel factor.1 |
      rules {codomain := .interface factor.1, redex := .value factor.2.val.2, reactum := .value reactum}}

def emissionValue {rules : Reaction (signature := signature) (Parallel := Parallel) → Prop}
    {target : signature.Srt} {whole : Class signature Parallel target} (supplied : Emission rules whole) :
    (.origin : RawObject signature Parallel) ⟶ .interface target :=
  .value (supplied.1.2.val.1.fill supplied.2.val)

theorem emission_finite {rules : Reaction (signature := signature) (Parallel := Parallel) → Prop}
    (fibres : FiniteReactumFibres rules) {target : signature.Srt} (whole : Class signature Parallel target) :
    Finite (Emission rules whole) := by
  let _ := rawFactor_finite whole
  let _ : ∀ factor : RawFactor whole,
      Finite {reactum : Class signature Parallel factor.1 |
        rules {codomain := .interface factor.1, redex := .value factor.2.val.2, reactum := .value reactum}} :=
    fun factor => fibres factor.1 factor.2.val.2
  exact inferInstance

theorem targets_finite_at_value {rules : Reaction (signature := signature) (Parallel := Parallel) → Prop}
    (fibres : FiniteReactumFibres rules) {first : RawObject signature Parallel} {last : signature.Srt}
    (agent : (.origin : RawObject signature Parallel) ⟶ first) (label : first ⟶ .interface last)
    (whole : Class signature Parallel last) (completeRead : agent ≫ label = RawArrow.value whole) :
    Set.Finite {target | ActIPO rules label agent target} := by
  classical
  let _ := emission_finite fibres whole
  let decode : Unit ⊕ Emission rules whole → ((.origin : RawObject signature Parallel) ⟶ .interface last) :=
    Sum.elim (fun _ => .value whole) emissionValue
  apply (Set.finite_range decode).subset
  intro target actual
  obtain ⟨⟨codomain, redex, reactum⟩, admitted, reaction, square, _minimal, resultRead⟩ := actual
  cases codomain with
  | origin =>
    cases redex
    cases reactum
    exact ⟨.inl (), (resultRead.trans (square.symm.trans completeRead)).symm⟩
  | interface sort =>
    cases redex with
    | value before =>
      cases reactum with
      | value after =>
        cases reaction with
        | context context =>
          have filling : context.fill before = whole := RawArrow.value.inj (square.symm.trans completeRead)
          let factor : RawFactor whole := ⟨sort, ⟨(context, before), filling⟩⟩
          let emission : Emission rules whole := ⟨factor, ⟨after, admitted⟩⟩
          exact ⟨.inr emission, resultRead.symm⟩

theorem imageFinite {rules : Reaction (signature := signature) (Parallel := Parallel) → Prop}
    (fibres : FiniteReactumFibres rules) : ImageFinite rules := by
  intro first last label agent
  cases last with
  | origin =>
    let _ : Finite ((.origin : RawObject signature Parallel) ⟶ .origin) :=
      Finite.of_injective (fun _ => PUnit.unit) (by intro before after _same; cases before; cases after; rfl)
    exact Set.toFinite _
  | interface sort =>
    cases completeRead : agent ≫ label with
    | value whole => exact targets_finite_at_value fibres agent label whole completeRead

theorem actual_ipo_iff_all_interface_modal
    {rules : Reaction (signature := signature) (Parallel := Parallel) → Prop}
    (fibres : FiniteReactumFibres rules) {interface : RawObject signature Parallel}
    (first second : (.origin : RawObject signature Parallel) ⟶ interface) :
    IPOBisimilar rules first second ↔ LogicallyEquivalent rules first second :=
  ipoBisimilar_iff_logicallyEquivalent rules (imageFinite fibres) first second

end Mettapedia.OSLF.SortedCommutative.ReactiveFiniteness
