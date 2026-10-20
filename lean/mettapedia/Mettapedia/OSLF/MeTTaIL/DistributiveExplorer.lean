import Mettapedia.OSLF.MeTTaIL.DistributiveSteps
import Mathlib.Data.List.Sublists

/-!
# The one-step successors of a canonical form

The successors of a process modulo composition distributing over an idempotent sum, computed on its
canonical form: for every redex of two atoms of a product and every reduct the rule gives it, every
nonempty set `T` of the products holding the redex, and every subset `R` of `T`, the canonical form
of the products outside `R` summed with the reduct composed with the sum of the remainders of `T`.
Chaos steps to itself.

`successors_iff`: a canonical form is a successor exactly when a presentation of the process steps to
a presentation of it. The rule is given twice: as a relation on presentations, and as a function on
canonical atoms (`fire?`), which must agree (`RuleSpec`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Distributive

open Syntax CanonicalBags PatternLexOrder
open scoped Pointwise

variable {decl : Decl}

variable (decl) in
/-- A root rule, as a relation on presentations and as a function on canonical atoms, agreeing:
every reduct the function gives is a firing of the atoms themselves, and every firing of a
presentation's atoms has a reduct the function gives at their canonical forms, up to its own
canonical form. -/
structure RuleSpec (fires : Pattern → Pattern → Pattern → Prop) (fire? : Pattern → Pattern → List Pattern) : Prop where
  atoms : ∀ {first second reduct : Pattern}, fires first second reduct →
    IsAtom decl (normal decl first) ∧ IsAtom decl (normal decl second)
  plain : ∀ {first second reduct : Pattern}, fires first second reduct →
    plain decl first = true ∧ plain decl second = true ∧ plain decl reduct = true
  sound : ∀ {first second reduct : Pattern}, IsAtom decl first → IsAtom decl second →
    normal decl first = first → normal decl second = second → reduct ∈ fire? first second →
      fires first second reduct
  complete : ∀ {first second reduct : Pattern}, fires first second reduct →
    ∃ reduct' ∈ fire? (normal decl first) (normal decl second), normal decl reduct' = normal decl reduct

/-- Every ordered pair of two different positions of a list. -/
def pairs : List Pattern → List (Pattern × Pattern)
  | [] => []
  | atom :: rest => rest.flatMap (fun other => [(atom, other), (other, atom)]) ++ pairs rest

/-- What remains of a product when the redex's two atoms are taken out. -/
def remainder (first second : Pattern) (product : List Pattern) : List Pattern := (product.erase first).erase second

/-- Whether a product holds both atoms of a redex. -/
def holds (first second : Pattern) (product : List Pattern) : Bool :=
  decide (first ∈ product) && decide (second ∈ product.erase first)

/-- The products of a list that are not among the removed ones, as products. -/
def kept (products' removed : List (List Pattern)) : List (List Pattern) :=
  products'.filter fun product : List Pattern =>
    decide ((product : Multiset Pattern) ∉ removed.map fun other : List Pattern => (other : Multiset Pattern))

variable (decl) in
/-- The step for a redex, its reduct, the products `T` it fires in and the products `R` it removes:
the products outside `R`, summed with the reduct composed with the sum of what remains of `T`. -/
def fired (products' : List (List Pattern)) (first second reduct : Pattern) (fired' removed : List (List Pattern)) : Pattern :=
  .collection decl.sum
    ((kept products' removed).map (prod decl) ++
      [.collection decl.product [reduct, .collection decl.sum (fired'.map fun product => prod decl (remainder first second product)) none] none])
    none

variable (decl) in
/-- **The one-step successors of a canonical form.** -/
def successors (fire? : Pattern → Pattern → List Pattern) (form : Pattern) : List Pattern :=
  match products decl form with
  | none => [form]
  | some products' =>
      (products'.flatMap pairs).flatMap fun (first, second) =>
        (fire? first second).flatMap fun reduct =>
          let holders := products'.filter (holds first second)
          ((holders.sublists.filter (· ≠ [])).flatMap fun fired' =>
            fired'.sublists.map fun removed => normal decl (fired decl products' first second reduct fired' removed))

/-! ## The successors are the steps -/

theorem mem_pairs : ∀ {product : List Pattern} {first second : Pattern}, (first, second) ∈ pairs product →
    first ∈ product ∧ second ∈ product
  | [], _, _, member => by simp [pairs] at member
  | atom :: rest, first, second, member => by
    simp only [pairs, List.mem_append, List.mem_flatMap, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at member
    rcases member with ⟨other, otherMember, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | inRest
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ otherMember⟩
    · exact ⟨List.mem_cons_of_mem _ otherMember, List.mem_cons_self⟩
    · obtain ⟨inFirst, inSecond⟩ := mem_pairs inRest
      exact ⟨List.mem_cons_of_mem _ inFirst, List.mem_cons_of_mem _ inSecond⟩

theorem pairs_of_holds : ∀ {product : List Pattern} {first second : Pattern}, first ∈ product →
    second ∈ product.erase first → (first, second) ∈ pairs product
  | [], _, _, inFirst, _ => by simp at inFirst
  | atom :: rest, first, second, inFirst, inSecond => by
    simp only [pairs, List.mem_append, List.mem_flatMap, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    by_cases same : first = atom
    · subst same
      rw [List.erase_cons_head] at inSecond
      exact .inl ⟨second, inSecond, .inl ⟨rfl, rfl⟩⟩
    · rw [List.erase_cons_tail (by intro equal; exact same (beq_iff_eq.mp equal).symm)] at inSecond
      have inRest : first ∈ rest := (List.mem_cons.mp inFirst).resolve_left same
      rcases List.mem_cons.mp inSecond with rfl | inSecondRest
      · exact .inl ⟨first, inRest, .inr ⟨rfl, rfl⟩⟩
      · exact .inr (pairs_of_holds inRest inSecondRest)

theorem holds_iff {first second : Pattern} {product : List Pattern} :
    holds first second product = true ↔ first ∈ product ∧ second ∈ product.erase first := by
  simp [holds]

/-- A product holding a redex is the redex composed with its remainder. -/
theorem cons_remainder {first second : Pattern} {product : List Pattern} (holding' : holds first second product = true) :
    first ::ₘ second ::ₘ (remainder first second product : Multiset Pattern) = product := by
  obtain ⟨inFirst, inSecond⟩ := holds_iff.mp holding'
  simp only [remainder, ← Multiset.coe_erase]
  have secondIn : second ∈ (product : Multiset Pattern).erase first := by
    rw [Multiset.coe_erase]; exact Multiset.mem_coe.mpr inSecond
  rw [Multiset.cons_erase secondIn, Multiset.cons_erase (Multiset.mem_coe.mpr inFirst)]

theorem remainder_subset {first second : Pattern} {product : List Pattern} :
    ∀ atom ∈ remainder first second product, atom ∈ product := fun _ member =>
  List.mem_of_mem_erase (List.mem_of_mem_erase member)

/-- A composition of good atoms denotes its one product. -/
theorem denote_prod (valid : decl.Valid) : ∀ {atoms' : List Pattern}, (∀ atom ∈ atoms', GoodAtom (decl := decl) atom) →
    denote decl (prod decl atoms') = some {(atoms' : Multiset Pattern)} := by
  intro atoms' good
  rw [denote_product valid fun atom member => restFree_of_plain (good atom member).2.2]
  induction atoms' with
  | nil => simp [totalOf, Finset.singleton_zero]
  | cons atom rest ih =>
    rw [totalOf_cons, ih fun other member => good other (List.mem_cons_of_mem _ member)]
    have here := good atom List.mem_cons_self
    unfold denote
    rw [here.2.1, value_atom here.1]
    simp [plus, Finset.singleton_add_singleton, Multiset.singleton_add]

theorem unionOf_append (left right : List Pattern) :
    unionOf decl (left ++ right) = cup (unionOf decl left) (unionOf decl right) := by
  induction left with
  | nil =>
    rw [List.nil_append]
    show unionOf decl right = cup (some ∅) (unionOf decl right)
    cases unionOf decl right <;> simp [cup]
  | cons first rest ih => rw [List.cons_append, unionOf_cons, unionOf_cons, ih, cup_assoc]

/-- A sum of compositions of good atoms denotes its products. -/
theorem unionOf_prods (valid : decl.Valid) : ∀ {products' : List (List Pattern)},
    (∀ product ∈ products', ∀ atom ∈ product, GoodAtom (decl := decl) atom) →
      unionOf decl (products'.map (prod decl)) = some (presented products')
  | [], _ => by simp [unionOf, presented]
  | product :: rest, good => by
    rw [List.map_cons, unionOf_cons, denote_prod valid (good product List.mem_cons_self),
      unionOf_prods valid fun other member => good other (List.mem_cons_of_mem _ member)]
    simp only [cup, Option.some.injEq]
    ext bag
    simp [presented]

theorem plain_prod_good (valid : decl.Valid) {atoms' : List Pattern} (good : ∀ atom ∈ atoms', GoodAtom (decl := decl) atom) :
    plain decl (prod decl atoms') = true :=
  plain_prod valid fun atom member => (good atom member).2.2

/-- What a step built from good products denotes. -/
theorem denote_fired (valid : decl.Valid) {products' : List (List Pattern)} {first second reduct : Pattern}
    {fired' removed : List (List Pattern)}
    (good : ∀ product ∈ products', ∀ atom ∈ product, GoodAtom (decl := decl) atom)
    (firedHeld : ∀ product ∈ fired', product ∈ products') (nonempty : fired' ≠ [])
    (reductPlain : plain decl reduct = true) :
    plain decl (fired decl products' first second reduct fired' removed) = true ∧
      denote decl (fired decl products' first second reduct fired' removed) =
        cup (some (presented products' \ presented removed))
          (plus (denote decl reduct) (some (presented (fired'.map (remainder first second))))) := by
  have restGood : ∀ product ∈ kept products' removed, ∀ atom ∈ product, GoodAtom (decl := decl) atom :=
    fun product member => good product (List.mem_filter.mp member).1
  have remaindersGood : ∀ product ∈ fired'.map (remainder first second), ∀ atom ∈ product, GoodAtom (decl := decl) atom := by
    intro product member atom inProduct
    obtain ⟨held, heldMember, rfl⟩ := List.mem_map.mp member
    exact good held (firedHeld held heldMember) atom (remainder_subset atom inProduct)
  have remaindersNonempty : fired'.map (fun product => prod decl (remainder first second product)) ≠ [] := by
    simpa using nonempty
  have innerPlain : plain decl (.collection decl.sum (fired'.map fun product => prod decl (remainder first second product)) none) = true :=
    plain_sum remaindersNonempty fun item member => by
      obtain ⟨held, heldMember, rfl⟩ := List.mem_map.mp member
      exact plain_prod_good valid (remaindersGood _ (List.mem_map.mpr ⟨held, heldMember, rfl⟩))
  have corePlain : plain decl (.collection decl.product [reduct, .collection decl.sum
      (fired'.map fun product => prod decl (remainder first second product)) none] none) = true :=
    plain_product valid (by simp [reductPlain, innerPlain])
  have elementsPlain : ∀ item ∈ (kept products' removed).map (prod decl) ++ [.collection decl.product [reduct,
        .collection decl.sum (fired'.map fun product => prod decl (remainder first second product)) none] none],
      plain decl item = true := by
    intro item member
    rcases List.mem_append.mp member with inRest | inCore
    · obtain ⟨product, productMember, rfl⟩ := List.mem_map.mp inRest
      exact plain_prod_good valid (restGood product productMember)
    · rw [List.mem_singleton] at inCore; subst inCore; exact corePlain
  refine ⟨plain_sum (by simp) elementsPlain, ?_⟩
  unfold fired
  rw [denote_sum valid fun item member => restFree_of_plain (elementsPlain item member), unionOf_append,
    unionOf_prods valid restGood, unionOf_cons]
  have innerDenote : denote decl (.collection decl.sum (fired'.map fun product => prod decl (remainder first second product)) none) =
      some (presented (fired'.map (remainder first second))) := by
    rw [denote_sum valid fun item member => by
      obtain ⟨held, heldMember, rfl⟩ := List.mem_map.mp member
      exact restFree_of_plain (plain_prod_good valid (remaindersGood _ (List.mem_map.mpr ⟨held, heldMember, rfl⟩)))]
    have mapped : fired'.map (fun product => prod decl (remainder first second product)) =
        (fired'.map (remainder first second)).map (prod decl) := by simp [List.map_map, Function.comp_def]
    rw [mapped, unionOf_prods valid remaindersGood]
  rw [denote_product valid (by simp [restFree_of_plain reductPlain, restFree_of_plain innerPlain]), totalOf_cons,
    totalOf_cons, innerDenote]
  have filtered : presented (kept products' removed) = presented products' \ presented removed := by
    ext bag
    simp only [kept, mem_presented, List.mem_filter, Finset.mem_sdiff, List.mem_map, decide_eq_true_eq, not_exists,
      not_and]
    constructor
    · rintro ⟨product, ⟨productMember, notRemoved⟩, rfl⟩
      exact ⟨⟨product, productMember, rfl⟩, fun r rMember same => notRemoved r rMember same⟩
    · rintro ⟨⟨product, productMember, rfl⟩, notRemoved⟩
      exact ⟨product, ⟨productMember, fun r rMember same => notRemoved r rMember same⟩, rfl⟩
  rw [filtered]
  simp [totalOf, unionOf, plus_zero, cup]
  cases denote decl reduct <;> simp [plus]

/-- **A step from a process reaches a process.** -/
theorem Reduces.plain_target (valid : decl.Valid) {fires : Pattern → Pattern → Pattern → Prop}
    (reductPlain : ∀ {first second reduct : Pattern}, fires first second reduct → plain decl reduct = true)
    {source target : Pattern} (step : Reduces decl fires source target) (isPlain : plain decl source = true) :
    plain decl target = true := by
  induction step with
  | @fire before middle after first second reduct fired' =>
    have elements := (plain_collection isPlain).2.2
    apply plain_product valid
    intro element member
    rw [List.append_assoc, List.cons_append] at member
    rcases List.mem_append.mp member with inBefore | inRest
    · exact elements element (List.mem_append_left _ (List.mem_append_left _ inBefore))
    · rcases List.mem_cons.mp inRest with rfl | inRest
      · exact reductPlain fired'
      · rcases List.mem_append.mp inRest with inMiddle | inAfter
        · exact elements element (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ inMiddle)))
        · exact elements element (List.mem_append_right _ (List.mem_cons_of_mem _ inAfter))
  | diverge => exact isPlain
  | @product before after element changed _ ih =>
    obtain ⟨around, here⟩ := forall_around_iff.mp (plain_collection isPlain).2.2
    exact plain_product valid (forall_around around (ih here))
  | @sum before after element changed _ ih =>
    obtain ⟨around, here⟩ := forall_around_iff.mp (plain_collection isPlain).2.2
    exact plain_sum (by simp) (forall_around around (ih here))

/-- A pattern denoting chaos has chaos as its canonical form. -/
theorem normal_of_denote_none {pattern : Pattern} (chaos : denote decl pattern = none) :
    normal decl pattern = .apply decl.absorbing [] := by
  unfold denote value at chaos
  cases found : products decl (normal decl pattern) with
  | none => exact products_none.mp found
  | some ps => rw [found] at chaos; cases chaos

/-- Congruent processes denote the same. -/
theorem denote_of_congruent (valid : decl.Valid) {left right : Pattern} (leftPlain : plain decl left = true)
    (rightPlain : plain decl right = true) (related : Congruent decl left right) : denote decl left = denote decl right := by
  unfold denote
  rw [(congruent_iff valid leftPlain rightPlain).mp related]

/-- A product of the canonical form holding a redex, with the given remainder. -/
theorem holder_of_mem {products' : List (List Pattern)} {first second : Pattern} {rest : Multiset Pattern}
    (member : first ::ₘ second ::ₘ rest ∈ presented products') :
    ∃ product ∈ products', holds first second product = true ∧
      (remainder first second product : Multiset Pattern) = rest ∧ (product : Multiset Pattern) = first ::ₘ second ::ₘ rest := by
  obtain ⟨product, productMember, same⟩ := mem_presented.mp member
  have firstIn : first ∈ product := Multiset.mem_coe.mp (by rw [same]; simp)
  have erased : ((product : Multiset Pattern).erase first) = second ::ₘ rest := by
    rw [same, Multiset.erase_cons_head]
  have secondIn : second ∈ product.erase first := by
    rw [← Multiset.mem_coe, ← Multiset.coe_erase, erased]; simp
  have holding' : holds first second product = true := holds_iff.mpr ⟨firstIn, secondIn⟩
  refine ⟨product, productMember, holding', ?_, same⟩
  have composed := cons_remainder holding'
  rw [same] at composed
  exact (Multiset.cons_inj_right _).mp ((Multiset.cons_inj_right _).mp composed)

/-- **The successors of a canonical form are the steps**: the canonical form of a process is a
successor of the canonical form of another exactly when a presentation of the second steps to a
presentation of the first. -/
theorem successors_iff (valid : decl.Valid) {fires : Pattern → Pattern → Pattern → Prop}
    {fire? : Pattern → Pattern → List Pattern} (spec : RuleSpec decl fires fire?)
    {source target : Pattern} (sourcePlain : plain decl source = true) (targetPlain : plain decl target = true) :
    normal decl target ∈ successors decl fire? (normal decl source) ↔
      ∃ presentation stepped, plain decl presentation = true ∧ Congruent decl source presentation ∧
        Reduces decl fires presentation stepped ∧ Congruent decl stepped target := by
  have chaosPlain : plain decl (.apply decl.absorbing []) = true := plain_constant _
  have reductPlain : ∀ {first second reduct : Pattern}, fires first second reduct → plain decl reduct = true :=
    fun fired' => (spec.plain fired').2.2
  constructor
  · intro member
    unfold successors at member
    cases productsFound : products decl (normal decl source) with
    | none =>
      rw [productsFound] at member
      rw [List.mem_singleton] at member
      have sourceChaos := products_none.mp productsFound
      refine ⟨.apply decl.absorbing [], .apply decl.absorbing [], chaosPlain, ?_, .diverge, ?_⟩
      · exact (congruent_iff valid sourcePlain chaosPlain).mpr (by rw [sourceChaos, normal_constant])
      · exact (congruent_iff valid chaosPlain targetPlain).mpr (by rw [member, sourceChaos, normal_constant])
    | some ps =>
      rw [productsFound] at member
      simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_sublists, decide_eq_true_eq] at member
      obtain ⟨⟨first, second⟩, ⟨product, productMember, pairMember⟩, reduct, reductMember, fired', ⟨firedSub, firedNonempty⟩,
        removed, removedSub, equal⟩ := member
      have sourceDenote : denote decl source = some (presented ps) := by simp [denote, value, productsFound]
      have good := good_of_denote valid sourcePlain sourceDenote
      have listGood : ∀ product ∈ ps, ∀ atom ∈ product, GoodAtom (decl := decl) atom := fun product member atom inProduct =>
        good _ (mem_presented.mpr ⟨product, member, rfl⟩) atom (Multiset.mem_coe.mpr inProduct)
      obtain ⟨firstIn, secondIn⟩ := mem_pairs pairMember
      have firstGood := listGood product productMember first firstIn
      have secondGood := listGood product productMember second secondIn
      have fired'' := spec.sound firstGood.1 secondGood.1 firstGood.2.1 secondGood.2.1 reductMember
      have firedHeld : ∀ held ∈ fired', held ∈ ps ∧ holds first second held = true := fun held member =>
        List.mem_filter.mp (firedSub.subset member) |>.imp_right id
      obtain ⟨firedPlain, firedDenote⟩ := denote_fired (first := first) (second := second) (removed := removed) valid listGood
        (fun held member => (firedHeld held member).1) firedNonempty (reductPlain fired'')
      have inFamily : InFamily (denote decl source) (normal decl first) (normal decl second) (denote decl reduct)
          (denote decl (fired decl ps first second reduct fired' removed)) := by
        rw [sourceDenote, firstGood.2.1, secondGood.2.1]
        refine ⟨presented (fired'.map (remainder first second)), presented removed, ?_, ?_, ?_, firedDenote⟩
        · obtain ⟨held, heldMember⟩ := List.exists_mem_of_ne_nil fired' firedNonempty
          exact ⟨_, mem_presented.mpr ⟨_, List.mem_map.mpr ⟨held, heldMember, rfl⟩, rfl⟩⟩
        · intro bag member
          obtain ⟨rest, restMember, rfl⟩ := Finset.mem_image.mp member
          obtain ⟨chosen, chosenMember, rfl⟩ := mem_presented.mp restMember
          obtain ⟨held, heldMember, rfl⟩ := List.mem_map.mp chosenMember
          rw [cons_remainder (firedHeld held heldMember).2]
          exact mem_presented.mpr ⟨held, (firedHeld held heldMember).1, rfl⟩
        · intro bag member
          obtain ⟨held, heldMember, rfl⟩ := mem_presented.mp member
          have inFired := removedSub.subset heldMember
          refine Finset.mem_image.mpr ⟨_, mem_presented.mpr ⟨_, List.mem_map.mpr ⟨held, inFired, rfl⟩, rfl⟩, ?_⟩
          exact cons_remainder (firedHeld held inFired).2
      obtain ⟨presentation, stepped, presentationPlain, congruentSource, step, steppedDenote⟩ :=
        family_step valid spec.atoms spec.plain sourcePlain fired'' inFamily
      have steppedPlain := Reduces.plain_target valid reductPlain step presentationPlain
      refine ⟨presentation, stepped, presentationPlain, congruentSource, step, ?_⟩
      apply (congruent_iff valid steppedPlain targetPlain).mpr
      rw [← equal]
      exact Canonical.eq (normal_canonical valid stepped (restFree_of_plain steppedPlain))
        (normal_canonical valid _ (restFree_of_plain firedPlain)) steppedDenote
  · rintro ⟨presentation, stepped, presentationPlain, congruentSource, step, congruentTarget⟩
    have steppedPlain := Reduces.plain_target valid reductPlain step presentationPlain
    have sameSource := denote_of_congruent valid sourcePlain presentationPlain congruentSource
    have sameTarget := (congruent_iff valid steppedPlain targetPlain).mp congruentTarget
    have chaosCase : denote decl source = none → denote decl stepped = none →
        normal decl target ∈ successors decl fire? (normal decl source) := by
      intro sourceChaos steppedChaos
      have sourceNormal := normal_of_denote_none sourceChaos
      unfold successors
      rw [sourceNormal, products_none.mpr rfl, ← sameTarget, normal_of_denote_none steppedChaos]
      exact List.mem_singleton_self _
    rcases step_family valid spec.atoms reductPlain presentationPlain step with
      ⟨presentationChaos, steppedChaos⟩ | ⟨first, second, reduct, fired'', member⟩
    · exact chaosCase (sameSource.trans presentationChaos) steppedChaos
    · rw [← sameSource] at member
      cases sourceDenoted : denote decl source with
      | none =>
        rw [sourceDenoted] at member
        exact chaosCase sourceDenoted member
      | some products' =>
        rw [sourceDenoted] at member
        obtain ⟨remainders, removed, nonempty, holdsSub, removedHeld, steppedEq⟩ := member
        have productsFound : ∃ ps, products decl (normal decl source) = some ps ∧ presented ps = products' := by
          unfold denote value at sourceDenoted
          cases found : products decl (normal decl source) with
          | none => rw [found] at sourceDenoted; cases sourceDenoted
          | some ps => rw [found] at sourceDenoted; cases sourceDenoted; exact ⟨ps, rfl, rfl⟩
        obtain ⟨ps, found, rfl⟩ := productsFound
        obtain ⟨reduct', reductMember, reductSame⟩ := spec.complete fired''
        set x := normal decl first
        set y := normal decl second
        let holders := ps.filter (holds x y)
        let fired' := holders.filter fun held : List Pattern => decide ((remainder x y held : Multiset Pattern) ∈ remainders)
        let removed' := fired'.filter fun held : List Pattern => decide (((held : List Pattern) : Multiset Pattern) ∈ removed)
        obtain ⟨rest, restMember⟩ := nonempty
        obtain ⟨product, productMember, productHolds, productRest, productSame⟩ :=
          holder_of_mem (holdsSub (Finset.mem_image.mpr ⟨rest, restMember, rfl⟩))
        have productFired : product ∈ fired' := by
          simp only [fired', holders, List.mem_filter, decide_eq_true_eq]
          exact ⟨⟨productMember, productHolds⟩, by rw [productRest]; exact restMember⟩
        have firedHeld : ∀ held ∈ fired', held ∈ ps ∧ holds x y held = true := fun held member => by
          simp only [fired', holders, List.mem_filter, decide_eq_true_eq] at member
          exact member.1
        have sourceDenote : denote decl source = some (presented ps) := by simp [denote, value, found]
        have good := good_of_denote valid sourcePlain sourceDenote
        have listGood : ∀ product ∈ ps, ∀ atom ∈ product, GoodAtom (decl := decl) atom :=
          fun product member atom inProduct => good _ (mem_presented.mpr ⟨product, member, rfl⟩) atom (Multiset.mem_coe.mpr inProduct)
        have reductPlain' : plain decl reduct' = true := by
          have xGood := listGood product productMember x (holds_iff.mp productHolds).1
          have yGood := listGood product productMember y (List.mem_of_mem_erase (holds_iff.mp productHolds).2)
          exact (spec.plain (spec.sound xGood.1 yGood.1 xGood.2.1 yGood.2.1 reductMember)).2.2
        obtain ⟨firedPlain, firedDenote⟩ := denote_fired (first := x) (second := y) (removed := removed') valid listGood
          (fun held member => (firedHeld held member).1) (List.ne_nil_of_mem productFired) reductPlain'
        have remaindersSame : presented (fired'.map (remainder x y)) = remainders := by
          ext bag
          simp only [mem_presented, List.mem_map]
          constructor
          · rintro ⟨_, ⟨held, heldMember, rfl⟩, rfl⟩
            simp only [fired', holders, List.mem_filter, decide_eq_true_eq] at heldMember
            exact heldMember.2
          · intro bagMember
            obtain ⟨held, heldMember, heldHolds, heldRest, _⟩ :=
              holder_of_mem (holdsSub (Finset.mem_image.mpr ⟨bag, bagMember, rfl⟩))
            refine ⟨remainder x y held, ⟨held, ?_, rfl⟩, heldRest⟩
            simp only [fired', holders, List.mem_filter, decide_eq_true_eq]
            exact ⟨⟨heldMember, heldHolds⟩, by rw [heldRest]; exact bagMember⟩
        have removedSame : presented removed' = removed := by
          ext bag
          simp only [mem_presented]
          constructor
          · rintro ⟨held, heldMember, rfl⟩
            simp only [removed', List.mem_filter, decide_eq_true_eq] at heldMember
            exact heldMember.2
          · intro bagMember
            obtain ⟨rest', restMember', rfl⟩ := Finset.mem_image.mp (removedHeld bagMember)
            obtain ⟨held, heldMember, heldHolds, heldRest, heldSame⟩ := holder_of_mem (holdsSub (Finset.mem_image.mpr ⟨rest', restMember', rfl⟩))
            refine ⟨held, ?_, heldSame⟩
            simp only [removed', fired', holders, List.mem_filter, decide_eq_true_eq]
            exact ⟨⟨⟨heldMember, heldHolds⟩, by rw [heldRest]; exact restMember'⟩, by rw [heldSame]; exact bagMember⟩
        have reductDenote : denote decl reduct' = denote decl reduct := by unfold denote; rw [reductSame]
        have firedEq : normal decl (fired decl ps x y reduct' fired' removed') = normal decl target := by
          rw [← sameTarget]
          refine Canonical.eq (normal_canonical valid _ (restFree_of_plain firedPlain))
            (normal_canonical valid stepped (restFree_of_plain steppedPlain)) ?_
          change denote decl _ = denote decl stepped
          rw [firedDenote, removedSame, remaindersSame, reductDenote, steppedEq]
        unfold successors
        rw [found]
        simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_sublists, decide_eq_true_eq]
        refine ⟨(x, y), ⟨product, productMember, pairs_of_holds (holds_iff.mp productHolds).1 (holds_iff.mp productHolds).2⟩,
          reduct', reductMember, fired', ⟨List.filter_sublist, List.ne_nil_of_mem productFired⟩, removed',
          List.filter_sublist, firedEq⟩

end Mettapedia.OSLF.MeTTaIL.Distributive
