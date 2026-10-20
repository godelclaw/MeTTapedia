import Mettapedia.OSLF.MeTTaIL.ModelWeight

/-!
# Model normal forms are the common fixed points

A term that the law normal form, the wrapper normal form, the quote-drop normal form and the canonical
form all keep is a model normal form (`normal_of_fixed`): nothing is left to splice, no wrapper to
collapse, no quote-drop pair at a constructor, and every set holds canonical elements once. A collapse
at the root would make the term lighter than itself.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax CollectionLaws CanonicalBags ReflectiveSubstitution QuoteDrop

theorem map_fixed {f : Pattern → Pattern} :
    ∀ {items : List Pattern}, items.map f = items → ∀ item ∈ items, f item = item
  | [], _, _, member => absurd member List.not_mem_nil
  | _ :: _, same, item, member => by
    simp only [List.map_cons, List.cons.injEq] at same
    rcases List.mem_cons.mp member with rfl | later
    · exact same.1
    · exact map_fixed same.2 item later

/-- Every element of a collection the canonical form keeps is its own canonical form. -/
theorem canon_fixed_elements {kind : CollType} {items : List Pattern} (arranged : arrange kind (items.map canon) = items) :
    ∀ item ∈ items, canon item = item := by
  intro item member
  rw [← arranged] at member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp ((arrange_mem item).mp member)
  exact canon_idempotent original

/-- **A term that every normal form keeps is a model normal form.** -/
theorem normal_of_fixed (laws : List Laws) (declaration : ReflectivePresentationDecl) :
    ∀ pattern : Pattern, normalize laws pattern = pattern → wrapperNormal laws pattern = pattern →
      normal declaration pattern = pattern → canon pattern = pattern → Normal laws declaration pattern
  | .bvar index, _, _, _, _ => .bvar index
  | .fvar name, _, _, _, _ => .fvar name
  | .apply label arguments, lawFixed, wrapperFixed, quoteFixed, canonFixed => by
    rw [normalize] at lawFixed
    rw [wrapperNormal_apply] at wrapperFixed
    rw [normal_apply] at quoteFixed
    rw [canon_apply] at canonFixed
    simp only [Pattern.apply.injEq, true_and] at lawFixed wrapperFixed canonFixed
    rcases finish_cases (declaration := declaration) label (arguments.map (normal declaration)) with
      kept | ⟨name, shape, collapsed⟩
    · rw [kept] at quoteFixed
      simp only [Pattern.apply.injEq, true_and] at quoteFixed
      refine .apply (fun argument member => ?_) (by rw [← quoteFixed]; exact kept)
      have : sizeOf argument < sizeOf (Pattern.apply label arguments) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
      exact normal_of_fixed laws declaration argument (map_fixed lawFixed argument member)
        (map_fixed wrapperFixed argument member) (map_fixed quoteFixed argument member)
        (map_fixed canonFixed argument member)
    · exfalso
      rw [collapsed] at quoteFixed
      have le := map_keeps_or_lighter_le (items := arguments)
        (fun item _ => normal_keeps_or_lighter (declaration := declaration) item)
      rw [shape] at le
      have heavy := congrArg weight quoteFixed
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weight_apply] at le heavy
      omega
  | .lambda binder body, lawFixed, wrapperFixed, quoteFixed, canonFixed => by
    rw [normalize] at lawFixed
    rw [wrapperNormal_lambda] at wrapperFixed
    rw [normal_lambda] at quoteFixed
    rw [canon] at canonFixed
    simp only [Pattern.lambda.injEq, true_and] at lawFixed wrapperFixed quoteFixed canonFixed
    exact .lambda (normal_of_fixed laws declaration body lawFixed wrapperFixed quoteFixed canonFixed)
  | .multiLambda arity binders body, lawFixed, wrapperFixed, quoteFixed, canonFixed => by
    rw [normalize] at lawFixed
    rw [wrapperNormal_multiLambda] at wrapperFixed
    rw [normal_multiLambda] at quoteFixed
    rw [canon] at canonFixed
    simp only [Pattern.multiLambda.injEq, true_and] at lawFixed wrapperFixed quoteFixed canonFixed
    exact .multiLambda (normal_of_fixed laws declaration body lawFixed wrapperFixed quoteFixed canonFixed)
  | .subst body replacement, lawFixed, wrapperFixed, quoteFixed, canonFixed => by
    rw [normalize] at lawFixed
    rw [wrapperNormal_subst] at wrapperFixed
    rw [normal_subst] at quoteFixed
    rw [canon] at canonFixed
    simp only [Pattern.subst.injEq] at lawFixed wrapperFixed quoteFixed canonFixed
    exact .subst (normal_of_fixed laws declaration body lawFixed.1 wrapperFixed.1 quoteFixed.1 canonFixed.1)
      (normal_of_fixed laws declaration replacement lawFixed.2 wrapperFixed.2 quoteFixed.2 canonFixed.2)
  | .collection kind items rest, lawFixed, wrapperFixed, quoteFixed, canonFixed => by
    rw [normal_collection] at quoteFixed
    simp only [Pattern.collection.injEq, true_and, and_true] at quoteFixed
    rw [canon_collection] at canonFixed
    have arranged : arrange kind (items.map canon) = items := (Pattern.collection.inj canonFixed).2.1
    have canonItems := canon_fixed_elements arranged
    have sets : kind = .hashSet → items.Nodup ∧ ∀ item ∈ items, canon item = item := by
      rintro rfl
      refine ⟨?_, canonItems⟩
      rw [← arranged, arrange_set]
      exact List.nodup_dedup _
    have settled := normalize_settled laws (.collection kind items rest)
    rw [lawFixed] at settled
    cases found : lawFor laws kind with
    | none =>
      rw [wrapperNormal_plain found] at wrapperFixed
      simp only [Pattern.collection.injEq, true_and, and_true] at wrapperFixed
      have plainLaw : items.map (normalize laws) = items := by
        rw [normalize] at lawFixed
        simp only [found] at lawFixed
        simpa using lawFixed
      refine .collectionPlain (fun item member => ?_) found
      have : sizeOf item < sizeOf (Pattern.collection kind items rest) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
      exact normal_of_fixed laws declaration item (map_fixed plainLaw item member) (map_fixed wrapperFixed item member)
        (map_fixed quoteFixed item member) (canonItems item member)
    | some law =>
      obtain ⟨_, inner⟩ := settled
      have itemFacts := inner kind items rest law rfl found
      rw [wrapperNormal_law found] at wrapperFixed
      have wrapperItems : items.map (wrapperNormal laws) = items ∧
          wrapFinish law kind items rest = .collection kind items rest := by
        match rest, items, wrapperFixed with
        | none, [item], wrapperFixed =>
          exfalso
          simp only [List.map_cons, List.map_nil, wrapFinish] at wrapperFixed
          have heavy := congrArg weight wrapperFixed
          have lighter := wrapperNormal_keeps_or_lighter laws item
          rw [weight_collection] at heavy
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at heavy
          rcases lighter with same | lighter
          · rw [same] at heavy; omega
          · omega
        | none, [], wrapperFixed =>
          simp only [List.map_nil, wrapFinish] at wrapperFixed ⊢
          split at wrapperFixed
          · cases wrapperFixed
          · exact ⟨trivial, rfl⟩
        | none, first :: second :: others, wrapperFixed =>
          simp only [List.map_cons, wrapFinish, Pattern.collection.injEq, true_and, and_true] at wrapperFixed
          refine ⟨by simpa using wrapperFixed, rfl⟩
        | some name, items, wrapperFixed =>
          simp only [wrapFinish, Pattern.collection.injEq, true_and, and_true] at wrapperFixed
          exact ⟨wrapperFixed, rfl⟩
      have eachNormal : ∀ item ∈ items, Normal laws declaration item := by
        intro item member
        have : sizeOf item < sizeOf (Pattern.collection kind items rest) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
        exact normal_of_fixed laws declaration item (itemFacts item member).1 (map_fixed wrapperItems.1 item member)
          (map_fixed quoteFixed item member) (canonItems item member)
      refine .collectionLaw eachNormal found (fun item member => ?_) wrapperItems.2 sets
      rw [deepSplice_eq_splice found (eachNormal item member)]
      exact (itemFacts item member).2
termination_by pattern => sizeOf pattern

end Mettapedia.OSLF.MeTTaIL.Wrappers
