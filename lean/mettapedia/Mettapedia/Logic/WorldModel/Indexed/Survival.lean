import Mathlib.Logic.Equiv.Basic
import Mettapedia.TypeTheory.DependentFamilyObserverFactorization
import Mettapedia.Logic.WorldModel.Indexed.Doctrine

/-!
# What survives a lossy map

One law, stated once over Mathlib's `Function.FactorsThrough`:

* **Consumers.** A consumer `c : S → Z` is preserved by every map of states that
  preserves an observation `obs` exactly when `c` factors through `obs`
  (`factorsThrough_iff_perm_invariant`, `factorsThrough_iff_endo_invariant`).
  Inside the doctrine the observation is the answer profile at a world: a
  consumer of a world model survives every morphism out of it, in its fibre or
  in the whole total category, exactly when it factors through the profile at
  its world (`survives_fibre_iff`, `survives_total_iff`).
* **Dependent families.** Every dependent family on states descends along an
  observation exactly when the observation is injective, both up to fibrewise
  equivalence (`allFamiliesFactor_iff_injective`) and with equal fibres
  (`allFamiliesDescend_iff_injective`); for predicates the same boundary holds
  constructively (`allPredicatesDescend_iff_injective`).  Inside the doctrine:
  every family on the states of a world model descends to its profiles exactly
  when its extraction loses nothing (`allFamiliesFactor_profile_iff`).

No section of the observation is assumed: the boundary is injectivity, not
exactness of a split readout.
-/

set_option autoImplicit false

open CategoryTheory Opposite
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

namespace Mettapedia.Logic.WorldModel.Indexed

universe vB uB u v w

section Consumers

variable {S : Type u} {O : Sort v} {Z : Sort w}

/-- A transposition of two states with equal observation preserves the
observation. -/
theorem comp_swap_eq_of_eq [DecidableEq S] (obs : S → O) {s t : S} (same : obs s = obs t) :
    obs ∘ Equiv.swap s t = obs := by
  funext x
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs with hs ht
  · rw [hs, same]
  · rw [ht, same]
  · rfl

/-- **Consumer law, permutation form.** A consumer is invariant under every
permutation of states that preserves the observation exactly when it factors
through the observation. -/
theorem factorsThrough_iff_perm_invariant (obs : S → O) (c : S → Z) :
    c.FactorsThrough obs ↔ ∀ σ : Equiv.Perm S, obs ∘ σ = obs → c ∘ σ = c := by
  classical
  constructor
  · intro factors σ preserves
    funext s
    exact factors (congrFun preserves s)
  · intro invariant s t same
    have := congrFun (invariant (Equiv.swap s t) (comp_swap_eq_of_eq obs same)) s
    simpa [Equiv.swap_apply_left] using this.symm

/-- **Consumer law, endomap form.** -/
theorem factorsThrough_iff_endo_invariant (obs : S → O) (c : S → Z) :
    c.FactorsThrough obs ↔ ∀ h : S → S, obs ∘ h = obs → c ∘ h = c := by
  constructor
  · intro factors h preserves
    funext s
    exact factors (congrFun preserves s)
  · intro invariant
    refine (factorsThrough_iff_perm_invariant obs c).2 fun σ preserves => ?_
    exact invariant σ preserves

/-- What factors through a composite factors through its first map. -/
theorem FactorsThrough.of_comp {T : Sort*} {c : S → Z} {h : S → T} {k : T → O}
    (factors : c.FactorsThrough (k ∘ h)) : c.FactorsThrough h :=
  fun _ _ same => factors (congrArg k same)

/-- A consumer that factors through a map factors through every later
observation that the map determines. -/
theorem FactorsThrough.trans {T : Sort*} {c : S → Z} {h : S → T}
    (factors : c.FactorsThrough h) {obs : S → O} (determined : h.FactorsThrough obs) :
    c.FactorsThrough obs :=
  fun _ _ same => factors (determined same)

/-- **Consumer law, view form.** A consumer survives every map that preserves
a view (into any carrier with its own view) exactly when it factors through the
view. -/
theorem survives_view_iff {V : Type v} (view : S → V) (c : S → Z) :
    (∀ (T : Type v) (viewT : T → V) (h : S → T), viewT ∘ h = view → c.FactorsThrough h) ↔
      c.FactorsThrough view := by
  constructor
  · intro survives
    exact survives V id view rfl
  · intro factors T viewT h preserves s t same
    apply factors
    rw [← congrFun preserves s, ← congrFun preserves t]
    exact congrArg viewT same

/-- A consumer of the view is kept, with the same readout, by every
view-preserving map. -/
theorem kept_of_view_preserving {T : Sort*} {V : Sort*} {view : S → V} {viewT : T → V}
    {h : S → T} (preserves : viewT ∘ h = view) (g : V → Z) :
    (g ∘ viewT) ∘ h = g ∘ view := by
  rw [Function.comp_assoc, preserves]

/-- The recovery form used by most local statements of the law: with a
nonempty answer type, a consumer factors through an observation exactly when
some function of the observation recovers it. -/
theorem factorsThrough_iff_exists_recover [Nonempty Z] (obs : S → O) (c : S → Z) :
    c.FactorsThrough obs ↔ ∃ recover : O → Z, ∀ s, recover (obs s) = c s := by
  rw [Function.factorsThrough_iff]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e, fun _ => rfl⟩
  · rintro ⟨e, he⟩
    exact ⟨e, funext fun s => (he s).symm⟩

end Consumers

section Families

variable {S : Type u} {O : Type v}

/-- An anchored equality family, in any fibre universe. -/
def anchoredEquality (anchor : S) (s : S) : Type w := ULift.{w} (PLift (anchor = s))

/-- If every anchored equality family factors, up to equivalence, through an
observation, the observation is injective. -/
theorem injective_of_anchored_factor (obs : S → O)
    (factor : ∀ anchor : S, Nonempty (FamilyFactorization obs (anchoredEquality.{u, w} anchor))) :
    Function.Injective obs := by
  intro s t same
  obtain ⟨factorization⟩ := factor s
  exact ((factorization.fibreEquiv same) (ULift.up (PLift.up rfl))).down.down

/-- The family on observations that reads the fibre of a chosen preimage. -/
noncomputable def chosenFibreFamily (obs : S → O) (F : S → Type w) (o : O) : Type w :=
  open scoped Classical in
  if h : ∃ s, obs s = o then F (Classical.choose h) else PUnit

theorem chosenFibreFamily_obs {obs : S → O} (injective : Function.Injective obs)
    (F : S → Type w) (s : S) : chosenFibreFamily obs F (obs s) = F s := by
  classical
  have h : ∃ s', obs s' = obs s := ⟨s, rfl⟩
  unfold chosenFibreFamily
  rw [dif_pos h]
  exact congrArg F (injective (Classical.choose_spec h))

/-- **Family law, strict form.** Every family on states is the pullback of a
family on observations, with equal fibres, exactly when the observation is
injective. -/
theorem allFamiliesDescend_iff_injective (obs : S → O) :
    (∀ F : S → Type w, ∃ G : O → Type w, ∀ s, F s = G (obs s)) ↔ Function.Injective obs := by
  constructor
  · intro descend
    refine injective_of_anchored_factor obs fun anchor => ?_
    obtain ⟨G, hG⟩ := descend (anchoredEquality.{u, w} anchor)
    exact ⟨{ targetFamily := G, identify := fun s => Equiv.cast (hG s) }⟩
  · intro injective F
    exact ⟨chosenFibreFamily obs F, fun s => (chosenFibreFamily_obs injective F s).symm⟩

/-- **Family law, up to fibrewise equivalence.** -/
theorem allFamiliesFactor_iff_injective (obs : S → O) :
    (∀ F : S → Type w, Nonempty (FamilyFactorization obs F)) ↔ Function.Injective obs := by
  constructor
  · intro factor
    exact injective_of_anchored_factor obs fun anchor => factor _
  · intro injective F
    obtain ⟨G, hG⟩ := (allFamiliesDescend_iff_injective.{u, v, w} obs).2 injective F
    exact ⟨{ targetFamily := G, identify := fun s => Equiv.cast (hG s) }⟩

/-- **Predicate law.** Every predicate on states is the pullback of a predicate
on observations exactly when the observation is injective.  The descended
predicate is the existential image; no choice is used. -/
theorem allPredicatesDescend_iff_injective (obs : S → O) :
    (∀ p : S → Prop, ∃ q : O → Prop, ∀ s, q (obs s) ↔ p s) ↔ Function.Injective obs := by
  constructor
  · intro descend s t same
    obtain ⟨q, hq⟩ := descend (fun x => s = x)
    exact (hq t).1 (same ▸ (hq s).2 rfl)
  · intro injective p
    refine ⟨fun o => ∃ s, obs s = o ∧ p s, fun s => ⟨?_, fun hs => ⟨s, rfl, hs⟩⟩⟩
    rintro ⟨t, same, ht⟩
    exact injective same ▸ ht

/-- **Predicate law, fibre-constancy form.** Every predicate on states is
constant on the fibres of an observation exactly when the observation is
injective; the anchored equality predicates decide it. -/
theorem allPredicatesFactor_iff_injective {T : Sort u} {U : Sort v} (obs : T → U) :
    (∀ p : T → Prop, p.FactorsThrough obs) ↔ Function.Injective obs := by
  constructor
  · intro factor s t same
    have := factor (fun x => s = x) same
    exact cast this rfl
  · intro injective p
    exact injective.factorsThrough p

end Families

/-! ## The law inside the doctrine -/

section Doctrine

variable {B : Type uB} [Category.{vB} B] (P : Bᵒᵖ ⥤ AddCommMonCat.{u})
variable {Z : Sort w}

/-- **Consumers in a fibre.** A consumer of a world model at `b` survives every
morphism of world models at `b` out of it exactly when it factors through the
profile at `b`. -/
theorem survives_fibre_iff {b : B} (X : Over (P.obj (op b))) (c : X.left → Z) :
    (∀ (Y : Over (P.obj (op b))) (h : X ⟶ Y), c.FactorsThrough h.left.hom) ↔
      c.FactorsThrough X.hom.hom := by
  constructor
  · intro survives
    exact survives (Over.mk (𝟙 _)) (Over.homMk X.hom (by simp))
  · intro factors Y h
    refine FactorsThrough.of_comp (k := Y.hom.hom) ?_
    intro s t same
    apply factors
    have w := Over.w h
    have hs := congrArg (fun k : X.left ⟶ P.obj (op b) => k.hom s) w
    have ht := congrArg (fun k : X.left ⟶ P.obj (op b) => k.hom t) w
    exact hs.symm.trans
      ((show (h.left ≫ Y.hom).hom s = (h.left ≫ Y.hom).hom t from same).trans ht)

/-- **Consumers across worlds.** A consumer of a world model survives every
morphism of the total category out of it, to any world, exactly when it
factors through the profile at its own world. -/
theorem survives_total_iff (X : Total P) (c : (Total.model P X).left → Z) :
    (∀ (Y : Total P) (φ : X ⟶ Y), c.FactorsThrough
        ((totalHomEquiv P φ).2.1.hom)) ↔
      c.FactorsThrough (Total.model P X).hom.hom := by
  constructor
  · intro survives
    exact survives (Total.mk P X.base (Over.mk (𝟙 (P.obj (op X.base)))))
      (homOver P (𝟙 X.base) (X := Total.model P X)
        (Y := Over.mk (𝟙 (P.obj (op X.base)))) (Total.model P X).hom (by simp))
  · intro factors Y φ s t same
    apply factors
    have w := (totalHomEquiv P φ).2.2
    have hs := congrArg (fun k : (Total.model P X).left ⟶ P.obj (op X.base) => k.hom s) w
    have ht := congrArg (fun k : (Total.model P X).left ⟶ P.obj (op X.base) => k.hom t) w
    exact hs.symm.trans ((congrArg (fun x => ((Total.model P Y).hom ≫
      P.map (totalHomEquiv P φ).1.op).hom x) same).trans ht)

/-- **Families in the doctrine.** Every dependent family on the states of a
world model descends to its profiles exactly when its extraction is
injective, that is, when the model loses nothing its world can ask. -/
theorem allFamiliesFactor_profile_iff {b : B} (X : Over (P.obj (op b))) :
    (∀ F : X.left → Type w, Nonempty (FamilyFactorization X.hom.hom F)) ↔
      Function.Injective X.hom.hom :=
  allFamiliesFactor_iff_injective _

/-- Positive control: the terminal world model, the profiles themselves,
supports every family. -/
theorem allFamiliesFactor_terminal (b : B) :
    ∀ F : (P.obj (op b)) → Type w,
      Nonempty (FamilyFactorization (Over.mk (𝟙 (P.obj (op b)))).hom.hom F) :=
  (allFamiliesFactor_iff_injective _).2 (fun _ _ same => same)

end Doctrine

end Mettapedia.Logic.WorldModel.Indexed
