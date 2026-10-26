import Mettapedia.Languages.MeTTa.DeclarationFaces.Admission
import Mettapedia.Languages.MeTTa.DeclarationFaces.Controls
import Mettapedia.Languages.MeTTa.TransformQuantifiers
import Mettapedia.Languages.MeTTa.DeclarationFaces.CollectionTypes

/-!
# Space rules as typed declarations: formation typing of transforms and preservation

A store holds atoms of one declared element sort: `(Store T)`. A transform reads or takes atoms
matching its source patterns and writes its sink templates at the commit, one row per match.

* **Formation typing** (`TransformDecl.WellTyped`): in one context of sorts for the pattern
  variables, every source pattern is a constructor pattern of sort `T`, every sink has sort `T`, and
  every sink variable is bound by a source. Sources may share variables: a join.
* **The check** (`checkTransform`, `checkTransform_sound`): the variable sorts are inferred from the
  source patterns at `T`, required to agree where a variable occurs twice, and the sinks are checked at
  `T` with the machinery of equation typing.
* **Preservation** (`fires_typed`, `firesSet_typed`): a firing of a well-typed transform maps a
  well-typed store to a well-typed store, for bag stores (the commit is the transform study's
  `Footprints.fire`) and for set stores.
* **Keep and consume over the two store kinds** (`support_fire_keepOnly`,
  `Controls.support_fire_take_differs`): the support of a bag store follows a keep-only firing on
  the set store, so a set store computes the support of the bag store's facts (the
  semiring-annotated store of `GSLT.Causality.SemiringFactStores`, `mem_saturation_iff_presence`);
  with a take it does not: consuming one of two copies leaves the fact present in the bag and absent
  from the set.

Negative control: a Petri net step whose sink writes `(tok red)` into a store of tokens on places is
refused by the check (`Controls.illTyped_refused`), and firing it from a well-typed store gives a store
that is not well typed (`Controls.illTyped_breaks_preservation`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm
open Mettapedia.Languages.MeTTa.TransformQuantifiers (Footprints)

universe u

variable {S : Type u} [DecidableEq S]

/-- Whether a source reads or takes its atom. -/
inductive Mode where
  | read
  | take
  deriving DecidableEq, Repr

/-- A source: a mode and a pattern. -/
structure Source (S : Type u) where
  mode : Mode
  pattern : Tm S

/-- **A transform**: its sources and the sink templates it writes. -/
structure TransformDecl (S : Type u) where
  sources : List (Source S)
  sinks : List (Tm S)

namespace TransformDecl

variable (t : TransformDecl S)

/-- What a row takes: the instances of the take sources. -/
def rowTake (σ : String → Tm S) : Multiset (Tm S) :=
  ((t.sources.filter fun s => s.mode = .take).map fun s => s.pattern.subst σ : List (Tm S))

/-- What a row writes: the instances of the sinks. -/
def rowWrite (σ : String → Tm S) : Multiset (Tm S) := (t.sinks.map (Tm.subst σ) : List (Tm S))

/-- The rows of a transform, as footprints of the transform study. -/
def footprints : Footprints (String → Tm S) (Tm S) := ⟨t.rowTake, t.rowWrite⟩

/-- A row at a store: every source's instance is in the store. -/
def Row (M : Multiset (Tm S)) (σ : String → Tm S) : Prop :=
  ∀ s ∈ t.sources, s.pattern.subst σ ∈ M

/-- **A firing at a bag store**: an enabled row is committed. -/
def Fires (M N : Multiset (Tm S)) : Prop :=
  ∃ σ, t.Row M σ ∧ t.rowTake σ ≤ M ∧ N = t.footprints.fire M σ

/-- **A firing at a set store**: what the row takes is removed, what it writes is added. -/
def FiresSet (M N : Finset (Tm S)) : Prop :=
  ∃ σ, (∀ s ∈ t.sources, s.pattern.subst σ ∈ M) ∧
    N = (M \ (t.rowTake σ).toFinset) ∪ (t.rowWrite σ).toFinset

/-- Every sink variable is bound by a source. -/
def SinksBound : Prop := ∀ w ∈ t.sinks, ∀ x ∈ w.vars, ∃ s ∈ t.sources, x ∈ s.pattern.vars

/-- **Formation typing** of a transform against a store's element sort. -/
def WellTyped (sig : Signature S) (T : Sort') : Prop :=
  t.SinksBound ∧ ∃ Γ : Ctx, (∀ s ∈ t.sources, IsPattern sig s.pattern ∧ HasSort sig Γ s.pattern T) ∧
    ∀ w ∈ t.sinks, HasSort sig Γ w T

end TransformDecl

/-- **A well-typed store**: every atom has the store's element sort. -/
def StoreTyped (sig : Signature S) (T : Sort') (M : Multiset (Tm S)) : Prop :=
  ∀ a ∈ M, HasSort sig Ctx.empty a T

theorem subst_id_sort (τ : Sort') : τ.subst Tm.var = τ := subst_id τ

omit [DecidableEq S] in
/-- The instantiating terms of a row at a well-typed store have the sorts of the variables. -/
theorem row_typed {sig : Signature S} (wf : sig.WellFormed) {t : TransformDecl S} {T : Sort'}
    {Γ : Ctx} (sources : ∀ s ∈ t.sources, IsPattern sig s.pattern ∧ HasSort sig Γ s.pattern T)
    {σ : String → Tm S} {M : Multiset (Tm S)} (row : ∀ s ∈ t.sources, s.pattern.subst σ ∈ M)
    (typedStore : ∀ a ∈ M, HasSort sig Ctx.empty a T) :
    ∀ s ∈ t.sources, ∀ x ∈ s.pattern.vars, ∀ τx, Γ x = some τx → HasSort sig Ctx.empty (σ x) τx := by
  intro s hs x hx τx hτ
  obtain ⟨pattern, typed⟩ := sources s hs
  have inst := typedStore _ (row s hs)
  have := HasSort.pattern_inversion wf σ Tm.var typed pattern (by rwa [subst_id_sort]) x hx τx hτ
  rwa [subst_id_sort] at this

omit [DecidableEq S] in
/-- The sinks of a row at a well-typed store have the store's sort. -/
theorem rowWrite_typed {sig : Signature S} (wf : sig.WellFormed) {t : TransformDecl S} {T : Sort'}
    (typed : t.WellTyped sig T) {σ : String → Tm S} {M : Multiset (Tm S)}
    (row : ∀ s ∈ t.sources, s.pattern.subst σ ∈ M)
    (typedStore : ∀ a ∈ M, HasSort sig Ctx.empty a T) :
    ∀ a ∈ t.rowWrite σ, HasSort sig Ctx.empty a T := by
  obtain ⟨bound, Γ, sources, sinks⟩ := typed
  intro a ha
  simp only [TransformDecl.rowWrite, Multiset.mem_coe, List.mem_map] at ha
  obtain ⟨w, hw, rfl⟩ := ha
  apply HasSort.substTerm σ (sinks w hw)
  intro x hx τx hτ
  obtain ⟨s, hs, hxs⟩ := bound w hw x hx
  exact row_typed wf sources row typedStore s hs x hxs τx hτ

/-- **Preservation at a bag store**: a firing of a well-typed transform maps a well-typed store to a
well-typed store. -/
theorem fires_typed {sig : Signature S} (wf : sig.WellFormed) {t : TransformDecl S} {T : Sort'}
    (typed : t.WellTyped sig T) {M N : Multiset (Tm S)} (typedStore : StoreTyped sig T M)
    (fires : t.Fires M N) : StoreTyped sig T N := by
  obtain ⟨σ, row, _, rfl⟩ := fires
  intro a ha
  simp only [Footprints.fire, TransformDecl.footprints] at ha
  rcases Multiset.mem_add.mp ha with kept | written
  · exact typedStore a (Multiset.mem_of_le (Multiset.sub_le_self _ _) kept)
  · exact rowWrite_typed wf typed row typedStore a written

/-- **Preservation at a set store.** -/
theorem firesSet_typed {sig : Signature S} (wf : sig.WellFormed) {t : TransformDecl S} {T : Sort'}
    (typed : t.WellTyped sig T) {M N : Finset (Tm S)}
    (typedStore : ∀ a ∈ M, HasSort sig Ctx.empty a T) (fires : t.FiresSet M N) :
    ∀ a ∈ N, HasSort sig Ctx.empty a T := by
  obtain ⟨σ, row, rfl⟩ := fires
  intro a ha
  rcases Finset.mem_union.mp ha with kept | written
  · exact typedStore a (Finset.mem_sdiff.mp kept).1
  · exact rowWrite_typed wf typed (M := M.val) row (fun b hb => typedStore b hb) a
      (Multiset.mem_toFinset.mp written)

/-- **Keep-only rules: the set store follows the support of the bag store.** -/
theorem support_fire_keepOnly {t : TransformDecl S} (keepOnly : ∀ s ∈ t.sources, s.mode = .read)
    (M : Multiset (Tm S)) (σ : String → Tm S) :
    (t.footprints.fire M σ).toFinset = (M.toFinset \ (t.rowTake σ).toFinset) ∪ (t.rowWrite σ).toFinset := by
  have noTake : t.rowTake σ = 0 := by
    simp only [TransformDecl.rowTake, Multiset.coe_eq_zero, List.map_eq_nil_iff,
      List.filter_eq_nil_iff, decide_eq_true_eq]
    intro s hs same
    rw [keepOnly s hs] at same
    cases same
  simp [Footprints.fire, TransformDecl.footprints, noTake, Multiset.toFinset_add]

/-! ## The formation check -/

/-- The sorts the source patterns give their variables, at the store's sort. -/
def sourceBindings (sig : Signature S) (T : Sort') : List (Source S) → Option (List (String × Sort'))
  | [] => some []
  | s :: rest =>
      match inferPattern sig s.pattern T, sourceBindings sig T rest with
      | some a, some b => some (a ++ b)
      | _, _ => none

/-- **The formation check of a transform.** -/
def checkTransform (sig : Signature S) (t : TransformDecl S) (T : Sort') : Bool :=
  match sourceBindings sig T t.sources with
  | some bindings =>
      decide (∀ pair ∈ bindings, ctxOf bindings pair.1 = some pair.2) &&
        t.sinks.all (fun w => checkTm sig (ctxOf bindings) w T) &&
        decide (∀ w ∈ t.sinks, ∀ x ∈ w.vars, ∃ s ∈ t.sources, x ∈ s.pattern.vars)
  | none => false

theorem sourceBindings_sound {sig : Signature S} (wf : sig.WellFormed) {T : Sort'} :
    ∀ {sources : List (Source S)} {bindings : List (String × Sort')},
      sourceBindings sig T sources = some bindings →
        ∀ Γ : Ctx, (∀ pair ∈ bindings, Γ pair.1 = some pair.2) →
          ∀ s ∈ sources, IsPattern sig s.pattern ∧ HasSort sig Γ s.pattern T
  | [], bindings, _, Γ, _, s, hs => absurd hs List.not_mem_nil
  | s :: rest, bindings, h, Γ, hΓ, s', hs' => by
      simp only [sourceBindings] at h
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hs' with rfl | later
        · obtain ⟨_, pattern, typed⟩ := inferPattern_sound wf _ _ a ha
          exact ⟨pattern, typed Γ fun pair m => hΓ pair (List.mem_append_left _ m)⟩
        · exact sourceBindings_sound wf hb Γ (fun pair m => hΓ pair (List.mem_append_right _ m)) s'
            later
      · cases h

/-- **The formation check is sound.** -/
theorem checkTransform_sound {sig : Signature S} (wf : sig.WellFormed) {t : TransformDecl S}
    {T : Sort'} (h : checkTransform sig t T = true) : t.WellTyped sig T := by
  unfold checkTransform at h
  split at h
  · rename_i bindings hb
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨consistent, sinks⟩, bound⟩ := h
    exact ⟨bound, ctxOf bindings, sourceBindings_sound wf hb _ consistent,
      fun w hw => checkTm_sound wf _ w T (sinks w hw)⟩
  · cases h

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.MeTTa.DeclarationFaces.Controls (num)

/-- Places, colours, and tokens on places. -/
def petriSig : Signature String :=
  ⟨[⟨"Place", [], [("P1", []), ("P2", []), ("P3", [])]⟩,
    ⟨"Colour", [], [("red", [])]⟩,
    ⟨"Token", [], [("tok", [.app "Place" []])]⟩], []⟩

/-- The sort of the store's atoms. -/
abbrev token : Sort' := .app "Token" []

theorem petriSig_wf : petriSig.WellFormed := by decide

/-- `(transform &net (, (take (tok P1)) (take (tok P2))) (tok P3))`. -/
def petriStep : TransformDecl String :=
  ⟨[⟨.take, .app "tok" [.app "P1" []]⟩, ⟨.take, .app "tok" [.app "P2" []]⟩],
   [.app "tok" [.app "P3" []]]⟩

/-- The same step writing `(tok red)`. -/
def illTypedStep : TransformDecl String :=
  ⟨[⟨.take, .app "tok" [.app "P1" []]⟩, ⟨.take, .app "tok" [.app "P2" []]⟩],
   [.app "tok" [.app "red" []]]⟩

/-- **Positive control**: the Petri net step is well typed against a store of tokens. -/
theorem petriStep_typed : petriStep.WellTyped petriSig token :=
  checkTransform_sound petriSig_wf (by decide)

/-- **Negative control**: the step writing `(tok red)` is refused. -/
theorem illTyped_refused : checkTransform petriSig illTypedStep token = false := by decide

/-- A marking with one token on each of the first two places. -/
def marking : Multiset (Tm String) := {.app "tok" [.app "P1" []], .app "tok" [.app "P2" []]}

theorem tok_typed (p : String) (hp : p ∈ ["P1", "P2", "P3"]) :
    HasSort petriSig Ctx.empty (.app "tok" [.app p []]) token := by
  have place : HasSort petriSig Ctx.empty (.app p []) (.app "Place" []) := by
    have := HasSort.ctor (sig := petriSig) (Γ := Ctx.empty)
      (d := ⟨"Place", [], [("P1", []), ("P2", []), ("P3", [])]⟩) (c := p) (fields := [])
      (args := []) Tm.var (by simp [petriSig]) (by simp at hp; rcases hp with rfl | rfl | rfl <;> simp)
      rfl (fun i hi => absurd hi (by simp))
    simpa [DataDecl.sort] using this
  have := HasSort.ctor (sig := petriSig) (Γ := Ctx.empty)
    (d := ⟨"Token", [], [("tok", [.app "Place" []])]⟩) (c := "tok") (fields := [.app "Place" []])
    (args := [.app p []]) Tm.var (by simp [petriSig]) (by simp) rfl fun i hi hj => by
      have : i = 0 := by simpa using hi
      subst this
      simpa using place
  simpa [DataDecl.sort] using this

theorem marking_typed : StoreTyped petriSig token marking := by
  intro a ha
  simp only [marking, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact tok_typed "P1" (by simp)
  · exact tok_typed "P2" (by simp)

/-- **Positive control**: the Petri net step fires on the marking, and the result is well typed. -/
theorem petri_fires :
    petriStep.Fires marking {.app "tok" [.app "P3" []]} ∧
      StoreTyped petriSig token {.app "tok" [.app "P3" []]} := by
  have fires : petriStep.Fires marking {.app "tok" [.app "P3" []]} :=
    ⟨Tm.var, fun s hs => by
      simp only [petriStep, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> simp [marking],
     by decide, by decide⟩
  exact ⟨fires, fires_typed petriSig_wf petriStep_typed marking_typed fires⟩

/-- `(tok red)` has no sort. -/
theorem tok_red_untyped (τ : Sort') :
    ¬ HasSort petriSig Ctx.empty (.app "tok" [.app "red" []]) τ := by
  intro typed
  rcases HasSort.app_inv typed with ⟨d, hd, fields, hc, θ, _, len, args⟩ | ⟨fd, hfd, _, _, _, _⟩
  · simp only [petriSig, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · simp at hc
    · simp at hc
    · simp only [List.mem_singleton, Prod.mk.injEq, true_and] at hc
      subst hc
      have inner := args 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at inner
      rcases HasSort.app_inv inner with ⟨d', hd', fields', hc', θ', hsort, _, _⟩ |
          ⟨fd, hfd, _, _, _, _⟩
      · simp only [petriSig, List.mem_cons, List.not_mem_nil, or_false] at hd'
        rcases hd' with rfl | rfl | rfl
        · simp at hc'
        · simp [DataDecl.sort] at hsort
        · simp at hc'
      · simp [petriSig] at hfd
  · simp [petriSig] at hfd

/-- **Negative control**: firing the ill-typed step from a well-typed store gives a store that is
not well typed: preservation fails without formation typing. -/
theorem illTyped_breaks_preservation :
    illTypedStep.Fires marking {.app "tok" [.app "red" []]} ∧
      ¬ StoreTyped petriSig token {.app "tok" [.app "red" []]} := by
  refine ⟨⟨Tm.var, fun s hs => ?_, by decide, by decide⟩, fun typed => ?_⟩
  · simp only [illTypedStep, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp [marking]
  · exact tok_red_untyped token (typed _ (by simp))

/-- Two copies of a fact, and a rule that takes one. -/
def twoCopies : Multiset (Tm String) := {.app "tok" [.app "P1" []], .app "tok" [.app "P1" []]}

/-- `(transform &s (take (tok P1)) ())`. -/
def takeOne : TransformDecl String := ⟨[⟨.take, .app "tok" [.app "P1" []]⟩], []⟩

/-- **Consume over the two store kinds differs**: taking one of two copies leaves the fact in the
bag store's support and removes it from the set store. -/
theorem support_fire_take_differs :
    (takeOne.footprints.fire twoCopies Tm.var).toFinset ≠
      (twoCopies.toFinset \ (takeOne.rowTake Tm.var).toFinset) ∪ (takeOne.rowWrite Tm.var).toFinset := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.DeclarationFaces
