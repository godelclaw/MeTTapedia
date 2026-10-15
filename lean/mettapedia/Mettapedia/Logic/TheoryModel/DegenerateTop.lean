import Mettapedia.Logic.TheoryModel.Consistency
import Mettapedia.Logic.TheoryModel.Weakness
import Mettapedia.Logic.TheoryModel.IdentityCarve

/-!
# The inconsistent top and degenerate structures

The largest theory, the set of all sentences, is the top of the theory
lattice.  Whether it has a model depends on the candidate structures.

* **Degenerate structures.**  A structure satisfying every sentence is
  degenerate (`Degenerate`).  The models of the top are exactly the degenerate
  structures (`models_univ_eq_degenerate`); they lie in every model class
  (`degenerate_subset_models`) and form the least elementary class
  (`degenerate_subset_of_isExtent`).
* **Two readings of the top.**  With an unsatisfiable sentence, for instance
  with negation, there is no degenerate structure and the top has no model
  (`models_univ_eq_empty_of_unsatisfiable`, `not_degenerate_of_negation`).  When
  a degenerate structure is among the candidates, as the one-point algebra is
  for an equational language, every theory is consistent
  (`consistent_of_degenerate`) and consistency stops separating theories.
* **No axiom carves a degenerate structure away** (`degenerate_mem_carve`): a
  carve-out adds sentences, and a degenerate structure satisfies them all.
  Excluding it is a choice of universe, the non-degenerate structures
  (`nondegenerate`), where the top again has no hosted model
  (`modelsIn_nondegenerate_univ`).
* **Weakness.**  The weakness of the top is the measure of the degenerate
  structures, and it bounds every theory's weakness from below
  (`weaknessOf_univ`, `le_weaknessOf_of_degenerate`); the empty theory has
  maximal weakness (`weaknessOf_empty`).

**Two languages side by side** (`sumSat`).  When a structure is a pair and each
sentence is read in its own component, a consistent theory in the second
component changes no consequence in the first (`entails_inl_iff`), and an
inconsistent one entails everything (`entails_of_not_consistent`).  The
instance that matters: the second language says which types are inhabited
(`inhabitedSat`).  Its top, every type inhabited, has exactly one model, the
permissive structure (`models_inhabited_univ`), so it is consistent in the
permissive universe and changes no consequence of the first language
(`permissive_top_conservative`), while it entails every inhabitation
(`permissive_top_inhabits`).  In the universe where a chosen type is empty it
has no model (`modelsIn_emptyType_univ`).

**Fragments of a top.**  A model of a theory is a model of every theory it
contains, and witnesses each of their non-consequences
(`not_entails_of_top_model`); a degenerate model witnesses none
(`degenerate_not_refutes`); no model of a theory lies in a universe that refutes
one of its consequences (`modelsIn_eq_empty_of_entails`).  For derivability,
non-derivability transfers down any judgment-preserving translation
(`Embeds.not_mem`), while closure under a relation transfers only along a
conservative one (`closedUnder_of_conservative`); the control
`ClosureControl.not_closed_fragment` is a fragment of a closed top that is not
closed.

**Weakness across a declared translation.**  Along a translation of structures
and sentences that preserves and reflects satisfaction, the host's weakness
order on translated theories is carried back to the guest
(`models_subset_of_translation`), and the guest's order is carried forward when
every host structure is the image of a guest structure
(`models_subset_translation_of_surjective`).  Without that coverage the host can
separate guest theories of equal weakness (`TranslationControl.host_separates`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel

open Set Order

universe uStr uSent uStr₁ uSent₁ uStr₂ uSent₂ uTy uW uJ uJ'

section Degenerate

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)

/-- A structure is degenerate when it satisfies every sentence. -/
def Degenerate (m : Str) : Prop :=
  ∀ φ, Sat m φ

/-- The degenerate structures. -/
def degenerate : Set Str :=
  {m | Degenerate Sat m}

/-- The structures refuting some sentence. -/
def nondegenerate : Set Str :=
  {m | ∃ φ, ¬ Sat m φ}

variable {Sat}

/-- **The models of the theory of all sentences are exactly the degenerate
structures.** -/
theorem models_univ_eq_degenerate : models Sat (univ : Set Sent) = degenerate Sat :=
  Set.ext fun _ => ⟨fun model φ => model (mem_univ φ), fun degenerate _ _ => degenerate _⟩

/-- A degenerate structure is a model of every theory. -/
theorem degenerate_subset_models (T : Set Sent) : degenerate Sat ⊆ models Sat T :=
  fun _ degenerate _ _ => degenerate _

/-- The degenerate structures form an elementary class. -/
theorem isExtent_degenerate : IsExtent Sat (degenerate Sat) :=
  ⟨univ, models_univ_eq_degenerate⟩

/-- **The degenerate structures form the least elementary class.** -/
theorem degenerate_subset_of_isExtent {K : Set Str} (elementary : IsExtent Sat K) :
    degenerate Sat ⊆ K := by
  obtain ⟨T, rfl⟩ := elementary
  exact degenerate_subset_models T

/-- **Tarskian reading**: with a sentence no structure satisfies, the theory of
all sentences has no model. -/
theorem models_univ_eq_empty_of_unsatisfiable {falsum : Sent}
    (unsatisfiable : ∀ m, ¬ Sat m falsum) : models Sat (univ : Set Sent) = ∅ :=
  eq_empty_of_forall_notMem fun m model => unsatisfiable m (model (mem_univ falsum))

/-- The theory of all sentences has no model exactly when no structure is
degenerate. -/
theorem models_univ_eq_empty_iff :
    models Sat (univ : Set Sent) = ∅ ↔ ∀ m, ¬ Degenerate Sat m := by
  rw [models_univ_eq_degenerate]
  exact ⟨fun empty m degenerate => (empty ▸ degenerate : m ∈ (∅ : Set Str)),
    fun none => eq_empty_of_forall_notMem fun m degenerate => none m degenerate⟩

/-- With a negation, no structure is degenerate. -/
theorem not_degenerate_of_negation (neg : Sent → Sent)
    (sat_neg : ∀ m φ, Sat m (neg φ) ↔ ¬ Sat m φ) (φ : Sent) (m : Str) :
    ¬ Degenerate Sat m :=
  fun degenerate => (sat_neg m φ).mp (degenerate (neg φ)) (degenerate φ)

/-- **Algebraic reading**: a degenerate structure makes every theory
consistent. -/
theorem consistent_of_degenerate {m : Str} (degenerate : Degenerate Sat m) (T : Set Sent) :
    Consistent Sat T :=
  ⟨m, fun _ _ => degenerate _⟩

/-- The theory of all sentences is consistent exactly when a degenerate
structure exists. -/
theorem consistent_univ_iff : Consistent Sat (univ : Set Sent) ↔ ∃ m, Degenerate Sat m :=
  ⟨fun ⟨m, model⟩ => ⟨m, fun φ => model (mem_univ φ)⟩,
    fun ⟨_, degenerate⟩ => consistent_of_degenerate degenerate univ⟩

/-- **No axiom carves a degenerate structure away.** -/
theorem degenerate_mem_carve {U : Set Str} {Φ : Set Sent} {m : Str} (hosted : m ∈ U)
    (degenerate : Degenerate Sat m) : m ∈ carve Sat U Φ :=
  ⟨hosted, fun _ _ => degenerate _⟩

/-- A non-degenerate structure is not degenerate. -/
theorem nondegenerate_subset_compl : nondegenerate Sat ⊆ (degenerate Sat)ᶜ :=
  fun _ ⟨φ, refuted⟩ degenerate => refuted (degenerate φ)

/-- Classically, the non-degenerate structures are exactly the others. -/
theorem nondegenerate_eq_compl : nondegenerate Sat = (degenerate Sat)ᶜ := by
  apply Subset.antisymm nondegenerate_subset_compl
  intro m notDegenerate
  by_contra none
  exact notDegenerate fun φ => by
    by_contra refuted
    exact none ⟨φ, refuted⟩

/-- In the universe of non-degenerate structures the theory of all sentences
has no hosted model. -/
theorem modelsIn_nondegenerate_univ : modelsIn Sat (nondegenerate Sat) (univ : Set Sent) = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨⟨φ, refuted⟩, model⟩ => refuted (model (mem_univ φ))

/-- A degenerate model refutes nothing, so it witnesses no non-consequence. -/
theorem degenerate_not_refutes {m : Str} (degenerate : Degenerate Sat m) (φ : Sent) :
    ¬ ¬ Sat m φ :=
  fun refuted => refuted (degenerate φ)

/-! ### Weakness of the top -/

section Measure

variable {W : Type uW}

/-- The weakness of the theory of all sentences is the measure of the
degenerate structures. -/
theorem weaknessOf_univ (μ : Set Str → W) :
    weaknessOf Sat μ (univ : Set Sent) = μ (degenerate Sat) := by
  unfold weaknessOf
  rw [models_univ_eq_degenerate]

/-- The degenerate structures bound every theory's weakness from below. -/
theorem le_weaknessOf_of_degenerate [Preorder W] {μ : Set Str → W}
    (monotone : MonotoneMeasure μ)
    (T : Set Sent) : μ (degenerate Sat) ≤ weaknessOf Sat μ T :=
  monotone (degenerate_subset_models T)

/-- The empty theory has every structure as a model: maximal weakness. -/
theorem weaknessOf_empty (μ : Set Str → W) :
    weaknessOf Sat μ (∅ : Set Sent) = μ univ := by
  unfold weaknessOf
  rw [models_empty]

end Measure

/-! ### Models of a top and its fragments -/

/-- **A model of a theory witnesses, for every theory it contains, each
sentence it refutes as a non-consequence.** -/
theorem not_entails_of_top_model {top fragment : Set Sent} (included : fragment ⊆ top)
    {m : Str} (model : m ∈ models Sat top) {φ : Sent} (refuted : ¬ Sat m φ) :
    ¬ Entails Sat fragment φ :=
  fun entails => refuted (entails (models_anti included model))

/-- No model of a theory lies in a universe that refutes one of its
consequences. -/
theorem modelsIn_eq_empty_of_entails {top : Set Sent} {U : Set Str} {φ : Sent}
    (entails : Entails Sat top φ) (refutedIn : ∀ m ∈ U, ¬ Sat m φ) :
    modelsIn Sat U top = ∅ :=
  eq_empty_of_forall_notMem fun m ⟨hosted, model⟩ => refutedIn m hosted (entails model)

end Degenerate

/-! ## Two languages side by side -/

section Sum

variable {Str₁ : Type uStr₁} {Sent₁ : Type uSent₁} {Str₂ : Type uStr₂} {Sent₂ : Type uSent₂}
  (Sat₁ : Str₁ → Sent₁ → Prop) (Sat₂ : Str₂ → Sent₂ → Prop)

/-- A structure is a pair, and each sentence is read in its own component. -/
def sumSat : Str₁ × Str₂ → Sent₁ ⊕ Sent₂ → Prop
  | m, .inl φ => Sat₁ m.1 φ
  | m, .inr ψ => Sat₂ m.2 ψ

/-- A theory in each language. -/
def sumTheory (T₁ : Set Sent₁) (T₂ : Set Sent₂) : Set (Sent₁ ⊕ Sent₂) :=
  Sum.inl '' T₁ ∪ Sum.inr '' T₂

variable {Sat₁ Sat₂}

/-- The models of a pair of theories are the pairs of models. -/
theorem models_sumTheory (T₁ : Set Sent₁) (T₂ : Set Sent₂) :
    models (sumSat Sat₁ Sat₂) (sumTheory T₁ T₂) = models Sat₁ T₁ ×ˢ models Sat₂ T₂ := by
  ext m
  constructor
  · intro model
    exact ⟨fun φ member => model (Or.inl ⟨φ, member, rfl⟩),
      fun ψ member => model (Or.inr ⟨ψ, member, rfl⟩)⟩
  · rintro ⟨first, second⟩ χ (⟨φ, member, rfl⟩ | ⟨ψ, member, rfl⟩)
    · exact first member
    · exact second member

/-- **A consistent theory in the second language changes no consequence in the
first.** -/
theorem entails_inl_iff {T₁ : Set Sent₁} {T₂ : Set Sent₂} (consistent : Consistent Sat₂ T₂)
    {φ : Sent₁} :
    Entails (sumSat Sat₁ Sat₂) (sumTheory T₁ T₂) (.inl φ) ↔ Entails Sat₁ T₁ φ := by
  obtain ⟨n, secondModel⟩ := consistent
  constructor
  · intro entails m firstModel
    have model : (m, n) ∈ models (sumSat Sat₁ Sat₂) (sumTheory T₁ T₂) := by
      rw [models_sumTheory]
      exact ⟨firstModel, secondModel⟩
    exact entails model
  · intro entails m model
    rw [models_sumTheory] at model
    exact entails model.1

/-- An inconsistent theory in the second language entails every sentence. -/
theorem entails_of_not_consistent {T₁ : Set Sent₁} {T₂ : Set Sent₂}
    (inconsistent : ¬ Consistent Sat₂ T₂) (χ : Sent₁ ⊕ Sent₂) :
    Entails (sumSat Sat₁ Sat₂) (sumTheory T₁ T₂) χ := by
  intro m model
  rw [models_sumTheory] at model
  exact (inconsistent ⟨m.2, model.2⟩).elim

end Sum

/-! ## The permissive top: every type inhabited -/

section Inhabitation

variable {Ty : Type uTy}

/-- A structure of the inhabitation language says which types are inhabited. -/
def inhabitedSat (inhabited : Set Ty) (A : Ty) : Prop :=
  A ∈ inhabited

/-- **The theory "every type is inhabited" has exactly one model, the
permissive structure.** -/
theorem models_inhabited_univ : models inhabitedSat (univ : Set Ty) = {univ} := by
  ext inhabited
  constructor
  · intro model
    exact eq_univ_of_forall fun A => model (mem_univ A)
  · rintro rfl A _
    exact mem_univ A

/-- It is consistent among all structures. -/
theorem consistent_inhabited_univ : Consistent inhabitedSat (univ : Set Ty) :=
  ⟨univ, fun A _ => mem_univ A⟩

/-- The structures in which a chosen type is empty. -/
def emptyType (empty : Ty) : Set (Set Ty) :=
  {inhabited | empty ∉ inhabited}

/-- In the universe where a chosen type is empty, the theory "every type is
inhabited" has no model. -/
theorem modelsIn_emptyType_univ (empty : Ty) :
    modelsIn inhabitedSat (emptyType empty) (univ : Set Ty) = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨notInhabited, model⟩ => notInhabited (model (mem_univ empty))

variable {Str₁ : Type uStr₁} {Sent₁ : Type uSent₁} {Sat₁ : Str₁ → Sent₁ → Prop}

/-- **The permissive top changes no consequence of the first language.** -/
theorem permissive_top_conservative {T₁ : Set Sent₁} {φ : Sent₁} :
    Entails (sumSat Sat₁ inhabitedSat) (sumTheory T₁ (univ : Set Ty)) (.inl φ) ↔
      Entails Sat₁ T₁ φ :=
  entails_inl_iff consistent_inhabited_univ

/-- **The permissive top entails that every type is inhabited.** -/
theorem permissive_top_inhabits {T₁ : Set Sent₁} (A : Ty) :
    Entails (sumSat Sat₁ inhabitedSat) (sumTheory T₁ (univ : Set Ty)) (.inr A) := by
  intro m model
  rw [models_sumTheory, models_inhabited_univ] at model
  have permissive : m.2 = univ := model.2
  show A ∈ m.2
  rw [permissive]
  exact mem_univ A

end Inhabitation

/-! ## Derivability: what transfers from a top to a fragment -/

section Derivability

variable {J : Type uJ} {J' : Type uJ'}

/-- A fragment embeds into a top along a translation of judgments when every
judgment it derives translates to one the top derives. -/
def Embeds (fragment : Set J) (top : Set J') (translate : J → J') : Prop :=
  ∀ j ∈ fragment, translate j ∈ top

/-- The embedding is conservative when the fragment derives every judgment
whose translation the top derives. -/
def Conservative (fragment : Set J) (top : Set J') (translate : J → J') : Prop :=
  ∀ j, translate j ∈ top → j ∈ fragment

/-- A set of derivable judgments is closed under a relation, for instance
reduction of the subject of a typing judgment. -/
def ClosedUnder (derivable : Set J) (step : J → J → Prop) : Prop :=
  ∀ j ∈ derivable, ∀ k, step j k → k ∈ derivable

/-- **Non-derivability transfers down every embedding.** -/
theorem Embeds.not_mem {fragment : Set J} {top : Set J'} {translate : J → J'}
    (embeds : Embeds fragment top translate) {j : J} (notTop : translate j ∉ top) :
    j ∉ fragment :=
  fun derived => notTop (embeds j derived)

/-- **Closure transfers down a conservative embedding** that carries the
fragment's steps to the top's. -/
theorem closedUnder_of_conservative {fragment : Set J} {top : Set J'} {translate : J → J'}
    {step : J → J → Prop} {step' : J' → J' → Prop}
    (embeds : Embeds fragment top translate) (conservative : Conservative fragment top translate)
    (closed : ClosedUnder top step') (carries : ∀ j k, step j k → step' (translate j) (translate k)) :
    ClosedUnder fragment step :=
  fun j derived k stepped =>
    conservative k (closed (translate j) (embeds j derived) (translate k) (carries j k stepped))

namespace ClosureControl

/-- Two judgments, and a step from the first to the second. -/
def step : Bool → Bool → Prop :=
  fun j k => j = false ∧ k = true

/-- The top derives both judgments and is closed under the step. -/
def top : Set Bool := univ

/-- The fragment derives only the first. -/
def fragment : Set Bool := {false}

theorem top_closed : ClosedUnder top step :=
  fun _ _ k _ => mem_univ k

theorem fragment_embeds : Embeds fragment top id :=
  fun j _ => mem_univ j

/-- **A fragment of a closed top need not be closed**: the embedding is not
conservative. -/
theorem not_closed_fragment : ¬ ClosedUnder fragment step := by
  intro closed
  have derived : true ∈ fragment := closed false rfl true ⟨rfl, rfl⟩
  exact Bool.noConfusion (derived : true = false)

theorem not_conservative : ¬ Conservative fragment top id := by
  intro conservative
  exact not_closed_fragment
    (closedUnder_of_conservative fragment_embeds conservative top_closed fun _ _ stepped => stepped)

end ClosureControl

end Derivability

/-! ## Weakness across a declared translation -/

section Translation

variable {Str : Type uStr} {Sent : Type uSent} {Str' : Type uStr₂} {Sent' : Type uSent₂}
  {Sat : Str → Sent → Prop} {Sat' : Str' → Sent' → Prop}

/-- **The host's weakness order on translated theories is carried back to the
guest.** -/
theorem models_subset_of_translation (f : Str → Str') (g : Sent → Sent')
    (sat_iff : ∀ m φ, Sat m φ ↔ Sat' (f m) (g φ)) {T T' : Set Sent}
    (hostOrder : models Sat' (g '' T') ⊆ models Sat' (g '' T)) :
    models Sat T' ⊆ models Sat T := by
  rw [models_eq_preimage f g sat_iff T', models_eq_preimage f g sat_iff T]
  exact Set.preimage_mono hostOrder

/-- **The guest's weakness order is carried forward when every host structure
is the image of a guest structure.** -/
theorem models_subset_translation_of_surjective (f : Str → Str') (g : Sent → Sent')
    (sat_iff : ∀ m φ, Sat m φ ↔ Sat' (f m) (g φ)) (surjective : Function.Surjective f)
    {T T' : Set Sent} (guestOrder : models Sat T' ⊆ models Sat T) :
    models Sat' (g '' T') ⊆ models Sat' (g '' T) := by
  intro m' model'
  obtain ⟨m, rfl⟩ := surjective m'
  have model : m ∈ models Sat T' := by
    rw [models_eq_preimage f g sat_iff T']
    exact model'
  have weaker := guestOrder model
  rw [models_eq_preimage f g sat_iff T] at weaker
  exact weaker

namespace TranslationControl

/-- A guest with one structure satisfying both sentences. -/
def guestSat : Unit → Bool → Prop :=
  fun _ _ => True

/-- A host with a second structure that refutes `false`. -/
def hostSat : Bool → Bool → Prop :=
  fun m φ => m = true ∨ φ = true

theorem sat_iff : ∀ m φ, guestSat m φ ↔ hostSat ((fun _ => true) m) (id φ) :=
  fun _ _ => ⟨fun _ => Or.inl rfl, fun _ => trivial⟩

/-- **The host separates two guest theories of equal weakness**: the guest has
the same models for `{false}` and `{true}`, while the host's models of the
translated `{true}` are not among those of the translated `{false}`. -/
theorem host_separates :
    models guestSat ({false} : Set Bool) = models guestSat {true} ∧
      ¬ models hostSat (id '' ({true} : Set Bool)) ⊆ models hostSat (id '' {false}) := by
  constructor
  · ext m
    exact ⟨fun _ _ _ => trivial, fun _ _ _ => trivial⟩
  · intro included
    have model : false ∈ models hostSat (id '' ({true} : Set Bool)) := by
      rintro φ ⟨ψ, member, rfl⟩
      exact Or.inr member
    have refuted := included model ⟨false, rfl, rfl⟩
    rcases refuted with impossible | impossible <;> exact Bool.noConfusion impossible

end TranslationControl

end Translation

end Mettapedia.Logic.TheoryModel
