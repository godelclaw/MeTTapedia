import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder
import Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula

/-!
# Embedding the modal μ-calculus

A μ-calculus formula over actions reads in a labelled transition system. It embeds into the generated
formulas over a native structure that realizes the system. Each action names a step label and a
direction, and the system's transitions are the structure's steps with that label, forwards or
backwards (`Realizes`).

- **Polarity.** μ-calculus formulas have negation, and generated formulas are in negation normal form.
  The embedding translates a negation's body at the opposite polarity; a fixed point at negative
  polarity becomes its dual (`ofMu`).
- **Exactness** (`sat_ofMu`): a formula embeds exactly, at both polarities, when every fixed-point
  variable occurs at the polarity of its binder (`muConsistent`), the usual positivity of μ-calculus
  formulas. Without it the readings differ: `μX. ¬X` holds everywhere, and its embedding nowhere.
- **Traversals** (`realizes_transitionSystem`, `satisfies_iff_sat`): the future and past of the step
  span of any native structure are its forward and backward steps. So the μ-calculus that the explored
  graphs, the finite checkers and the certificates speak is a fragment of the generated logic.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings

open Mettapedia.Logic.ModalMuCalculus (LTS satisfies)

universe u v

variable {Act : Type v} (modality : Act → Direction × StepLabel)

/-- Some step of the action leads to the formula. -/
def someStep {n : ℕ} (action : Act) (formula : Formula n) : Formula n :=
  match modality action with
  | (.forward, label) => .possibly label formula
  | (.backward, label) => .sometimeBefore label formula

/-- Every step of the action leads to the formula. -/
def everyStep {n : ℕ} (action : Act) (formula : Formula n) : Formula n :=
  match modality action with
  | (.forward, label) => .necessarily label formula
  | (.backward, label) => .alwaysBefore label formula

/-- **A μ-calculus formula as a generated formula**, at a polarity: the formula itself at `true`, its
negation at `false`. -/
def ofMu : {n : ℕ} → Bool → Mettapedia.Logic.ModalMuCalculus.Formula Act n → Formula n
  | _, true, .tt => .top
  | _, false, .tt => .bot
  | _, true, .ff => .bot
  | _, false, .ff => .top
  | _, polarity, .neg inner => ofMu (!polarity) inner
  | _, true, .conj left right => .and (ofMu true left) (ofMu true right)
  | _, false, .conj left right => .or (ofMu false left) (ofMu false right)
  | _, true, .disj left right => .or (ofMu true left) (ofMu true right)
  | _, false, .disj left right => .and (ofMu false left) (ofMu false right)
  | _, true, .diamond action inner => someStep modality action (ofMu true inner)
  | _, false, .diamond action inner => everyStep modality action (ofMu false inner)
  | _, true, .box action inner => everyStep modality action (ofMu true inner)
  | _, false, .box action inner => someStep modality action (ofMu false inner)
  | _, true, .mu body => .mu (ofMu true body)
  | _, false, .mu body => .nu (ofMu false body)
  | _, true, .nu body => .nu (ofMu true body)
  | _, false, .nu body => .mu (ofMu false body)
  | _, _, .var index => .var index

/-- **Every fixed-point variable occurs at the polarity of its binder.** `signs` gives the polarities of
the free ones; a negation flips the polarity. -/
def muConsistent : {n : ℕ} → (Fin n → Bool) → Bool → Mettapedia.Logic.ModalMuCalculus.Formula Act n → Bool
  | _, _, _, .tt | _, _, _, .ff => true
  | _, signs, polarity, .neg inner => muConsistent signs (!polarity) inner
  | _, signs, polarity, .conj left right | _, signs, polarity, .disj left right =>
    muConsistent signs polarity left && muConsistent signs polarity right
  | _, signs, polarity, .diamond _ inner | _, signs, polarity, .box _ inner => muConsistent signs polarity inner
  | _, signs, polarity, .mu body | _, signs, polarity, .nu body =>
    muConsistent (Fin.cons polarity signs) polarity body
  | _, signs, polarity, .var index => signs index == polarity

variable {Carrier : Type u}

/-- **A native structure realizes a transition system** when each action's transitions are the steps
with its label, in its direction. -/
def Realizes (S : NativeStructure Carrier) (lts : LTS Carrier Act) : Prop :=
  ∀ source action target, lts.trans source action target ↔
    match modality action with
    | (.forward, label) => S.step source label target
    | (.backward, label) => S.step target label source

/-- A generated environment that agrees with a μ-calculus environment, complemented at the negative
variables. -/
def MuAgrees {n : ℕ} (valuation : Mettapedia.Logic.ModalMuCalculus.Env Carrier n) (signs : Fin n → Bool)
    (env : Env Carrier n) : Prop :=
  ∀ index element, element ∈ env index ↔ cond (signs index) (element ∈ valuation index) (element ∉ valuation index)

theorem MuAgrees.extend {n : ℕ} {valuation : Mettapedia.Logic.ModalMuCalculus.Env Carrier n} {signs : Fin n → Bool}
    {env : Env Carrier n} (agrees : MuAgrees valuation signs env) (sign : Bool) (candidate set : Set Carrier)
    (same : ∀ element, element ∈ set ↔ cond sign (element ∈ candidate) (element ∉ candidate)) :
    MuAgrees (valuation.extend candidate) (Fin.cons sign signs) (env.extend set) := by
  intro index element
  refine Fin.cases ?_ (fun index => ?_) index
  · simpa [Mettapedia.Logic.ModalMuCalculus.Env.extend, Env.extend] using same element
  · have := agrees index element
    simpa [Mettapedia.Logic.ModalMuCalculus.Env.extend, Env.extend] using this

variable {modality}

theorem sat_someStep {S : NativeStructure Carrier} {lts : LTS Carrier Act} (realizes : Realizes modality S lts)
    {n : ℕ} (env : Env Carrier n) (action : Act) (formula : Formula n) (holds : Carrier → Prop)
    (same : ∀ element, S.sat env formula element ↔ holds element) (element : Carrier) :
    S.sat env (someStep modality action formula) element ↔ ∃ next, lts.trans element action next ∧ holds next := by
  unfold someStep
  have key := fun next => realizes element action next
  rcases direction : modality action with ⟨_ | _, label⟩ <;> simp only [direction] at key ⊢
  · exact exists_congr fun next => and_congr (key next).symm (same next)
  · exact exists_congr fun next => and_congr (key next).symm (same next)

theorem sat_everyStep {S : NativeStructure Carrier} {lts : LTS Carrier Act} (realizes : Realizes modality S lts)
    {n : ℕ} (env : Env Carrier n) (action : Act) (formula : Formula n) (holds : Carrier → Prop)
    (same : ∀ element, S.sat env formula element ↔ holds element) (element : Carrier) :
    S.sat env (everyStep modality action formula) element ↔ ∀ next, lts.trans element action next → holds next := by
  unfold everyStep
  have key := fun next => realizes element action next
  rcases direction : modality action with ⟨_ | _, label⟩ <;> simp only [direction] at key ⊢
  · exact forall_congr' fun next => imp_congr (key next).symm (same next)
  · exact forall_congr' fun next => imp_congr (key next).symm (same next)

/-- **μ-calculus formulas embed exactly**, at both polarities, when their fixed-point variables occur at
the polarity of their binders. -/
theorem sat_ofMu {S : NativeStructure Carrier} {lts : LTS Carrier Act} (realizes : Realizes modality S lts) :
    ∀ {n : ℕ} (formula : Mettapedia.Logic.ModalMuCalculus.Formula Act n) {polarity : Bool} {signs : Fin n → Bool}
      {valuation : Mettapedia.Logic.ModalMuCalculus.Env Carrier n} {env : Env Carrier n},
      muConsistent signs polarity formula = true → MuAgrees valuation signs env → ∀ element,
        (S.sat env (ofMu modality polarity formula) element ↔
          cond polarity (satisfies lts valuation formula element) (¬ satisfies lts valuation formula element))
  | _, .tt, polarity, _, _, _, _, _, _ => by cases polarity <;> simp [ofMu, NativeStructure.sat, satisfies]
  | _, .ff, polarity, _, _, _, _, _, _ => by cases polarity <;> simp [ofMu, NativeStructure.sat, satisfies]
  | _, .neg inner, polarity, _, _, _, coherent, agrees, element => by
    simp only [muConsistent] at coherent
    have := sat_ofMu realizes inner coherent agrees element
    cases polarity
    · simpa [ofMu, satisfies] using this
    · simpa [ofMu, satisfies] using this
  | _, .conj left right, polarity, _, _, _, coherent, agrees, element => by
    simp only [muConsistent, Bool.and_eq_true] at coherent
    have first := sat_ofMu realizes left coherent.1 agrees element
    have second := sat_ofMu realizes right coherent.2 agrees element
    cases polarity
    · simp only [ofMu, NativeStructure.sat, cond] at first second ⊢
      rw [first, second, satisfies, not_and_or]
    · simp only [ofMu, NativeStructure.sat, cond] at first second ⊢
      rw [first, second, satisfies]
  | _, .disj left right, polarity, _, _, _, coherent, agrees, element => by
    simp only [muConsistent, Bool.and_eq_true] at coherent
    have first := sat_ofMu realizes left coherent.1 agrees element
    have second := sat_ofMu realizes right coherent.2 agrees element
    cases polarity
    · simp only [ofMu, NativeStructure.sat, cond] at first second ⊢
      rw [first, second, satisfies, not_or]
    · simp only [ofMu, NativeStructure.sat, cond] at first second ⊢
      rw [first, second, satisfies]
  | _, .diamond action inner, polarity, _, valuation, env, coherent, agrees, element => by
    simp only [muConsistent] at coherent
    cases polarity
    · rw [show ofMu modality false (.diamond action inner) = everyStep modality action (ofMu modality false inner) from rfl,
        sat_everyStep realizes env action _ (fun next => ¬ satisfies lts valuation inner next)
          (fun next => sat_ofMu realizes inner coherent agrees next)]
      simp [satisfies, LTS.successors]
    · rw [show ofMu modality true (.diamond action inner) = someStep modality action (ofMu modality true inner) from rfl,
        sat_someStep realizes env action _ (fun next => satisfies lts valuation inner next)
          (fun next => sat_ofMu realizes inner coherent agrees next)]
      simp [satisfies, LTS.successors]
  | _, .box action inner, polarity, _, valuation, env, coherent, agrees, element => by
    simp only [muConsistent] at coherent
    cases polarity
    · rw [show ofMu modality false (.box action inner) = someStep modality action (ofMu modality false inner) from rfl,
        sat_someStep realizes env action _ (fun next => ¬ satisfies lts valuation inner next)
          (fun next => sat_ofMu realizes inner coherent agrees next)]
      simp [satisfies, LTS.successors]
    · rw [show ofMu modality true (.box action inner) = everyStep modality action (ofMu modality true inner) from rfl,
        sat_everyStep realizes env action _ (fun next => satisfies lts valuation inner next)
          (fun next => sat_ofMu realizes inner coherent agrees next)]
      simp [satisfies, LTS.successors]
  | _, .mu body, polarity, signs, valuation, env, coherent, agrees, element => by
    simp only [muConsistent] at coherent
    cases polarity
    · change (∃ invariant : Set Carrier, element ∈ invariant ∧ ∀ other ∈ invariant,
          S.sat (env.extend invariant) (ofMu modality false body) other) ↔
        ¬ ∀ closedSet : Set Carrier, (∀ other, satisfies lts (valuation.extend closedSet) body other → other ∈ closedSet) →
          element ∈ closedSet
      constructor
      · rintro ⟨invariant, inside, preserved⟩ least
        refine least invariantᶜ (fun other holds member => ?_) inside
        exact (sat_ofMu realizes body coherent
          (agrees.extend false invariantᶜ invariant fun _ => by simp) other).mp (preserved other member) holds
      · intro notLeast
        simp only [not_forall, exists_prop] at notLeast
        obtain ⟨closedSet, closedUnder, outside⟩ := notLeast
        refine ⟨closedSetᶜ, outside, fun other member => ?_⟩
        exact (sat_ofMu realizes body coherent
          (agrees.extend false closedSet closedSetᶜ fun _ => Iff.rfl) other).mpr fun holds => member (closedUnder other holds)
    · change (∀ closedSet : Set Carrier, (∀ other,
          S.sat (env.extend closedSet) (ofMu modality true body) other → other ∈ closedSet) → element ∈ closedSet) ↔
        ∀ closedSet : Set Carrier, (∀ other, satisfies lts (valuation.extend closedSet) body other → other ∈ closedSet) →
          element ∈ closedSet
      exact forall_congr' fun closedSet => imp_congr_left (forall_congr' fun other => imp_congr_left
        (sat_ofMu realizes body coherent (agrees.extend true closedSet closedSet fun _ => Iff.rfl) other))
  | _, .nu body, polarity, signs, valuation, env, coherent, agrees, element => by
    simp only [muConsistent] at coherent
    cases polarity
    · change (∀ closedSet : Set Carrier, (∀ other,
          S.sat (env.extend closedSet) (ofMu modality false body) other → other ∈ closedSet) → element ∈ closedSet) ↔
        ¬ ∃ invariant : Set Carrier, element ∈ invariant ∧ ∀ other ∈ invariant,
          satisfies lts (valuation.extend invariant) body other
      constructor
      · rintro least ⟨invariant, inside, preserved⟩
        have := least invariantᶜ fun other holds member =>
          ((sat_ofMu realizes body coherent (agrees.extend false invariant invariantᶜ fun _ => Iff.rfl) other).mp holds)
            (preserved other member)
        exact this inside
      · intro noInvariant closedSet closedUnder
        by_contra outside
        refine noInvariant ⟨closedSetᶜ, outside, fun other member => ?_⟩
        by_contra fails
        exact member (closedUnder other ((sat_ofMu realizes body coherent
          (agrees.extend false closedSetᶜ closedSet fun _ => by simp) other).mpr fails))
    · change (∃ invariant : Set Carrier, element ∈ invariant ∧ ∀ other ∈ invariant,
          S.sat (env.extend invariant) (ofMu modality true body) other) ↔
        ∃ invariant : Set Carrier, element ∈ invariant ∧ ∀ other ∈ invariant,
          satisfies lts (valuation.extend invariant) body other
      exact exists_congr fun invariant => and_congr_right fun _ => forall_congr' fun other => imp_congr_right fun _ =>
        sat_ofMu realizes body coherent (agrees.extend true invariant invariant fun _ => Iff.rfl) other
  | _, .var index, polarity, signs, valuation, env, coherent, agrees, element => by
    simp only [muConsistent, beq_iff_eq] at coherent
    have := agrees index element
    rw [coherent] at this
    cases polarity <;> exact this

/-! ## Traversals of the step span -/

open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula (Traversal transitionSystem)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder (stepSpan)

/-- The future is a step, and the past a step taken backwards. -/
def traversal : Traversal → Direction × StepLabel
  | .future => (.forward, .any)
  | .past => (.backward, .any)

/-- **The traversals of a native structure's step span are its steps**, forwards and backwards. -/
theorem realizes_transitionSystem {Carrier : Type} (S : NativeStructure Carrier) :
    Realizes traversal S (transitionSystem (stepSpan S)) := by
  intro source direction target
  cases direction
  · constructor
    · rintro ⟨edge, starts, ends⟩
      exact starts ▸ ends ▸ edge.2
    · intro step
      exact ⟨⟨(source, target), step⟩, rfl, rfl⟩
  · constructor
    · rintro ⟨edge, ends, starts⟩
      exact starts ▸ ends ▸ edge.2
    · intro step
      exact ⟨⟨(target, source), step⟩, rfl, rfl⟩

/-- **A closed μ-calculus formula over traversals holds exactly where its embedding does.** -/
theorem satisfies_iff_sat {Carrier : Type} (S : NativeStructure Carrier)
    (formula : Mettapedia.Logic.ModalMuCalculus.Formula Traversal 0) (positive : muConsistent Fin.elim0 true formula = true)
    (element : Carrier) :
    satisfies (transitionSystem (stepSpan S)) Mettapedia.Logic.ModalMuCalculus.Env.empty formula element ↔
      S.sat Env.closed (ofMu traversal true formula) element :=
  (sat_ofMu (realizes_transitionSystem S) formula positive (fun index => index.elim0) element).symm

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings
