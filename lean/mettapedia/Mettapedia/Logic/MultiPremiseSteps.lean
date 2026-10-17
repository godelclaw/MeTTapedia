import Mettapedia.Logic.RuleMulticategoryGraphs

/-!
# Atomic multi-pattern steps as multi-premise rules

A store holds atom occurrences in stable slots. One atomic step cites slots
whose atoms it keeps, cites slots whose atoms it consumes, and produces new
atoms, provided its rule admits the kept, consumed and produced atoms (the guard
is part of that decision). This is the shape of a multi-headed CHR simpagation
rule and of an MM2 execution step.

**Monotone steps are derivations.** Without consumption, a step with one
product is exactly a rule instance whose premises are the kept atoms:
running such steps is replay of the corresponding derivation graph
(`run_monotone`). Hence every accepted trace denotes, at every step, a closed
morphism of the free multicategory on the rule instances
(`RuleWitness.unfold_root`), and acceptance and those morphisms are invariant
under every reordering that keeps each premise before its consumer
(`DerivationGraph.replayWith_permute`, `RuleWitness.unfold_permute`). A monotone
step with several products is unobservable as a unit: it runs exactly as the
sequence of its single-product components (`run_split`).

What the correspondence keeps: rule witnesses, the ordered and repeated
premise occurrences, every conclusion, acceptance (including refusal of unused
bad steps) and the step count. What it forgets: the order of independent steps,
sharing (a graph and its unfolded tree are one morphism), and the identity of
steps that are not used by the selected root.

**Consumption is linear.** A consumed slot can never be cited again
(`consumed_not_cited`), so consumed occurrences cannot be shared or
duplicated, and two steps competing for one occurrence lead to different
stores (`consumption_not_confluent`). Steps with independent footprints
commute, with the same live atoms up to the order of their products
(`independent_commute`): consuming traces are correct up to permutation of
independent steps exactly in this footprint sense. With several products consumed
together, a two-step process can carry two wires between its steps, while
every composite in the tree-shaped single-wire-cut grammar carries one wire fewer than it has
generators (`PolyComposite.wires_add_one`, `process_not_polycategorical`).
This excludes representations in that grammar preserving generator and wire
counts, not all categorical presentations of consuming processes. A monoidal
presentation is not formalized here. Negative reads (absence) are outside this
step shape.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.MultiPremiseSteps

universe u v w

open DerivationGraph

variable {Atom : Type u}

/-- A store of occurrences: a slot holds an atom until it is consumed. -/
abbrev Store (Atom : Type u) := Array (Option Atom)

/-- The live atoms at the cited slots, in citation order. -/
def readLive (store : Store Atom) : List Nat → Option (List Atom)
  | [] => some []
  | i :: rest =>
      match store[i]? with
      | some (some atom) => (readLive store rest).map (atom :: ·)
      | _ => none

/-- Mark slots as consumed. -/
def consume (store : Store Atom) (slots : List Nat) : Store Atom :=
  store.mapIdx fun i atom => if i ∈ slots then none else atom

/-- One atomic step: a witness, kept slots, consumed slots and products. -/
structure Step (Atom : Type u) (W : Type v) where
  witness : W
  keep : List Nat
  take : List Nat
  produce : List Atom

/-- A rule system decides which witnesses license which kept, consumed and
produced atoms. -/
structure Rules (Atom : Type u) where
  W : Type v
  admits : W → List Atom → List Atom → List Atom → Bool

/-- Fire one step: all cited slots are live, consumed slots are distinct and
not also kept, and the rule admits the step. -/
def fire (R : Rules.{u, v} Atom) (store : Store Atom) (step : Step Atom R.W) :
    Option (Store Atom) :=
  match readLive store step.keep, readLive store step.take with
  | some kept, some taken =>
      if decide (step.take.Nodup ∧ ∀ i ∈ step.take, i ∉ step.keep) &&
          R.admits step.witness kept taken step.produce then
        some (consume store step.take ++ (step.produce.map some).toArray)
      else none
  | _, _ => none

/-- Run a trace of steps. -/
def run (R : Rules.{u, v} Atom) : Store Atom → List (Step Atom R.W) → Option (Store Atom)
  | store, [] => some store
  | store, step :: rest =>
      match fire R store step with
      | none => none
      | some next => run R next rest

/-! ## Monotone single-product steps are derivation-graph replay -/

/-- The rule instances presented by monotone single-product steps. -/
def monotoneWitness (R : Rules.{u, v} Atom) :
    RuleWitness (fun premises conclusion => ∃ w, R.admits w premises [] [conclusion] = true) where
  W := R.W
  isInstance w premises conclusion := R.admits w premises [] [conclusion]
  sound w _ _ accepted := ⟨w, accepted⟩
  complete _ _ := id

/-- A graph node as a monotone step. -/
def toStep {R : Rules.{u, v} Atom} {Origin : Type w} (node : Node Atom R.W Origin) : Step Atom R.W :=
  ⟨node.witness, node.parents, [], [node.conclusion]⟩

theorem readLive_map (cache : Array Atom) :
    ∀ indices : List Nat, readLive (cache.map some) indices = lookupPremises cache indices
  | [] => rfl
  | i :: rest => by
      simp only [readLive, lookupPremises, Array.getElem?_map]
      cases cache[i]? with
      | none => rfl
      | some atom =>
          simp only [Option.map_some, readLive_map cache rest]
          cases lookupPremises cache rest <;> rfl

theorem consume_nil (store : Store Atom) : consume store [] = store := by
  apply Array.ext
  · simp [consume]
  · intro i _ _
    simp [consume]

/-- **Monotone single-product steps are exactly derivation-graph replay.** -/
theorem run_monotone (R : Rules.{u, v} Atom) {Origin : Type w} (cache : Array Atom)
    (nodes : List (Node Atom R.W Origin)) :
    run R (cache.map some) (nodes.map toStep) =
      (replayFrom (monotoneWitness R) cache nodes).map (Array.map some) := by
  induction nodes generalizing cache with
  | nil => rfl
  | cons node rest ih =>
      have fireEq : fire R (cache.map some) (toStep node) =
          (node.replay (monotoneWitness R) cache).map (Array.map some) := by
        simp only [fire, toStep, readLive_map]
        cases found : lookupPremises cache node.parents with
        | none => simp [Node.replay, found]
        | some premises =>
            by_cases accepted : R.admits node.witness premises [] [node.conclusion] = true
            · have pushed : consume (cache.map some) [] ++ ([node.conclusion].map some).toArray =
                  (cache.push node.conclusion).map some := by
                rw [consume_nil]
                simp
              simp [Node.replay, found, accepted, monotoneWitness, lookupPremises, consume_nil]
            · have refused : R.admits node.witness premises [] [node.conclusion] = false := by
                simpa using accepted
              simp [Node.replay, found, refused, monotoneWitness, lookupPremises]
      change (match fire R (cache.map some) (toStep node) with
        | none => none
        | some next => run R next (rest.map toStep)) =
        ((node.replay (monotoneWitness R) cache).bind fun next =>
          replayFrom (monotoneWitness R) next rest).map (Array.map some)
      rw [fireEq]
      cases node.replay (monotoneWitness R) cache with
      | none => rfl
      | some next => exact ih next

/-- Every step of an accepted monotone trace denotes a closed morphism of the free
multicategory on the step rules. -/
theorem run_monotone_unfolds (R : Rules.{u, v} Atom) {Origin : Type w}
    {nodes : List (Node Atom R.W Origin)} {store : Store Atom}
    (accepted : run R #[] (nodes.map toStep) = some store) :
    ∃ terms : Array (Σ b, RuleSignature.Term (monotoneWitness R).signature
        CartesianMulticategory.closedContext b),
      replayWith (RuleWitness.termStep (monotoneWitness R)) #[] nodes = some terms ∧
        (terms.map Sigma.fst).map some = store := by
  have same := run_monotone R #[] nodes
  simp only [Array.map_empty] at same
  rw [same] at accepted
  cases replayed : replayFrom (monotoneWitness R) #[] nodes with
  | none => rw [replayed] at accepted; cases accepted
  | some cache =>
      rw [replayed] at accepted
      obtain ⟨terms, unfolded, projected⟩ := RuleWitness.unfold_root (monotoneWitness R) replayed
      exact ⟨terms, unfolded, by rw [projected]; exact Option.some.inj accepted⟩

/-! ## Monotone multi-product steps are sequences of single-product steps -/

/-- Single-product components: a witness, the full product list and a position. -/
def split [DecidableEq Atom] (R : Rules.{u, v} Atom) : Rules.{u, max u v} Atom where
  W := R.W × List Atom × Nat
  admits := fun ⟨w, products, index⟩ kept taken produced =>
    taken.isEmpty && R.admits w kept [] products &&
      match products[index]?, produced with
      | some product, [single] => decide (product = single)
      | _, _ => false

/-- The single-product components of a monotone step, in product order. -/
def components [DecidableEq Atom] {R : Rules.{u, v} Atom} (step : Step Atom R.W) :
    List (Step Atom (split R).W) :=
  (List.finRange step.produce.length).map fun (index : Fin step.produce.length) =>
    ⟨(step.witness, step.produce, (index : Nat)), step.keep, [], [step.produce.get index]⟩

theorem readLive_lt {store : Store Atom} :
    ∀ {indices : List Nat} {atoms : List Atom}, readLive store indices = some atoms →
      ∀ i ∈ indices, i < store.size
  | [], _, _ => by simp
  | i :: rest, atoms, found => by
      simp only [readLive] at found
      cases entry : store[i]? with
      | none => rw [entry] at found; cases found
      | some value =>
          cases value with
          | none => rw [entry] at found; cases found
          | some atom =>
              rw [entry] at found
              cases later : readLive store rest with
              | none => rw [later] at found; cases found
              | some others =>
                  intro j member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact (Array.getElem?_eq_some_iff.mp entry).1
                  · exact readLive_lt later j member

theorem readLive_append {store : Store Atom} {indices : List Nat} {atoms : List Atom}
    (found : readLive store indices = some atoms) (more : Store Atom) :
    readLive (store ++ more) indices = some atoms := by
  induction indices generalizing atoms with
  | nil => exact found
  | cons i rest ih =>
      have inside := readLive_lt found i List.mem_cons_self
      simp only [readLive] at found ⊢
      rw [Array.getElem?_append_left inside]
      cases entry : store[i]? with
      | none => rw [entry] at found; cases found
      | some value =>
          cases value with
          | none => rw [entry] at found; cases found
          | some atom =>
              rw [entry] at found
              cases later : readLive store rest with
              | none => rw [later] at found; cases found
              | some others =>
                  rw [later] at found
                  simp only [ih later]
                  exact found

/-- Running single-product components appends their products one at a time. -/
theorem run_components [DecidableEq Atom] (R : Rules.{u, v} Atom) (w : R.W) (keep : List Nat) (products : List Atom)
    (kept : List Atom) (admitted : R.admits w kept [] products = true) :
    ∀ (indices : List (Fin products.length)) (store : Store Atom),
      readLive store keep = some kept →
        run (split R) store (indices.map fun (index : Fin products.length) =>
            (⟨(w, products, (index : Nat)), keep, [], [products.get index]⟩ : Step Atom (split R).W)) =
          some (store ++ (indices.map fun index => some (products.get index)).toArray)
  | [], store, _ => by simp [run]
  | index :: rest, store, found => by
      have lookup : products[(index : Nat)]? = some (products.get index) := by simp
      have fired : fire (split R) store ⟨(w, products, (index : Nat)), keep, [], [products.get index]⟩ =
          some (store.push (some (products.get index))) := by
        simp only [fire, found, readLive, List.nodup_nil, List.not_mem_nil, false_implies,
          implies_true, and_self, decide_true, Bool.true_and, split, List.isEmpty_nil,
          admitted, lookup]
        simp [consume_nil]
      simp only [List.map_cons, run, fired]
      rw [run_components R w keep products kept admitted rest _
        (by simpa using readLive_append found #[some (products.get index)])]
      simp

/-- **Atomicity of monotone production is unobservable.** A monotone step with
products runs exactly as its single-product components. -/
theorem run_split [DecidableEq Atom] (R : Rules.{u, v} Atom) (store store' : Store Atom) (step : Step Atom R.W)
    (monotone : step.take = []) (fired : fire R store step = some store') :
    run (split R) store (components step) = some store' := by
  obtain ⟨w, keep, take, products⟩ := step
  simp only at monotone
  subst monotone
  simp only [fire, readLive] at fired
  cases found : readLive store keep with
  | none => rw [found] at fired; cases fired
  | some kept =>
      rw [found] at fired
      by_cases admitted : R.admits w kept [] products = true
      · simp only [List.nodup_nil, List.not_mem_nil, false_implies, implies_true, and_self,
          decide_true, admitted, Bool.and_self, if_true, Option.some.injEq] at fired
        subst fired
        have run := run_components R w keep products kept admitted (List.finRange products.length)
          store found
        rw [components]
        simp only at run ⊢
        rw [run, consume_nil]
        have mapped : (List.finRange products.length).map (fun index => some (products.get index)) =
            products.map some := by
          rw [show (fun index => some (products.get index)) = some ∘ products.get from rfl,
            ← List.map_map, List.map_get_finRange]
        rw [mapped]
      · simp [admitted] at fired

/-! ## Consumption is linear -/

theorem consume_getElem? (store : Store Atom) (slots : List Nat) (i : Nat) (inside : i < store.size) :
    (consume store slots)[i]? = some (if i ∈ slots then none else store[i]) := by
  simp [consume, inside]

/-- A fired step leaves each consumed slot dead and every dead slot dead. -/
theorem fire_dead_slots {R : Rules.{u, v} Atom} {store store' : Store Atom}
    {step : Step Atom R.W} (fired : fire R store step = some store') (i : Nat)
    (dead : i ∈ step.take ∨ store[i]? = some none) : store'[i]? = some none := by
  simp only [fire] at fired
  cases kept : readLive store step.keep with
  | none => rw [kept] at fired; cases fired
  | some keptAtoms =>
      cases taken : readLive store step.take with
      | none => rw [kept, taken] at fired; cases fired
      | some takenAtoms =>
          simp only [kept, taken] at fired
          split at fired
          · cases Option.some.inj fired
            have inside : i < store.size := by
              rcases dead with member | dead
              · exact readLive_lt taken i member
              · exact (Array.getElem?_eq_some_iff.mp dead).1
            have consumedSize : i < (consume store step.take).size := by simpa [consume] using inside
            rw [Array.getElem?_append_left consumedSize, consume_getElem? store step.take i inside]
            rcases dead with member | dead
            · simp [member]
            · have value : store[i] = none := by
                rw [Array.getElem?_eq_getElem inside] at dead
                exact Option.some.inj dead
              simp [value]
          · cases fired

theorem readLive_dead {store : Store Atom} {i : Nat} (dead : store[i]? = some none) :
    ∀ {indices : List Nat}, i ∈ indices → readLive store indices = none
  | j :: rest, member => by
      simp only [readLive]
      rcases List.mem_cons.mp member with rfl | member
      · rw [dead]
      · cases store[j]? with
        | none => rfl
        | some value =>
            cases value with
            | none => rfl
            | some atom => rw [readLive_dead dead member]; rfl

/-- A step citing a dead slot is refused. -/
theorem fire_refuses_dead {R : Rules.{u, v} Atom} {store : Store Atom} {step : Step Atom R.W}
    {i : Nat} (dead : store[i]? = some none) (cited : i ∈ step.keep ∨ i ∈ step.take) :
    fire R store step = none := by
  simp only [fire]
  rcases cited with member | member
  · rw [readLive_dead dead member]
  · rw [readLive_dead dead member]
    cases readLive store step.keep <;> rfl

theorem run_dead_not_cited {R : Rules.{u, v} Atom} {i : Nat} :
    ∀ {store final : Store Atom} {steps : List (Step Atom R.W)},
      run R store steps = some final → store[i]? = some none →
        ∀ later ∈ steps, i ∉ later.keep ∧ i ∉ later.take
  | _, _, [], _, _ => by simp
  | store, final, step :: rest, accepted, dead => by
      simp only [run] at accepted
      cases fired : fire R store step with
      | none => rw [fired] at accepted; cases accepted
      | some next =>
          rw [fired] at accepted
          intro later member
          rcases List.mem_cons.mp member with rfl | member
          · constructor
            · intro cited
              rw [fire_refuses_dead dead (Or.inl cited)] at fired
              cases fired
            · intro cited
              rw [fire_refuses_dead dead (Or.inr cited)] at fired
              cases fired
          · exact run_dead_not_cited accepted (fire_dead_slots fired i (Or.inr dead)) later member

/-- **Consumption is linear.** In an accepted trace, a consumed occurrence is
never cited again: it can be neither kept nor consumed a second time. -/
theorem consumed_not_cited {R : Rules.{u, v} Atom} {store final : Store Atom}
    {step : Step Atom R.W} {rest : List (Step Atom R.W)}
    (accepted : run R store (step :: rest) = some final) {i : Nat} (taken : i ∈ step.take) :
    ∀ later ∈ rest, i ∉ later.keep ∧ i ∉ later.take := by
  simp only [run] at accepted
  cases fired : fire R store step with
  | none => rw [fired] at accepted; cases accepted
  | some next =>
      rw [fired] at accepted
      exact run_dead_not_cited accepted (fire_dead_slots fired i (Or.inl taken))

/-! ## Independent consuming steps commute -/

/-- The live atoms of a store, in slot order. -/
def live (store : Store Atom) : List Atom := store.toList.filterMap id

theorem live_append (first second : Store Atom) : live (first ++ second) = live first ++ live second := by
  simp [live, List.filterMap_append]

theorem consume_size (store : Store Atom) (slots : List Nat) : (consume store slots).size = store.size := by
  simp [consume]

theorem consume_comm (store : Store Atom) (first second : List Nat) :
    consume (consume store first) second = consume (consume store second) first := by
  apply Array.ext
  · simp [consume_size]
  · intro i _ _
    simp only [consume, Array.getElem_mapIdx]
    by_cases inFirst : i ∈ first <;> by_cases inSecond : i ∈ second <;> simp [inFirst, inSecond]

theorem consume_append (store more : Store Atom) (slots : List Nat)
    (inside : ∀ i ∈ slots, i < store.size) :
    consume (store ++ more) slots = consume store slots ++ more := by
  unfold consume
  apply Array.ext
  · simp
  · intro i hi hi'
    simp only [Array.getElem_mapIdx]
    by_cases low : i < store.size
    · rw [Array.getElem_append_left (by simpa using low), Array.getElem_append_left (by simpa using low)]
      simp only [Array.getElem_mapIdx]
    · have notIn : i ∉ slots := fun member => low (inside i member)
      rw [if_neg notIn, Array.getElem_append_right (by simpa using low),
        Array.getElem_append_right (by simpa using low)]
      simp

/-- Reading slots that were neither consumed nor appended reads the original store. -/
theorem readLive_consume_append {store more : Store Atom} {slots : List Nat} :
    ∀ {indices : List Nat}, (∀ i ∈ indices, i < store.size ∧ i ∉ slots) →
      readLive (consume store slots ++ more) indices = readLive store indices
  | [], _ => rfl
  | i :: rest, outside => by
      have here := outside i List.mem_cons_self
      simp only [readLive]
      have entry : (consume store slots ++ more)[i]? = store[i]? := by
        rw [Array.getElem?_append_left (by simpa [consume_size] using here.1),
          consume_getElem? store slots i here.1, if_neg here.2, Array.getElem?_eq_getElem here.1]
      rw [entry, readLive_consume_append fun j member => outside j (List.mem_cons_of_mem _ member)]

/-- Unfold a successful firing. -/
theorem fire_eq_some {R : Rules.{u, v} Atom} {store result : Store Atom} {step : Step Atom R.W}
    (fired : fire R store step = some result) :
    ∃ kept taken, readLive store step.keep = some kept ∧ readLive store step.take = some taken ∧
      (decide (step.take.Nodup ∧ ∀ i ∈ step.take, i ∉ step.keep) &&
        R.admits step.witness kept taken step.produce) = true ∧
      result = consume store step.take ++ (step.produce.map some).toArray := by
  simp only [fire] at fired
  cases keptFound : readLive store step.keep with
  | none => rw [keptFound] at fired; cases fired
  | some kept =>
      cases takenFound : readLive store step.take with
      | none => simp [keptFound, takenFound] at fired
      | some taken =>
          simp only [keptFound, takenFound] at fired
          split at fired
          · rename_i admitted
            exact ⟨kept, taken, rfl, rfl, admitted, (Option.some.inj fired).symm⟩
          · cases fired

/-- **Independent consuming steps commute.** If the second step cites only slots
of the original store that the first does not consume, and the first cites no
slot that the second consumes, then the two steps also fire in the other order,
and the live atoms agree up to the order of the two products. -/
theorem independent_commute {R : Rules.{u, v} Atom} {store middle final : Store Atom}
    {first second : Step Atom R.W}
    (secondOutside : ∀ i, i ∈ second.keep ∨ i ∈ second.take → i < store.size ∧ i ∉ first.take)
    (firstOutside : ∀ i, i ∈ first.keep ∨ i ∈ first.take → i ∉ second.take)
    (firedFirst : fire R store first = some middle) (firedSecond : fire R middle second = some final) :
    ∃ middle' final', fire R store second = some middle' ∧ fire R middle' first = some final' ∧
      (live final').Perm (live final) := by
  obtain ⟨kept₁, taken₁, keep₁, take₁, admitted₁, rfl⟩ := fire_eq_some firedFirst
  obtain ⟨kept₂, taken₂, keep₂, take₂, admitted₂, rfl⟩ := fire_eq_some firedSecond
  have firstInside : ∀ i, i ∈ first.keep ∨ i ∈ first.take → i < store.size := by
    rintro i (member | member)
    · exact readLive_lt keep₁ i member
    · exact readLive_lt take₁ i member
  have keep₂' : readLive store second.keep = some kept₂ := by
    rw [← keep₂]
    exact (readLive_consume_append fun i member => secondOutside i (Or.inl member)).symm
  have take₂' : readLive store second.take = some taken₂ := by
    rw [← take₂]
    exact (readLive_consume_append fun i member => secondOutside i (Or.inr member)).symm
  have firedSecond' : fire R store second =
      some (consume store second.take ++ (second.produce.map some).toArray) := by
    simp only [fire, keep₂', take₂']
    rw [if_pos admitted₂]
  have keep₁' : readLive (consume store second.take ++ (second.produce.map some).toArray) first.keep =
      some kept₁ := by
    rw [readLive_consume_append fun i member =>
      ⟨firstInside i (Or.inl member), firstOutside i (Or.inl member)⟩]
    exact keep₁
  have take₁' : readLive (consume store second.take ++ (second.produce.map some).toArray) first.take =
      some taken₁ := by
    rw [readLive_consume_append fun i member =>
      ⟨firstInside i (Or.inr member), firstOutside i (Or.inr member)⟩]
    exact take₁
  refine ⟨consume store second.take ++ (second.produce.map some).toArray,
    consume (consume store second.take ++ (second.produce.map some).toArray) first.take ++
      (first.produce.map some).toArray, firedSecond', ?_, ?_⟩
  · simp only [fire, keep₁', take₁']
    rw [if_pos admitted₁]
  · have secondTakeInside : ∀ i ∈ second.take, i < store.size :=
      fun i member => (secondOutside i (Or.inr member)).1
    have firstTakeInside : ∀ i ∈ first.take, i < store.size :=
      fun i member => firstInside i (Or.inr member)
    rw [consume_append _ _ _ (by simpa [consume_size] using firstTakeInside),
      consume_append _ _ _ (by simpa [consume_size] using secondTakeInside), consume_comm]
    simp only [live_append, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm

namespace Controls

/-- Every step is admitted; only liveness and disjointness are checked. -/
def free : Rules.{0, 0} Nat := ⟨Unit, fun _ _ _ _ => true⟩

def start : Store Nat := #[some 0]

def first : Step Nat free.W := ⟨(), [], [0], [1]⟩

def second : Step Nat free.W := ⟨(), [], [0], [2]⟩

/-- **Consumption is not confluent.** Two steps competing for one occurrence
reach different stores, and neither can then fire the other. -/
theorem consumption_not_confluent :
    fire free start first = some #[none, some 1] ∧ fire free start second = some #[none, some 2] ∧
      fire free #[none, some 1] second = none ∧ fire free #[none, some 2] first = none := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- A monotone step may keep the same occurrence twice: kept premises are shared. -/
theorem keep_twice : fire free start ⟨(), [0, 0], [], [3]⟩ = some #[some 0, some 3] := by decide

/-- A step may not consume one occurrence twice. -/
theorem take_twice_refused : fire free start ⟨(), [], [0, 0], [3]⟩ = none := by decide

/-- A step may not keep and consume the same occurrence. -/
theorem keep_and_take_refused : fire free start ⟨(), [0], [0], [3]⟩ = none := by decide

/-- Splitting `a` into `b` and `c`, then joining `b` and `c` into `d`. -/
def splitStep : Step Nat free.W := ⟨(), [], [0], [1, 2]⟩

def joinStep : Step Nat free.W := ⟨(), [], [1, 2], [3]⟩

theorem process_runs : run free start [splitStep, joinStep] = some #[none, none, none, some 3] := by
  decide

/-- Two consuming steps on different occurrences commute up to the order of their
products. -/
theorem independent_steps_commute :
    run free #[some 0, some 1] [⟨(), [], [0], [2]⟩, ⟨(), [], [1], [3]⟩] =
        some #[none, none, some 2, some 3] ∧
      run free #[some 0, some 1] [⟨(), [], [1], [3]⟩, ⟨(), [], [0], [2]⟩] =
        some #[none, none, some 3, some 2] := by
  constructor <;> decide

end Controls

/-! ## Polycategorical composites carry tree-shaped wiring -/

/-- The tree-shaped syntax of generators and cuts along one object. This
forgets object labels, typing and any equations on composites. -/
inductive PolyComposite (G : Type u) : Type u
  | gen (generator : G)
  | cut (left right : PolyComposite G)

namespace PolyComposite

variable {G : Type u}

def generators : PolyComposite G → Nat
  | .gen _ => 1
  | .cut left right => left.generators + right.generators

/-- Internal wires: one per composition. -/
def wires : PolyComposite G → Nat
  | .gen _ => 0
  | .cut left right => left.wires + right.wires + 1

/-- Every composite in this grammar has one internal wire fewer than it has
generators. -/
theorem wires_add_one (t : PolyComposite G) : t.wires + 1 = t.generators := by
  induction t with
  | gen => rfl
  | cut left right ihLeft ihRight =>
      simp only [wires, generators]
      omega

end PolyComposite

/-- Internal wires of a trace from an initial store: citations of slots produced
inside the trace. -/
def internalWires {W : Type v} (initial : Nat) (steps : List (Step Atom W)) : Nat :=
  (steps.map fun step => ((step.keep ++ step.take).filter (initial ≤ ·)).length).sum

/-- The split/join process runs with two steps and two internal wires. No
composite in the tree-shaped single-wire-cut grammar preserves both counts.
This does not rule out other categorical representations. -/
theorem process_not_polycategorical :
    run Controls.free Controls.start [Controls.splitStep, Controls.joinStep] ≠ none ∧
      internalWires 1 [Controls.splitStep, Controls.joinStep] = 2 ∧
      ∀ {G : Type} (t : PolyComposite G), t.generators = 2 → t.wires ≠ 2 := by
  refine ⟨by rw [Controls.process_runs]; simp, by decide, ?_⟩
  intro G t generators
  have := t.wires_add_one
  omega

end Mettapedia.Logic.MultiPremiseSteps
