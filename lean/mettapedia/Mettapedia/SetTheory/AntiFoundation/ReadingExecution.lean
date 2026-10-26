import Mettapedia.SetTheory.AntiFoundation.ReadingFinite
import Mettapedia.SetTheory.AntiFoundation.ReadingRelations
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFiniteBoolean
import Mettapedia.GSLT.Core.GSLT

/-!
# Certified stopping of finite graph readings

Execution retains its successive Boolean tables. Only agreement on every
enumerated pair licenses completion. The seed determines which fixed point
that completion means: equality grows to the least reading; the total
relation decreases to bisimilarity. Arbitrary stable relations need not be
setoids. Counts measure full refinement rounds, not their physical cost.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation.ReadingExecution

open Function Mettapedia.GSLT
open Mettapedia.TypeTheory.MaterialSets.Hypersets
variable {α : Type}

abbrev Table (α : Type) := α → α → Bool

def tablesAgree (elems : List α) (first second : Table α) : Bool :=
  elems.all (fun a => elems.all (fun b => first a b == second a b))

theorem tablesAgree_iff (elems : List α) (complete : ∀ a, a ∈ elems) (M N : Table α) :
    tablesAgree elems M N = true ↔ M = N := by
  simp only [tablesAgree, List.all_eq_true, beq_iff_eq]
  exact ⟨fun equal => funext fun a => funext fun b => equal a (complete a) b (complete b),
    fun equal _ _ _ _ => congrFun (congrFun equal _) _⟩

inductive State (α : Type) where
  | active (round : Nat) (table : Table α)
  | done (round : Nat) (table : Table α)

variable (elems : List α) (edgeB : Table α)

inductive Step : State α → State α → Prop where
  | advance (n : Nat) (M : Table α)
      (changing : tablesAgree elems M (matrixStep elems edgeB M) = false) :
      Step (.active n M) (.active (n+1) (matrixStep elems edgeB M))
  | finish (n : Nat) (M : Table α)
      (stable : tablesAgree elems M (matrixStep elems edgeB M) = true) :
      Step (.active n M) (.done n M)

def theory : GSLT where
  Term := State α
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step elems edgeB
  rewrites_resp_left := fun equal transition => by subst_vars; exact ⟨_, transition, rfl⟩
  rewrites_resp_right := fun transition equal => by subst_vars; exact transition

/-- A returned execution retains the actual path, rather than only its endpoint. -/
structure Execution (n : Nat) (seed : Table α) where
  round : Nat
  table : Table α
  path : (theory elems edgeB).RewritePath (.active n seed) (.done round table)

def execute? : (fuel n : Nat) → (seed : Table α) → Option (Execution elems edgeB n seed)
  | 0, _, _ => none
  | fuel+1, n, seed =>
      if stable : tablesAgree elems seed (matrixStep elems edgeB seed) = true then
        some ⟨n, seed, .cons (.finish n seed stable) (.nil _)⟩
      else (execute? fuel (n+1) (matrixStep elems edgeB seed)).map fun later =>
        ⟨later.round, later.table, .cons (.advance n seed (Bool.eq_false_iff.mpr stable)) later.path⟩

def refineUntil? (fuel : Nat) (seed : Table α) : Option (Nat × Table α) :=
  (execute? elems edgeB fuel 0 seed).map (fun result => (result.round, result.table))

/-- Every complete path, not just a path produced by `execute?`, has this interpretation. -/
theorem complete_path (seed : Table α) {k : Nat} {M : Table α}
    (path : (theory elems edgeB).RewritePath (.active 0 seed) (.done k M)) :
    M = (matrixStep elems edgeB)^[k] seed ∧
      tablesAgree elems M (matrixStep elems edgeB M) = true ∧ path.length = k+1 ∧
      ∀ i < k, tablesAgree elems ((matrixStep elems edgeB)^[i] seed)
        ((matrixStep elems edgeB)^[i+1] seed) = false := by
  let changing n := ∀ i < n, tablesAgree elems ((matrixStep elems edgeB)^[i] seed)
    ((matrixStep elems edgeB)^[i+1] seed) = false
  let invariant : State α → Nat → Prop
    | .active n table, count => table = (matrixStep elems edgeB)^[n] seed ∧ count = n ∧ changing n
    | .done n table, count => table = (matrixStep elems edgeB)^[n] seed ∧
        tablesAgree elems table (matrixStep elems edgeB table) = true ∧ count = n+1 ∧ changing n
  have transfer : ∀ {source target : State α}
      (route : (theory elems edgeB).RewritePath source target),
      ∀ count, invariant source count → invariant target (count + route.length) := by
    intro source target route
    exact GSLT.RewritePath.rec (S := theory elems edgeB)
      (motive := fun source target route =>
        ∀ count, invariant source count → invariant target (count + route.length))
      (fun _ count valid => by simpa [GSLT.RewritePath.length] using valid)
      (fun {_ middle _} transition rest ih count valid => by
      have next : invariant middle (count+1) := by
        cases transition with
        | advance n table changed =>
            refine ⟨by rw [valid.1, iterate_succ_apply'], by omega, ?_⟩
            intro i earlier
            rcases Nat.lt_succ_iff_lt_or_eq.mp earlier with before | rfl
            · exact valid.2.2 i before
            · simpa only [iterate_succ_apply', ← valid.1] using changed
        | finish n table stable => exact ⟨valid.1, stable, by omega, valid.2.2⟩
      simpa [GSLT.RewritePath.length, Nat.add_assoc] using ih (count+1) next) route
  simpa [invariant, changing] using transfer path 0 ⟨rfl, rfl, by omega⟩

theorem refineUntil?_sound (fuel : Nat) (seed : Table α) {k : Nat} {M : Table α}
    (returned : refineUntil? elems edgeB fuel seed = some (k, M)) :
    M = (matrixStep elems edgeB)^[k] seed ∧
      tablesAgree elems M (matrixStep elems edgeB M) = true ∧
      ∀ i < k, tablesAgree elems ((matrixStep elems edgeB)^[i] seed)
        ((matrixStep elems edgeB)^[i+1] seed) = false := by
  obtain ⟨run, _, equal⟩ := Option.map_eq_some_iff.mp returned
  cases equal
  exact ⟨(complete_path elems edgeB seed run.path).1,
    (complete_path elems edgeB seed run.path).2.1, (complete_path elems edgeB seed run.path).2.2.2⟩

/-- A stable round within the supplied fuel ensures an actual returned execution. -/
theorem execute?_complete (fuel : Nat) : ∀ (n k : Nat) (seed : Table α), k < fuel →
    tablesAgree elems ((matrixStep elems edgeB)^[k] seed)
      ((matrixStep elems edgeB)^[k+1] seed) = true →
      (execute? elems edgeB fuel n seed).isSome := by
  induction fuel with
  | zero => intro n k seed bound; omega
  | succ fuel ih =>
      intro n k seed bound stable
      simp only [execute?]
      split_ifs with ready
      · rfl
      · cases k with
        | zero => exact (ready (by simpa using stable)).elim
        | succ k =>
            simpa only [Option.isSome_map] using ih (n+1) k (matrixStep elems edgeB seed)
              (by omega) (by simpa only [iterate_succ_apply] using stable)

variable [Fintype α] [DecidableEq α]
variable (complete : ∀ a, a ∈ elems) (edge : Edge α)
variable (hedge : ∀ x y, edgeB x y = true ↔ edge x y)
include complete hedge

omit [Fintype α] in
theorem reading_of_stopped (K : Setoid α) (seed : Table α)
    (represents : ∀ a b, seed a b = true ↔ K a b) {k : Nat} {M : Table α}
    (path : (theory elems edgeB).RewritePath (.active 0 seed) (.done k M)) :
    step edge ((step edge)^[k] K) = (step edge)^[k] K := by
  obtain ⟨value, stable, _⟩ := complete_path elems edgeB seed path
  have fixed := (tablesAgree_iff elems complete M _).mp stable
  rw [← iterate_succ_apply' (step edge) k]
  ext a b
  have agrees := matrixIter_iff elems complete edge edgeB hedge seed K represents
  rw [← agrees (k+1), iterate_succ_apply', ← value, ← fixed, value, agrees k]

/-- Both ordered seed directions terminate within the pair bound plus finalization. -/
theorem ordered_terminates (K : Setoid α) (seed : Table α)
    (represents : ∀ a b, seed a b = true ↔ K a b)
    (ordered : K ≤ step edge K ∨ step edge K ≤ K) :
    (refineUntil? elems edgeB (Fintype.card α * Fintype.card α + 1) seed).isSome := by
  simp only [refineUntil?, Option.isSome_map]
  apply execute?_complete elems edgeB _ 0 (Fintype.card α * Fintype.card α) seed (by omega)
  apply (tablesAgree_iff elems complete _ _).2
  funext a b
  apply Bool.eq_iff_iff.mpr
  rw [matrixIter_iff elems complete edge edgeB hedge seed K represents,
    matrixIter_iff elems complete edge edgeB hedge seed K represents,
    ordered_iterate_stabilizes (step edge) K ordered]


/-- The same stopped table has the least-reading-above-seed interpretation. -/
theorem stopped_closure (K : Setoid α) (seed : Table α)
    (represents : ∀ a b, seed a b = true ↔ K a b) (bisimulation : K ≤ step edge K)
    {k : Nat} {M : Table α}
    (path : (theory elems edgeB).RewritePath (.active 0 seed) (.done k M)) (a b : α) :
    M a b = true ↔ stepClosure edge K a b := by
  have fixed := reading_of_stopped elems edgeB complete edge hedge K seed represents path
  have same : (step edge)^[k] K = stepClosure edge K := le_antisymm
    (iterate_le_of_reading edge (le_stepClosure edge bisimulation)
      (stepClosure_reading edge bisimulation).le k)
    (stepClosure_le_of_reading edge (le_iterate edge bisimulation k) fixed.le)
  rw [(complete_path elems edgeB seed path).1,
    matrixIter_iff elems complete edge edgeB hedge seed K represents, same]

omit [Fintype α] in
theorem stopped_bisimilarity {k : Nat} {M : Table α}
    (path : (theory elems edgeB).RewritePath (.active 0 (fun _ _ => true)) (.done k M))
    (a b : α) : M a b = true ↔ Bisimilar edge edge a b := by
  have represents : ∀ a b : α, true = true ↔ (⊤ : Setoid α) a b := by intros; simp
  have fixed := reading_of_stopped elems edgeB complete edge hedge ⊤ _ represents path
  have same := iterate_top_fixed_eq_gfp edge (by rw [iterate_succ_apply']; exact fixed)
  rw [(complete_path elems edgeB _ path).1,
    matrixIter_iff elems complete edge edgeB hedge _ ⊤ represents, same, gfp_eq_bisimilar]
  rfl

omit [Fintype α] in
/-- Deletion refinement and the pure child-class step agree from the total seed. -/
theorem total_rounds_agree [Mettapedia.SetTheory.Profiles.ConstructiveFinite.Enumeration α]
    [DecidableRel edge] (n : Nat) (a b : α) :
    (matrixStep elems edgeB)^[n] (fun _ _ => true) a b =
      Profiles.ProfileGraphReadout.FiniteBoolean.rounds edge edge n a b := by
  have represents : ∀ a b : α, true = true ↔ (⊤ : Setoid α) a b := by intros; simp
  have raw := matrixIter_iff elems complete edge edgeB hedge _ ⊤ represents
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
      have previous (x y : α) :
          Profiles.ProfileGraphReadout.FiniteBoolean.rounds edge edge n x y = true ↔
            ((step edge)^[n] ⊤) x y := by rw [← ih]; exact raw n x y
      apply Bool.eq_iff_iff.mpr
      rw [iterate_succ_apply', matrixStep_true_iff elems complete edge edgeB hedge _ _ (raw n),
        Profiles.ProfileGraphReadout.FiniteBoolean.rounds,
        Profiles.ProfileGraphReadout.FiniteBoolean.refine, Bool.and_eq_true, decide_eq_true_eq]
      simp only [Profiles.ProfileGraphReadout.FiniteBoolean.Matches, previous]
      change (step edge ((step edge)^[n] ⊤)) a b ↔
        ((step edge)^[n] ⊤) a b ∧ (step edge ((step edge)^[n] ⊤)) a b
      have decreasing := iterate_top_succ_le edge n
      rw [iterate_succ_apply'] at decreasing
      exact ⟨fun related => ⟨decreasing related, related⟩, And.right⟩

omit [Fintype α] [DecidableEq α] complete hedge

namespace Controls

/-- Agreement on one queried pair is weaker than agreement of the complete table. -/
theorem unchanged_pair_not_completion :
    matrixStep nestElems nestEdgeB (fun _ _ => true) .blank .blank = true ∧
      tablesAgree nestElems (fun _ _ => true)
        (matrixStep nestElems nestEdgeB (fun _ _ => true)) = false := by decide

/-- Different stable seeds keep different node distinctions on the same graph. -/
theorem seeds_select_different_readings :
    (refineUntil? cycleElems cycleEdgeB 1 (fun x y => decide (x = y))).map
      (fun result => result.2 .l .r) = some false ∧
    (refineUntil? cycleElems cycleEdgeB 1 (fun _ _ => true)).map
      (fun result => result.2 .l .r) = some true := by decide

end Controls

end Mettapedia.SetTheory.AntiFoundation.ReadingExecution
