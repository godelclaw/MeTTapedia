import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Equivalence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls

/-!
# Controls: the equivalence native types induce

- **Bisimilar but distinct.** In two copies of a one-step chain, `0 → 1` and `2 → 3`, the starts `0` and
  `2` are bisimilar (`bisimilar_starts`), so they agree on every behavioural formula
  (`starts_agree`). A singleton type tells them apart (`singleton_separates`). Behaviour alone does
  not determine the term.
- **Past steps separate.** In `0 → 1 → 2` and `3 → 4`, the ends `2` and `4` are both stuck, yet `2` has
  a predecessor that has a predecessor and `4` does not (`past_separates`). So they are not bisimilar
  (`ends_not_bisimilar`): bisimilarity here looks backward as well as forward.
- **A language's states.** In `tiny`, `Par Nil (Out Nil)` and `Par (Out Nil) Nil` are different terms,
  and some formula tells them apart (`tiny_separates`). With commutativity they are one term modulo the
  equations, and they agree on every formula (`tinyComm_agree`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquivalenceControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls
  (nilTerm out par tiny tinyComm tiny_equivalent commuted_equivalent)
open NativeStructure

/-- A finite structure whose steps are an edge relation under every label, with one named element. -/
def chains {size : ℕ} (edge : Fin size → Fin size → Bool) (named : Fin size → Bool) : FiniteStructure (Fin size) where
  elements := List.finRange size
  complete := List.mem_finRange
  step source _ target := edge source target
  built _ _ _ := false
  split _ _ _ _ := false
  empty _ _ := false
  single _ _ _ := false
  body _ _ := false
  multiBody _ _ _ := false
  bound _ _ := false
  typed _ _ := false
  named element term := named element && term == nilTerm
  same first second := decide (first = second)
  apply inner _ := inner

/-! ## Bisimilar but distinct -/

def twoChains : FiniteStructure (Fin 4) :=
  chains (fun source target => (source, target) == (0, 1) || (source, target) == (2, 3)) (· == 0)

/-- Swap the two chains, or stay. -/
def swapped (first second : Fin 4) : Bool :=
  first == second || (first, second) ∈ [(0, 2), (2, 0), (1, 3), (3, 1)]

theorem swapped_forth : ∀ first second next : Fin 4, swapped first second = true →
    twoChains.step first .any next = true → ∃ next', twoChains.step second .any next' = true ∧ swapped next next' = true := by
  decide

theorem swapped_pastForth : ∀ first second previous : Fin 4, swapped first second = true →
    twoChains.step previous .any first = true →
      ∃ previous', twoChains.step previous' .any second = true ∧ swapped previous previous' = true := by
  decide

theorem swapped_symm : ∀ first second : Fin 4, swapped first second = true → swapped second first = true := by decide

/-- **The swap is a bisimulation.** -/
theorem swapped_bisimulation : twoChains.native.Bisimulation fun first second => swapped first second = true where
  forth := fun related step => swapped_forth _ _ _ related step
  back := fun {first second _ next'} related step => by
    obtain ⟨next, step', back⟩ := swapped_forth second first next' (swapped_symm _ _ related) step
    exact ⟨next, step', swapped_symm _ _ back⟩
  pastForth := fun related step => swapped_pastForth _ _ _ related step
  pastBack := fun {first second _ previous'} related step => by
    obtain ⟨previous, step', back⟩ := swapped_pastForth second first previous' (swapped_symm _ _ related) step
    exact ⟨previous, step', swapped_symm _ _ back⟩

theorem bisimilar_starts : twoChains.native.Bisimilar 0 2 := ⟨_, swapped_bisimulation, rfl⟩

/-- **Bisimilar starts agree on every behavioural formula.** -/
theorem starts_agree : twoChains.native.BehaviourallyEquivalent 0 2 :=
  (behaviourallyEquivalent_iff_bisimilar twoChains.imageFinite).mpr bisimilar_starts

/-- **A singleton type tells them apart.** -/
theorem singleton_separates :
    twoChains.native.sat Env.closed (.is nilTerm) 0 ∧ ¬ twoChains.native.sat Env.closed (.is nilTerm) 2 :=
  ⟨(twoChains.check_iff _ _).mp (by decide), fun holds => absurd ((twoChains.check_iff _ _).mpr holds) (by decide)⟩

/-! ## Past steps separate -/

def pastChains : FiniteStructure (Fin 5) :=
  chains (fun source target => (source, target) ∈ [(0, 1), (1, 2), (3, 4)]) fun _ => false

/-- Some step leads here from an element some step leads to. -/
def twoBefore : Formula 0 := .sometimeBefore .any (.sometimeBefore .any .top)

theorem ends_stuck :
    pastChains.native.sat Env.closed (.necessarily .any .bot) 2 ∧
      pastChains.native.sat Env.closed (.necessarily .any .bot) 4 :=
  ⟨(pastChains.check_iff _ _).mp (by decide), (pastChains.check_iff _ _).mp (by decide)⟩

/-- **The past tells the stuck ends apart.** -/
theorem past_separates :
    pastChains.native.sat Env.closed twoBefore 2 ∧ ¬ pastChains.native.sat Env.closed twoBefore 4 :=
  ⟨(pastChains.check_iff _ _).mp (by decide), fun holds => absurd ((pastChains.check_iff _ _).mpr holds) (by decide)⟩

theorem ends_not_bisimilar : ¬ pastChains.native.Bisimilar 2 4 := fun related =>
  past_separates.2 (sat_of_bisimilar twoBefore rfl (Env.respects_closed _) related past_separates.1)

/-! ## A language's states -/

/-- **In `tiny`, the commuted terms are told apart.** -/
theorem tiny_separates : ¬ ∀ formula : Formula 0,
    ((referenceStructure RelationEnv.empty tiny).sat Env.closed formula (par nilTerm (out nilTerm)) ↔
      (referenceStructure RelationEnv.empty tiny).sat Env.closed formula (par (out nilTerm) nilTerm)) := by
  rw [agree_iff_objectEquivalent RelationEnv.empty tiny (by decide) (by decide), tiny_equivalent]
  decide

/-- **With commutativity they agree on every formula.** -/
theorem tinyComm_agree : ∀ formula : Formula 0,
    ((referenceStructure RelationEnv.empty tinyComm).sat Env.closed formula (par nilTerm (out nilTerm)) ↔
      (referenceStructure RelationEnv.empty tinyComm).sat Env.closed formula (par (out nilTerm) nilTerm)) :=
  (agree_iff_objectEquivalent RelationEnv.empty tinyComm (by decide) (by decide)).mpr commuted_equivalent

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquivalenceControls
