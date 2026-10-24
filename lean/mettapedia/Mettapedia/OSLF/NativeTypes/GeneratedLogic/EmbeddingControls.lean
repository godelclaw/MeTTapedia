import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SyntacticEmbeddings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.MuEmbedding
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorEmbeddings

/-!
# Controls: embedding the other formula languages

- **Structural-modal formulas.** `Nil` satisfies "built by `Nil`" and `Out` does not; the bag `{A, B}`
  splits into an empty part and the rest, and is not empty itself (`nil_headed`, `out_not_nil`, `bag_cut`,
  `bag_not_empty`).
- **OSLF formulas.** "A box around the empty bag" holds where it should (`boxed_empty`). The positivity
  condition is needed: `μX. X → ⊥` is not positive (`not_positive`); it holds everywhere, and its
  embedding nowhere (`unguarded_differs`).
- **The μ-calculus.** On the counter `0 → 1 → 2`, "some step" holds at `0` and its embedding agrees
  (`counter_steps`); "every run is finite" is positive (`finite_runs_positive`). `μX. ¬X` is not
  positive, holds everywhere, and its embedding nowhere (`mu_not_differs`).
- **The front door.** On the counter, "some step reaches `2`" holds at `1` and fails at `0`, and so do
  its embeddings (`front_door_one`, `front_door_zero`). A negated test becomes the test's negative
  variable (`negated_test_shape`).
- **Propositional codes.** An implication's premise is read at the opposite polarity
  (`implication_shape`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.EmbeddingControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings
open Mettapedia.Logic.ModalMuCalculus (satisfies)
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula (Traversal)

/-! ## Structural-modal formulas -/

/-- The span with no steps. -/
def still : Mettapedia.OSLF.Framework.DerivedModalities.ReductionSpan.{0, 0} Pattern where
  Edge := Empty
  source edge := nomatch edge
  target edge := nomatch edge

def nilFormula : Mettapedia.OSLF.StructuralModal.Formula := .headed "Nil" []

theorem nil_headed : (syntactic (spanStep still)).sat Env.closed (ofStructuralModal nilFormula) (.apply "Nil" []) :=
  (sat_ofStructuralModal still nilFormula _).mpr ⟨[], rfl, trivial⟩

theorem out_not_nil : ¬ (syntactic (spanStep still)).sat Env.closed (ofStructuralModal nilFormula) (.apply "Out" []) := by
  rw [sat_ofStructuralModal]
  rintro ⟨_, same, _⟩
  injection same with label
  exact absurd label (by decide)

def atomA : Pattern := .apply "A" []
def atomB : Pattern := .apply "B" []

theorem bag_cut :
    (syntactic (spanStep still)).sat Env.closed
      (ofStructuralModal (.cut .hashBag (.emptyColl .hashBag) .top)) (.collection .hashBag [atomA, atomB] none) :=
  (sat_ofStructuralModal still _ _).mpr ⟨[], [atomA, atomB], rfl, rfl, trivial⟩

theorem bag_not_empty :
    ¬ (syntactic (spanStep still)).sat Env.closed (ofStructuralModal (.emptyColl .hashBag))
      (.collection .hashBag [atomA, atomB] none) := by
  rw [sat_ofStructuralModal]
  intro same
  injection same with _ elements
  cases elements

/-! ## OSLF formulas -/

open Mettapedia.OSLF.Formula (OSLFFormula semEnv fullFrame ScopeEnv)

/-- One atom slot pair; these formulas use no atoms. -/
def atomFree : String → Fin 2 := fun _ => 0
def atomFails : String → Fin 2 := fun _ => 1

/-- The environment of no atoms: the positive slot is empty and the negative one full. -/
def noAtoms : Env Pattern 2 := fun index => if index = 0 then ∅ else Set.univ

theorem noAtoms_agree :
    Agrees atomFree atomFails (fun _ _ => False) ScopeEnv.empty (fun _ => true) 0 noAtoms where
  positive_atom _ _ := by simp [noAtoms, atomFree, atomSlot]
  negative_atom _ _ := by simp [noAtoms, atomFails, atomSlot]
  scope_variable _ bounded _ := absurd bounded (Nat.not_lt_zero _)

/-- No steps. -/
def noStep : Pattern → Pattern → Prop := fun _ _ => False

/-- A box around the empty bag. -/
def boxedEmpty : OSLFFormula := .headed "Box" (.emptyColl .hashBag)

theorem boxed_empty :
    (syntactic noStep).sat noAtoms (ofOSLF atomFree atomFails 0 true boxedEmpty)
      (.apply "Box" [.collection .hashBag [] none]) :=
  (sat_ofOSLF noStep (fun _ _ => False) boxedEmpty (by decide) (by decide) noAtoms_agree _).mpr ⟨_, rfl, rfl⟩

/-- `μX. X → ⊥`: its variable occurs in a premise. -/
def unguarded : OSLFFormula := .mu (.imp (.var 0) .bot)

theorem not_positive : consistent (fun _ => true) true unguarded = false := by decide

/-- **Without positivity the readings differ**: `μX. X → ⊥` holds everywhere, its embedding nowhere. -/
theorem unguarded_differs (term : Pattern) :
    semEnv noStep fullFrame (fun _ _ => False) ScopeEnv.empty unguarded term ∧
      ¬ (syntactic noStep).sat noAtoms (ofOSLF atomFree atomFails 0 true unguarded) term := by
  constructor
  · intro candidate _ closedUnder
    by_contra outside
    exact outside (closedUnder term fun inside => outside inside)
  · intro least
    exact (least ∅ (fun _ holds => holds.elim id False.elim) : False)

/-! ## The μ-calculus -/

/-- The counter `0 → 1 → 2`, with no other relations. -/
def counter : NativeStructure (Fin 3) where
  step source _ target := target.val = source.val + 1
  built _ _ _ := False
  split _ _ _ _ := False
  empty _ _ := False
  single _ _ _ := False
  body _ _ := False
  multiBody _ _ _ := False
  bound _ _ := False
  typed _ _ := False
  named _ _ := False
  same first second := first = second
  apply inner _ := inner

theorem counter_steps :
    counter.sat Env.closed (ofMu traversal true (.diamond .future .tt)) 0 :=
  (satisfies_iff_sat counter (.diamond .future .tt) (by decide) 0).mp ⟨1, ⟨⟨(0, 1), rfl⟩, rfl, rfl⟩, trivial⟩

/-- "Every run is finite". -/
def finiteRuns : Mettapedia.Logic.ModalMuCalculus.Formula Traversal 0 := .mu (.box .future (.var 0))

theorem finite_runs_positive : muConsistent Fin.elim0 true finiteRuns = true := by decide

/-- `μX. ¬X`. -/
def muNot : Mettapedia.Logic.ModalMuCalculus.Formula Traversal 0 := .mu (.neg (.var 0))

/-- **Without positivity the readings differ**: `μX. ¬X` holds everywhere, its embedding nowhere. -/
theorem mu_not_differs (state : Fin 3) :
    muConsistent Fin.elim0 true muNot = false ∧
      satisfies (Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula.transitionSystem
        (Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder.stepSpan counter))
        Mettapedia.Logic.ModalMuCalculus.Env.empty muNot state ∧
      ¬ counter.sat Env.closed (ofMu traversal true muNot) state := by
  refine ⟨by decide, ?_, ?_⟩
  · intro closedSet closedUnder
    by_contra outside
    exact outside (closedUnder state fun inside => outside (by
      simpa [satisfies, Mettapedia.Logic.ModalMuCalculus.Env.extend] using inside))
  · intro least
    exact (least ∅ (fun _ holds => holds) : False)

/-! ## The front door -/

open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Test denotation)

/-- The counter as a GSLT without equations. -/
def counterSystem : Mettapedia.GSLT.GSLT.{0} where
  Term := Fin 3
  equations := { r := Eq, iseqv := eq_equivalence }
  rewrites source target := target.val = source.val + 1
  rewrites_resp_left := by
    intro _ _ target same step
    exact ⟨target, same ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step same
    exact same ▸ step

/-- The test "is `2`". -/
def isTwo : Test counterSystem (fun _ => True) :=
  Test.ofBoolean ⟨fun (state : Fin 3) => state = 2, by
      intro first second related
      change first = second at related
      subst second
      rfl⟩
    (fun (state : Fin 3) => decide (state = 2)) (fun (_ : Fin 3) => decide_eq_true_iff)

/-- The test's two variables. -/
def holdsSlot : Unit → Fin 2 := fun _ => 0
def failsSlot : Unit → Fin 2 := fun _ => 1

def testEnv : Env (Fin 3) 2 := Fin.cons {state | state = 2} (Fin.cons {state | state ≠ 2} Fin.elim0)

/-- "Some step reaches `2`". -/
def reachesTwo : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Unit := .possibility (.atom ())

theorem front_door_iff (state : Fin 3) :
    counter.sat testEnv (ofCore holdsSlot failsSlot (fun _ => .hashBag) true reachesTwo) state ↔
      (denotation (fun _ => isTwo) reachesTwo (.empty counterSystem)).1 state :=
  sat_ofCore (fun _ => isTwo) (.empty counterSystem) (S := counter) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    reachesTwo true trivial state

theorem front_door_one : counter.sat testEnv (ofCore holdsSlot failsSlot (fun _ => .hashBag) true reachesTwo) 1 := by
  rw [front_door_iff]
  exact (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond_spec counterSystem _ (1 : Fin 3)).mpr
    ⟨(2 : Fin 3), rfl, rfl⟩

theorem front_door_zero : ¬ counter.sat testEnv (ofCore holdsSlot failsSlot (fun _ => .hashBag) true reachesTwo) 0 := by
  rw [front_door_iff]
  intro holds
  obtain ⟨next, step, atTwo⟩ :=
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond_spec counterSystem _ (0 : Fin 3)).mp holds
  change next.val = 0 + 1 at step
  change next = (2 : Fin 3) at atTwo
  subst atTwo
  exact absurd step (by decide)

theorem negated_test_shape :
    ofCore holdsSlot failsSlot (fun _ => .hashBag) true (.neg (.atom ()) : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Unit) =
      .var (failsSlot ()) :=
  rfl

/-! ## Propositional codes -/

theorem implication_shape :
    ofExpression (m := 4) (fun index => if index = 0 then 0 else 1) (fun index => if index = 0 then 2 else 3) true
      (.implication (.leaf 0) (.leaf 1)) = .or (.var 2) (.var 1) :=
  rfl

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.EmbeddingControls
