import MettapediaFourColor.StripChoiceLoopRepair
import MettapediaFourColor.StripSourceExtension
import Mettapedia.GraphTheory.Kempe.BoundaryListTransport

/-!
# Core lists forget the support of a boundary operation

In each of D0063 and D0099, two proper boundaries induce exactly the same
list at every core vertex. Recolouring port six by the same palette map
makes only one input extendible. Thus even the full list assignment does
not determine this operation's extension outcome.

The refined cut summary retains separate forbidden-colour sets for moving
and fixed ports. Its uniform transport theorem computes the updated lists
on both sources. Successful lists consume joint forest reconstruction.
This is an exact source-update statement, not a claim that an arbitrary
exterior permits the displayed recolouring, or a general progress theorem.
-/

namespace FourColor.StripListTransport

open SimpleGraph Color TriangleStripAnchors TriangleStripLists
open ColoringListPropagation BoundaryListTransport

abbrev source : Bool → Source | false => .d0063 | true => .d0099
abbrev ring : Bool → ℕ | false => 10 | true => 11

abbrev Boundary (s : Bool) := Fin (ring s) → Color
abbrev Lists (s : Bool) := Fin (size (source s)) → Finset Color

instance (s : Bool) : NeZero (ring s) := ⟨by cases s <;> decide⟩
instance (s : Bool) : NeZero (size (source s)) := ⟨by cases s <;> decide⟩

def ports : (s : Bool) → Fin (size (source s)) → Finset (Fin (ring s))
  | false => fun v => (StripChoiceLoops.attachments v).toFinset
  | true => fun v => (StripResponseSummary.attachments v).toFinset

def boundary : (s : Bool) → Bool → Boundary s
  | false, false => ![c0,c1,c0,c1,c3,c2,c0,c2,c0,c1]
  | false, true => ![c0,c1,c0,c1,c3,c0,c2,c0,c2,c1]
  | true, false => ![c0,c1,c0,c1,c3,c2,c0,c2,c3,c2,c3]
  | true, true => ![c0,c1,c0,c1,c3,c0,c2,c0,c3,c2,c3]

def cut (s : Bool) : Finset (Fin (ring s)) := {⟨6,by cases s <;> decide⟩}
def update (s : Bool) (b : Boundary s) := change (cut s) (c1 + ·) b

def lists (s : Bool) (b : Boundary s) : Lists s := allowed (ports s) b

def Proper : (s : Bool) → Boundary s → Prop
  | false => StripChoiceLoops.ProperBoundary
  | true => StripSourceExtension.ProperBoundary

instance (s) (b : Boundary s) : Decidable (Proper s b) := by
  cases s with
  | false => exact inferInstanceAs (Decidable (StripChoiceLoops.ProperBoundary b))
  | true => exact inferInstanceAs (Decidable (StripSourceExtension.ProperBoundary b))

def Extends (s : Bool) (b : Boundary s) : Prop :=
  ∃ C : (core (source s)).Coloring Color, ∀ v, C v ∈ lists s b v

def Full : (s : Bool) → Boundary s → Prop
  | false, b => ∃ K : FiveTriangleCollapseObstruction.lower.graph.Coloring Color,
      ∀ i, K (StripChoiceLoops.port i) = b i
  | true, b => ∃ K : input0099.graph.Coloring Color,
      ∀ i, K (StripResponseSummary.port i) = b i

theorem lower_lists (b : Boundary false) : lists false b = StripChoiceLoops.allowed b := by
  classical
  funext v
  ext a
  simp [lists, allowed, ports, StripChoiceLoops.allowed]

theorem upper_lists (b : Boundary true) (v) (a) :
    a ∈ lists true b v ↔ StripResponseSummary.unary b v a := by
  classical
  simp [lists, allowed, ports, StripResponseSummary.unary]

/-- Every source edge, including every boundary attachment, is retained. -/
theorem full_iff (s : Bool) (b : Boundary s) (proper : Proper s b) :
    Full s b ↔ Extends s b := by
  classical
  cases s with
  | false =>
    constructor
    · rintro ⟨K,hK⟩
      let C : StripChoiceLoops.coreGraph.Coloring Color :=
        .mk (fun v => K (StripChoiceLoops.vertex v)) (fun h => K.valid h)
      refine ⟨C,fun v => ?_⟩
      rw [lower_lists]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i hi => ?_⟩
      change K (StripChoiceLoops.vertex v) ≠ b i
      rw [← hK i]
      exact K.valid ((StripChoiceLoops.attachments_complete v i).mpr hi)
    · rintro ⟨C,fit⟩
      let K : FiveTriangleCollapseObstruction.lower.graph.Coloring Color :=
        .mk (StripChoiceLoopRepair.complete b C) (fun h =>
          StripChoiceLoopRepair.complete_valid b C proper
            (fun v => (lower_lists b) ▸ fit v) _ _ h)
      exact ⟨K,fun i => StripChoiceLoopRepair.complete_port b C i⟩
  | true =>
    constructor
    · rintro ⟨K,hK⟩
      let C : (core .d0099).Coloring Color :=
        .mk (fun v => K (vertex0099 v)) (fun h => K.valid h)
      refine ⟨C,fun v => (upper_lists b v (C v)).mpr (fun i hi => ?_)⟩
      change K (vertex0099 v) ≠ b i
      rw [← hK i]
      exact K.valid ((StripResponseSummary.attachments_complete v i).mpr hi)
    · rintro ⟨C,fit⟩
      have valid : StripResponseSummary.ValidCore b C :=
        ⟨fun v => (upper_lists b v (C v)).mp (fit v), fun e he =>
          C.valid ((StripResponseSummary.edges_complete _ _).mpr (Or.inl he))⟩
      exact ⟨StripSourceExtension.colouring b C proper valid,
        fun i => StripSourceExtension.colour_port b C i⟩

theorem proper : ∀ s t, Proper s (boundary s t) ∧ Proper s (update s (boundary s t)) := by
  intro s
  cases s <;> decide +kernel

theorem same_lists : ∀ s, lists s (boundary s false) = lists s (boundary s true) := by
  intro s
  cases s <;> decide +kernel

def obstruction : (s : Bool) → List (Fin (size (source s)) × Fin (size (source s)))
  | false => ([(0,4),(2,4)] : List (Fin 7 × Fin 7))
  | true => ([(0,3)] : List (Fin 8 × Fin 8))

def blockedVertex : (s : Bool) → Fin (size (source s)) | false => (4 : Fin 7) | true => (3 : Fin 8)

theorem obstruction_edges (s : Bool) :
    ∀ e ∈ obstruction s, (core (source s)).Adj e.1 e.2 := by
  cases s <;> decide +kernel

theorem emptied : ∀ s t : Bool,
    run (lists s (if t then update s (boundary s false) else boundary s false))
      (obstruction s) (blockedVertex s) = ∅ := by
  intro s
  cases s <;> decide +kernel

theorem initial_fails (s : Bool) (t : Bool) : ¬ Extends s (boundary s t) := by
  have h := empty_refutes (G := core (source s)) (lists s (boundary s false))
    (obstruction s) (obstruction_edges s) (blockedVertex s) (emptied s false)
  cases t with
  | false => exact h
  | true => unfold Extends; rw [← same_lists s]; exact h

theorem changed_fails (s : Bool) : ¬ Extends s (update s (boundary s false)) :=
  empty_refutes (G := core (source s)) _ (obstruction s) (obstruction_edges s)
    (blockedVertex s) (emptied s true)

/-- The retained cut computes the actual new lists on arbitrary source boundaries. -/
theorem updated_lists (s : Bool) (b : Boundary s) (v) :
    lists s (update s b) v =
      interpret (advance (c1 + ·) (summary (ports s) (cut s) b v)) :=
  allowed_change (ports s) (cut s) _ b v

/-- Both positive consumers use the same joint anchors and forest guard. -/
theorem changed_guard : ∀ s,
    Guard (source s)
      (fun v => interpret (advance (c1 + ·)
        (summary (ports s) (cut s) (boundary s true) v))) (fun _ => c0) 2 := by
  intro s
  cases s <;> unfold Guard Supported <;> decide +kernel

theorem changed_extends (s : Bool) : Extends s (update s (boundary s true)) := by
  obtain ⟨C,fit,_⟩ := guard_colouring (source s) _ _ 2 (changed_guard s)
  exact ⟨C,fun v => (updated_lists s _ v).symm ▸ fit v⟩

/-- Actual source colourings distinguish the results of the same local operation. -/
theorem source_distinguishes (s : Bool) :
    (¬ Full s (update s (boundary s false))) ∧ Full s (update s (boundary s true)) :=
  ⟨fun h => changed_fails s ((full_iff s _ (proper s false).2).mp h),
    (full_iff s _ (proper s true).2).mpr (changed_extends s)⟩

/-- No function of the evaluated core lists alone computes the extension
outcome after this operation, even restricted to proper input and output. -/
theorem no_list_only_transport (s : Bool) : ¬ ∃ result : Lists s → Prop,
    ∀ b : Boundary s, Proper s b → Proper s (update s b) →
      (result (lists s b) ↔ Full s (update s b)) := by
  rintro ⟨result,h⟩
  obtain ⟨bad,good⟩ := source_distinguishes s
  have before := (h _ (proper s true).1 (proper s true).2).mpr good
  rw [← same_lists s] at before
  exact bad ((h _ (proper s false).1 (proper s false).2).mp before)

/-- The moving/fixed summary distinguishes exactly the observation lost here. -/
theorem refined_distinguishes : ∀ s,
    (fun v => summary (ports s) (cut s) (boundary s false) v) ≠
      (fun v => summary (ports s) (cut s) (boundary s true) v) := by
  intro s
  cases s <;> decide +kernel

def word (s : Bool) (t : Bool) (i : Fin (ring s)) : Color :=
  boundary s t i + boundary s t
    ⟨(i.val + 1) % ring s, Nat.mod_lt _ (by cases s <;> decide)⟩

def mate : (s : Bool) → Bool → Fin (ring s) → Fin (ring s)
  | false, false => ![0,1,2,7,4,6,5,3,8,9]
  | false, true => ![0,1,2,4,3,6,5,8,7,9]
  | true, false => ![0,1,2,10,4,6,5,7,8,9,3]
  | true, true => ![0,1,2,4,3,6,5,10,8,9,7]

def start (s : Bool) : Fin (ring s) := ⟨5,by cases s <;> decide⟩

theorem mate_valid : ∀ s t, Function.Involutive (mate s t) ∧
    KempeMatchingChromogram.Noncrossing (mate s t) ∧
    (∀ i, word s t i ≠ 0) ∧ (∀ i, mate s t i = i ↔ word s t i = c1) := by
  intro s
  cases s <;> unfold Function.Involutive <;> decide +kernel

theorem input_trace : ∀ s t, trace (List.ofFn (boundary s t)) = List.ofFn (word s t) := by
  intro s
  cases s <;> decide +kernel

theorem update_trace : ∀ s t, trace (List.ofFn (update s (boundary s t))) =
    List.ofFn (KempeIntervalRepair.switch (word s t) (start s) (mate s t (start s))) := by
  intro s
  cases s <;> decide +kernel

/-- Each update switches a whole component in one supplied abstract
chromogram. No simultaneous physical realization of the examples is assumed. -/
theorem same_chord (s t : Bool) :
    matchg [] (trace (List.ofFn (boundary s t)))
      (KempeMatchingChromogram.gram (mate s t) (word s t)) ∧
    matchg [] (trace (List.ofFn (update s (boundary s t))))
      (KempeMatchingChromogram.gram (mate s t) (word s t)) := by
  rw [input_trace,update_trace]
  obtain ⟨inv,planar,active,fixed⟩ := mate_valid s t
  exact ⟨(KempeMatchingChromogram.reconstruct _ _ inv planar active fixed).1,
    KempeIntervalRepair.switch_matches _ _ inv planar active fixed (start s)⟩

end FourColor.StripListTransport
