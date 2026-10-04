import MettapediaFourColor.StripEndpointTransport
import MettapediaFourColor.GraphDiskEuler
import Mettapedia.GraphTheory.Kempe.SeparatedChains

/-!
# Physical realizations of the list-transport obstruction

Two small planar disk exteriors realize the D0063 and D0099 examples.
Each exterior has two proper colourings with identical full source lists.
The same one-port update is an actual singleton-component switch in each
colouring, but only one resulting boundary admits a source colouring.

The old lists and the old endpoint colour compute the updated lists. Both
positive cases reconstruct through the same compact update and forest law.
These exteriors have
low-degree vertices: minimal-counterexample hypotheses and geometric supply
are not asserted. Source attribution is inherited from StripListTransport.
-/

namespace FourColor.StripPhysicalListTransport

open SimpleGraph Color KempeBoundarySplit
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

abbrev count : Bool → ℕ | false => 11 | true => 13
abbrev width := StripListTransport.ring
instance (s : Bool) : NeZero (count s) := ⟨by cases s <;> decide⟩

def star : (s : Bool) → Fin (count s) → List (Fin (count s))
  | false =>
    ![[1,4,9],
      [0,2,4],
      [1,3,4],
      [2,4],
      [0,1,2,3,5,9],
      [4,6,10,8,9],
      [5,7,10],
      [6,8,10],
      [5,10,7,9],
      [0,4,5,8],
      [5,6,7,8]]
  | true =>
    ![[1,10],
      [0,2,4,5,12,7,8,9,10],
      [1,3,4],
      [2,4],
      [1,2,3,5],
      [1,4,6,11,12],
      [5,7,11],
      [1,12,11,6,8],
      [1,7,9],
      [1,8,10],
      [0,1,9],
      [5,6,7,12],
      [1,5,11,7]]

theorem row_nodup : ∀ s v, (star s v).Nodup := by intro s; cases s <;> decide +kernel
theorem row_symm : ∀ s u v, v ∈ star s u → u ∈ star s v := by intro s; cases s <;> decide +kernel
theorem row_loopless : ∀ s v, v ∉ star s v := by intro s; cases s <;> decide +kernel
theorem row_nonempty : ∀ s v, star s v ≠ [] := by intro s; cases s <;> decide +kernel

def exterior (s : Bool) : SimpleGraph (Fin (count s)) where
  Adj u v := v ∈ star s u
  symm := ⟨row_symm s⟩
  loopless := ⟨row_loopless s⟩
instance (s) : DecidableRel (exterior s).Adj := by unfold exterior; infer_instance

def rows (s : Bool) : GraphRotationRows.Rows (exterior s) :=
  ⟨star s, row_nodup s, fun _ _ => Iff.rfl⟩
def rotation (s : Bool) := (rows s).rotation
  (⟨(0,1), by cases s <;> decide +kernel⟩ : (exterior s).Dart)

theorem cyclic (s : Bool) : (rotation s).IsVertexwiseCyclic := (rows s).cyclic _

def tour : (s : Bool) → List (Fin (count s))
  | false => [0,1,2,3,4,5,6,7,8,9,8,10,8,7,6,5,4,3,2,1,0]
  | true => [0,1,2,3,4,5,6,7,8,9,10,9,8,7,11,12,11,7,6,5,4,3,2,1,0]

theorem tour_nonempty : ∀ s, tour s ≠ [] := by intro s; cases s <;> decide +kernel
theorem tour_chain : ∀ s, (tour s).IsChain (exterior s).Adj := by
  intro s
  cases s <;> decide +kernel
theorem tour_covers : ∀ s v, v ∈ tour s := by intro s; cases s <;> decide +kernel

theorem connected (s : Bool) : (exterior s).Connected := by
  let p := Walk.ofSupport (tour s) (tour_nonempty s) (tour_chain s)
  have reach (v : Fin (count s)) : (exterior s).Reachable ((tour s).head (tour_nonempty s)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers s v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem covered (s : Bool) : Function.Surjective (fun d : (exterior s).Dart => d.fst) := by
  intro v
  obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil (star s v) (row_nonempty s v)
  exact ⟨⟨(v,w),hw⟩,rfl⟩

def port (s : Bool) (i : Fin (width s)) : Fin (count s) :=
  i.castLE (by cases s <;> decide)

theorem boundary_edges : ∀ s i, (exterior s).Adj (port s i) (port s (i+1)) := by
  intro s; cases s <;> decide +kernel

def boundaryDart (s : Bool) (i : Fin (width s)) : (exterior s).Dart :=
  ⟨(port s i,port s (i+1)),boundary_edges s i⟩
def ring (s : Bool) := List.ofFn (boundaryDart s)
def ringPairs (s : Bool) := List.ofFn (fun i => (port s i,port s (i+1)))

theorem mem_ring_iff (s : Bool) (d : (exterior s).Dart) : d ∈ ring s ↔ d.toProd ∈ ringPairs s := by
  have eq : (ring s).map Dart.toProd = ringPairs s := by
    simp [ring, ringPairs, Function.comp_def, boundaryDart]
  rw [← eq,List.mem_map]
  exact ⟨fun h => ⟨d,h,rfl⟩,fun ⟨a,ha,h⟩ => Dart.toProd_injective h ▸ ha⟩

def step (s : Bool) (p : Fin (count s) × Fin (count s)) := (p.2,(rows s).next p.2 p.1)

theorem face_check : ∀ s u v, (exterior s).Adj u v → (u,v) ∉ ringPairs s →
    step s (step s (step s (u,v))) = (u,v) := by intro s; cases s <;> decide +kernel

theorem triangles (s : Bool) : ∀ d : (exterior s).Dart, d ∉ ring s →
    (rotation s).toRotationSystem.phi ((rotation s).toRotationSystem.phi
      ((rotation s).toRotationSystem.phi d)) = d := by
  intro d hd
  apply Dart.ext
  exact face_check s d.fst d.snd d.adj ((mem_ring_iff s d).not.mp hd)

theorem boundary (s : Bool) : IsCyclicChain
    (fun a b => b = (rotation s).toRotationSystem.phi a) (ring s) := by
  cases s with
  | false =>
    change IsCyclicChain (fun a b : (exterior false).Dart =>
      b = (rotation false).vertexRotation a.symm)
      (boundaryDart false 0 ::
        [boundaryDart false 1,
         boundaryDart false 2,
         boundaryDart false 3,
         boundaryDart false 4,
         boundaryDart false 5,
         boundaryDart false 6,
         boundaryDart false 7,
         boundaryDart false 8,
         boundaryDart false 9])
    rw [isCyclicChain_cons]
    decide +kernel
  | true =>
    change IsCyclicChain (fun a b : (exterior true).Dart =>
      b = (rotation true).vertexRotation a.symm)
      (boundaryDart true 0 ::
        [boundaryDart true 1,
         boundaryDart true 2,
         boundaryDart true 3,
         boundaryDart true 4,
         boundaryDart true 5,
         boundaryDart true 6,
         boundaryDart true 7,
         boundaryDart true 8,
         boundaryDart true 9,
         boundaryDart true 10])
    rw [isCyclicChain_cons]
    decide +kernel

theorem distinct : ∀ s, (ring s).Nodup := by intro s; cases s <;> decide +kernel
theorem ordered (s : Bool) : (ring s).map (fun d => d.fst) = List.ofFn (port s) := by
  simp [ring, Function.comp_def, boundaryDart]

theorem dart_count (s : Bool) : Nat.card (exterior s).Dart = if s then 50 else 40 := by
  rw [(rows s).dart_count]
  cases s <;> decide +kernel

theorem planar (s : Bool) : (SimpleGraphBridge.rotationHypermap (rotation s)).Planar :=
  GraphDiskEuler.planar (rotation s) (cyclic s) (connected s) (covered s) (ring s)
    (by cases s <;> decide +kernel) (boundary s) (distinct s) (triangles s)
    (by rw [Nat.card_fin,dart_count]; cases s <;> decide +kernel)

theorem closed (s : Bool) : KempeClosed (GraphTrace (exterior s) (List.ofFn (port s))) := by
  have h := PlanarGraphBoundaryClosure.rotation_closed (rotation s) (cyclic s) (planar s)
    (ring s) (boundary s) (distinct s) (triangles s)
  rwa [ordered] at h

def values (s t : Bool) (v : Fin (count s)) : Color :=
  if h : v.val < width s then StripListTransport.boundary s t ⟨v.val,h⟩
  else if v.val = width s then (if t then c1 else c3)
  else if t then c2 else c0

def root (s : Bool) : Fin (count s) := ⟨6,by cases s <;> decide⟩
def afterValues (s t : Bool) (v : Fin (count s)) : Color :=
  if v = root s then c1 + values s t v else values s t v

theorem proper : ∀ s t u v, (exterior s).Adj u v → values s t u ≠ values s t v := by
  intro s; cases s <;> decide +kernel

theorem after_proper : ∀ s t u v, (exterior s).Adj u v → afterValues s t u ≠ afterValues s t v := by
  intro s; cases s <;> decide +kernel

def state (s t : Bool) : (exterior s).Coloring Color := .mk (values s t) (fun h => proper s t _ _ h)
def afterState (s t : Bool) : (exterior s).Coloring Color :=
  .mk (afterValues s t) (fun h => after_proper s t _ _ h)

theorem read_before : ∀ s t i, state s t (port s i) = StripListTransport.boundary s t i := by
  intro s; cases s <;> decide +kernel

theorem read_after : ∀ s t i, afterState s t (port s i) =
    StripListTransport.update s (StripListTransport.boundary s t) i := by
  intro s; cases s <;> decide +kernel

def pair (t : Bool) : Color × Color := if t then (c2,c3) else (c0,c1)

theorem isolated : ∀ s t y, (exterior s).Adj (root s) y →
    ¬ (state s t y = (pair t).1 ∨ state s t y = (pair t).2) := by
  intro s; cases s <;> decide +kernel

def certificate (s t : Bool) :
    KempeSeparatedChains.Certificate (state s t) (pair t).1 (pair t).2 where
  vertices := [root s]
  root := root s
  root_mem := by simp
  connected := by simp
  active := by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    cases s <;> cases t <;> decide +kernel
  closed := by
    intro x hx y edge hy
    simp only [List.mem_singleton] at hx
    subst x
    exact False.elim (isolated s t y edge hy)

theorem swap_eq (s t : Bool) : (certificate s t).swap = afterState s t := by
  ext v
  rw [KempeSeparatedChains.Certificate.swap_apply]
  change (if v ∈ [root s] then Equiv.swap (pair t).1 (pair t).2 (values s t v)
    else values s t v) = afterValues s t v
  revert v
  cases s <;> cases t <;> decide +kernel

noncomputable def physicalStep (s t : Bool) : Step (state s t) (afterState s t) :=
  (swap_eq s t) ▸ (certificate s t).step

/-- Identical full source lists are observed on two colourings of the same exterior. -/
theorem same_lists (s : Bool) :
    StripListTransport.lists s (fun i => state s false (port s i)) =
      StripListTransport.lists s (fun i => state s true (port s i)) := by
  simp_rw [read_before]
  exact StripListTransport.same_lists s

/-- The actual switch agrees with the endpoint operation on the ordered ports. -/
theorem endpoint_read (s t : Bool) :
    (fun i => afterState s t (port s i)) =
      StripEndpointTransport.change s (c1 + StripListTransport.boundary s t 6)
        (StripListTransport.boundary s t) := by
  cases s <;> cases t <;> decide +kernel

/-- Two small guard checks, with the same joint anchor choice, consume the
compact updated lists. No original boundary assignment is used by `advance`. -/
theorem compact_guard : ∀ s,
    TriangleStripLists.Guard (StripListTransport.source s)
      (StripEndpointTransport.advance s (StripListTransport.boundary s true 6)
        (c1 + StripListTransport.boundary s true 6)
        (StripListTransport.lists s (StripListTransport.boundary s true)))
      (fun _ => c0) 2 := by
  intro s
  cases s <;> unfold TriangleStripLists.Guard ColoringListPropagation.Supported <;>
    decide +kernel

/-- The positive physical switches reconstruct full source colourings via
the endpoint law, retaining every ordered boundary value. -/
theorem compact_reconstruct (s : Bool) :
    StripListTransport.Full s (fun i => afterState s true (port s i)) := by
  rw [endpoint_read]
  apply StripEndpointTransport.guard_full_change s _ _ (StripListTransport.proper s true).1
    ?_ (fun _ => c0) 2 (compact_guard s)
  rw [← endpoint_read]
  simp_rw [read_after]
  exact (StripListTransport.proper s true).2

/-- A physically available command has different actual source-extension outcomes. -/
theorem source_distinguishes (s : Bool) :
    (¬ StripListTransport.Full s (fun i => afterState s false (port s i))) ∧
      StripListTransport.Full s (fun i => afterState s true (port s i)) := by
  refine ⟨?_, compact_reconstruct s⟩
  simp_rw [read_after]
  exact (StripListTransport.source_distinguishes s).1

/-- Restricting to this planar exterior and these physical singleton switches
still does not make the evaluated-list observation sufficient. The command
swaps the root colour with its xor-one mate; its pair depends on that colour. -/
theorem no_list_only_physical_transport (s : Bool) :
    ¬ ∃ result : StripListTransport.Lists s → Prop, ∀ t : Bool,
      (result (StripListTransport.lists s (fun i => state s t (port s i))) ↔
        StripListTransport.Full s (fun i => afterState s t (port s i))) := by
  rintro ⟨result,h⟩
  obtain ⟨bad,good⟩ := source_distinguishes s
  have yes := (h true).mpr good
  rw [← same_lists s] at yes
  exact bad ((h false).mp yes)

end FourColor.StripPhysicalListTransport
