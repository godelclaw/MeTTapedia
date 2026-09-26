import Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeMateDependence
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring
import Mettapedia.GraphTheory.Hypermap.Connectivity
import Mettapedia.GraphTheory.OrbitCountSplitting

/-!
# A planar embedding of the fixed-component Kempe obstruction

The rotation system uses the literal endpoints of `PentagonKempePlateau`.
Its vertex fibres are exactly the rotation cycles. A descending parent
certificate reaches every dart, and all three orbit counts
are certified in the kernel. The resulting connected hypermap is planar.
The five degree-one terminals occur on the outer face in the prescribed order.

The obstruction concerns deterministic boundary updates under Kempe switches;
it does not contradict compositional support semantics for gluing.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempePlaneWitness

open PentagonKempePlateau
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open OrbitCountSplitting

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev Dart := Fin 40 × Fin 2

def vertex (d : Dart) : Fin 30 :=
  if d.2 = 0 then (ends d.1).1 else (ends d.1).2

def index (d : Dart) : Nat := 2 * d.1.val + d.2.val

private def readNat (raw : String) (i : Nat) : Nat :=
  10 * ((raw.toUTF8[2 * i]!).toNat - 48) +
    ((raw.toUTF8[2 * i + 1]!).toNat - 48)

private def decodeDart (n : Nat) : Dart :=
  (⟨n / 2 % 40, Nat.mod_lt _ (by decide)⟩, ⟨n % 2, Nat.mod_lt _ (by decide)⟩)

private def readDart (raw : String) (d : Dart) : Dart := decodeDart (readNat raw (index d))

private def rhoTable : String :=
  "0008021204180122061103241028143216362007054019440946135026311552303517543439215638432358424948272560476229663368377041744576645351786355677372595779716175657769"

private def rhoInvTable : String :=
  "0006021004200819012412090326143016340522183807421148284713523229155436331756403721584441236025504645276431633567397243714975516662775368557957747069597661786573"

def rotation : Equiv.Perm Dart where
  toFun := readDart rhoTable
  invFun := readDart rhoInvTable
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def edgeFlip : Equiv.Perm Dart :=
  Equiv.prodCongr (Equiv.refl (Fin 40)) (Equiv.swap 0 1)

def map : RotationSystem (Fin 30) (Fin 40) where
  D := Dart
  edgeOf := Prod.fst
  vertOf := vertex
  alpha := edgeFlip
  rho := rotation
  alpha_involutive := by decide +kernel
  alpha_fixfree := by decide +kernel
  edge_alpha := by decide +kernel
  edge_fiber_two := by
    intro e
    have h : Finset.univ.filter (fun d : Dart => d.1 = e) =
        ({e} : Finset (Fin 40)) ×ˢ (Finset.univ : Finset (Fin 2)) := by
      ext ⟨d, i⟩
      fin_cases i <;> simp [eq_comm]
    rw [h, Finset.card_product]
    simp
  vert_rho := by decide +kernel
  outer := (0, 0)
  no_self_loops := by decide +kernel

/-- The rotation describes exactly the endpoint graph used by the colouring
counterexample; no vertex or edge identification is hidden in the embedding. -/
theorem endpoints_exact (e : Fin 40) :
    map.vertOf (e, 0) = (ends e).1 ∧ map.vertOf (e, 1) = (ends e).2 := by
  simp [map, vertex]

private theorem label_of_sameCycle {D A : Type*} [Fintype D]
    (p : Equiv.Perm D) (label : D → A) (hinv : ∀ d, label (p d) = label d)
    {d e : D} (h : p.SameCycle d e) : label d = label e := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, hinv] using ih

private theorem sameCycle_of_certificate {D A : Type*} [Fintype D]
    (p : Equiv.Perm D) (label : D → A) (representative : A → D) (offset : D → Nat)
    (hinv : ∀ d, label (p d) = label d)
    (htrace : ∀ d, (p ^ offset d) (representative (label d)) = d) (d e : D) :
    p.SameCycle d e ↔ label d = label e := by
  constructor
  · exact label_of_sameCycle p label hinv
  · intro heq
    have hd : p.SameCycle (representative (label d)) d :=
      ⟨offset d, by rw [zpow_natCast]; exact htrace d⟩
    have he : p.SameCycle (representative (label e)) e :=
      ⟨offset e, by rw [zpow_natCast]; exact htrace e⟩
    rw [heq] at hd
    exact hd.symm.trans he

private theorem count_of_certificate {D : Type*} [Fintype D] [DecidableEq D] {n : Nat}
    (p : Equiv.Perm D) (label : D → Fin n) (representative : Fin n → D) (offset : D → Nat)
    (hinv : ∀ d, label (p d) = label d)
    (htrace : ∀ d, (p ^ offset d) (representative (label d)) = d)
    (hrep : ∀ i, label (representative i) = i) : orbitCount p = n := by
  simpa using orbitCount_eq_card_of_completeInvariant label
    (sameCycle_of_certificate p label representative offset hinv htrace)
    (fun i => ⟨representative i, hrep i⟩)

def embedding : Hypermap Dart := Hypermap.ofRotationSystem map

private def vertexRep (v : Fin 30) : Dart := decodeDart (readNat "000204010314160507091315172123252729333741455153555759616569" v.val)
private def vertexOffset (d : Dart) : Nat := readNat "0000000000000100020001020200000000000201010002000100010002000102020001020200010202000102020002010102020001000100010001000100020101000201020002010102020102010201" (index d)
private def faceLabel (d : Dart) : Fin 12 :=
  ⟨readNat "0000000000000100000102000002000000000003030001030201040200040500000506000006070003070803010802090901040905040605070608070908041010090510061007111106081109111011" (index d) % 12, Nat.mod_lt _ (by decide)⟩
private def faceRep (f : Fin 12) : Dart := decodeDart (readNat "000610192630343842476371" f.val)
private def faceOffset (d : Dart) : Nat := readNat "0021040318170020010500020504090813121900011601040104000306040007100400111405001502040003020402000103010501030103010401030203020001040204020302000103020403030202" (index d)

private theorem vertex_invariant : ∀ d, vertex (embedding.node d) = vertex d := by decide +kernel
private theorem vertex_trace : ∀ d, (embedding.node ^ vertexOffset d) (vertexRep (vertex d)) = d :=
  by decide +kernel

/-- Node cycles are exactly the displayed endpoint vertices. -/
theorem node_fibres_exact (d e : Dart) : embedding.node.SameCycle d e ↔ vertex d = vertex e :=
  sameCycle_of_certificate embedding.node vertex vertexRep vertexOffset vertex_invariant vertex_trace d e

private def rank (d : Dart) : Nat := readNat
  "0001100907060203030407060809181714130504070805060506101111121514161614151211091010090708080908090708101113141718121310111011131412131516171613121415131213141516" (index d)

private def parent (d : Dart) : Dart := readDart
  "0000031205180106060811241012153217361907052019220924135026283152303517343739213838432342424448462548475029523354375641584560646251646366697371595772716175767778" d

private theorem parent_checked : ∀ d : Dart, d ≠ (0, 0) →
    rank (parent d) < rank d ∧
      (embedding.edge (parent d) = d ∨ embedding.node (parent d) = d) := by
  decide +kernel

/-- A strictly descending parent certificate connects every dart to the root. -/
theorem root_reachable (d : Dart) :
    WordReachable [embedding.edge, embedding.node, embedding.face] (0, 0) d := by
  suffices h : ∀ n d, rank d = n →
      WordReachable [embedding.edge, embedding.node, embedding.face] (0, 0) d from
    h (rank d) d rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d hn
    by_cases hd : d = (0, 0)
    · subst d
      exact WordReachable.refl _ _
    · obtain ⟨hrank, hstep⟩ := parent_checked d hd
      have hp := ih (rank (parent d)) (by simpa [hn] using hrank) (parent d) rfl
      rcases hstep with he | he
      · exact he ▸ hp.trans (wordReachable_step
          (g := embedding.edge) List.mem_cons_self (parent d))
      · exact he ▸ hp.trans (wordReachable_step
          (g := embedding.node) (List.mem_cons_of_mem _ List.mem_cons_self) (parent d))

theorem component_count : Hypermap.compCount embedding = 1 := by
  have h := wordOrbitCount_eq_card_of_completeInvariant
    (L := [embedding.edge, embedding.node, embedding.face]) (fun _ : Dart => ())
    (fun d e => ⟨fun _ => rfl, fun _ => (root_reachable d).symm.trans (root_reachable e)⟩)
    (fun _ => ⟨(0, 0), rfl⟩)
  simpa [Hypermap.compCount] using h

theorem edge_count : orbitCount embedding.edge = 40 :=
  count_of_certificate embedding.edge Prod.fst (fun e => (e, 0)) (fun d => d.2.val)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem vertex_count : orbitCount embedding.node = 30 :=
  count_of_certificate embedding.node vertex vertexRep vertexOffset
    vertex_invariant vertex_trace (by decide +kernel)

private theorem face_invariant : ∀ d, faceLabel (embedding.face d) = faceLabel d :=
  by decide +kernel

private theorem face_trace : ∀ d, (embedding.face ^ faceOffset d) (faceRep (faceLabel d)) = d :=
  by decide +kernel

theorem face_count : orbitCount embedding.face = 12 :=
  count_of_certificate embedding.face faceLabel faceRep faceOffset
    face_invariant face_trace (by decide +kernel)

/-- The existing Euler-defect definition of hypermap planarity. -/
theorem planar : embedding.Planar := by
  simp only [Hypermap.Planar, Hypermap.eulerDefect, Hypermap.eulerLhs,
    Hypermap.eulerRhs_eq_card_add_two_mul_compCount,
    edge_count, vertex_count, face_count, component_count]
  decide

/-- The distinguished outward dart of each boundary edge. -/
def terminal (i : Fin 5) : Dart := (ports i, 0)

/-- A cyclic listing of the outer-face darts. -/
def outerDart (i : Fin 22) : Dart :=
  decodeDart (readNat "00081103021228311514323517163639210504180701" i.val)

theorem outerDart_zero : outerDart 0 = map.outer := by
  change outerDart 0 = ((0, 0) : Dart)
  decide +kernel

theorem outerDart_injective : Function.Injective outerDart := by decide +kernel

theorem outerDart_next : ∀ i, embedding.face (outerDart i) = outerDart (i + 1) :=
  by decide +kernel

/-- Reading the outer face encounters the five terminals in port order. -/
theorem terminals_in_order :
    ((List.finRange 22).map outerDart).filter (fun d => decide (∃ i, d = terminal i)) =
      (List.finRange 5).map terminal := by decide +kernel

theorem terminal_on_outer (i : Fin 5) : embedding.face.SameCycle map.outer (terminal i) := by
  apply (sameCycle_of_certificate embedding.face faceLabel faceRep faceOffset
    face_invariant face_trace _ _).mpr
  have h : ∀ j, faceLabel map.outer = faceLabel (terminal j) := by decide +kernel
  exact h i

theorem terminal_vertices_distinct : Function.Injective (vertex ∘ terminal) :=
  by decide +kernel

/-- Exactly the five terminals have degree one; every other vertex is cubic. -/
theorem vertex_degrees : ∀ v : Fin 30,
    (map.dartsAt v).card = if ∃ i, v = vertex (terminal i) then 1 else 3 :=
  by decide +kernel

theorem endpoints_finset (e : Fin 40) :
    map.endpoints e = {(ends e).1, (ends e).2} := by
  have hd : (e, 0) ∈ map.dartsOn e := map.mem_dartsOn.mpr rfl
  have ha : map.alpha (e, 0) = (e, 1) := by
    change (e, Equiv.swap (0 : Fin 2) 1 0) = (e, 1)
    rw [Equiv.swap_apply_left]
  rw [map.endpoints_eq_pair_of_mem hd, ha, (endpoints_exact e).1, (endpoints_exact e).2]

/-- The embedding's edge adjacency is exactly the literal incidence relation. -/
theorem edge_adj_iff (e f : Fin 40) :
    map.edgeAdjacencyGraph.Adj e f ↔ e ≠ f ∧ InternalEdgeOpening.Touch ends e f := by
  rw [RotationSystem.edgeAdjacencyGraph_adj_iff, endpoints_finset, endpoints_finset]
  simp only [Finset.mem_insert, Finset.mem_singleton, InternalEdgeOpening.Touch]
  aesop

/-- Each of the four endpoint colourings is a proper colouring of the
rotation system's edge-adjacency graph, with identical edge values. -/
def edgeColoring (s : Fin 4) : map.EdgeColoring (Fin 3) where
  toFun := PentagonKempeMateDependence.coloring s
  map_rel' h := by
    obtain ⟨hne, ht⟩ := (edge_adj_iff _ _).mp h
    exact PentagonKempeMateDependence.colorings_proper s _ _ hne ht

def ChannelConnected (c : Fin 40 → Fin 3) (p : Fin 3) : Fin 40 → Fin 40 → Prop :=
  Relation.EqvGen (fun e f => map.edgeAdjacencyGraph.Adj e f ∧ Active c p e ∧ Active c p f)

/-- Kempe connectedness transports exactly; deleting reflexive local steps
does not change equivalence closure. -/
theorem channelConnected_iff (c : Fin 40 → Fin 3) (p : Fin 3) (e f : Fin 40) :
    ChannelConnected c p e f ↔ PentagonKempeMateDependence.Connected c p e f := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
      exact Relation.EqvGen.rel _ _ ⟨((edge_adj_iff a b).mp h.1).2, h.2⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | rel a b h =>
      by_cases hab : a = b
      · subst b
        exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ ⟨(edge_adj_iff a b).mpr ⟨hab, h.1⟩, h.2⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def SameBoundaryData (c d : map.EdgeColoring (Fin 3)) : Prop :=
  boundary c = boundary d ∧ ∀ p i j,
    ChannelConnected c p (ports i) (ports j) ↔ ChannelConnected d p (ports i) (ports j)

theorem sameBoundaryData_iff (c d : map.EdgeColoring (Fin 3)) :
    SameBoundaryData c d ↔ PentagonKempeMateDependence.SameBoundaryData c d := by
  simp only [SameBoundaryData, PentagonKempeMateDependence.SameBoundaryData,
    channelConnected_iff]

/-- On this connected planar five-pole, the same exact rooted component
switch changes boundary observations differently at identical boundary data. -/
theorem planar_fixed_component_obstruction :
    embedding.Planar ∧ Hypermap.compCount embedding = 1 ∧
    SameBoundaryData (edgeColoring 0) (edgeColoring 1) ∧
    (∀ s : Fin 2, ∀ e, PentagonKempeMateDependence.regionMask e = true ↔
      ChannelConnected (edgeColoring (s.castAdd 2)) 0 (ports 0) e) ∧
    (∀ e, edgeColoring 2 e = PentagonKempePlateau.switch (edgeColoring 0) 0
      PentagonKempeMateDependence.regionMask e) ∧
    (∀ e, edgeColoring 3 e = PentagonKempePlateau.switch (edgeColoring 1) 0
      PentagonKempeMateDependence.regionMask e) ∧
    ¬SameBoundaryData (edgeColoring 2) (edgeColoring 3) := by
  refine ⟨planar, component_count,
    (sameBoundaryData_iff _ _).mpr PentagonKempeMateDependence.same_before,
    ?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · intro s e
    rw [channelConnected_iff]
    exact PentagonKempeMateDependence.common_root_component s e
  · intro h
    exact PentagonKempeMateDependence.different_after ((sameBoundaryData_iff _ _).mp h)

end Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempePlaneWitness
