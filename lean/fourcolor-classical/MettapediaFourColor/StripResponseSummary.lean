import MettapediaFourColor.StripTwoRoundRepair
import MettapediaFourColor.PatchWitness

/-!
# Exact source elimination and a boundary-update obstruction

The six binary relations below eliminate the D0099 ears in source order.
They retain common witnesses and every intervening edge constraint. Their
terminal relation is equivalent to core extension for arbitrary boundary
colours. Equality of evaluated relations does not assert preservation under
subsequent boundary updates.
-/

namespace FourColor.StripResponseSummary

open Color TriangleStripAnchors

abbrev Boundary := Fin 11 → Color

def port (i : Fin 11) : Fin 19 := ⟨i.val, by omega⟩

def attachments : Fin 8 → List (Fin 11) :=
  ![[6,7,8],[8],[3,4],[4,5,6],[8,9],[1,2,3],[9,10],[0,1,10]]

theorem attachments_complete : ∀ v i,
    input0099.graph.Adj (vertex0099 v) (port i) ↔ i ∈ attachments v := by decide +kernel

def unary (b : Boundary) (v : Fin 8) (a : Color) : Prop :=
  ∀ i ∈ attachments v, a ≠ b i

instance (b : Boundary) (v : Fin 8) (a : Color) : Decidable (unary b v a) := by
  unfold unary
  infer_instance

/-- Actual internal edges, with one orientation retained for each. -/
def edges : List (Fin 8 × Fin 8) :=
  [(0,1),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6),
    (4,6),(5,6),(5,7),(6,7)]

theorem edges_complete : ∀ (u v : Fin 8),
    (core .d0099).Adj u v ↔ (u,v) ∈ edges ∨ (v,u) ∈ edges := by
  change ∀ u v : Fin 8, (_ ≠ _ ∧ (_ ∨ _ ∨ _)) ↔ _
  unfold NearLinearDiamondData.Input.ringEdge
  decide +kernel

def ValidCore (b : Boundary) (f : Fin 8 → Color) : Prop :=
  (∀ v, unary b v (f v)) ∧ ∀ e ∈ edges, f e.1 ≠ f e.2

/-- A common-witness join, including the edge between the surviving ports. -/
def join (A B C : Color → Prop) (R S : Color → Color → Prop)
    (a b : Color) : Prop :=
  A a ∧ B b ∧ a ≠ b ∧ ∃ c, C c ∧ R a c ∧ S c b

instance (A B C : Color → Prop) (R S : Color → Color → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C]
    [DecidableRel R] [DecidableRel S] (a b : Color) : Decidable (join A B C R S a b) := by
  unfold join
  infer_instance

def r0 (b : Boundary) := join (unary b 1) (unary b 3) (unary b 0) (· ≠ ·) (· ≠ ·)
def r1 (b : Boundary) := join (unary b 1) (unary b 2) (unary b 3) (r0 b) (· ≠ ·)
def r2 (b : Boundary) := join (unary b 2) (unary b 4) (unary b 1) (fun a c => r1 b c a) (· ≠ ·)
def r3 (b : Boundary) := join (unary b 2) (unary b 6) (unary b 4) (r2 b) (· ≠ ·)
def r4 (b : Boundary) := join (unary b 5) (unary b 6) (unary b 2) (· ≠ ·) (r3 b)
def r5 (b : Boundary) := join (unary b 6) (unary b 7) (unary b 5) (fun a c => r4 b c a) (· ≠ ·)

instance (b : Boundary) : DecidableRel (r0 b) := by unfold r0; infer_instance
instance (b : Boundary) : DecidableRel (r1 b) := by unfold r1; infer_instance
instance (b : Boundary) : DecidableRel (r2 b) := by unfold r2; infer_instance
instance (b : Boundary) : DecidableRel (r3 b) := by unfold r3; infer_instance
instance (b : Boundary) : DecidableRel (r4 b) := by unfold r4; infer_instance
instance (b : Boundary) : DecidableRel (r5 b) := by unfold r5; infer_instance

def relation (b : Boundary) (j : Fin 6) : Color → Color → Prop :=
  match j.val with
  | 0 => r0 b | 1 => r1 b | 2 => r2 b | 3 => r3 b | 4 => r4 b | _ => r5 b

instance (b : Boundary) (j : Fin 6) : DecidableRel (relation b j) := by
  unfold relation
  split <;> infer_instance

/-- Exact extension and reconstruction, uniformly over the boundary colours. -/
theorem terminal_iff (b : Boundary) :
    (∃ a c, r5 b a c) ↔ ∃ f, ValidCore b f := by
  constructor
  · rintro ⟨a6, a7, h6, h7, h67, a5, h5, h4, h57⟩
    rcases h4 with ⟨_, _, h56, a2, h2, h52, h3⟩
    rcases h3 with ⟨_, _, h26, a4, h4, hR2, h46⟩
    rcases hR2 with ⟨_, _, h24, a1, h1, hR1, h14⟩
    rcases hR1 with ⟨_, _, h12, a3, h3, hR0, h32⟩
    rcases hR0 with ⟨_, _, h13, a0, h0, h10, h03⟩
    refine ⟨![a0,a1,a2,a3,a4,a5,a6,a7], ?_⟩
    simp [ValidCore, edges, Fin.forall_fin_succ, h0, h1, h2, h3, h4, h5, h6, h7,
      h67, h57, h56, h52, h26, h46, h24, h14, h12, h32.symm, h13, h10, h03, ne_comm]
  · rintro ⟨f, hU, hE⟩
    have e {i j : Fin 8} (h : (i,j) ∈ edges) : f i ≠ f j := hE _ h
    refine ⟨f 6, f 7, hU 6, hU 7, e (by decide), f 5, hU 5, ?_, e (by decide)⟩
    refine ⟨hU 5, hU 6, e (by decide), f 2, hU 2, (e (i := 2) (j := 5) (by decide)).symm, ?_⟩
    refine ⟨hU 2, hU 6, e (by decide), f 4, hU 4, ?_, e (by decide)⟩
    refine ⟨hU 2, hU 4, e (by decide), f 1, hU 1, ?_, e (by decide)⟩
    refine ⟨hU 1, hU 2, e (by decide), f 3, hU 3, ?_, (e (i := 2) (j := 3) (by decide)).symm⟩
    exact ⟨hU 1, hU 3, e (by decide), f 0, hU 0,
      (e (i := 0) (j := 1) (by decide)).symm, e (by decide)⟩

/-- Source colourings satisfy the exact core constraints. -/
theorem valid_of_colouring (b : Boundary) (k : input0099.graph.Coloring Color)
    (hb : ∀ i, k (port i) = b i) : ValidCore b (fun v => k (vertex0099 v)) := by
  constructor
  · intro v i hi
    rw [← hb i]
    exact k.valid ((attachments_complete v i).mpr hi)
  · intro e he
    apply k.valid
    exact (edges_complete e.1 e.2).mpr (Or.inl he)

/-- No full source colouring can have a trace with an empty terminal relation. -/
theorem no_trace (b : Boundary) (empty : ¬ ∃ a c, r5 b a c) :
    ¬ KempeBoundarySplit.GraphTrace input0099.graph input0099.boundary
      (trace (List.ofFn b)) := by
  rintro ⟨k, hk⟩
  have hb : input0099.boundary.map k = List.ofFn (fun i => k (port i)) := by
    rw [List.ofFn_eq_map]
    rfl
  rw [hb] at hk
  have hs := ringColors_eq_shift (A := List.ofFn b)
    (B := List.ofFn (fun i => k (port i))) (by simp) hk
  let s := (List.ofFn b).headD 0 + (List.ofFn (fun i => k (port i))).headD 0
  have hi : ∀ i, k (port i) = s + b i := by
    have hf : (fun i => k (port i)) = (fun i => s + b i) :=
      List.ofFn_injective (by simpa only [List.map_ofFn, Function.comp_def, s] using hs)
    exact congrFun hf
  let shifted : input0099.graph.Coloring Color := .mk (fun v => s + k v)
    (fun h eq => k.valid h (add_left_cancel eq))
  have hg : ∀ i, shifted (port i) = b i := by
    intro i
    change s + k (port i) = b i
    rw [hi, ← add_assoc, Color.add_self, zero_add]
  exact empty ((terminal_iff b).mpr ⟨_, valid_of_colouring b shifted hg⟩)

def boundary : Bool → Boundary
  | false => ![c0,c1,c0,c1,c3,c2,c0,c3,c1,c0,c1]
  | true => ![c0,c1,c3,c1,c3,c2,c0,c3,c1,c0,c1]

/-- The same update of the same interval in each boundary. -/
def update (b : Boundary) (i : Fin 11) : Color :=
  if 2 ≤ i.val ∧ i.val ≤ 9 then c3 + b i else b i

/-- A common noncrossing matching layout for the two inputs. Its chromogram
is allowed to depend on the endpoint colours. -/
def mate : Fin 11 → Fin 11 := ![10,9,3,2,5,4,6,8,7,1,0]

def normalized (b : Boundary) (i : Fin 11) : Color :=
  EdgePerm.e321 (b i + b ⟨(i.val + 1) % 11, Nat.mod_lt _ (by decide)⟩)

theorem mate_valid : Function.Involutive mate ∧
    KempeMatchingChromogram.Noncrossing mate ∧
    ∀ s : Bool, (∀ i, normalized (boundary s) i ≠ 0) ∧
      (∀ i, mate i = i ↔ normalized (boundary s) i = c1) := by
  unfold Function.Involutive
  decide +kernel

theorem input_trace : ∀ s : Bool,
    (trace (List.ofFn (boundary s))).map EdgePerm.e321 =
      List.ofFn (normalized (boundary s)) := by decide +kernel

theorem update_trace : ∀ s : Bool,
    (trace (List.ofFn (update (boundary s)))).map EdgePerm.e321 =
      List.ofFn (KempeIntervalRepair.switch (normalized (boundary s)) 1 (mate 1)) :=
  by decide +kernel

/-- Each input and its update match the same chromogram: the update switches
the whole chord between boundary edges 1 and 9. This asserts an abstract
component matching, not realization by a particular surrounding graph. -/
theorem same_chord_update (s : Bool) :
    matchg [] ((trace (List.ofFn (boundary s))).map EdgePerm.e321)
      (KempeMatchingChromogram.gram mate (normalized (boundary s))) ∧
    matchg [] ((trace (List.ofFn (update (boundary s)))).map EdgePerm.e321)
      (KempeMatchingChromogram.gram mate (normalized (boundary s))) := by
  rw [input_trace, update_trace]
  exact ⟨(KempeMatchingChromogram.reconstruct mate _ mate_valid.1 mate_valid.2.1
    (mate_valid.2.2 s).1 (mate_valid.2.2 s).2).1,
    KempeIntervalRepair.switch_matches mate _ mate_valid.1 mate_valid.2.1
      (mate_valid.2.2 s).1 (mate_valid.2.2 s).2 1⟩

theorem only_one_port : ∀ i, i ≠ 2 → boundary false i = boundary true i := by decide +kernel

theorem retained_port_differs : boundary false 2 ≠ boundary true 2 := by decide +kernel

theorem equal_relations : ∀ j a c,
    relation (boundary false) j a c ↔ relation (boundary true) j a c := by decide +kernel

theorem empty_after_update : ¬ ∃ a c, r5 (update (boundary true)) a c := by decide +kernel

/-- One updated boundary is an already checked full source colouring. -/
theorem extends_after_update : KempeBoundarySplit.GraphTrace input0099.graph
    input0099.boundary (trace (List.ofFn (update (boundary false)))) := by
  exact ⟨StripTwoRoundRepair.colouring 0, by decide +kernel⟩

theorem fails_after_update : ¬ KempeBoundarySplit.GraphTrace input0099.graph
    input0099.boundary (trace (List.ofFn (update (boundary true)))) :=
  no_trace _ empty_after_update

/-- The evaluated joint relations are not a congruence for boundary updates.
A transport preserving this operation must retain additional observations. -/
theorem not_update_congruence : ¬ (∀ b c : Boundary,
    (∀ j a d, relation b j a d ↔ relation c j a d) →
    (KempeBoundarySplit.GraphTrace input0099.graph input0099.boundary
      (trace (List.ofFn (update b))) ↔
     KempeBoundarySplit.GraphTrace input0099.graph input0099.boundary
      (trace (List.ofFn (update c))))) := by
  intro transport
  exact fails_after_update ((transport _ _ equal_relations).mp extends_after_update)

end FourColor.StripResponseSummary
