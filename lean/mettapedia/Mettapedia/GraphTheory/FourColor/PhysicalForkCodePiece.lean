import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeTransport
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeBase

/-!
# Open pieces of cubic maps

An open piece is a finite graph whose vertices carry three cyclically ordered
slots.  Each end of each edge occupies one slot; a slot that no end occupies is
open.  A piece is embedded in a cubic map when its vertices, edges and slots
are sent to vertices, edges and darts of the map so that the rotation of the
map steps through the slots of each vertex, the ends of each edge go to the two
darts of its image, and open slots go to darts of other edges.

The image of the edges of an embedded piece is an edge shore.  Its middle
vertices are the images of the vertices with an open slot, and its `two` field
counts the ends at those vertices.  Nothing about the rest of the map enters.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodePiece

open Equiv Equiv.Perm
open GoertzelV24ForkInterfaceSupport GoertzelV24OrderedCutFaceReturnProfile
open EdgeShoreFaceForkFold PhysicalForkCodeFaces PhysicalForkCodeCut PhysicalForkCodeEuler
open PhysicalForkCodeFold PhysicalForkCode

theorem zmod3_cases : ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

theorem zmod3_add_ne : ∀ k : ZMod 3, k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 2 ≠ k + 1 := by decide

theorem zmod3_add_three : ∀ k : ZMod 3, k + 1 + 1 + 1 = k := by decide

noncomputable section
attribute [local instance] Classical.propDecidable

/-- An open piece of a cubic map. -/
structure Piece where
  V : Type
  E : Type
  [instFintypeV : Fintype V]
  [instDecEqV : DecidableEq V]
  [instFintypeE : Fintype E]
  [instDecEqE : DecidableEq E]
  place : E × Bool → V × ZMod 3
  place_injective : Function.Injective place
  loopless : ∀ e, (place (e, false)).1 ≠ (place (e, true)).1
  covered : ∀ v, ∃ x, (place x).1 = v

attribute [instance] Piece.instFintypeV Piece.instDecEqV Piece.instFintypeE Piece.instDecEqE

namespace Piece

variable (P : Piece)

/-- A slot occupied by an end of an edge. -/
def Filled (s : P.V × ZMod 3) : Prop := s ∈ Set.range P.place

/-- A vertex with an open slot. -/
def IsOpen (v : P.V) : Prop := ∃ k, ¬ P.Filled (v, k)

abbrev OpenV := {v : P.V // P.IsOpen v}

/-- The vertex carries two consecutive ends. -/
def two (v : P.V) : Bool := decide (∃ k : ZMod 3, P.Filled (v, k) ∧ P.Filled (v, k + 1))

theorem filled_place (x : P.E × Bool) : P.Filled (P.place x) := ⟨x, rfl⟩

end Piece

/-! ## Embeddings -/

variable {V' E' : Type*} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']

/-- An embedding of a piece in a rotation system. -/
structure Emb (P : Piece) (RS : RotationSystem V' E') where
  vmap : P.V → V'
  vmap_injective : Function.Injective vmap
  emap : P.E → E'
  emap_injective : Function.Injective emap
  smap : P.V × ZMod 3 → RS.D
  vertOf_smap : ∀ s, RS.vertOf (smap s) = vmap s.1
  rho_smap : ∀ v k, RS.rho (smap (v, k)) = smap (v, k + 1)
  edgeOf_place : ∀ x, RS.edgeOf (smap (P.place x)) = emap x.1
  alpha_place : ∀ e b, RS.alpha (smap (P.place (e, b))) = smap (P.place (e, !b))
  open_not_shore : ∀ s, ¬ P.Filled s → RS.edgeOf (smap s) ∉ Set.range emap

namespace Emb

variable {P : Piece} {RS : RotationSystem V' E'} (emb : Emb P RS)

/-- The shore of an embedded piece. -/
def shore : Finset E' := Finset.univ.image emb.emap

theorem mem_shore {e : E'} : e ∈ emb.shore ↔ e ∈ Set.range emb.emap := by
  simp [shore]

theorem smap_add (v : P.V) (k : ZMod 3) :
    emb.smap (v, k + 1) = RS.rho (emb.smap (v, k)) := (emb.rho_smap v k).symm

theorem smap_add_two (v : P.V) (k : ZMod 3) :
    emb.smap (v, k + 2) = RS.rho (RS.rho (emb.smap (v, k))) := by
  rw [emb.rho_smap, emb.rho_smap, add_assoc, one_add_one_eq_two]

variable (hC : Cubic3 RS)
include hC

theorem smap_injective : Function.Injective emb.smap := by
  rintro ⟨v, k⟩ ⟨w, l⟩ h
  have hv : v = w := emb.vmap_injective (by
    rw [← emb.vertOf_smap (v, k), ← emb.vertOf_smap (w, l), h])
  subst hv
  have hne := zmod3_add_ne k
  rcases zmod3_cases (l - k) with h0 | h1 | h2
  · have : l = k := by rw [sub_eq_zero] at h0; exact h0
    rw [this]
  · have hl : l = k + 1 := by rw [← h1]; ring
    rw [hl, smap_add] at h
    exact absurd h.symm (hC.moves _)
  · have hl : l = k + 2 := by rw [← h2]; ring
    rw [hl, smap_add_two] at h
    exact absurd h.symm (rho_rho_ne hC _)

/-- The darts at the image of a vertex are its three slots. -/
theorem dart_at (v : P.V) {d : RS.D} (hd : RS.vertOf d = emb.vmap v) :
    ∃ k, emb.smap (v, k) = d := by
  obtain ⟨x, hx⟩ := P.covered v
  set k := (P.place x).2
  have h0 : RS.vertOf d = RS.vertOf (emb.smap (v, k)) := by rw [emb.vertOf_smap, hd]
  rcases hC.fiber (emb.smap (v, k)) d h0 with h | h | h
  · exact ⟨k, h.symm⟩
  · exact ⟨k + 1, by rw [emb.smap_add]; exact h.symm⟩
  · exact ⟨k + 2, by rw [emb.smap_add_two]; exact h.symm⟩

omit hC in
theorem inShore_smap_place (x : P.E × Bool) : InShore RS.edgeOf emb.shore (emb.smap (P.place x)) := by
  change RS.edgeOf _ ∈ emb.shore
  rw [emb.mem_shore, emb.edgeOf_place]
  exact ⟨x.1, rfl⟩

/-- Shore darts are the images of the ends. -/
theorem inShore_iff (d : RS.D) :
    InShore RS.edgeOf emb.shore d ↔ ∃ x, emb.smap (P.place x) = d := by
  constructor
  · intro hd
    change RS.edgeOf d ∈ emb.shore at hd
    obtain ⟨e, he⟩ := emb.mem_shore.mp hd
    have hmem : ∀ b, emb.smap (P.place (e, b)) ∈ RS.dartsOn (emb.emap e) := fun b =>
      (RotationSystem.mem_dartsOn RS).mpr (emb.edgeOf_place (e, b))
    have hne : emb.smap (P.place (e, false)) ≠ emb.smap (P.place (e, true)) := fun h =>
      absurd (P.place_injective (emb.smap_injective hC h)) (by simp)
    have hsub : ({emb.smap (P.place (e, false)), emb.smap (P.place (e, true))} : Finset RS.D) =
        RS.dartsOn (emb.emap e) := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hmem false
        · rw [Finset.mem_singleton.mp hy]; exact hmem true
      · rw [Finset.card_pair hne]
        exact (RS.edge_fiber_two (emb.emap e)).le
    have hdm : d ∈ RS.dartsOn (emb.emap e) := (RotationSystem.mem_dartsOn RS).mpr he.symm
    rw [← hsub] at hdm
    rcases Finset.mem_insert.mp hdm with h | h
    · exact ⟨(e, false), h.symm⟩
    · exact ⟨(e, true), (Finset.mem_singleton.mp h).symm⟩
  · rintro ⟨x, rfl⟩
    exact emb.inShore_smap_place x

theorem inShore_smap_iff (s : P.V × ZMod 3) :
    InShore RS.edgeOf emb.shore (emb.smap s) ↔ P.Filled s := by
  rw [emb.inShore_iff hC]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, emb.smap_injective hC hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem mem_touched_iff (v' : V') :
    v' ∈ touched RS emb.shore ↔ ∃ v, emb.vmap v = v' := by
  rw [mem_touched]
  constructor
  · rintro ⟨d, hv, hd⟩
    obtain ⟨x, rfl⟩ := (emb.inShore_iff hC d).mp hd
    exact ⟨(P.place x).1, by rw [← hv, emb.vertOf_smap]⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨x, hx⟩ := P.covered v
    exact ⟨emb.smap (P.place x), by rw [emb.vertOf_smap, hx], emb.inShore_smap_place x⟩

/-- **The middle vertices of an embedded piece are the images of its open
vertices.** -/
theorem mem_mid_iff (v' : V') :
    v' ∈ mid RS.endpoints emb.shore ↔ ∃ v, P.IsOpen v ∧ emb.vmap v = v' := by
  rw [PhysicalForkCodeFaces.mem_mid_iff]
  constructor
  · rintro ⟨⟨d, hv, hd⟩, ⟨d', hv', hd'⟩⟩
    obtain ⟨x, rfl⟩ := (emb.inShore_iff hC d).mp hd
    rw [emb.vertOf_smap] at hv
    obtain ⟨k, rfl⟩ := emb.dart_at hC (P.place x).1 (hv'.trans hv.symm)
    exact ⟨(P.place x).1, ⟨k, fun hk => hd' ((emb.inShore_smap_iff hC _).mpr hk)⟩, hv⟩
  · rintro ⟨v, ⟨k, hk⟩, rfl⟩
    obtain ⟨x, hx⟩ := P.covered v
    refine ⟨⟨emb.smap (P.place x), by rw [emb.vertOf_smap, hx], emb.inShore_smap_place x⟩,
      ⟨emb.smap (v, k), emb.vertOf_smap _, fun h => hk ((emb.inShore_smap_iff hC _).mp h)⟩⟩

/-- The middle vertices, named by the open vertices. -/
def midEquiv : P.OpenV ≃ MidVertex RS emb.shore :=
  Equiv.ofBijective (fun w => ⟨emb.vmap w.1, (emb.mem_mid_iff hC _).mpr ⟨w.1, w.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (emb.vmap_injective (congrArg Subtype.val h)), fun y => by
      obtain ⟨v, hv, hy⟩ := (emb.mem_mid_iff hC y.1).mp y.2
      exact ⟨⟨v, hv⟩, Subtype.ext hy⟩⟩

@[simp] theorem midEquiv_apply (w : P.OpenV) : (emb.midEquiv hC w).1 = emb.vmap w.1 := rfl

/-- The labelling of the middle vertices induced by a labelling of the open
vertices. -/
def label {n : ℕ} (ℓ : Fin n ≃ P.OpenV) : Fin n ≃ MidVertex RS emb.shore :=
  ℓ.trans (emb.midEquiv hC)

@[simp] theorem label_apply {n : ℕ} (ℓ : Fin n ≃ P.OpenV) (i : Fin n) :
    (emb.label hC ℓ i).1 = emb.vmap (ℓ i).1 := rfl

/-- The interface dart of the shore at the image of an open vertex, read as a
slot: the occupied slot followed by an open one. -/
theorem iface_slot {n : ℕ} (ℓ : Fin n ≃ P.OpenV) (i : Fin n) :
    ∃ k, RS.alpha (faceLabel hC emb.shore (emb.label hC ℓ) i).1 = emb.smap ((ℓ i).1, k) ∧
      P.Filled ((ℓ i).1, k) ∧ ¬ P.Filled ((ℓ i).1, k + 1) := by
  obtain ⟨hS, hS', hv⟩ := leftMark_facts hC (emb.label hC ℓ) i
  rw [label_apply] at hv
  obtain ⟨k, hk⟩ := emb.dart_at hC (ℓ i).1 hv
  refine ⟨k, hk.symm, (emb.inShore_smap_iff hC _).mp (hk ▸ hS), fun h => hS' ?_⟩
  rw [← hk, emb.rho_smap]
  exact (emb.inShore_smap_iff hC _).mpr h

/-- **The `two` field of an embedded piece is its own.** -/
theorem codeTwo_eq {n : ℕ} (ℓ : Fin n ≃ P.OpenV) (i : Fin n) :
    codeTwo hC emb.shore (emb.label hC ℓ) i = P.two (ℓ i).1 := by
  obtain ⟨k, hk, hf, ho⟩ := emb.iface_slot hC ℓ i
  unfold codeTwo Piece.two
  rw [hk, emb.rho_smap, emb.rho_smap, decide_eq_decide, emb.inShore_smap_iff hC]
  constructor
  · intro h2
    exact ⟨k + 1 + 1, h2, by rw [zmod3_add_three]; exact hf⟩
  · rintro ⟨l, hl, hl'⟩
    have hne := zmod3_add_ne k
    rcases zmod3_cases (l - k) with h0 | h1 | h2
    · have : l = k := by rw [sub_eq_zero] at h0; exact h0
      subst this
      exact absurd hl' ho
    · have : l = k + 1 := by rw [← h1]; ring
      subst this
      exact absurd hl ho
    · have : l = k + 2 := by rw [← h2]; ring
      subst this
      rw [show k + 1 + 1 = k + 2 by ring]
      exact hl

omit hC in
theorem shore_card : emb.shore.card = Fintype.card P.E := by
  rw [shore, Finset.card_image_of_injective _ emb.emap_injective, Finset.card_univ]

theorem touched_card : (touched RS emb.shore).card = Fintype.card P.V := by
  have : touched RS emb.shore = Finset.univ.image emb.vmap := by
    ext v'
    rw [emb.mem_touched_iff hC]
    simp
  rw [this, Finset.card_image_of_injective _ emb.vmap_injective, Finset.card_univ]

end Emb

/-! ## Realization -/

/-- **A piece realizes a code.**  Its `two` field is the piece's own, and in
every cubic map in which the piece is embedded its shore has the code, is
connected, and satisfies Euler's formula for the sphere. -/
structure Realizes (P : Piece) {n : ℕ} (ℓ : Fin n ≃ P.OpenV) (c : Code n) : Prop where
  two : ∀ i, c.two i = P.two (ℓ i).1
  shore : ∀ {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
    (RS : RotationSystem.{0, 0, 0} V' E') (hC : Cubic3 RS)
    (_hcubic : ∀ v : V', (Finset.univ.filter fun e => v ∈ RS.endpoints e).card = 3)
    (emb : Emb P RS),
      encode hC emb.shore (emb.label hC ℓ) = c ∧ ShoreConnected RS emb.shore ∧
        (touched RS emb.shore).card +
          (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha emb.shore).partition.parts.card =
            2 + emb.shore.card

/-! ## A single edge -/

/-- A single edge: its two ends sit in slot `0` at two vertices. -/
def leafPiece : Piece where
  V := Fin 2
  E := Unit
  place x := (if x.2 then 1 else 0, 0)
  place_injective := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases a <;> cases b <;> simp_all
  loopless _ := by simp
  covered v := by
    fin_cases v
    · exact ⟨((), false), rfl⟩
    · exact ⟨((), true), rfl⟩

theorem leafPiece_filled (v : Fin 2) (k : ZMod 3) : leafPiece.Filled (v, k) ↔ k = 0 := by
  constructor
  · rintro ⟨⟨⟨⟩, b⟩, h⟩
    have := congrArg Prod.snd h
    exact this.symm
  · rintro rfl
    exact ⟨((), v = 1), by fin_cases v <;> simp [leafPiece]⟩

theorem leafPiece_isOpen (v : Fin 2) : leafPiece.IsOpen v :=
  ⟨1, fun h => absurd ((leafPiece_filled v 1).mp h) (by decide)⟩

theorem leafPiece_two (v : Fin 2) : leafPiece.two v = false := by
  unfold Piece.two
  rw [decide_eq_false_iff_not]
  rintro ⟨k, h1, h2⟩
  rw [leafPiece_filled] at h1 h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- The two ends of the single edge, as its open vertices. -/
def leafLabel : Fin 2 ≃ leafPiece.OpenV where
  toFun i := ⟨i, leafPiece_isOpen i⟩
  invFun v := v.1
  left_inv _ := rfl
  right_inv _ := rfl

theorem shoreFace_single_card {V' E' : Type*} [Fintype V'] [DecidableEq V'] [Fintype E']
    [DecidableEq E'] (RS : RotationSystem V' E') (e : E') :
    (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha {e}).partition.parts.card = 1 := by
  set σ := shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha {e}
  rw [← GoertzelV24FaceOrbitPartitionBridge.card_permOrbit_eq_card_partition_parts]
  have hdarts : ∀ y : {d // InShore RS.edgeOf {e} d}, ∀ x : {d // InShore RS.edgeOf {e} d},
      y = x ∨ y.1 = RS.alpha x.1 := by
    intro y x
    have hy : RS.edgeOf y.1 = RS.edgeOf x.1 := by
      have h1 := y.2; have h2 := x.2
      simp only [InShore, Finset.mem_singleton] at h1 h2
      rw [h1, h2]
    rcases (edge_darts x.1 y.1).mp hy with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  have hmove : ∀ x, σ x ≠ x := by
    intro x hx
    have hv : RS.vertOf (σ x).1 = RS.vertOf (RS.alpha x.1) := by
      change RS.vertOf (nextHitPerm RS.rho (InShore RS.edgeOf {e})
        (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha {e} x)).1 = _
      rw [vertOf_nextHit]
      rfl
    rw [hx] at hv
    exact RS.no_self_loops x.1 hv
  have hsame : ∀ x y, σ.SameCycle x y := by
    intro x y
    rcases hdarts y x with rfl | h
    · exact Perm.SameCycle.refl _ _
    · rcases hdarts (σ x) x with h' | h'
      · exact absurd h' (hmove x)
      · exact ⟨1, by rw [zpow_one]; exact Subtype.ext (h'.trans h.symm)⟩
  obtain ⟨d0, hd0⟩ : ∃ x : {d // InShore RS.edgeOf {e} d}, True := by
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < (RS.dartsOn e).card by
      have := RS.edge_fiber_two e
      unfold RotationSystem.dartsOn
      omega)
    exact ⟨⟨d, by simp [InShore, (RotationSystem.mem_dartsOn RS).mp hd]⟩, trivial⟩
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk (Perm.SameCycle.setoid σ) d0, fun q => ?_⟩
  induction q using Quotient.inductionOn with
  | h z => exact Quotient.sound (hsame z d0)

theorem leafPiece_realizes : Realizes leafPiece leafLabel leafCode where
  two i := (leafPiece_two (leafLabel i).1).symm
  shore := by
    intro V' E' _ _ _ _ RS hC _ emb
    have hS : emb.shore = {emb.emap ()} := by
      ext e
      simp only [Emb.shore, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟩, rfl⟩; rfl
      · rintro rfl; exact ⟨(), rfl⟩
    have htouch := emb.touched_card hC
    have hcard := emb.shore_card
    refine ⟨?_, ?_, ?_⟩
    · generalize emb.label hC leafLabel = ℓ
      revert ℓ
      rw [hS]
      intro ℓ
      exact encode_leaf hC (emb.emap ()) ℓ
    · rw [hS]
      exact shoreConnected_single (emb.emap ())
    · rw [htouch, hcard, hS, shoreFace_single_card]
      rfl

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodePiece
