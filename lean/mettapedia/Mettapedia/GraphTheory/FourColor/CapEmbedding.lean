import Mettapedia.GraphTheory.FourColor.PresentedCapEnum
import Mettapedia.GraphTheory.FourColor.KempeCertificateEnum

/-!
# A configuration that appears as a deleted disk, and the end-to-end exclusion

An isomorphism of open tangles for colouring purposes (vertices, interior darts and boundary
darts correspond, respecting incidence and the edge involution) transports seam supports
(`mem_innerSupport_of_iso`).  When a presented configuration is isomorphic to the deleted
side of a least counterexample, with its ports numbered by the shore's facial order, the
deleted side's support in certificate coordinates is the configuration's enumerated word
list (`mem_wordsOf_deleted_iff`).

`false_of_certificate` puts everything together: a presented configuration appearing as a
deleted disk, a smaller presented cap on the same ports passing the disc check, and an
enumerated Kempe certificate whose base is the configuration's word list and whose nodes
cover the cap's word list, contradict minimality.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace KempeDerivation
namespace CapEmbedding

open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24ClosedCountReplacement GoertzelV24PhysicalClosedCountBridge
open GoertzelV24RawNooseCountPumping
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSideOpenTangle
open SimpleGraphDartRotation
open CapExclusion PresentedCap

universe u

/-! ## Isomorphisms of open tangles, for colourings -/

/-- vertices, interior darts and boundary darts correspond, respecting incidence and the
edge involution; the rotation is irrelevant for Tait colourings -/
structure OpenTangleIso {V I B V' I' B' : Type*} (T : OpenTangleData V I B)
    (T' : OpenTangleData V' I' B') where
  vert : V ≃ V'
  interior : I ≃ I'
  boundary : B ≃ B'
  interiorVert_eq : ∀ d, T'.interiorVert (interior d) = vert (T.interiorVert d)
  boundaryVert_eq : ∀ b, T'.boundaryVert (boundary b) = vert (T.boundaryVert b)
  alpha_eq : ∀ d, T'.interiorAlpha (interior d) = interior (T.interiorAlpha d)

namespace OpenTangleIso

variable {V I B V' I' B' : Type*} {T : OpenTangleData V I B} {T' : OpenTangleData V' I' B'}

def symm (iso : OpenTangleIso T T') : OpenTangleIso T' T where
  vert := iso.vert.symm
  interior := iso.interior.symm
  boundary := iso.boundary.symm
  interiorVert_eq := fun d => by
    apply iso.vert.injective
    rw [← iso.interiorVert_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  boundaryVert_eq := fun b => by
    apply iso.vert.injective
    rw [← iso.boundaryVert_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  alpha_eq := fun d => by
    apply iso.interior.injective
    rw [← iso.alpha_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end OpenTangleIso

section Transport

variable {V I B V' I' B' L : Type u} [Fintype V] [Fintype I] [Fintype B] [DecidableEq V]
  [DecidableEq I] [DecidableEq B] [Fintype V'] [Fintype I'] [Fintype B'] [DecidableEq V']
  [DecidableEq I'] [DecidableEq B'] [Fintype L] [DecidableEq L]
  {T : OpenTangleData V I B} {T' : OpenTangleData V' I' B'}

/-- the dart of the target's closed port tangle read back in the source -/
def backDart (iso : OpenTangleIso T T') : I' ⊕ (L ⊕ EmptyPort.{u}) → I ⊕ (L ⊕ EmptyPort.{u})
  | Sum.inl d => Sum.inl (iso.interior.symm d)
  | Sum.inr p => Sum.inr p

theorem backDart_injective (iso : OpenTangleIso T T') :
    Function.Injective (backDart (L := L) iso) := by
  rintro (d | p) (d' | p') h <;> simp only [backDart] at h
  · rw [iso.interior.symm.injective (Sum.inl_injective h)]
  · cases h
  · cases h
  · rw [Sum.inr_injective h]

theorem vert_backDart (iso : OpenTangleIso T T') (matching : L ≃ B)
    (d : I' ⊕ (L ⊕ EmptyPort.{u})) :
    (rightClosedPortTangle T' (matching.trans iso.boundary)).vert d =
      iso.vert ((rightClosedPortTangle T matching).vert (backDart iso d)) := by
  rcases d with d | p | e
  · show T'.interiorVert d = iso.vert (T.interiorVert (iso.interior.symm d))
    rw [← iso.interiorVert_eq, Equiv.apply_symm_apply]
  · show T'.boundaryVert (iso.boundary (matching p)) = iso.vert (T.boundaryVert (matching p))
    exact iso.boundaryVert_eq _
  · exact e.elim

/-- **seam supports transport along an isomorphism** -/
theorem mem_innerSupport_of_iso (iso : OpenTangleIso T T') (matching : L ≃ B) (y : L → Color)
    (h : y ∈ innerSupport (rightClosedPortTangle T matching)) :
    y ∈ innerSupport (rightClosedPortTangle T' (matching.trans iso.boundary)) := by
  obtain ⟨⟨col, ⟨hnz, hdistinct⟩, hword⟩⟩ := h
  refine ⟨⟨⟨fun d => col.color (backDart iso d), ?_⟩, ⟨?_, ?_⟩, ?_⟩⟩
  · intro d
    show col.color (Sum.inl (iso.interior.symm (T'.interiorAlpha d))) =
      col.color (Sum.inl (iso.interior.symm d))
    have : iso.interior.symm (T'.interiorAlpha d) = T.interiorAlpha (iso.interior.symm d) := by
      apply iso.interior.injective
      rw [Equiv.apply_symm_apply, ← iso.alpha_eq, Equiv.apply_symm_apply]
    rw [this]
    exact col.invariant _
  · intro d
    exact hnz _
  · intro d d' hv hne
    rw [vert_backDart, vert_backDart] at hv
    exact hdistinct _ _ (iso.vert.injective hv) fun h => hne (backDart_injective iso h)
  · funext p
    rcases p with p | e
    · exact congrFun hword (Sum.inl p)
    · exact e.elim

end Transport

/-! ## The deleted side as a presented configuration -/

section Deleted

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- the deleted side's support in certificate coordinates is the configuration's word list -/
theorem mem_wordsOf_deleted_iff (graphData : Data G) (deleted : Finset V)
    (outerDeleted : RetainedDart graphData.toRotationSystem (deletedSideKeep deleted))
    {n : Nat} [NeZero n]
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem (deletedRegionKeep deleted))
    {VK NK : Nat} (K : Pres VK NK n) (hK : K.Valid)
    (iso : OpenTangleIso
      (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
      (K.toCap hK))
    (hports : ∀ b, iso.boundary (complementBoundaryAlphaEquiv graphData.toRotationSystem
      deleted b) = order.symm b)
    (w : Word n) :
    w ∈ wordsOf order (taitInnerSupport (rightClosedPortTangle
        (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
        (complementBoundaryAlphaEquiv graphData.toRotationSystem deleted))) ↔
      w ∈ K.capWords hK := by
  have hmatch : (complementBoundaryAlphaEquiv graphData.toRotationSystem deleted).trans
      iso.boundary = order.symm :=
    Equiv.ext hports
  rw [← K.mem_wordsOf_taitInnerSupport_iff hK order w]
  show cutWordColor (fun l => w (order.symm l)) ∈ innerSupport _ ↔
    cutWordColor (fun l => w (order.symm l)) ∈ innerSupport _
  constructor
  · intro h
    have := mem_innerSupport_of_iso iso _ _ h
    rwa [hmatch] at this
  · intro h
    have := mem_innerSupport_of_iso iso.symm (order.symm) _ h
    have hmatch' : order.symm.trans iso.symm.boundary =
        complementBoundaryAlphaEquiv graphData.toRotationSystem deleted := by
      rw [← hmatch]
      exact Equiv.ext fun b => by simp [OpenTangleIso.symm]
    rwa [hmatch'] at this

/-- the configuration's vertex count is the disk's -/
theorem card_deleted_eq (graphData : Data G) (deleted : Finset V)
    (outerDeleted : RetainedDart graphData.toRotationSystem (deletedSideKeep deleted))
    {n : Nat} [NeZero n] {VK NK : Nat} (K : Pres VK NK n) (hK : K.Valid)
    (iso : OpenTangleIso
      (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
      (K.toCap hK)) :
    deleted.card = VK := by
  have h1 : Fintype.card {v : V // deletedSideKeep deleted v} = VK := by
    rw [Fintype.card_congr iso.vert, Fintype.card_fin]
  rw [← h1]
  have h2 : Fintype.card {v : V // deletedSideKeep deleted v} =
      Fintype.card {v : V // v ∈ deleted} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight fun v => by simp [deletedSideKeep, deletedRegionKeep]
  rw [h2, Fintype.card_coe]

/-! ## The end-to-end exclusion -/

/-- **A presented configuration with a certified smaller cap is not a disk of a least
counterexample.** -/
theorem false_of_certificate
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (deleted : Finset V)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex | ¬ deletedRegionKeep deleted vertex}).Connected)
    (outerRetained : RetainedDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart graphData.toRotationSystem (deletedSideKeep deleted))
    {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (hsuccessor : order.permCongr (finRotate n) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem (deletedRegionKeep deleted))
    -- the configuration, as it appears
    {VK NK : Nat} (K : Pres VK NK n) (hK : K.Valid)
    (iso : OpenTangleIso
      (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
      (K.toCap hK))
    (hports : ∀ b, iso.boundary (complementBoundaryAlphaEquiv graphData.toRotationSystem
      deleted b) = order.symm b)
    -- the cap
    {VC NC : Nat} (C : Pres VC NC n) (hC : C.Valid) (hdisc : C.discCheck hC = true)
    (hsmall : VC < VK)
    -- the certificate
    (cert : CertificateEnum n) (hok : cert.Ok (K.capWords hK))
    (hcover : ∀ w ∈ C.capWords hC, w ∈ cert.nodes.map fun t => t.1) :
    False := by
  have hcard := card_deleted_eq graphData deleted outerDeleted K hK iso
  refine false_of_derivable_cap graphData minimal deleted hretainedConnected hdeletedConnected
    outerRetained outerDeleted hn order hsuccessor (C.toCap hC) order.symm
    (C.capDiscData_of_discCheck _ _ order.symm
      (Pres.capHubRotation_eq_finRotate _ _ order hsuccessor) hC hdisc)
    (by rw [Fintype.card_fin, hcard]; exact hsmall) ?_
  intro w hw
  rw [C.mem_wordsOf_taitInnerSupport_iff hC order w] at hw
  have hbase : ∀ u ∈ K.capWords hK, u ∈ wordsOf order (taitInnerSupport (rightClosedPortTangle
      (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
      (complementBoundaryAlphaEquiv graphData.toRotationSystem deleted))) := by
    intro u hu
    exact (mem_wordsOf_deleted_iff graphData deleted outerDeleted order K hK iso hports u).2 hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (hcover w hw)
  obtain ⟨j, hj, hjt⟩ := List.getElem_of_mem ht
  rw [← hjt]
  exact cert.derivable_of_ok hbase hok j hj

/-- **The same, with the certificate's own base list**, each base word verified by the
enumerator on the configuration, and the cap's words covered by the base or the nodes. -/
theorem false_of_certificate'
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (deleted : Finset V)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex | ¬ deletedRegionKeep deleted vertex}).Connected)
    (outerRetained : RetainedDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart graphData.toRotationSystem (deletedSideKeep deleted))
    {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (order : Fin n ≃ BoundaryDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (hsuccessor : order.permCongr (finRotate n) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem (deletedRegionKeep deleted))
    {VK NK : Nat} (K : Pres VK NK n) (hK : K.Valid)
    (iso : OpenTangleIso
      (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
      (K.toCap hK))
    (hports : ∀ b, iso.boundary (complementBoundaryAlphaEquiv graphData.toRotationSystem
      deleted b) = order.symm b)
    {VC NC : Nat} (C : Pres VC NC n) (hC : C.Valid) (hdisc : C.discCheck hC = true)
    (hsmall : VC < VK)
    (base : List (Word n)) (hbaseK : ∀ u ∈ base, K.acceptsWord u = true)
    (cert : CertificateEnum n) (hok : cert.Ok base)
    (hcover : ∀ w ∈ C.capWords hC, w ∈ base ∨ w ∈ cert.nodes.map fun t => t.1) :
    False := by
  have hcard := card_deleted_eq graphData deleted outerDeleted K hK iso
  refine false_of_derivable_cap graphData minimal deleted hretainedConnected hdeletedConnected
    outerRetained outerDeleted hn order hsuccessor (C.toCap hC) order.symm
    (C.capDiscData_of_discCheck _ _ order.symm
      (Pres.capHubRotation_eq_finRotate _ _ order hsuccessor) hC hdisc)
    (by rw [Fintype.card_fin, hcard]; exact hsmall) ?_
  intro w hw
  rw [C.mem_wordsOf_taitInnerSupport_iff hC order w] at hw
  have hbase : ∀ u ∈ base, u ∈ wordsOf order (taitInnerSupport (rightClosedPortTangle
      (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
      (complementBoundaryAlphaEquiv graphData.toRotationSystem deleted))) := by
    intro u hu
    rw [mem_wordsOf_deleted_iff graphData deleted outerDeleted order K hK iso hports u,
      K.mem_capWords_iff hK, ← K.acceptsWord_iff hK]
    exact hbaseK u hu
  rcases hcover w hw with hbw | hnw
  · exact Derivable.base (hbase w hbw)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hnw
    obtain ⟨j, hj, hjt⟩ := List.getElem_of_mem ht
    rw [← hjt]
    exact cert.derivable_of_ok hbase hok j hj

end Deleted

end CapEmbedding
end KempeDerivation
end Mettapedia.GraphTheory.FourColor
