import Mettapedia.GraphTheory.FourColor.VertexCodeDartGeometry
import Mettapedia.GraphTheory.FourColor.VertexCodeCyclicEncoder

/-!
# Source labels for a cyclic vertex-code step

The decoder's old darts plus new star are put in bijection with the enlarged
source side. Labels retain the ambient edge mates and rotation, not merely
colour support. The model below is the geometric induction invariant.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeSourceGeometry

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24RotationCutDartDecomposition
open TubeSlab.VertexTransfer TubeSlab.NestedSideWire VertexCodePartition
open VertexCodeCyclicEncoder VertexCodeDartGeometry VertexCodeRealization

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u,u,u} V E} {inner : V → Prop} {v : V}
variable {W I : Type*} {l r : ℕ}

def joinVertices (hv : ¬ inner v) : {w // inner w} ⊕ Unit ≃ {w // enlarged inner v w} where
  toFun := Sum.elim (fun w => ⟨w.1, .inl w.2⟩) (fun _ => ⟨v, .inr rfl⟩)
  invFun w := if h : inner w.1 then .inl ⟨w.1, h⟩ else .inr ()
  left_inv := by
    rintro (w | ⟨⟩)
    · simp [w.2]
    · simp [hv]
  right_inv := by
    intro w
    dsimp only
    split_ifs with h
    · rfl
    · exact Subtype.ext (w.2.resolve_left h).symm

def joinDarts : RetainedDart RS inner ⊕ NewDart RS inner v ≃
    RetainedDart RS (enlarged inner v) where
  toFun := Sum.elim (fun d => ⟨d.1, .inl d.2⟩) (fun d => ⟨d.1, d.2.1⟩)
  invFun d := if h : inner (RS.vertOf d.1) then .inl ⟨d.1, h⟩ else .inr ⟨d.1, d.2, h⟩
  left_inv := by
    rintro (d | d)
    · simp [d.2]
    · simp [d.2.2]
  right_inv := by intro d; dsimp only; split_ifs <;> rfl

/-- A source-side rotation-map isomorphism with fixed boundary coordinates.
Only the edge flip on internal darts is asserted; exposed darts have no
internal mate. The distinguished outer dart is not prescribed: a swept side
need not contain the ambient outer dart. -/
structure Model (T : TwoSidedOpenTangleData W I (Fin 0) (Fin l))
    (mi : Fin l ≃ BoundaryDart RS inner) where
  vertex : W ≃ {w // inner w}
  dart : I ⊕ Fin l ≃ RetainedDart RS inner
  vert : ∀ d, (vertex (T.vertOf (compact d))).1 = RS.vertOf (dart d).1
  rho : ∀ d, (dart (compact.symm (T.rho (compact d)))).1 = RS.rho (dart d).1
  mate : ∀ i, (dart (.inl (T.interiorAlpha i))).1 = RS.alpha (dart (.inl i)).1
  port : ∀ i, (dart (.inr i)).1 = (mi i).1.1

variable (se : Fin 3 ≃ NewDart RS inner v)
  (mi : Fin l ≃ BoundaryDart RS inner)
  (mo : Fin r ≃ BoundaryDart RS (enlarged inner v))

theorem slot_in {t : Fin 3} {i : Fin l} (h : (encodeWith se mi mo).1 t = .inl i) :
    (se t).1 = RS.alpha (mi i).1.1 := by
  change Sum.map mi.symm mo.symm (port (se t)) = .inl i at h
  unfold port at h
  split_ifs at h with hi
  · have he : mi i = incoming (se t) hi := by
      rw [← Sum.inl.inj h]; exact mi.apply_symm_apply _
    rw [he]
    exact (RS.alpha_involutive _).symm
  · cases h

theorem slot_out {t : Fin 3} {j : Fin r} (h : (encodeWith se mi mo).1 t = .inr j) :
    (se t).1 = (mo j).1.1 := by
  change Sum.map mi.symm mo.symm (port (se t)) = .inr j at h
  unfold port at h
  split_ifs at h with hi
  · cases h
  · have he : mo j = outgoing (se t) hi := by
      rw [← Sum.inr.inj h]; exact mo.apply_symm_apply _
    rw [he]; rfl

theorem wire_label {j : Fin r} {i : Fin l} (h : (encodeWith se mi mo).2 j = some i) :
    (mi i).1.1 = (mo j).1.1 := by
  simp only [encodeWith] at h
  split_ifs at h with hi
  have he : mi i = throughFromOuter inclusion (mo j) hi := by
    rw [← Option.some.inj h]; exact mi.apply_symm_apply _
  exact congrArg (fun b : BoundaryDart RS inner => b.1.1) he

theorem new_consumed (h : Valid (encodeWith se mi mo)) (p : Consumed (encodeWith se mi mo)) :
    (se ((starOrder _ h).symm (.inl p))).1 = RS.alpha (mi p.1).1.1 := by
  apply slot_in se mi mo
  rw [← starOrder_spec _ h, Equiv.apply_symm_apply]
  rfl

theorem new_fresh (h : Valid (encodeWith se mi mo)) (p : Fresh (encodeWith se mi mo)) :
    (se ((starOrder _ h).symm (.inr p))).1 = (mo p.1).1.1 := by
  apply slot_out se mi mo
  rw [← starOrder_spec _ h, Equiv.apply_symm_apply]
  rfl

variable {T : TwoSidedOpenTangleData W I (Fin 0) (Fin l)}

def nextDart (M : Model T mi) (h : Valid (encodeWith se mi mo)) :
    (((I ⊕ Empty) ⊕ (Consumed (encodeWith se mi mo) ⊕ Consumed (encodeWith se mi mo))) ⊕ Fin r) ≃
      RetainedDart RS (enlarged inner v) :=
  (((compact.trans (stepDarts _ h).symm).trans (Equiv.sumCongr M.dart se)).trans joinDarts)

theorem nextDart_old (M : Model T mi) (h : Valid (encodeWith se mi mo)) (d : I ⊕ Fin l) :
    (nextDart se mi mo M h (compact.symm (stepDarts _ h (.inl d)))).1 = (M.dart d).1 := by
  simp only [nextDart, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inl]
  rfl

theorem nextDart_new (M : Model T mi) (h : Valid (encodeWith se mi mo)) (i : Fin 3) :
    (nextDart se mi mo M h (compact.symm (stepDarts _ h (.inr i)))).1 = (se i).1 := by
  simp only [nextDart, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inr]
  rfl

theorem nextDart_interior (M : Model T mi) (h : Valid (encodeWith se mi mo)) (i : I) :
    (nextDart se mi mo M h (.inl (.inl (.inl i)))).1 = (M.dart (.inl i)).1 :=
  nextDart_old se mi mo M h (.inl i)

theorem nextDart_left (M : Model T mi) (h : Valid (encodeWith se mi mo))
    (p : Consumed (encodeWith se mi mo)) :
    (nextDart se mi mo M h (.inl (.inr (.inl p)))).1 = (mi p.1).1.1 := by
  have he := nextDart_old se mi mo M h (.inr p.1)
  rw [stepDarts_consumed, M.port] at he
  exact he

theorem nextDart_right (M : Model T mi) (h : Valid (encodeWith se mi mo))
    (p : Consumed (encodeWith se mi mo)) :
    (nextDart se mi mo M h (.inl (.inr (.inr p)))).1 = RS.alpha (mi p.1).1.1 := by
  have he := nextDart_new se mi mo M h ((starOrder _ h).symm (.inl p))
  rw [stepDarts_new, new_consumed] at he
  exact he

theorem nextDart_port (M : Model T mi) (h : Valid (encodeWith se mi mo)) (j : Fin r) :
    (nextDart se mi mo M h (.inr j)).1 = (mo j).1.1 := by
  obtain ⟨p, rfl⟩ := (outputEquiv (encodeWith se mi mo)).surjective j
  rcases p with p | p
  · have he := nextDart_old se mi mo M h (.inr p.1.2)
    rw [stepDarts_retained, M.port] at he
    exact he.trans (wire_label se mi mo p.2)
  · have he := nextDart_new se mi mo M h ((starOrder _ h).symm (.inr p))
    rw [stepDarts_new, new_fresh] at he
    exact he

def nextVertex (M : Model T mi) (hv : ¬ inner v) : W ⊕ Unit ≃ {w // enlarged inner v w} :=
  (Equiv.sumCongr M.vertex (Equiv.refl Unit)).trans (joinVertices hv)

theorem nextDart_vert (M : Model T mi) (h : Valid (encodeWith se mi mo)) (hv : ¬ inner v)
    (d : ((I ⊕ Empty) ⊕ (Consumed (encodeWith se mi mo) ⊕ Consumed (encodeWith se mi mo))) ⊕ Fin r) :
    (nextVertex mi M hv ((attach _ h T).vertOf (compact d))).1 =
      RS.vertOf (nextDart se mi mo M h d).1 := by
  obtain ⟨x, hx⟩ := (stepDarts (I := I) _ h).surjective (compact d)
  have hd : compact.symm (stepDarts _ h x) = d := by rw [hx, Equiv.symm_apply_apply]
  rw [← hd, Equiv.apply_symm_apply]
  rcases x with x | i
  · rw [vert_old, nextDart_old]
    exact M.vert x
  · rw [vert_new, nextDart_new]
    exact (newDart_base (se i)).symm

theorem nextDart_rho (M : Model T mi) (h : Valid (encodeWith se mi mo))
    (hse : ∀ i : Fin 3, RS.rho (se i).1 = (se (i + 1)).1)
    (d : ((I ⊕ Empty) ⊕ (Consumed (encodeWith se mi mo) ⊕ Consumed (encodeWith se mi mo))) ⊕ Fin r) :
    (nextDart se mi mo M h (compact.symm ((attach _ h T).rho (compact d)))).1 =
      RS.rho (nextDart se mi mo M h d).1 := by
  obtain ⟨x, hx⟩ := (stepDarts (I := I) _ h).surjective (compact d)
  have hd : compact.symm (stepDarts _ h x) = d := by rw [hx, Equiv.symm_apply_apply]
  rw [← hd, Equiv.apply_symm_apply]
  rcases x with x | i
  · rw [rho_old, nextDart_old, nextDart_old]
    exact M.rho x
  · rw [rho_new, nextDart_new, nextDart_new]
    exact (hse i).symm

theorem nextDart_mate (M : Model T mi) (h : Valid (encodeWith se mi mo))
    (i : (I ⊕ Empty) ⊕ (Consumed (encodeWith se mi mo) ⊕ Consumed (encodeWith se mi mo))) :
    (nextDart se mi mo M h (.inl ((attach _ h T).interiorAlpha i))).1 =
      RS.alpha (nextDart se mi mo M h (.inl i)).1 := by
  rcases i with (i | e) | (p | p)
  · change (nextDart se mi mo M h (.inl (.inl (.inl (T.interiorAlpha i))))).1 = _
    rw [nextDart_interior, nextDart_interior]
    exact M.mate i
  · exact e.elim
  · change (nextDart se mi mo M h (.inl (.inr (.inr p)))).1 = _
    rw [nextDart_right, nextDart_left]
  · change (nextDart se mi mo M h (.inl (.inr (.inl p)))).1 = _
    rw [nextDart_left, nextDart_right, RS.alpha_involutive]

/-- Decoding the actual emitted letter enlarges the actual represented source
side, with the source rotation and the prescribed new boundary coordinates. -/
def Model.step (M : Model T mi) (hv : ¬ inner v)
    (hse : ∀ i : Fin 3, RS.rho (se i).1 = (se (i + 1)).1) :
    Model (attach (encodeWith se mi mo) (encodeWith_valid se mi mo hv) T) mo where
  vertex := nextVertex mi M hv
  dart := nextDart se mi mo M (encodeWith_valid se mi mo hv)
  vert := nextDart_vert se mi mo M _ hv
  rho := nextDart_rho se mi mo M _ hse
  mate := nextDart_mate se mi mo M _
  port := nextDart_port se mi mo M _

section First

def emptyCoords : Fin 0 ≃ BoundaryDart RS (fun _ => False) where
  toFun := Fin.elim0
  invFun b := b.1.2.elim
  left_inv i := i.elim0
  right_inv b := b.1.2.elim

def firstVertices (v : V) : Unit ≃ {w // enlarged (fun _ : V => False) v w} where
  toFun _ := ⟨v, .inr rfl⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv w := Subtype.ext (w.2.resolve_left id).symm

def firstSourceDarts : NewDart RS (fun _ => False) v ≃
    RetainedDart RS (enlarged (fun _ => False) v) where
  toFun d := ⟨d.1, d.2.1⟩
  invFun d := ⟨d.1, d.2, id⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (se₀ : Fin 3 ≃ NewDart RS (fun _ => False) v)
  (mo₀ : Fin r ≃ BoundaryDart RS (enlarged (fun _ => False) v))

def firstDart (h : Valid (encodeWith se₀ emptyCoords mo₀)) :
    Empty ⊕ Fin r ≃ RetainedDart RS (enlarged (fun _ => False) v) :=
  ((initialDarts _ h).symm.trans se₀).trans firstSourceDarts

theorem firstDart_new (h : Valid (encodeWith se₀ emptyCoords mo₀)) (i : Fin 3) :
    (firstDart se₀ mo₀ h (initialDarts _ h i)).1 = (se₀ i).1 := by
  simp only [firstDart, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

def firstModel (hse : ∀ i : Fin 3, RS.rho (se₀ i).1 = (se₀ (i + 1)).1) :
    Model (initial (encodeWith se₀ emptyCoords mo₀)
      (encodeWith_valid se₀ emptyCoords mo₀ (not_false))) mo₀ where
  vertex := firstVertices v
  dart := firstDart se₀ mo₀ _
  vert := by
    intro d
    obtain ⟨i, rfl⟩ := (initialDarts _ (encodeWith_valid se₀ emptyCoords mo₀ not_false)).surjective d
    rw [firstDart_new]
    exact (newDart_base (se₀ i)).symm
  rho := by
    intro d
    obtain ⟨i, rfl⟩ := (initialDarts _ (encodeWith_valid se₀ emptyCoords mo₀ not_false)).surjective d
    rw [initial_rho, firstDart_new, firstDart_new]
    exact (hse i).symm
  mate := fun i => i.elim
  port := by
    intro j
    let h := encodeWith_valid se₀ emptyCoords mo₀ not_false
    let p : Fresh (encodeWith se₀ emptyCoords mo₀) := ⟨j, initial_wire _ j⟩
    have he := firstDart_new se₀ mo₀ h ((starOrder _ h).symm (.inr p))
    rw [initialDarts_new, new_fresh] at he
    exact he

end First

end
end Mettapedia.GraphTheory.FourColor.VertexCodeSourceGeometry
