import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryEssentialGluing

/-!
# Boundary partitions compute connectivity of literal gluing

No side is required to be connected. Connectivity between seam ports is
exactly the equivalence closure of connectivity within the two sides.
If every side component meets a port, this also decides connectivity of
the entire glued multigraph. Loops and parallel edges are retained.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryConnectivity

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24BoundaryEssentialGluing.Multigraph

variable {VH VK EH EK P : Type*}
  (H : Multigraph VH EH) (K : Multigraph VK EK) (pH : P → VH) (pK : P → VK)

/-- The two boundary connectivity relations, before taking their join. -/
def BoundaryStep (a b : P) : Prop := H.Reach (pH a) (pH b) ∨ K.Reach (pK a) (pK b)

def BoundaryReach : P → P → Prop := Relation.ReflTransGen (BoundaryStep H K pH pK)

/-- Every vertex can reach some boundary port within its own side. -/
def PortVisible : Prop := ∀ v : VH, ∃ p : P, H.Reach v (pH p)

theorem reach_left {u v : VH} (h : H.Reach u v) :
    (glue H K pH pK).Reach (.inl u) (.inl v) :=
  glue_reach_inl (fun _ h => h) h

theorem reach_right {u v : VK} (h : K.Reach u v) :
    (glue H K pH pK).Reach (.inr u) (.inr v) :=
  glue_reach_inr (fun _ h => h) h

theorem reach_seam (p : P) : (glue H K pH pK).Reach (.inl (pH p)) (.inr (pK p)) :=
  Relation.ReflTransGen.single (glue_step_seam p (fun h => h))

theorem reach_of_boundaryReach {a b : P} (h : BoundaryReach H K pH pK a b) :
    (glue H K pH pK).Reach (.inl (pH a)) (.inl (pH b)) := by
  induction h with
  | refl => exact .refl
  | @tail p q _ hs ih =>
    rcases hs with hh | hk
    · exact ih.trans (reach_left H K pH pK hh)
    · exact ih.trans (((reach_seam H K pH pK p).trans
        (reach_right H K pH pK hk)).trans (reach_symm (reach_seam H K pH pK q)))

/-- A boundary-reachable port followed by a walk inside the current side. -/
def FromPort (a : P) : VH ⊕ VK → Prop
  | .inl v => ∃ p, BoundaryReach H K pH pK a p ∧ H.Reach (pH p) v
  | .inr v => ∃ p, BoundaryReach H K pH pK a p ∧ K.Reach (pK p) v

theorem fromPort_edge (a : P) (e : EH ⊕ EK ⊕ P) :
    FromPort H K pH pK a ((glue H K pH pK).fst e) ↔
      FromPort H K pH pK a ((glue H K pH pK).snd e) := by
  rcases e with e | e | p
  · change (∃ q, BoundaryReach H K pH pK a q ∧ H.Reach (pH q) (H.fst e)) ↔
      (∃ q, BoundaryReach H K pH pK a q ∧ H.Reach (pH q) (H.snd e))
    constructor <;> rintro ⟨q, hq, hpath⟩
    · exact ⟨q, hq, hpath.tail ⟨e, not_false, .inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨q, hq, hpath.tail ⟨e, not_false, .inr ⟨rfl, rfl⟩⟩⟩
  · change (∃ q, BoundaryReach H K pH pK a q ∧ K.Reach (pK q) (K.fst e)) ↔
      (∃ q, BoundaryReach H K pH pK a q ∧ K.Reach (pK q) (K.snd e))
    constructor <;> rintro ⟨q, hq, hpath⟩
    · exact ⟨q, hq, hpath.tail ⟨e, not_false, .inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨q, hq, hpath.tail ⟨e, not_false, .inr ⟨rfl, rfl⟩⟩⟩
  · change (∃ q, BoundaryReach H K pH pK a q ∧ H.Reach (pH q) (pH p)) ↔
      (∃ q, BoundaryReach H K pH pK a q ∧ K.Reach (pK q) (pK p))
    constructor <;> rintro ⟨q, hq, hpath⟩
    · exact ⟨p, hq.tail (.inl hpath), .refl⟩
    · exact ⟨p, hq.tail (.inr hpath), .refl⟩

theorem fromPort_of_reach (a : P) {v : VH ⊕ VK}
    (h : (glue H K pH pK).Reach (.inl (pH a)) v) : FromPort H K pH pK a v := by
  induction h with
  | refl => exact ⟨a, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨e, _, he⟩ := hs
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (fromPort_edge H K pH pK a e).mp ih
    · exact (fromPort_edge H K pH pK a e).mpr ih

/-- Exact boundary path compression, even if hidden components exist. -/
theorem boundaryReach_iff (a b : P) :
    BoundaryReach H K pH pK a b ↔ (glue H K pH pK).Reach (.inl (pH a)) (.inl (pH b)) := by
  refine ⟨reach_of_boundaryReach H K pH pK, ?_⟩
  intro h
  obtain ⟨q, hq, hlocal⟩ := fromPort_of_reach H K pH pK a h
  exact hq.tail (.inl hlocal)

theorem reaches_left_port (hH : PortVisible H pH) (hK : PortVisible K pK) (v : VH ⊕ VK) :
    ∃ p : P, (glue H K pH pK).Reach v (.inl (pH p)) := by
  rcases v with v | v
  · obtain ⟨p, hp⟩ := hH v
    exact ⟨p, reach_left H K pH pK hp⟩
  · obtain ⟨p, hp⟩ := hK v
    exact ⟨p, (reach_right H K pH pK hp).trans (reach_symm (reach_seam H K pH pK p))⟩

/-- The join of boundary partitions decides whole-composite connectivity
when no component is invisible at the seam. No port nonemptiness is needed
for the multigraph's reflexive connectedness convention. -/
theorem connected_iff (hH : PortVisible H pH) (hK : PortVisible K pK) :
    (glue H K pH pK).Connected ↔ ∀ a b, BoundaryReach H K pH pK a b := by
  constructor
  · intro h a b
    exact (boundaryReach_iff H K pH pK a b).mpr (h _ _)
  · intro h u v
    obtain ⟨p, hp⟩ := reaches_left_port H K pH pK hH hK u
    obtain ⟨q, hq⟩ := reaches_left_port H K pH pK hH hK v
    exact (hp.trans (reach_of_boundaryReach H K pH pK (h p q))).trans (reach_symm hq)

theorem visible_left_of_connected (p : P) (h : (glue H K pH pK).Connected) :
    PortVisible H pH := by
  intro v
  obtain ⟨q, _, hq⟩ := fromPort_of_reach H K pH pK p (h (.inl (pH p)) (.inl v))
  exact ⟨q, reach_symm hq⟩

section Replacement
variable {VK' EK' : Type*} (K' : Multigraph VK' EK') (pK' : P → VK')

theorem boundaryReach_congr (heq : ∀ a b, K.Reach (pK a) (pK b) ↔ K'.Reach (pK' a) (pK' b))
    (a b : P) : BoundaryReach H K pH pK a b ↔ BoundaryReach H K' pH pK' a b := by
  constructor <;> intro h
  · induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (hs.imp id (fun hk => (heq _ _).mp hk))
  · induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (hs.imp id (fun hk => (heq _ _).mpr hk))

/-- Replacing an interior carrier with the same boundary connectivity
partition preserves connectivity in every port-visible exterior. -/
theorem replacement_connected (hH : PortVisible H pH) (hK : PortVisible K pK)
    (hK' : PortVisible K' pK')
    (heq : ∀ a b, K.Reach (pK a) (pK b) ↔ K'.Reach (pK' a) (pK' b)) :
    (glue H K pH pK).Connected ↔ (glue H K' pH pK').Connected := by
  rw [connected_iff H K pH pK hH hK, connected_iff H K' pH pK' hH hK']
  exact forall_congr' (fun a => forall_congr' (fun b => boundaryReach_congr H K pH pK K' pK' heq a b))

/-- With a nonempty seam, the exterior need not be assumed port-visible:
if either composite is connected, that condition follows from its paths. -/
theorem replacement_connected_any_exterior (p : P) (hK : PortVisible K pK)
    (hK' : PortVisible K' pK')
    (heq : ∀ a b, K.Reach (pK a) (pK b) ↔ K'.Reach (pK' a) (pK' b)) :
    (glue H K pH pK).Connected ↔ (glue H K' pH pK').Connected := by
  constructor
  · intro h
    exact (replacement_connected H K pH pK K' pK'
      (visible_left_of_connected H K pH pK p h) hK hK' heq).mp h
  · intro h
    exact (replacement_connected H K pH pK K' pK'
      (visible_left_of_connected H K' pH pK' p h) hK hK' heq).mpr h
end Replacement

end Mettapedia.GraphTheory.FourColor.BoundaryConnectivity
