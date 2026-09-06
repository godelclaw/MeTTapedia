import Mettapedia.GraphTheory.FourColor.GeneralTubeNodes

/-!
# Presented tangles

A slab shape is presented by a list of vertex triples of slots — an interior
edge, an in-port, or an out-port — together with the positions of the two
ends of each edge and of each port.  Validity (each position carries the slot
it claims, edges join distinct vertices, every slot occurrence is accounted
for) is decidable.  From a valid presentation the two-sided tangle is built
generically (`toTangle`): interior darts are edge ends, the involution swaps
the ends, the rotation cycles the three slots of a vertex.  New shapes then
cost a data list and `decide`; the closed form of the relation and the
enumerator are proved once, on presentations.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace Presented

open GoertzelV24OpenTangleComposition

/-- a slot of a vertex triple -/
inductive Slot (N k : Nat)
  | edge (e : Fin N)
  | inp (i : Fin k)
  | out (i : Fin k)
  deriving DecidableEq, Repr

/-- a position: a vertex and one of its three slots -/
abbrev Pos (V : Nat) := Fin V × Fin 3

/-- a presentation: `V` vertices with triples of slots, `N` interior edges with the
positions of their two ends, `k` ports a side with their positions -/
structure Pres (V N k : Nat) where
  tri : Fin V → Fin 3 → Slot N k
  endPos : Fin N → Bool → Pos V
  inPos : Fin k → Pos V
  outPos : Fin k → Pos V

namespace Pres

variable {V N k : Nat} (P : Pres V N k)

def slotAt (p : Pos V) : Slot N k := P.tri p.1 p.2

/-- validity -/
def Valid : Prop :=
  (∀ e b, P.slotAt (P.endPos e b) = Slot.edge e) ∧
  (∀ e, (P.endPos e false).1 ≠ (P.endPos e true).1) ∧
  (∀ i, P.slotAt (P.inPos i) = Slot.inp i) ∧
  (∀ i, P.slotAt (P.outPos i) = Slot.out i) ∧
  (∀ p : Pos V,
    (∀ e, P.slotAt p = Slot.edge e → p = P.endPos e false ∨ p = P.endPos e true) ∧
    (∀ i, P.slotAt p = Slot.inp i → p = P.inPos i) ∧
    (∀ i, P.slotAt p = Slot.out i → p = P.outPos i))

instance decValid : Decidable P.Valid := by
  unfold Valid
  infer_instance

/-- interior darts: edge ends -/
abbrev IDart := Fin N × Bool

/-- all darts -/
abbrev D := IDart (N := N) ⊕ (Fin k ⊕ Fin k)

/-- the position of a dart -/
def pos : D (N := N) (k := k) → Pos V
  | Sum.inl (e, b) => P.endPos e b
  | Sum.inr (Sum.inl i) => P.inPos i
  | Sum.inr (Sum.inr i) => P.outPos i

/-- the dart at a position -/
def dartAt [DecidableEq (Pos V)] (p : Pos V) : D (N := N) (k := k) :=
  match P.slotAt p with
  | Slot.edge e => if p = P.endPos e false then Sum.inl (e, false) else Sum.inl (e, true)
  | Slot.inp i => Sum.inr (Sum.inl i)
  | Slot.out i => Sum.inr (Sum.inr i)

theorem pos_dartAt (hP : P.Valid) (p : Pos V) : P.pos (P.dartAt p) = p := by
  obtain ⟨hend, -, hin, hout, hcover⟩ := hP
  obtain ⟨hce, hci, hco⟩ := hcover p
  unfold dartAt
  cases h : P.slotAt p with
  | edge e =>
    by_cases hp : p = P.endPos e false
    · simp [hp, pos]
    · simp only [hp, if_false, pos]
      rcases hce e h with hc | hc
      · exact absurd hc hp
      · exact hc.symm
  | inp i => simp [pos, hci i h]
  | out i => simp [pos, hco i h]

theorem dartAt_pos (hP : P.Valid) (d : D (N := N) (k := k)) : P.dartAt (P.pos d) = d := by
  obtain ⟨hend, hne, hin, hout, hcover⟩ := hP
  rcases d with ⟨e, b⟩ | i | i
  · simp only [pos, dartAt, hend e b]
    cases b
    · simp
    · have : P.endPos e true ≠ P.endPos e false := fun h => hne e (congrArg Prod.fst h).symm
      simp [this]
  · simp [pos, dartAt, hin i]
  · simp [pos, dartAt, hout i]

/-- the position bijection -/
noncomputable def posEquiv (hP : P.Valid) : D (N := N) (k := k) ≃ Pos V where
  toFun := P.pos
  invFun := P.dartAt
  left_inv := P.dartAt_pos hP
  right_inv := P.pos_dartAt hP

/-- the slot cycle at a vertex -/
def slotCycle : Equiv.Perm (Pos V) :=
  (Equiv.refl (Fin V)).prodCongr (Equiv.addRight (1 : Fin 3))

/-- the rotation: cycle the three slots of a vertex -/
noncomputable def rho (hP : P.Valid) : Equiv.Perm (D (N := N) (k := k)) :=
  (P.posEquiv hP).trans (slotCycle.trans (P.posEquiv hP).symm)

def vertOf (d : D (N := N) (k := k)) : Fin V := (P.pos d).1

theorem vertOf_rho (hP : P.Valid) (d : D (N := N) (k := k)) :
    P.vertOf (P.rho hP d) = P.vertOf d := by
  simp only [vertOf, rho, Equiv.trans_apply, posEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
  rw [P.pos_dartAt hP]
  rfl

/-- **the tangle of a valid presentation** -/
noncomputable def toTangle [NeZero k] (hP : P.Valid) :
    TwoSidedOpenTangleData (Fin V) (IDart (N := N)) (Fin k) (Fin k) where
  interiorVert := fun d => (P.endPos d.1 d.2).1
  leftVert := fun i => (P.inPos i).1
  rightVert := fun i => (P.outPos i).1
  interiorAlpha := (Equiv.refl (Fin N)).prodCongr (Function.Involutive.toPerm not Bool.not_not)
  interiorAlpha_involutive := by rintro ⟨e, b⟩; cases b <;> rfl
  interiorAlpha_fixfree := by rintro ⟨e, b⟩; cases b <;> simp
  rho := P.rho hP
  vert_rho := fun d => by
    have h := P.vertOf_rho hP d
    rcases hd : P.rho hP d with ⟨e, b⟩ | i | i <;> rcases d with ⟨e', b'⟩ | i' | i' <;>
      simp only [twoSidedOpenTangleVertOf] <;> rw [hd] at h <;> exact h
  interior_no_self_loops := by
    rintro ⟨e, b⟩ h
    cases b
    · exact hP.2.1 e h
    · exact hP.2.1 e h.symm
  outer := Sum.inr (Sum.inl 0)

end Pres

end Presented
end TubeSlab
end Mettapedia.GraphTheory.FourColor
