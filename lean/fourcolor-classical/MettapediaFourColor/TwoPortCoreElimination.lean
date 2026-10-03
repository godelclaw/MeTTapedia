import MettapediaFourColor.FiveTriangleCollapseObstruction
import Mettapedia.GraphTheory.Kempe.EarGuard

/-!
# Two-port elimination in the D0092 and D0063 cores

The exact decoded catalogue graphs have five triangular ears, removed in
the orders below. Every stage consumes the same general elimination law
with arbitrary unary lists and arbitrary inherited binary constraints.
Consequently constraints introduced by an earlier stage need not be reset
to ordinary colour inequality. The remaining two vertices are adjacent.

The source strings and attribution are inherited from
`FiveTriangleCollapseObstruction`. These are extension operations, not
a proof of arbitrary-exterior reducibility of either configuration.
-/

namespace FourColor.TwoPortCoreElimination

open SimpleGraph BinaryConstraints FiveTriangleCollapseObstruction

def upperVertex (x : Fin 7) : Fin 18 := ⟨11 + x.val, by omega⟩
def lowerVertex (x : Fin 7) : Fin 17 := ⟨10 + x.val, by omega⟩

/-- False selects D0092; true selects D0063. All internal edges come from
the decoded source, including incidences not used in a particular ear. -/
def core : Bool → SimpleGraph (Fin 7)
  | false => upper.graph.comap upperVertex
  | true => lower.graph.comap lowerVertex

instance (which : Bool) : DecidableRel (core which).Adj := by
  cases which <;> dsimp [core] <;> infer_instance

/-- Each triple is the removed vertex followed by its two remaining ports.
Indices are zero-based within the seven-vertex core. -/
def step : Bool → Fin 5 → Fin 7 × Fin 7 × Fin 7
  | false => ![(2,1,3), (3,0,1), (1,0,4), (4,0,6), (0,5,6)]
  | true => ![(2,1,4), (1,4,5), (5,3,4), (4,0,3), (0,3,6)]

def active (which : Bool) (k : Fin 6) : Set (Fin 7) :=
  {x | ∀ j : Fin 5, j.val < k.val → x ≠ (step which j).1}

instance (which : Bool) (k : Fin 6) : DecidablePred (· ∈ active which k) := by
  unfold active
  infer_instance

theorem stages_valid : ∀ (which : Bool) (k : Fin 5),
    let s := active which k.castSucc
    let v := (step which k).1
    let u := (step which k).2.1
    let w := (step which k).2.2
    v ∈ s ∧ u ∈ s ∧ w ∈ s ∧ u ≠ v ∧ w ≠ v ∧
    (core which).Adj v u ∧ (core which).Adj v w ∧ (core which).Adj u w ∧
    ∀ x ∈ s, (core which).Adj v x → x = u ∨ x = w := by
  decide +kernel

/-- The next stage is exactly the current one with its specified ear removed. -/
theorem next_active : ∀ (which : Bool) (k : Fin 5) (x : Fin 7),
    x ∈ active which k.succ ↔
      x ∈ active which k.castSucc ∧ x ≠ (step which k).1 := by
  decide +kernel

theorem terminal_edge : ∀ which : Bool,
    ∃ u w : Fin 7, u ≠ w ∧ (core which).Adj u w ∧
      ∀ x, x ∈ active which 5 ↔ x = u ∨ x = w := by
  decide +kernel

/-- Each of the ten actual source stages is an exact two-port constraint
elimination, uniformly over all palettes, lists and inherited relations. -/
theorem stage_elimination {A : Type*} (which : Bool) (k : Fin 5)
    (L : ↥(active which k.castSucc) → A → Prop)
    (R : ↥(active which k.castSucc) → ↥(active which k.castSucc) → A → A → Prop) :
    ∃ v : ↥(active which k.castSucc),
      ∃ u w : ↥(({v} : Set ↥(active which k.castSucc))ᶜ),
        v.val = (step which k).1 ∧ u.val.val = (step which k).2.1 ∧
        w.val.val = (step which k).2.2 ∧
        ((∃ f, Valid ((core which).induce (active which k.castSucc)) L R f) ↔
          ∃ f, Valid (((core which).induce (active which k.castSucc)).induce
            ({v} : Set ↥(active which k.castSucc))ᶜ) (fun x => L x)
            (EarRelation L R v u w) f) := by
  obtain ⟨hv, hu, hw, huv, hwv, hvu, hvw, huw, neighbours⟩ := stages_valid which k
  let v : ↥(active which k.castSucc) := ⟨(step which k).1, hv⟩
  let u : ↥(({v} : Set ↥(active which k.castSucc))ᶜ) :=
    ⟨⟨(step which k).2.1, hu⟩, fun h => huv (congrArg Subtype.val h)⟩
  let w : ↥(({v} : Set ↥(active which k.castSucc))ᶜ) :=
    ⟨⟨(step which k).2.2, hw⟩, fun h => hwv (congrArg Subtype.val h)⟩
  refine ⟨v, u, w, rfl, rfl, rfl, ear_iff _ L R v u w hvu hvw huw ?_⟩
  intro x hx
  exact (neighbours x x.property hx).imp Subtype.ext Subtype.ext

end FourColor.TwoPortCoreElimination
