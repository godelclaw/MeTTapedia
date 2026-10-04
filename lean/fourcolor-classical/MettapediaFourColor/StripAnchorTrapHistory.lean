import MettapediaFourColor.StripAnchorTrap
import MettapediaFourColor.StripGuardedOrbit

/-!
# Arbitrary histories at the physical anchor trap

Every fixed-pair phase from the palette orbit either remains in that orbit
or loses joint one-hole choices without extending. Consequently a policy
which permits an immediate extension but otherwise preserves those choices
cannot finish, regardless of the number or lengths of its phases.

At the invariant orbit, the minimum number of non-anchor holes is one and
there are four optimal anchor choices. Thus this obstructs lexicographic
descent by minimum holes and then by the negative number of optimal choices.
The two-step physical escape explicitly sacrifices choices before extending.
-/

namespace FourColor.StripAnchorTrap

open Color SimpleGraph StripResponseSummary StripAnchoredExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

theorem pair_cases : ∀ a b : Color, a = b ∨ ∃ s : Fin 6,
    (a = (pair s).1 ∧ b = (pair s).2) ∨ (a = (pair s).2 ∧ b = (pair s).1) := by
  decide +kernel

theorem indexed_barrier (s : Fin 6) (D : exterior.Coloring Color)
    (hp : ∀ v, D v = state 0 v ∨ D v = Equiv.swap (pair s).1 (pair s).2 (state 0 v)) :
    Orbit D ∨ (¬ Full (read D) ∧ (choices (read D)).card < 4) := by
  obtain ⟨bits,hb⟩ := KempePhaseBoundary.endpoint (state 0) D _ _ hp
    id (roots s) (label s) (routes s)
  have eq : (D : Fin 12 → Color) = answer s bits := funext hb
  rw [eq]
  exact answer_barrier s bits

theorem base_barrier (a b : Color) (D : exterior.Coloring Color)
    (hp : ∀ v, D v = state 0 v ∨ D v = Equiv.swap a b (state 0 v)) :
    Orbit D ∨ (¬ Full (read D) ∧ (choices (read D)).card < 4) := by
  rcases pair_cases a b with eq | ⟨s,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
  · left
    refine ⟨Equiv.refl _,fun v => ?_⟩
    change D v = state 0 v
    simpa [eq] using hp v
  · exact indexed_barrier s D hp
  · exact indexed_barrier s D (by simpa only [Equiv.swap_comm] using hp)

def rename (g : Equiv.Perm Color) (C : exterior.Coloring Color) : exterior.Coloring Color :=
  .mk (fun v => g (C v)) (fun edge eq => C.valid edge (g.injective eq))

theorem orbit_profile {C : exterior.Coloring Color} (hc : Orbit C) :
    ¬ Full (read C) ∧ (choices (read C)).card = 4 := by
  obtain ⟨g,hg⟩ := hc
  have eq : read C = fun i => g (read (values 0) i) := funext (fun i => hg (port i))
  rw [eq,full_map,count_map]
  exact base_profile

/-- At a blocked one-hole state, nonworsening minimum-hole/choice rank
requires either completion or at least as many joint one-hole choices. -/
def Guard (C D : exterior.Coloring Color) : Prop :=
  Full (read D) ∨ (choices (read C)).card ≤ (choices (read D)).card

theorem pointwise_stays {C D : exterior.Coloring Color} (hc : Orbit C)
    (a b : Color) (hp : ∀ v, D v = C v ∨ D v = Equiv.swap a b (C v))
    (guard : Guard C D) : Orbit D := by
  exact StripGuardedOrbit.pointwise_stays port (state 0) 4 base_profile base_barrier
    hc a b hp guard

/-- A step may contain any finite number of switches of its selected pair. -/
def PreservesChoices (C D : exterior.Coloring Color) : Prop :=
  ∃ a b : Color, Relation.ReflTransGen (KempePairHistory.Step a b) C D ∧ Guard C D

theorem step_stays {C D : exterior.Coloring Color} (hc : Orbit C)
    (step : PreservesChoices C D) : Orbit D := by
  obtain ⟨a,b,history,guard⟩ := step
  exact pointwise_stays hc a b (KempePairHistory.pointwise history) guard

theorem history_stays {D : exterior.Coloring Color}
    (history : Relation.ReflTransGen PreservesChoices (state 0) D) : Orbit D := by
  induction history with
  | refl => exact ⟨Equiv.refl _,fun _ => rfl⟩
  | tail _ step ih => exact step_stays ih step

theorem history_nonextension {D : exterior.Coloring Color}
    (history : Relation.ReflTransGen PreservesChoices (state 0) D) : ¬ Full (read D) :=
  (orbit_profile (history_stays history)).1

/-- This excludes genuine source colourings with the retained port values. -/
theorem history_no_source {D : exterior.Coloring Color}
    (history : Relation.ReflTransGen PreservesChoices (state 0) D) :
    ¬ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (port i) := by
  rintro ⟨k,hk⟩
  apply history_nonextension history
  apply (full_iff _).mpr
  exact ⟨_,StripResponseSummary.valid_of_colouring (read D) k hk⟩

def repairPair : Fin 2 → Color × Color := ![(c0,c1),(c1,c3)]
def repairChain : Fin 2 → List (Fin 12) := ![[0,1,11,4],[7]]
def repairRoot (s : Fin 2) : Fin 12 := (repairChain s).head!

theorem repair_checked : ∀ s,
    repairRoot s ∈ repairChain s ∧ (repairChain s).IsChain exterior.Adj ∧
    (∀ x ∈ repairChain s, state s.castSucc x = (repairPair s).1 ∨
      state s.castSucc x = (repairPair s).2) ∧
    (∀ x ∈ repairChain s, ∀ y, exterior.Adj x y →
      (state s.castSucc y = (repairPair s).1 ∨ state s.castSucc y = (repairPair s).2) →
      y ∈ repairChain s) ∧
    (∀ x, state s.succ x = if x ∈ repairChain s then
      Equiv.swap (repairPair s).1 (repairPair s).2 (state s.castSucc x)
      else state s.castSucc x) := by decide +kernel

def repairCertificate (s : Fin 2) :
    KempeSeparatedChains.Certificate (state s.castSucc) (repairPair s).1 (repairPair s).2 where
  vertices := repairChain s
  root := repairRoot s
  root_mem := (repair_checked s).1
  connected := (repair_checked s).2.1
  active := (repair_checked s).2.2.1
  closed := (repair_checked s).2.2.2.1

theorem repair_eq (s : Fin 2) : (repairCertificate s).swap = state s.succ := by
  ext x
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact ((repair_checked s).2.2.2.2 x).symm

noncomputable def repairStep (s : Fin 2) : Step (state s.castSucc) (state s.succ) :=
  repair_eq s ▸ (repairCertificate s).step

noncomputable def repairHistory : History (state 0) (state 2) :=
  .cons (repairStep 0) (.cons (repairStep 1) (.refl _))

theorem repair_length : repairHistory.length = 2 := rfl

theorem intermediate_profile : ¬ Full (read (values 1)) ∧
    (choices (read (values 1))).card = 1 := by decide +kernel

def finalCore : Fin 8 → Color := ![c3,c2,c3,c1,c1,c1,c0,c3]
theorem final_valid : ValidCore (read (values 2)) finalCore := by
  unfold ValidCore
  decide +kernel

/-- The escape first reduces the number of optimal one-hole choices from
four to one; its second actual component switch restores all vertices. -/
theorem escape_profiles :
    (¬ Full (read (state 0)) ∧ (choices (read (state 0))).card = 4) ∧
    (¬ Full (read (state 1)) ∧ (choices (read (state 1))).card = 1) ∧
    Full (read (state 2)) :=
  ⟨base_profile,intermediate_profile,(full_iff _).mpr ⟨finalCore,final_valid⟩⟩

def wholeEdges : List (Fin 20 × Fin 20) :=
  (List.finRange 12).flatMap (fun v => (star v).map
    (fun w => (v.castAdd 8,w.castAdd 8))) ++
    StripResponseSummary.edges.map (fun e => (e.1.natAdd 12,e.2.natAdd 12)) ++
    (List.finRange 8).flatMap (fun i => (attachments i).map
      (fun j => (i.natAdd 12,j.castLE (by decide))))

def whole : SimpleGraph (Fin 20) where
  Adj u v := (u,v) ∈ wholeEdges ∨ (v,u) ∈ wholeEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel whole.Adj := by unfold whole; infer_instance

def sourceVertex (v : Fin 19) : Fin 20 :=
  Fin.addCases (m := 11) (n := 8) (motive := fun _ => Fin 20)
    (fun i => i.castLE (by decide)) (fun i => i.natAdd 12) v

theorem source_edges : ∀ u v, TriangleStripAnchors.input0099.graph.Adj u v →
    whole.Adj (sourceVertex u) (sourceVertex v) := by decide +kernel

theorem core_stars : ∀ i : Fin 8, ∀ v : Fin 20,
    whole.Adj (i.natAdd 12) v ↔ ∃ j : Fin 19,
      TriangleStripAnchors.input0099.graph.Adj (TriangleStripAnchors.vertex0099 i) j ∧
        sourceVertex j = v := by decide +kernel

def finalValues (v : Fin 20) : Color :=
  Fin.addCases (m := 12) (n := 8) (motive := fun _ => Color) (fun x => state 2 x) finalCore v

theorem whole_valid : ∀ u v, whole.Adj u v → finalValues u ≠ finalValues v := by decide +kernel
def finalColouring : whole.Coloring Color := .mk finalValues (fun h => whole_valid _ _ h)

theorem final_exterior (v : Fin 12) : finalColouring (v.castAdd 8) = state 2 v := by
  change Fin.addCases (m := 12) (n := 8) (motive := fun _ => Color)
    (fun x => state 2 x) finalCore (v.castAdd 8) = _
  simp

theorem reconstructed : Nonempty (History (state 0) (state 2)) ∧
    ∃ k : whole.Coloring Color, ∀ v : Fin 12, k (v.castAdd 8) = state 2 v :=
  ⟨⟨repairHistory⟩,finalColouring,final_exterior⟩

end FourColor.StripAnchorTrap
