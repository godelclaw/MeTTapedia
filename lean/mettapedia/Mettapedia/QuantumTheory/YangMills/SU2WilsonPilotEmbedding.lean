import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly

/-!
# The original SU(2) pilot blocks inside the periodic assembly

Translations of the pilot's side-two four-dimensional cube embed into the
SC4 torus. Its four plaquette links, including their orientations, agree with
the torus links. Consequently the pilot Wilson observables are literally the
assembly's plaquette observables. Adjacent translated blocks use the same
variable on their shared face.
-/
set_option autoImplicit false
noncomputable section
open Finset
open scoped Topology Classical
namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonPilotEmbedding
open StrongCouplingCrossing SU2WilsonBlockPilot
variable {n : ℕ}

/-- Translate the pilot vertices into the torus. -/
def embedVertex (x : Site 4 n) (v : BlockVertex) : Site 4 n :=
  x + fun i => ((v i).val : ZMod (n + 3))

def embedLink (x : Site 4 n) (e : BlockLink) : Link 4 n :=
  (embedVertex x e.origin, e.direction)

def embedPlaquette (x : Site 4 n) (p : BlockPlaquette) : Plaquette 4 n :=
  (embedVertex x p.origin, ⟨(p.first, p.second), p.ordered⟩)

theorem embedVertex_injective (x : Site 4 n) : Function.Injective (embedVertex x) := by
  intro v w h
  have hc := add_left_cancel h
  funext i
  apply Fin.ext
  have hi := congrArg ZMod.val (congrFun hc i)
  simpa only [ZMod.val_natCast,
    Nat.mod_eq_of_lt ((v i).isLt.trans_le (by omega : 3 ≤ n + 3)),
    Nat.mod_eq_of_lt ((w i).isLt.trans_le (by omega : 3 ≤ n + 3))] using hi

theorem embedLink_injective (x : Site 4 n) : Function.Injective (embedLink x) := by
  intro e f h
  have ho := embedVertex_injective x (congrArg Prod.fst h)
  have hd := congrArg Prod.snd h
  cases e
  cases f
  dsimp [embedLink] at ho hd
  cases ho
  cases hd
  rfl

theorem embedPlaquette_injective (x : Site 4 n) : Function.Injective (embedPlaquette x) := by
  intro p q h
  have ho := embedVertex_injective x (congrArg Prod.fst h)
  have hd := congrArg (fun p : Plaquette 4 n => p.2.val) h
  have hf := congrArg Prod.fst hd
  have hs := congrArg Prod.snd hd
  cases p
  cases q
  dsimp [embedPlaquette] at ho hf hs
  cases ho
  cases hf
  cases hs
  rfl

theorem embedVertex_endpoint (x : Site 4 n) (e : BlockLink) :
    embedVertex x e.endpoint = embedVertex x e.origin + step e.direction := by
  funext i
  by_cases hi : i = e.direction
  · subst i
    simp [embedVertex, BlockLink.endpoint, step, add_assoc]
  · simp [embedVertex, BlockLink.endpoint, step, hi]

/-- The original pilot's oriented boundary order. -/
def pilotLinkAt (p : BlockPlaquette) : Fin 4 → BlockLink :=
  ![p.firstLink, p.secondAfterFirst, p.firstAfterSecond, p.secondLink]

theorem embed_linkAt (x : Site 4 n) (p : BlockPlaquette) (i : Fin 4) :
    embedLink x (pilotLinkAt p i) = linkAt (embedPlaquette x p) i := by
  fin_cases i
  · rfl
  · change (embedVertex x p.firstLink.endpoint, p.second) =
      (embedVertex x p.origin + step p.first, p.second)
    rw [embedVertex_endpoint]
    rfl
  · change (embedVertex x p.secondLink.endpoint, p.first) =
      (embedVertex x p.origin + step p.second, p.first)
    rw [embedVertex_endpoint]
    rfl
  · rfl

/-- Pulling a full torus field back to one embedded pilot block. -/
def restrictField (x : Site 4 n) (U : Link 4 n → SU2) : BlockLinkField :=
  fun e => U (embedLink x e)

theorem holonomy_embed (x : Site 4 n) (U : Link 4 n → SU2) (p : BlockPlaquette) :
    plaquetteHolonomy (restrictField x U) p =
      StrongCouplingTwist.holonomy (fun i => U (linkAt (embedPlaquette x p) i)) := by
  simp_rw [← embed_linkAt x p]
  rfl

/-- The original pilot potential and the actual torus Wilson mark agree. -/
theorem potential_embed (x : Site 4 n) (U : Link 4 n → SU2) (p : BlockPlaquette) :
    plaquettePotential (restrictField x U) p =
      SU2BoundaryResponse.plaquetteEnergy (fun i => U (linkAt (embedPlaquette x p) i)) := by
  unfold plaquettePotential
  rw [holonomy_embed]
  rfl

/-- A tangential link on the right face of the pilot at the origin. -/
def rightFaceLink : BlockLink := ⟨![2, 0, 0, 0], 1, by decide⟩

/-- The corresponding link on the left face of its neighboring pilot. -/
def leftFaceLink : BlockLink := ⟨![0, 0, 0, 0], 1, by decide⟩

/-- Two adjacent side-two blocks share an actual link, not independent copies. -/
theorem adjacent_shared_link (x : Site 4 n) :
    embedLink x rightFaceLink = embedLink (x + step 0 + step 0) leftFaceLink := by
  apply Prod.ext
  · funext i
    fin_cases i <;> norm_num [embedLink, embedVertex, rightFaceLink, leftFaceLink, step, add_assoc]
  · rfl

#print axioms embedLink_injective
#print axioms embedPlaquette_injective
#print axioms holonomy_embed
#print axioms potential_embed
#print axioms adjacent_shared_link
end Mettapedia.QuantumTheory.YangMills.SU2WilsonPilotEmbedding
