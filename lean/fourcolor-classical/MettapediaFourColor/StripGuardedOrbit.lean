import MettapediaFourColor.StripAnchoredExtension
import Mettapedia.GraphTheory.Kempe.PairHistory

/-!
# A shared invariant for guarded anchor histories

A finite check at one colouring suffices for arbitrarily long guarded
histories on any graph. Palette covariance transports the check to the
whole orbit. Neither the vertex type nor the phase lengths are bounded.
-/

namespace FourColor.StripGuardedOrbit

open Color SimpleGraph StripResponseSummary StripAnchoredExtension

variable {V : Type*} {G : SimpleGraph V}

def Orbit (base c : V → Color) : Prop :=
  ∃ g : Equiv.Perm Color, ∀ v, c v = g (base v)

def read (port : Fin 11 → V) (c : V → Color) : Boundary := fun i => c (port i)

def Guard (port : Fin 11 → V) (C D : G.Coloring Color) : Prop :=
  Full (read port D) ∨ (choices (read port C)).card ≤ (choices (read port D)).card

def Phase (port : Fin 11 → V) (C D : G.Coloring Color) : Prop :=
  ∃ a b : Color, Relation.ReflTransGen (KempePairHistory.Step a b) C D ∧ Guard port C D

def rename (g : Equiv.Perm Color) (C : G.Coloring Color) : G.Coloring Color :=
  .mk (fun v => g (C v)) (fun edge eq => C.valid edge (g.injective eq))

variable (port : Fin 11 → V) (base : G.Coloring Color) (n : Nat)
  (profile : ¬ Full (read port base) ∧ (choices (read port base)).card = n)
  (barrier : ∀ (a b : Color) (D : G.Coloring Color),
    (∀ v, D v = base v ∨ D v = Equiv.swap a b (base v)) →
    Orbit base D ∨ (¬ Full (read port D) ∧ (choices (read port D)).card < n))

include profile in
theorem orbit_profile {C : G.Coloring Color} (hc : Orbit base C) :
    ¬ Full (read port C) ∧ (choices (read port C)).card = n := by
  obtain ⟨g,hg⟩ := hc
  have eq : read port C = fun i => g (read port base i) := funext (fun i => hg (port i))
  rw [eq,full_map,count_map]
  exact profile

include profile barrier

theorem pointwise_stays {C D : G.Coloring Color} (hc : Orbit base C)
    (a b : Color) (hp : ∀ v, D v = C v ∨ D v = Equiv.swap a b (C v))
    (guard : Guard port C D) : Orbit base D := by
  obtain ⟨g,hg⟩ := hc
  have hp' : ∀ v, rename g.symm D v = base v ∨
      rename g.symm D v = Equiv.swap (g.symm a) (g.symm b) (base v) := by
    intro v
    rcases hp v with h | h
    · left
      change g.symm (D v) = base v
      rw [h,hg v,Equiv.symm_apply_apply]
    · right
      change g.symm (D v) = _
      rw [h,g.symm.injective.map_swap,hg v,Equiv.symm_apply_apply]
  rcases barrier (g.symm a) (g.symm b) (rename g.symm D) hp' with good | bad
  · obtain ⟨k,hk⟩ := good
    refine ⟨k.trans g,fun v => ?_⟩
    have h := congrArg g (hk v)
    change g (g.symm (D v)) = g (k (base v)) at h
    change D v = g (k (base v))
    simpa only [Equiv.apply_symm_apply] using h
  · have noFull : ¬ Full (read port D) := by
      have hn := bad.1
      change ¬ Full (fun i => g.symm (read port D i)) at hn
      simpa only [full_map] using hn
    have small : (choices (read port D)).card < n := by
      have hn := bad.2
      change (choices (fun i => g.symm (read port D i))).card < n at hn
      simpa only [count_map] using hn
    have count := (orbit_profile port base n profile ⟨g,hg⟩).2
    rcases guard with done | more
    · exact False.elim (noFull done)
    · omega

theorem history_stays {D : G.Coloring Color}
    (history : Relation.ReflTransGen (Phase port) base D) : Orbit base D := by
  induction history with
  | refl => exact ⟨Equiv.refl _,fun _ => rfl⟩
  | tail _ step ih =>
    obtain ⟨a,b,hp,guard⟩ := step
    exact pointwise_stays port base n profile barrier ih a b
      (KempePairHistory.pointwise hp) guard

theorem history_nonextension {D : G.Coloring Color}
    (history : Relation.ReflTransGen (Phase port) base D) : ¬ Full (read port D) :=
  (orbit_profile port base n profile (history_stays port base n profile barrier history)).1

end FourColor.StripGuardedOrbit
