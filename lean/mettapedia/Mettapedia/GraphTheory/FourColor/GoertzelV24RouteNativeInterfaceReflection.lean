import Mettapedia.GraphTheory.FourColor.GoertzelV24DecomposableFiniteBase
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphericalRouteNativeBaseReflection

/-!
# Route-native interface profiles, and a base reflection that actually reduces

The two earlier reflection interfaces in this lane carry a free field

```
necessary_of_not_colorable :
  ∀ map …, ¬ RotationSystemTaitColorable … → Necessary (trace map …)
```

together with a free `Necessary`.  Taking `State := Unit` and
`Necessary := fun _ => False` turns that field into the base obligation
verbatim, so an inhabitant of the interface is exactly a proof of the thing
the interface was supposed to reduce.  The structure is not *trivially*
satisfiable; it is satisfiable only by someone who has already finished the
job, which is worse, because the types promise a reduction that is not there.

This module replaces the free adequacy field by a theorem.  The replacement
has four moving parts.

* `interfaceProfile` is the route's own instrument, written down: for a piece
  of a map and a width-`b` boundary interface, the finite set of boundary
  words realized by an *open* Tait colouring of that piece.  It lives in the
  fixed finite type `Finset (Fin b → Color)`, so bounded interface width —
  and nothing else — is what makes the state space finite.
* `interfaceProfile_univ_eq_empty_iff` anchors it: the profile of the whole
  map at any interface is empty exactly when the map is not Tait colourable.
  This is the step that used to be a field.
* `interfaceProfile_union` is the transfer law: along a cut whose interface
  separates the two sides, the profile of the union is the intersection of
  the two side profiles.  This is the composition the machine runs.
* `RouteNativeInterfaceInstrument` forces a carrier to *be* that instrument:
  finite, decidable, profile-faithful, closed under the transfer, and able to
  name the true profile of every bounded-width interface of every piece.

`Necessary` is then not a field at all — it is `profileOf s = ∅` — and the
degenerate carrier is refuted by `bananaRotationSystem`, four parallel edges
whose full-piece and empty-piece profiles differ.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RouteNativeInterfaceReflection

open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24DecomposableFiniteBase
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24SphericalRouteNativeBaseReflection
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

universe u v

/-! ## Bounded interfaces

An interface of width `b` is a total indexing `Fin b → Option E` of at most `b`
edges.  `none` is an absent port, so a cut carrying fewer than `b` edges pads
rather than changing the carrier: the profile type stays `Finset (Fin b → Color)`
whatever map it came from, and bounded width is the only source of finiteness. -/

section Interfaces

variable {E : Type*} [DecidableEq E] {b : Nat}

/-- The edges named by a width-`b` interface indexing. -/
def interfaceEdges (iface : Fin b → Option E) : Finset E :=
  Finset.univ.biUnion fun i => (iface i).toFinset

@[simp]
theorem mem_interfaceEdges (iface : Fin b → Option E) (e : E) :
    e ∈ interfaceEdges iface ↔ ∃ i, iface i = some e := by
  simp [interfaceEdges, Option.mem_toFinset, Option.mem_def]

/-- The boundary word a colouring displays at the interface.  An absent port
carries the non-colour `0`, which no legal edge colour ever takes. -/
def interfaceWord (iface : Fin b → Option E) (c : E → Color) : Fin b → Color :=
  fun i => (iface i).elim 0 c

omit [DecidableEq E] in
@[simp]
theorem interfaceWord_some {iface : Fin b → Option E} {i : Fin b} {e : E}
    (h : iface i = some e) (c : E → Color) : interfaceWord iface c i = c e := by
  simp [interfaceWord, h]

/-- The interface with every port absent. -/
def noPorts (b : Nat) (E : Type*) : Fin b → Option E := fun _ => none

@[simp]
theorem interfaceEdges_noPorts : interfaceEdges (noPorts b E) = ∅ := by
  refine Finset.subset_empty.1 fun e he => ?_
  obtain ⟨i, hi⟩ := (mem_interfaceEdges _ e).1 he
  exact absurd hi (by simp [noPorts])

end Interfaces

/-! ## Open Tait colourings of a piece -/

section Profiles

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

instance decidableEdgeAdjacency (RS : RotationSystem V E) :
    DecidableRel RS.edgeAdjacencyGraph.Adj := fun e f =>
  decidable_of_iff (e ≠ f ∧ ∃ v : V, v ∈ RS.endpoints e ∧ v ∈ RS.endpoints f)
    (RS.edgeAdjacencyGraph_adj_iff).symm

/-- An **open Tait colouring of a piece**: nonzero colours on the piece's
edges, proper at every shared endpoint.  Edges outside the piece are
unconstrained, which is exactly what makes a piece *open*. -/
def IsPieceColoring (RS : RotationSystem V E) (piece : Finset E)
    (c : E → Color) : Prop :=
  (∀ e ∈ piece, c e ≠ 0) ∧
    ∀ e ∈ piece, ∀ f ∈ piece, RS.edgeAdjacencyGraph.Adj e f → c e ≠ c f

instance (RS : RotationSystem V E) (piece : Finset E) :
    DecidablePred (IsPieceColoring RS piece) := fun c => by
  unfold IsPieceColoring
  infer_instance

theorem IsPieceColoring.mono {RS : RotationSystem V E} {big small : Finset E}
    {c : E → Color} (h : IsPieceColoring RS big c) (hsub : small ⊆ big) :
    IsPieceColoring RS small c :=
  ⟨fun e he => h.1 e (hsub he), fun e he f hf hadj => h.2 e (hsub he) f (hsub hf) hadj⟩

/-- A closed piece is exactly a Tait colouring of the whole map. -/
theorem taitColorable_iff_exists_pieceColoring (RS : RotationSystem V E) :
    RotationSystemTaitColorable RS ↔
      ∃ c : E → Color, IsPieceColoring RS Finset.univ c := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨⇑C, fun e _ => hC e, fun e _ f _ hadj => C.valid hadj⟩
  · rintro ⟨c, hzero, hproper⟩
    refine ⟨SimpleGraph.Coloring.mk c ?_, fun e => hzero e (Finset.mem_univ e)⟩
    intro e f hadj
    exact hproper e (Finset.mem_univ e) f (Finset.mem_univ f) hadj

/-! ## Finite interface profiles -/

/-- **The route-native finite interface profile.**  The boundary words that an
open Tait colouring of the piece (together with its interface edges) actually
realizes.  The carrier `Finset (Fin b → Color)` does not mention the map, so
bounded interface width is the only source of finiteness. -/
def interfaceProfile (RS : RotationSystem V E) (piece : Finset E)
    {b : Nat} (iface : Fin b → Option E) : Finset (Fin b → Color) :=
  ((Finset.univ : Finset (E → Color)).filter
      (IsPieceColoring RS (piece ∪ interfaceEdges iface))).image
    (interfaceWord iface)

theorem mem_interfaceProfile {RS : RotationSystem V E} {piece : Finset E}
    {b : Nat} {iface : Fin b → Option E} {word : Fin b → Color} :
    word ∈ interfaceProfile RS piece iface ↔
      ∃ c : E → Color,
        IsPieceColoring RS (piece ∪ interfaceEdges iface) c ∧
          interfaceWord iface c = word := by
  simp [interfaceProfile, Finset.mem_image, Finset.mem_filter]

/-! ### The anchor: an empty profile *is* non-colourability -/

/-- **The adequacy step, as a theorem.**  The profile of the whole map at any
interface is empty exactly when the map admits no Tait colouring.  In the old
interfaces this implication was a field that a trivial carrier could fill with
the base obligation itself. -/
theorem interfaceProfile_univ_eq_empty_iff (RS : RotationSystem V E)
    {b : Nat} (iface : Fin b → Option E) :
    interfaceProfile RS Finset.univ iface = ∅ ↔
      ¬ RotationSystemTaitColorable RS := by
  have hU : (Finset.univ : Finset E) ∪ interfaceEdges iface = Finset.univ :=
    Finset.eq_univ_iff_forall.2 fun e => Finset.mem_union_left _ (Finset.mem_univ e)
  rw [taitColorable_iff_exists_pieceColoring]
  constructor
  · intro hempty
    rintro ⟨c, hc⟩
    have hmem : interfaceWord iface c ∈ interfaceProfile RS Finset.univ iface :=
      mem_interfaceProfile.2 ⟨c, by rw [hU]; exact hc, rfl⟩
    rw [hempty] at hmem
    simp at hmem
  · intro hnone
    refine Finset.subset_empty.1 fun word hword => ?_
    rcases mem_interfaceProfile.1 hword with ⟨c, hc, -⟩
    rw [hU] at hc
    exact absurd ⟨c, hc⟩ hnone

/-! ### The transfer law -/

/-- **Composition along a separating interface.**  If the two sides of a cut
are disjoint and every adjacency across the cut is named by the interface,
then the profile of the composite piece is the intersection of the two side
profiles.  This is the route's transfer step: the finite state of a composite
is computed from the finite states of its parts, with no reference to the
ambient map beyond the two profiles. -/
theorem interfaceProfile_union (RS : RotationSystem V E) {A B : Finset E}
    {b : Nat} (iface : Fin b → Option E)
    (hdisj : Disjoint A B)
    (hsep : ∀ e ∈ A, ∀ f ∈ B, RS.edgeAdjacencyGraph.Adj e f →
      e ∈ interfaceEdges iface ∧ f ∈ interfaceEdges iface) :
    interfaceProfile RS (A ∪ B) iface =
      interfaceProfile RS A iface ∩ interfaceProfile RS B iface := by
  classical
  set S := interfaceEdges iface with hS
  have hleftsub : A ∪ S ⊆ A ∪ B ∪ S := by
    intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_right _ h
  have hrightsub : B ∪ S ⊆ A ∪ B ∪ S := by
    intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_right _ h
  ext word
  rw [Finset.mem_inter]
  constructor
  · intro hword
    rcases mem_interfaceProfile.1 hword with ⟨c, hc, hrestrict⟩
    exact ⟨mem_interfaceProfile.2 ⟨c, hc.mono hleftsub, hrestrict⟩,
      mem_interfaceProfile.2 ⟨c, hc.mono hrightsub, hrestrict⟩⟩
  · rintro ⟨hleft, hright⟩
    rcases mem_interfaceProfile.1 hleft with ⟨c₁, hc₁, hword₁⟩
    rcases mem_interfaceProfile.1 hright with ⟨c₂, hc₂, hword₂⟩
    -- the two side colourings agree on every interface edge
    have hagree : ∀ e ∈ S, c₁ e = c₂ e := by
      intro e he
      rcases (mem_interfaceEdges iface e).1 he with ⟨i, hi⟩
      have h₁ : c₁ e = word i := by rw [← hword₁]; simp [interfaceWord, hi]
      have h₂ : c₂ e = word i := by rw [← hword₂]; simp [interfaceWord, hi]
      rw [h₁, h₂]
    refine mem_interfaceProfile.2 ⟨fun e => if e ∈ A then c₁ e else c₂ e, ?_, ?_⟩
    · -- the spliced colouring agrees with each side on that side
      have hleftEq : ∀ e ∈ A ∪ S, (if e ∈ A then c₁ e else c₂ e) = c₁ e := by
        intro e he
        by_cases hA : e ∈ A
        · simp [hA]
        · have hSe : e ∈ S := by
            rcases Finset.mem_union.1 he with h | h
            · exact absurd h hA
            · exact h
          simp [hA, (hagree e hSe).symm]
      have hrightEq : ∀ e ∈ B ∪ S, (if e ∈ A then c₁ e else c₂ e) = c₂ e := by
        intro e he
        by_cases hA : e ∈ A
        · have hSe : e ∈ S := by
            rcases Finset.mem_union.1 he with h | h
            · exact absurd h (Finset.disjoint_left.1 hdisj hA)
            · exact h
          simp [hA, hagree e hSe]
        · simp [hA]
      constructor
      · intro e he
        show (if e ∈ A then c₁ e else c₂ e) ≠ 0
        by_cases hA : e ∈ A
        · rw [hleftEq e (Finset.mem_union_left _ hA)]
          exact hc₁.1 e (Finset.mem_union_left _ hA)
        · have he' : e ∈ B ∪ S := by
            rcases Finset.mem_union.1 he with h | h
            · rcases Finset.mem_union.1 h with h' | h'
              · exact absurd h' hA
              · exact Finset.mem_union_left _ h'
            · exact Finset.mem_union_right _ h
          rw [hrightEq e he']
          exact hc₂.1 e he'
      · intro e he f hf hadj
        show (if e ∈ A then c₁ e else c₂ e) ≠ (if f ∈ A then c₁ f else c₂ f)
        by_cases hAe : e ∈ A ∪ S
        · by_cases hAf : f ∈ A ∪ S
          · rw [hleftEq e hAe, hleftEq f hAf]
            exact hc₁.2 e hAe f hAf hadj
          · -- `f` is a `B`-only edge, so `e` must be a pure `A` edge
            have hfB : f ∈ B := by
              rcases Finset.mem_union.1 hf with h | h
              · rcases Finset.mem_union.1 h with h' | h'
                · exact absurd (Finset.mem_union_left _ h') hAf
                · exact h'
              · exact absurd (Finset.mem_union_right _ h) hAf
            by_cases hBe : e ∈ B ∪ S
            · rw [hrightEq e hBe, hrightEq f (Finset.mem_union_left _ hfB)]
              exact hc₂.2 e hBe f (Finset.mem_union_left _ hfB) hadj
            · have heA : e ∈ A := by
                rcases Finset.mem_union.1 hAe with h | h
                · exact h
                · exact absurd (Finset.mem_union_right _ h) hBe
              exact absurd ((hsep e heA f hfB hadj).1)
                (fun h => hBe (Finset.mem_union_right _ h))
        · have heB : e ∈ B := by
            rcases Finset.mem_union.1 he with h | h
            · rcases Finset.mem_union.1 h with h' | h'
              · exact absurd (Finset.mem_union_left _ h') hAe
              · exact h'
            · exact absurd (Finset.mem_union_right _ h) hAe
          by_cases hBf : f ∈ B ∪ S
          · rw [hrightEq e (Finset.mem_union_left _ heB), hrightEq f hBf]
            exact hc₂.2 e (Finset.mem_union_left _ heB) f hBf hadj
          · have hfA : f ∈ A := by
              rcases Finset.mem_union.1 hf with h | h
              · rcases Finset.mem_union.1 h with h' | h'
                · exact h'
                · exact absurd (Finset.mem_union_left _ h') hBf
              · exact absurd (Finset.mem_union_right _ h) hBf
            exact absurd ((hsep f hfA e heB hadj.symm).1)
              (fun h => hBf (Finset.mem_union_right _ h))
    · rw [← hword₁]
      funext i
      cases hi : iface i with
      | none => simp [interfaceWord, hi]
      | some e =>
          have hSe : e ∈ S := (mem_interfaceEdges iface e).2 ⟨i, hi⟩
          by_cases hA : e ∈ A
          · simp [interfaceWord, hi, hA]
          · simp [interfaceWord, hi, hA, (hagree e hSe).symm]

/-- **The separator hypothesis of `interfaceProfile_union`, in middle-set
form.**  A cut interface is legitimate exactly when it names every edge at
every vertex that sees both sides — which is precisely what a branch
decomposition's middle set records.  Given that, adjacency across the cut is
confined to the interface. -/
theorem sep_of_interface_covers_middle (RS : RotationSystem V E)
    {A B : Finset E} {b : Nat} (iface : Fin b → Option E)
    (hcover : ∀ v : V, (∃ e ∈ A, v ∈ RS.endpoints e) →
      (∃ f ∈ B, v ∈ RS.endpoints f) →
      ∀ g : E, v ∈ RS.endpoints g → g ∈ interfaceEdges iface) :
    ∀ e ∈ A, ∀ f ∈ B, RS.edgeAdjacencyGraph.Adj e f →
      e ∈ interfaceEdges iface ∧ f ∈ interfaceEdges iface := by
  intro e he f hf hadj
  obtain ⟨-, v, hve, hvf⟩ := (RS.edgeAdjacencyGraph_adj_iff).1 hadj
  exact ⟨hcover v ⟨e, he, hve⟩ ⟨f, hf, hvf⟩ e hve,
    hcover v ⟨e, he, hve⟩ ⟨f, hf, hvf⟩ f hvf⟩

/-- **The transfer law at a cut presented by its middle set.** -/
theorem interfaceProfile_union_of_middle_cover (RS : RotationSystem V E)
    {A B : Finset E} {b : Nat} (iface : Fin b → Option E)
    (hdisj : Disjoint A B)
    (hcover : ∀ v : V, (∃ e ∈ A, v ∈ RS.endpoints e) →
      (∃ f ∈ B, v ∈ RS.endpoints f) →
      ∀ g : E, v ∈ RS.endpoints g → g ∈ interfaceEdges iface) :
    interfaceProfile RS (A ∪ B) iface =
      interfaceProfile RS A iface ∩ interfaceProfile RS B iface :=
  interfaceProfile_union RS iface hdisj
    (sep_of_interface_covers_middle RS iface hcover)

end Profiles

/-! ## A separating witness: four parallel edges

Everything below rests on one concrete map.  `bananaRotationSystem` has two
vertices and four parallel edges, so any two of its edges are adjacent and no
three colours suffice; its *full* piece profile is therefore empty, while its
*empty* piece is unconstrained and its profile is not.  Two pieces of one map
with different profiles is exactly what a one-state carrier cannot reproduce. -/

section Banana

/-- Four parallel edges joining two vertices. -/
def bananaRotationSystem :
    RotationSystem.{u, u, u} (ULift Bool) (ULift (Fin 4)) where
  D := ULift (Fin 4) × Bool
  edgeOf := Prod.fst
  vertOf := fun d => ULift.up d.2
  alpha := ⟨fun d => (d.1, !d.2), fun d => (d.1, !d.2), fun d => by simp, fun d => by simp⟩
  rho := Equiv.refl _
  alpha_involutive := fun d => by simp
  alpha_fixfree := fun d => by
    obtain ⟨e, bb⟩ := d
    cases bb <;> simp
  edge_alpha := fun _ => rfl
  edge_fiber_two := by
    intro e
    have hset : (Finset.univ.filter
        (fun d : ULift.{u} (Fin 4) × Bool => d.1 = e)) = {(e, true), (e, false)} := by
      ext d
      obtain ⟨a, bb⟩ := d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro rfl
        cases bb <;> simp
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
    rw [hset, Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  vert_rho := fun _ => rfl
  outer := (ULift.up 0, true)
  no_self_loops := fun d => by
    obtain ⟨e, bb⟩ := d
    cases bb <;> simp

theorem banana_mem_endpoints (e : ULift.{u} (Fin 4)) :
    ULift.up true ∈ bananaRotationSystem.{u}.endpoints e :=
  (RotationSystem.mem_endpoints_iff _).2
    ⟨(e, true), (RotationSystem.mem_dartsOn _).2 rfl, rfl⟩

/-- Any two distinct edges of the four-banana share both endpoints. -/
theorem banana_adj {e f : ULift.{u} (Fin 4)} (hne : e ≠ f) :
    bananaRotationSystem.{u}.edgeAdjacencyGraph.Adj e f :=
  (RotationSystem.edgeAdjacencyGraph_adj_iff bananaRotationSystem.{u}).2
    ⟨hne, ULift.up true, banana_mem_endpoints e, banana_mem_endpoints f⟩

theorem banana_not_taitColorable :
    ¬ RotationSystemTaitColorable bananaRotationSystem.{u} := by
  rw [taitColorable_iff_exists_pieceColoring]
  rintro ⟨c, hzero, hproper⟩
  have hinj : Set.InjOn c (Finset.univ : Finset (ULift.{u} (Fin 4))) := by
    intro e _ f _ heq
    by_contra hne
    exact hproper e (Finset.mem_univ _) f (Finset.mem_univ _) (banana_adj hne) heq
  have hsub : (Finset.univ : Finset (ULift.{u} (Fin 4))).image c ⊆
      ({red, blue, purple} : Finset Color) := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨e, -, rfl⟩
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero (c e)
      (hzero e (Finset.mem_univ _)) with h | h | h <;> simp [h]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  have h4 : (Finset.univ : Finset (ULift.{u} (Fin 4))).card = 4 := by
    simp
  have h3 : ({red, blue, purple} : Finset Color).card = 3 := by decide
  rw [h4, h3] at hcard
  omega

/-- The four-banana's closed profile is dead. -/
theorem banana_profile_univ (b : Nat) :
    interfaceProfile bananaRotationSystem.{u} Finset.univ
      (noPorts b (ULift.{u} (Fin 4))) = ∅ :=
  (interfaceProfile_univ_eq_empty_iff _ _).2 banana_not_taitColorable

/-- Its empty piece is unconstrained, so that profile is alive. -/
theorem banana_profile_empty (b : Nat) :
    (interfaceProfile bananaRotationSystem.{u} ∅
      (noPorts b (ULift.{u} (Fin 4)))).Nonempty := by
  refine ⟨interfaceWord (noPorts b (ULift.{u} (Fin 4))) (fun _ => red),
    mem_interfaceProfile.2 ⟨fun _ => red, ?_, rfl⟩⟩
  rw [interfaceEdges_noPorts, Finset.union_empty]
  exact ⟨by simp, by simp⟩

end Banana

/-! ## The strengthened instrument

An inhabitant of `RouteNativeInterfaceInstrument` is forced to *be* the route's
interface machine, not an abstraction chosen once the answer is known:

1. the carrier is a `Fintype` with decidable equality, and `Necessary` is a
   `DecidablePred`, so "check every reachable state" terminates;
2. `stateOf` must return the **true** `interfaceProfile` of every piece of
   every map at every width-`b` interface — the state is pinned to the route's
   own extraction, not chosen after the fact;
3. the carrier is profile-faithful (`profileOf` injective), carries the
   route's transfer `glue`, and `reachable` is closed under every live
   transfer step.

`Necessary` is not a field: it is `profileOf s = ∅`, the route's dead
interface. -/

structure RouteNativeInterfaceInstrument.{u', v'} (b : Nat) (State : Type v') where
  /-- The state carrier is genuinely finite. -/
  stateFintype : Fintype State
  /-- …with decidable equality, so the audit is a terminating computation. -/
  stateDecEq : DecidableEq State
  /-- Every state decodes to a width-`b` route-native interface profile. -/
  profileOf : State → Finset (Fin b → Color)
  /-- The state *is* its profile: no spare bits in which to hide a proof. -/
  profileOf_injective : Function.Injective profileOf
  /-- The machine names a state for every bounded-width interface of every
  piece of every map. -/
  stateOf : ∀ {V E : Type u'} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E],
    RotationSystem.{u', u', u'} V E → Finset E → (Fin b → Option E) → State
  /-- …and that state carries the piece's **true** interface profile.  This is
  the factorization through the route's own instrument. -/
  stateOf_profile :
    ∀ {V E : Type u'} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (RS : RotationSystem.{u', u', u'} V E) (piece : Finset E)
      (iface : Fin b → Option E),
      profileOf (stateOf RS piece iface) = interfaceProfile RS piece iface
  /-- The route's transfer step on states. -/
  glue : State → State → State
  /-- …computing exactly the transfer of `interfaceProfile_union`. -/
  glue_profile : ∀ s t : State, profileOf (glue s t) = profileOf s ∩ profileOf t
  /-- The explicitly computed reachable closure. -/
  reachable : Finset State
  /-- …closed under every transfer step that does not die. -/
  reachable_glue_closed : ∀ s ∈ reachable, ∀ t ∈ reachable,
    (profileOf s ∩ profileOf t).Nonempty → glue s t ∈ reachable

namespace RouteNativeInterfaceInstrument

variable {b : Nat} {State : Type v}

/-- **The counterexample condition, derived rather than supplied.**  A state is
bad exactly when its interface profile is dead: no boundary word at all
extends to an open Tait colouring of the piece. -/
def Necessary (R : RouteNativeInterfaceInstrument.{u, v} b State) (s : State) : Prop :=
  R.profileOf s = ∅

instance instDecidableNecessary (R : RouteNativeInterfaceInstrument.{u, v} b State) :
    DecidablePred R.Necessary := fun s => by
  unfold Necessary
  infer_instance

/-- The instrument must separate states: the closed piece and the empty piece
of the four-banana have different profiles. -/
theorem exists_profileOf_ne (R : RouteNativeInterfaceInstrument.{u, v} b State) :
    ∃ s t : State, R.profileOf s ≠ R.profileOf t := by
  refine ⟨R.stateOf bananaRotationSystem.{u} Finset.univ (noPorts b _),
    R.stateOf bananaRotationSystem.{u} ∅ (noPorts b _), ?_⟩
  rw [R.stateOf_profile, R.stateOf_profile, banana_profile_univ]
  intro h
  exact absurd h.symm (Finset.nonempty_iff_ne_empty.1 (banana_profile_empty b))

/-- **The degenerate carrier is refuted by the types.**  No state type with
fewer than two elements is a route-native instrument. -/
theorem not_subsingleton (R : RouteNativeInterfaceInstrument.{u, v} b State) :
    ¬ Subsingleton State := by
  intro hsub
  obtain ⟨s, t, hst⟩ := R.exists_profileOf_ne
  exact hst (congrArg R.profileOf (Subsingleton.elim s t))

/-- **`State := Unit` no longer inhabits the interface.** -/
theorem isEmpty_unit (b : Nat) :
    IsEmpty (RouteNativeInterfaceInstrument.{u, 0} b Unit) :=
  ⟨fun R => R.not_subsingleton inferInstance⟩

/-- **`Necessary := fun _ => False` is refuted too.**  The dead interface of
the four-banana is a state of every instrument, so the counterexample
condition is never identically false. -/
theorem exists_necessary (R : RouteNativeInterfaceInstrument.{u, v} b State) :
    ∃ s : State, R.Necessary s :=
  ⟨R.stateOf bananaRotationSystem.{u} Finset.univ (noPorts b _), by
    show R.profileOf _ = ∅
    rw [R.stateOf_profile]
    exact banana_profile_univ b⟩

theorem necessary_ne_false (R : RouteNativeInterfaceInstrument.{u, v} b State) :
    R.Necessary ≠ fun _ => False := by
  intro h
  obtain ⟨s, hs⟩ := R.exists_necessary
  rw [h] at hs
  exact hs

/-- The audit really is a *finite* check: the reachable closure is a `Finset`
of a `Fintype`, so it visits at most `Fintype.card State` states. -/
theorem reachable_card_le (R : RouteNativeInterfaceInstrument.{u, v} b State) :
    R.reachable.card ≤ @Fintype.card State R.stateFintype := by
  letI := R.stateFintype
  exact Finset.card_le_univ R.reachable

/-- **Bounded interface width is the only source of that finiteness.**  Because
the carrier is profile-faithful it embeds in `Finset (Fin b → Color)`, whose
size depends on `b` alone and not on the maps the machine will meet. -/
theorem card_le_card_profile (R : RouteNativeInterfaceInstrument.{u, v} b State) :
    @Fintype.card State R.stateFintype ≤
      Fintype.card (Finset (Fin b → Color)) := by
  letI := R.stateFintype
  exact Fintype.card_le_of_injective R.profileOf R.profileOf_injective

end RouteNativeInterfaceInstrument

/-! ### The design is not over-constrained

The tautological instrument — the carrier *is* the profile type — inhabits the
structure, so the strengthening did not make it vacuous.  Its audit correctly
fails, because the dead interface is one of its reachable states: that failure
is precisely the route's remaining base work, now visible as a finite check
rather than hidden in a free field. -/

/-- The tautological route-native instrument. -/
def universalInstrument (b : Nat) :
    RouteNativeInterfaceInstrument.{u, 0} b (Finset (Fin b → Color)) where
  stateFintype := inferInstance
  stateDecEq := inferInstance
  profileOf := id
  profileOf_injective := Function.injective_id
  stateOf := fun RS piece iface => interfaceProfile RS piece iface
  stateOf_profile := fun _ _ _ => rfl
  glue := fun s t => s ∩ t
  glue_profile := fun _ _ => rfl
  reachable := Finset.univ
  reachable_glue_closed := fun _ _ _ _ _ => Finset.mem_univ _

theorem universalInstrument_audit_fails (b : Nat) :
    ¬ ∀ s ∈ (universalInstrument.{u} b).reachable,
        ((universalInstrument.{u} b).profileOf s).Nonempty := by
  intro h
  have hbad := h ∅ (Finset.mem_univ _)
  simp [universalInstrument] at hbad

/-! ## The strengthened spherical reflection

`TaitBaseReflection` is replaced by an instrument plus one *coverage* field.
The old adequacy field is gone: `necessary_of_not_colorable` is now the theorem
`interfaceProfile_univ_eq_empty_iff`, so it can no longer absorb the goal. -/

structure SphericalInterfaceReflection.{u', v'} (bound b : Nat) (State : Type v')
    extends RouteNativeInterfaceInstrument.{u', v'} b State where
  /-- **Coverage.**  The computed closure contains the state of every piece of
  every bounded map at every width-`b` interface.  This is a statement about
  the machine's own reachable set; colourability does not appear in it. -/
  piece_mem_reachable :
    ∀ {V : Type u'} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      (rotation : Data G),
      BridgelessSphericalCubicMapData rotation.toRotationSystem →
      Fintype.card V ≤ bound →
      ∀ (piece : Finset G.edgeSet) (iface : Fin b → Option G.edgeSet),
        stateOf rotation.toRotationSystem piece iface ∈ reachable

namespace SphericalInterfaceReflection

variable {bound b : Nat} {State : Type v}

/-- **The payoff.**  An inhabitant plus one finite check over the reachable
`Finset` discharges the bounded spherical base.  The finiteness is visible:
`reachable : Finset State`, `State` is a `Fintype`, and the audited predicate
is decidable. -/
theorem taitBaseVerifiedAt_of_audit
    (R : SphericalInterfaceReflection.{u, v} bound b State)
    (haudit : ∀ s ∈ R.reachable, (R.profileOf s).Nonempty) :
    TaitBaseVerifiedAt.{u} bound := by
  intro V _ _ G _ rotation mapData hbound
  by_contra hnot
  have hmem := R.piece_mem_reachable rotation mapData hbound
    Finset.univ (noPorts b G.edgeSet)
  have hlive := haudit _ hmem
  rw [R.stateOf_profile,
    (interfaceProfile_univ_eq_empty_iff rotation.toRotationSystem _).2 hnot] at hlive
  simp at hlive

/-- The same audit in replayable finite form: the filtered set of *dead*
reachable states is empty. -/
theorem taitBaseVerifiedAt_of_filter_eq_empty
    (R : SphericalInterfaceReflection.{u, v} bound b State)
    (haudit : R.reachable.filter R.toRouteNativeInterfaceInstrument.Necessary = ∅) :
    TaitBaseVerifiedAt.{u} bound := by
  refine R.taitBaseVerifiedAt_of_audit fun s hs => ?_
  rw [Finset.nonempty_iff_ne_empty]
  intro hdead
  have hmem : s ∈ R.reachable.filter R.toRouteNativeInterfaceInstrument.Necessary :=
    Finset.mem_filter.2 ⟨hs, hdead⟩
  rw [haudit] at hmem
  simp at hmem

/-- The audit as one decidable Boolean: a terminating computation over a
`Finset`, not a quantifier over an unknown class of maps. -/
theorem taitBaseVerifiedAt_of_decide
    (R : SphericalInterfaceReflection.{u, v} bound b State)
    (haudit : decide (∀ s ∈ R.reachable, R.profileOf s ≠ ∅) = true) :
    TaitBaseVerifiedAt.{u} bound :=
  R.taitBaseVerifiedAt_of_audit fun s hs =>
    Finset.nonempty_iff_ne_empty.2 (of_decide_eq_true haudit s hs)

/-- **Nothing is lost.**  Every strengthened spherical reflection is in
particular an old `TaitBaseReflection`, whose formerly free adequacy field is
now discharged by `interfaceProfile_univ_eq_empty_iff`. -/
noncomputable def toTaitBaseReflection [DecidableEq State]
    (R : SphericalInterfaceReflection.{u, v} bound b State) :
    TaitBaseReflection.{u, v} bound State where
  Necessary := R.toRouteNativeInterfaceInstrument.Necessary
  reachable := R.reachable
  trace {V} _ _ {G} _ rotation _ _ :=
    R.stateOf rotation.toRotationSystem Finset.univ (noPorts b G.edgeSet)
  trace_mem_reachable := by
    intro V _ _ G _ rotation mapData hbound
    exact R.piece_mem_reachable rotation mapData hbound _ _
  necessary_of_not_colorable := by
    intro V _ _ G _ rotation mapData hbound hnot
    show R.profileOf _ = ∅
    rw [R.stateOf_profile]
    exact (interfaceProfile_univ_eq_empty_iff _ _).2 hnot

end SphericalInterfaceReflection

/-- The design is inhabitable at the spherical joint too. -/
def universalSphericalReflection (bound b : Nat) :
    SphericalInterfaceReflection.{u, 0} bound b (Finset (Fin b → Color)) where
  toRouteNativeInterfaceInstrument := universalInstrument b
  piece_mem_reachable := by
    intro V _ _ G _ rotation _ _ piece iface
    exact Finset.mem_univ _

/-! ## The strengthened decomposable reflection

`DecomposableBaseReflection` receives the supplied branch decomposition, so its
coverage field can be stated where the route actually states it: at the shores
of the decomposition's own nodes.  A cut whose middle set has at most `w`
vertices touches at most `3 * w` edges of a cubic map, which is why the profile
width is `3 * w`. -/

/-- A shore named by some node of a rooted edge-leaf tree. -/
inductive IsSubtreeShore {E : Type*} [DecidableEq E] :
    EdgeLeafTree E → Finset E → Prop
  | self (tree : EdgeLeafTree E) : IsSubtreeShore tree tree.shore
  | left {l r : EdgeLeafTree E} {s : Finset E} :
      IsSubtreeShore l s → IsSubtreeShore (EdgeLeafTree.fork l r) s
  | right {l r : EdgeLeafTree E} {s : Finset E} :
      IsSubtreeShore r s → IsSubtreeShore (EdgeLeafTree.fork l r) s

structure DecomposableInterfaceReflection.{u', v'} (k w : Nat) (State : Type v')
    extends RouteNativeInterfaceInstrument.{u', v'} (3 * w) State where
  /-- **Coverage.**  The computed closure contains the state of the whole map
  and of every shore of the supplied decomposition, at every interface
  indexing.  Colourability does not appear: this is the route's own claim that
  its reachable closure covers what its sweep meets. -/
  node_mem_reachable :
    ∀ {V : Type u'} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      (rotation : Data G),
      BridgelessSphericalCubicMapData rotation.toRotationSystem →
      Fintype.card V ≤ rawVertexBound k w →
      ∀ (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
        (piece : Finset G.edgeSet) (iface : Fin (3 * w) → Option G.edgeSet),
        (piece = Finset.univ ∨ IsSubtreeShore decomposition.left piece ∨
          IsSubtreeShore decomposition.right piece) →
        stateOf rotation.toRotationSystem piece iface ∈ reachable

namespace DecomposableInterfaceReflection

variable {k w : Nat} {State : Type v}

/-- **The payoff.**  An inhabitant plus one finite check over the reachable
`Finset` discharges the restricted base obligation. -/
theorem taitBaseVerifiedOnDecomposable_of_audit
    (R : DecomposableInterfaceReflection.{u, v} k w State)
    (haudit : ∀ s ∈ R.reachable, (R.profileOf s).Nonempty) :
    TaitBaseVerifiedOnDecomposable.{u} k w := by
  intro V _ _ G _ rotation mapData hbound decomposition
  by_contra hnot
  have hmem := R.node_mem_reachable rotation mapData hbound decomposition
    Finset.univ (noPorts (3 * w) G.edgeSet) (Or.inl rfl)
  have hlive := haudit _ hmem
  rw [R.stateOf_profile,
    (interfaceProfile_univ_eq_empty_iff rotation.toRotationSystem _).2 hnot] at hlive
  simp at hlive

/-- The same audit in replayable finite form. -/
theorem taitBaseVerifiedOnDecomposable_of_filter_eq_empty
    (R : DecomposableInterfaceReflection.{u, v} k w State)
    (haudit : R.reachable.filter R.toRouteNativeInterfaceInstrument.Necessary = ∅) :
    TaitBaseVerifiedOnDecomposable.{u} k w := by
  refine R.taitBaseVerifiedOnDecomposable_of_audit fun s hs => ?_
  rw [Finset.nonempty_iff_ne_empty]
  intro hdead
  have hmem : s ∈ R.reachable.filter R.toRouteNativeInterfaceInstrument.Necessary :=
    Finset.mem_filter.2 ⟨hs, hdead⟩
  rw [haudit] at hmem
  simp at hmem

/-- The audit as one decidable Boolean: a terminating computation over a
`Finset`, not a quantifier over an unknown class of maps. -/
theorem taitBaseVerifiedOnDecomposable_of_decide
    (R : DecomposableInterfaceReflection.{u, v} k w State)
    (haudit : decide (∀ s ∈ R.reachable, R.profileOf s ≠ ∅) = true) :
    TaitBaseVerifiedOnDecomposable.{u} k w :=
  R.taitBaseVerifiedOnDecomposable_of_audit fun s hs =>
    Finset.nonempty_iff_ne_empty.2 (of_decide_eq_true haudit s hs)

/-- **Combinatorial Four-Colour headline from the strengthened reflection.**
The open inputs are the raw bounded-width decomposition and the reflection's
own coverage field, plus one finite check. -/
theorem combinatorialFourColorStatement_of_raw_and_audit
    (raw : RawBranchDecompositionSupply.{u} w)
    (R : DecomposableInterfaceReflection.{u, v} w w State)
    (haudit : ∀ s ∈ R.reachable, (R.profileOf s).Nonempty) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  combinatorialFourColorStatement_of_raw_and_decomposableBase w raw
    (R.taitBaseVerifiedOnDecomposable_of_audit haudit)

/-- **Nothing is lost.**  Every strengthened reflection is in particular an old
`DecomposableBaseReflection`. -/
noncomputable def toDecomposableBaseReflection [DecidableEq State]
    (R : DecomposableInterfaceReflection.{u, v} k w State) :
    DecomposableBaseReflection.{u, v} k w State where
  Necessary := R.toRouteNativeInterfaceInstrument.Necessary
  reachable := R.reachable
  trace {V} _ _ {G} _ rotation _ _ _ :=
    R.stateOf rotation.toRotationSystem Finset.univ (noPorts (3 * w) G.edgeSet)
  trace_mem_reachable := by
    intro V _ _ G _ rotation mapData hbound decomposition
    exact R.node_mem_reachable rotation mapData hbound decomposition _ _ (Or.inl rfl)
  necessary_of_not_colorable := by
    intro V _ _ G _ rotation mapData hbound decomposition hnot
    show R.profileOf _ = ∅
    rw [R.stateOf_profile]
    exact (interfaceProfile_univ_eq_empty_iff _ _).2 hnot

end DecomposableInterfaceReflection

/-- The design is inhabitable at the decomposable joint too. -/
def universalDecomposableReflection (k w : Nat) :
    DecomposableInterfaceReflection.{u, 0} k w (Finset (Fin (3 * w) → Color)) where
  toRouteNativeInterfaceInstrument := universalInstrument (3 * w)
  node_mem_reachable := by
    intro V _ _ G _ rotation _ _ decomposition piece iface _
    exact Finset.mem_univ _

/-! ## The defect and the fix, side by side

Everything in this section is machine-checked, so the comparison is not a
claim in prose.

*Old interfaces.*  `degenerate…` inhabits each of them at `State := Unit`,
`Necessary := fun _ => False`, `reachable := {()}` — from a proof of the base
obligation and nothing else.  `…_of_degenerate` is the converse: at that
instantiation an inhabitant *hands back* the base obligation with no audit
used at all, and `degenerate_audit_vacuous` shows the audit hypothesis is
vacuously true there.  So the old structure plus its audit is exactly as hard
as the thing it was supposed to reduce.

*New interfaces.*  `…isEmpty_unit` says that instantiation does not exist. -/

/-- The old spherical interface is inhabited at the degenerate carrier. -/
def degenerateTaitBaseReflection (bound : Nat)
    (base : TaitBaseVerifiedAt.{u} bound) :
    TaitBaseReflection.{u, 0} bound Unit where
  Necessary := fun _ => False
  reachable := {()}
  trace {V} _ _ {G} _ _ _ _ := ()
  trace_mem_reachable := by
    intro V _ _ G _ rotation mapData hbound
    exact Finset.mem_singleton_self _
  necessary_of_not_colorable := by
    intro V _ _ G _ rotation mapData hbound hnot
    exact hnot (base rotation mapData hbound)

/-- …and its audit hypothesis is vacuous there, so the audit does no work. -/
theorem degenerateTaitBaseReflection_audit_vacuous (bound : Nat)
    (base : TaitBaseVerifiedAt.{u} bound) :
    ∀ state ∈ (degenerateTaitBaseReflection bound base).reachable,
      ¬ (degenerateTaitBaseReflection bound base).Necessary state :=
  fun _ _ h => h

/-- **The defect, exactly.**  At the degenerate carrier, inhabiting the old
interface already yields the base obligation — `reachable` is never consulted
and no finite check occurs. -/
theorem taitBaseVerifiedAt_of_degenerate (bound : Nat)
    (R : TaitBaseReflection.{u, 0} bound Unit)
    (hN : R.Necessary = fun _ => False) : TaitBaseVerifiedAt.{u} bound := by
  intro V _ _ G _ rotation mapData hbound
  by_contra hnot
  have hbad := R.necessary_of_not_colorable rotation mapData hbound hnot
  rw [hN] at hbad
  exact hbad

/-- The old decomposable interface has the same defect. -/
def degenerateDecomposableBaseReflection (k w : Nat)
    (base : TaitBaseVerifiedOnDecomposable.{u} k w) :
    DecomposableBaseReflection.{u, 0} k w Unit where
  Necessary := fun _ => False
  reachable := {()}
  trace {V} _ _ {G} _ _ _ _ _ := ()
  trace_mem_reachable := by
    intro V _ _ G _ rotation mapData hbound decomposition
    exact Finset.mem_singleton_self _
  necessary_of_not_colorable := by
    intro V _ _ G _ rotation mapData hbound decomposition hnot
    exact hnot (base rotation mapData hbound decomposition)

theorem taitBaseVerifiedOnDecomposable_of_degenerate (k w : Nat)
    (R : DecomposableBaseReflection.{u, 0} k w Unit)
    (hN : R.Necessary = fun _ => False) :
    TaitBaseVerifiedOnDecomposable.{u} k w := by
  intro V _ _ G _ rotation mapData hbound decomposition
  by_contra hnot
  have hbad := R.necessary_of_not_colorable rotation mapData hbound decomposition hnot
  rw [hN] at hbad
  exact hbad

/-- **The fix, machine-visible.**  The strengthened spherical interface has no
inhabitant at the degenerate carrier. -/
theorem SphericalInterfaceReflection.isEmpty_unit (bound b : Nat) :
    IsEmpty (SphericalInterfaceReflection.{u, 0} bound b Unit) :=
  ⟨fun R => R.toRouteNativeInterfaceInstrument.not_subsingleton inferInstance⟩

/-- **The fix, machine-visible.**  Likewise at the decomposable joint. -/
theorem DecomposableInterfaceReflection.isEmpty_unit (k w : Nat) :
    IsEmpty (DecomposableInterfaceReflection.{u, 0} k w Unit) :=
  ⟨fun R => R.toRouteNativeInterfaceInstrument.not_subsingleton inferInstance⟩


end GoertzelV24RouteNativeInterfaceReflection

end Mettapedia.GraphTheory.FourColor
