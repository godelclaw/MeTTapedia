import Mettapedia.TypeTheory.RecursiveSpace

/-!
# Injective payload maps of recursive spaces

A payload map preserves bottom, constructor tags and every natural-indexed
child. An injective map embeds complete trees; its image is exactly the trees
whose payloads lie in the map's image. This supplies guarded carriers when a
data representation has extra target values. The inverse is semantic.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RecursiveSpace

open IndexedPolynomial
universe u v
variable {A : Type u} {B : Type v}

noncomputable def mapPayload (mapping : A → B) (tree : Tree A) : Tree B :=
  Fix.eliminate (polynomial A) (fun _ _ _ => Tree B)
    (fun _ _ shape _children mapped => match shape with
      | none => bottom
      | some point => construct point.1 (mapping point.2) mapped)
    PUnit.unit PUnit.unit tree

@[simp] theorem mapPayload_bottom (mapping : A → B) : mapPayload mapping bottom = bottom := rfl

@[simp] theorem mapPayload_construct (mapping : A → B) (tag : Nat) (payload : A)
    (children : Nat → Tree A) :
    mapPayload mapping (construct tag payload children) =
      construct tag (mapping payload) (fun n => mapPayload mapping (children n)) := rfl

theorem mapPayload_injective (mapping : A → B) (injective : Function.Injective mapping) :
    Function.Injective (mapPayload mapping) := by
  intro first
  apply induction (fun first => ∀ second, mapPayload mapping first = mapPayload mapping second → first = second)
    ?_ ?_ first
  · intro second
    apply induction (fun second => mapPayload mapping bottom = mapPayload mapping second → bottom = second)
      (fun _ => rfl) ?_ second
    intro tag payload children _ same
    exact False.elim (construct_ne_bottom _ _ _ same.symm)
  · intro tag payload children hypotheses second
    apply induction
      (fun second => mapPayload mapping (construct tag payload children) = mapPayload mapping second →
        construct tag payload children = second) ?_ ?_ second
    · intro same
      exact False.elim (construct_ne_bottom _ _ _ same)
    · intro otherTag otherPayload otherChildren _ same
      change construct tag (mapping payload) (fun n => mapPayload mapping (children n)) =
        construct otherTag (mapping otherPayload) (fun n => mapPayload mapping (otherChildren n)) at same
      obtain ⟨tags, payloads, branches⟩ := (construct_injective _ _ _ _ _ _).mp same
      have payloads := injective payloads
      subst otherTag
      subst otherPayload
      apply congrArg (construct tag payload)
      funext n
      exact hypotheses n (otherChildren n) (congrFun branches n)

noncomputable def AllPayload (predicate : B → Prop) (tree : Tree B) : Prop :=
  Fix.eliminate (polynomial B) (fun _ _ _ => Prop)
    (fun _ _ shape _children valid => match shape with
      | none => True
      | some point => predicate point.2 ∧ ∀ n, valid n)
    PUnit.unit PUnit.unit tree

theorem mapPayload_all (mapping : A → B) (tree : Tree A) :
    AllPayload (fun payload => ∃ original, mapping original = payload) (mapPayload mapping tree) := by
  apply induction
    (fun tree => AllPayload (fun payload => ∃ original, mapping original = payload) (mapPayload mapping tree))
    True.intro ?_ tree
  intro tag payload children hypotheses
  exact ⟨⟨payload, rfl⟩, hypotheses⟩

theorem allPayload_iff_exists_map (mapping : A → B) (tree : Tree B) :
    AllPayload (fun payload => ∃ original, mapping original = payload) tree ↔
      ∃ original, mapPayload mapping original = tree := by
  constructor
  · apply induction
      (fun tree => AllPayload (fun payload => ∃ original, mapping original = payload) tree →
        ∃ original, mapPayload mapping original = tree)
      (fun _ => ⟨bottom, rfl⟩) ?_ tree
    intro tag payload children hypotheses valid
    obtain ⟨original, same⟩ := valid.1
    let originals := fun n => Classical.choose (hypotheses n (valid.2 n))
    refine ⟨construct tag original originals, ?_⟩
    rw [mapPayload_construct, same]
    apply congrArg (construct tag payload)
    funext n
    exact Classical.choose_spec (hypotheses n (valid.2 n))
  · rintro ⟨original, rfl⟩
    exact mapPayload_all mapping original

noncomputable def payloadEmbedding (mapping : A → B) (injective : Function.Injective mapping) :
    Tree A ≃ {tree : Tree B // AllPayload (fun payload => ∃ original, mapping original = payload) tree} :=
  Equiv.ofBijective (fun tree => ⟨mapPayload mapping tree, mapPayload_all mapping tree⟩)
    ⟨fun _ _ same => mapPayload_injective mapping injective (congrArg Subtype.val same), by
      intro tree
      obtain ⟨original, same⟩ := (allPayload_iff_exists_map mapping tree.val).mp tree.property
      exact ⟨original, Subtype.ext same⟩⟩

namespace PayloadControls

def first : Tree Bool := construct 2 true (fun _ => bottom)
def second : Tree Bool := construct 2 false (fun _ => bottom)

theorem distinct_sources : first ≠ second := by
  intro same
  have impossible := ((construct_injective _ _ _ _ _ _).mp same).2.1
  cases impossible

theorem collapse_loses_payload : mapPayload (fun _ : Bool => ()) first =
    mapPayload (fun _ : Bool => ()) second := rfl

theorem boolean_roundtrip : mapPayload Bool.not (mapPayload Bool.not first) = first :=
  mapPayload_injective Bool.not
    (by intro left right same; cases left <;> cases right <;> cases same <;> rfl)
    (by rfl)

theorem foreign_payload_refused :
    ¬ AllPayload (fun payload => ∃ _original : Unit, false = payload)
      (construct 2 true (fun _ => bottom)) := by
  intro valid
  obtain ⟨_, impossible⟩ := valid.1
  cases impossible

end PayloadControls

#print axioms mapPayload_injective
#print axioms allPayload_iff_exists_map
#print axioms payloadEmbedding
#print axioms PayloadControls.collapse_loses_payload

end Mettapedia.TypeTheory.RecursiveSpace
