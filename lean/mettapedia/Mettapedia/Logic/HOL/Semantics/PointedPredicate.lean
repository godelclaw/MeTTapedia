import Mettapedia.Logic.HOL.PointedPredicate
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Full-domain interpretation of pointed predicate carriers

The functional syntax denotes a genuine pointed refinement: its carrier is
equivalent to an optional predicate witness. Presence recovers exactly the
original refinement. Guarded quantifiers transport in both directions;
erasing the guard changes existential truth for an empty predicate.

The source-denotation comparison assumes full Henkin domains explicitly.
The inverse of the semantic equivalence uses choice and is not a runtime
encoder or decoder. Native type admission is a separate checked operation.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.PointedPredicate.Semantics
universe u v w

abbrev Raw (A : Type u) := (A → ULift.{u} Prop) → ULift.{u} Prop

variable {A : Type u}

def absent (A : Type u) : Raw A := fun _ => .up False

def encode (value : A) : Raw A := fun property => property value

def Present (property : A → Prop) (value : Raw A) : Prop :=
  ∃ point, property point ∧ value = encode point

def Admitted (property : A → Prop) (value : Raw A) : Prop :=
  value = absent A ∨ Present property value

theorem encode_ne_absent (value : A) : encode value ≠ absent A := by
  intro same
  have tested := congrArg (fun function => (function (fun _ => .up True)).down) same
  exact tested.mp trivial

theorem encode_injective : Function.Injective (encode (A := A)) := by
  intro first second same
  have tested := congrArg (fun function => (function (fun point => .up (point = first))).down) same
  exact (tested.mp rfl).symm

theorem absent_not_present (property : A → Prop) : ¬ Present property (absent A) := by
  rintro ⟨point, _, same⟩
  exact encode_ne_absent point same.symm

def embed (property : A → Prop) : Option {point // property point} → {value // Admitted property value}
  | .none => ⟨absent A, .inl rfl⟩
  | .some point => ⟨encode point.val, .inr ⟨point.val, point.property, rfl⟩⟩

theorem embed_injective (property : A → Prop) : Function.Injective (embed property) := by
  intro first second same
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some point => exact False.elim (encode_ne_absent point.val (congrArg Subtype.val same).symm)
  | some first =>
    cases second with
    | none => exact False.elim (encode_ne_absent first.val (congrArg Subtype.val same))
    | some second =>
      have equal : first = second := Subtype.ext (encode_injective (congrArg Subtype.val same))
      exact congrArg Option.some equal

theorem embed_surjective (property : A → Prop) : Function.Surjective (embed property) := by
  rintro ⟨value, admitted⟩
  rcases admitted with absent | ⟨point, inside, same⟩
  · exact ⟨.none, Subtype.ext absent.symm⟩
  · exact ⟨.some ⟨point, inside⟩, Subtype.ext same.symm⟩

/-- The inverse is a semantic choice, not an executable datatype decoder. -/
noncomputable def equivalence (property : A → Prop) :
    Option {point // property point} ≃ {value // Admitted property value} :=
  Equiv.ofBijective (embed property) ⟨embed_injective property, embed_surjective property⟩

theorem present_embed (property : A → Prop) (value : Option {point // property point}) :
    Present property (embed property value).val ↔ value.isSome := by
  cases value with
  | none => simp only [embed, Option.isSome_none, Bool.false_eq_true, iff_false]; exact absent_not_present property
  | some point => simp only [Option.isSome_some, iff_true]; exact ⟨point.val, point.property, rfl⟩

theorem present_exists_iff (property : A → Prop) :
    (∃ value : {value // Admitted property value}, Present property value.val) ↔ ∃ point, property point := by
  constructor
  · rintro ⟨_, point, inside, _⟩; exact ⟨point, inside⟩
  · rintro ⟨point, inside⟩; exact ⟨embed property (.some ⟨point, inside⟩), point, inside, rfl⟩

theorem false_has_no_present : ¬ ∃ value : {value : Raw A // Admitted (fun _ => False) value},
    Present (fun _ => False) value.val := by
  rw [present_exists_iff]
  simp

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {α : Ty Base}
variable (M : HenkinModel.{u, v, w} Base Const)

theorem denote_none (valuation : M.Valuation Γ) :
    M.denote (none (Const := Const) α) valuation = absent (Ty.denote M.Carrier α) := rfl

theorem denote_some (value : Term Const Γ α) (valuation : M.Valuation Γ) :
    M.denote (some value) valuation = encode (M.denote value valuation) := by
  funext property
  change property (M.denote (weaken value) (M.extend valuation property)) = _
  rw [Soundness.denote_weaken M value valuation property]
  rfl

theorem eqv_iff_equal (full : M.FullDomains) {τ : Ty Base}
    (first second : Ty.denote M.Carrier τ) : M.Eqv τ first second ↔ first = second := by
  constructor
  · exact M.eq_of_eqv_of_fullDomains full
  · rintro rfl; exact M.eqv_refl (full _ _)

theorem denote_present (full : M.FullDomains)
    (property : Term Const Γ (α ⇒ .prop)) (value : Term Const Γ (Carrier α))
    (valuation : M.Valuation Γ) :
    (M.denote (present property value) valuation).down ↔
      Present (fun point => (M.denote property valuation point).down) (M.denote value valuation) := by
  simp only [present, HenkinModel.denote, PreModel.denote, Soundness.denote_weaken]
  change (∃ point, M.adm α point ∧ (M.denote property valuation point).down ∧
    M.Eqv (Carrier α) (M.denote value valuation)
      (M.denote (some (.var .vz)) (M.extend valuation point))) ↔ _
  simp only [denote_some, HenkinModel.denote, PreModel.denote, PreModel.extend]
  constructor
  · rintro ⟨point, _, inside, same⟩; exact ⟨point, inside, (eqv_iff_equal M full _ _).mp same⟩
  · rintro ⟨point, inside, same⟩; exact ⟨point, full _ _, inside, (eqv_iff_equal M full _ _).mpr same⟩

theorem denote_admitted (full : M.FullDomains)
    (property : Term Const Γ (α ⇒ .prop)) (value : Term Const Γ (Carrier α))
    (valuation : M.Valuation Γ) :
    (M.denote (admitted property value) valuation).down ↔
      Admitted (fun point => (M.denote property valuation point).down) (M.denote value valuation) := by
  change (M.Eqv _ (M.denote value valuation) (M.denote (none α) valuation) ∨
    (M.denote (present property value) valuation).down) ↔ _
  rw [eqv_iff_equal M full, denote_none, denote_present M full]
  rfl


theorem denote_predicate (full : M.FullDomains)
    (property : Term Const Γ (α ⇒ .prop)) (valuation : M.Valuation Γ)
    (value : Ty.denote M.Carrier (Carrier α)) :
    (M.denote (predicate property) valuation value).down ↔
      Admitted (fun point => (M.denote property valuation point).down) value := by
  change (M.denote (admitted (weaken property) (.var .vz)) (M.extend valuation value)).down ↔ _
  rw [denote_admitted M full]
  simp only [Soundness.denote_weaken, HenkinModel.denote, PreModel.denote, PreModel.extend]

/-- The actual source predicate has the pointed refinement as its full-domain
interpretation. No executable inverse is supplied by this equivalence. -/
noncomputable def denotationEquivalence (full : M.FullDomains)
    (property : Term Const Γ (α ⇒ .prop)) (valuation : M.Valuation Γ) :
    Option {point : Ty.denote M.Carrier α // (M.denote property valuation point).down} ≃
      {value : Ty.denote M.Carrier (Carrier α) //
        (M.denote (predicate property) valuation value).down} :=
  (equivalence (fun point => (M.denote property valuation point).down)).trans
    { toFun := fun value => ⟨value.val, (denote_predicate M full property valuation value.val).mpr value.property⟩
      invFun := fun value => ⟨value.val, (denote_predicate M full property valuation value.val).mp value.property⟩
      left_inv := by intro value; rfl
      right_inv := by intro value; rfl }

variable {A : Type u}

theorem guarded_forall (property : A → Prop) (observation : Raw A → Prop) :
    (∀ value, Present property value → observation value) ↔
      ∀ point, property point → observation (encode point) := by
  constructor
  · intro observed point inside; exact observed (encode point) ⟨point, inside, rfl⟩
  · rintro observed value ⟨point, inside, same⟩
    exact same ▸ observed point inside

theorem guarded_exists (property : A → Prop) (observation : Raw A → Prop) :
    (∃ value, Present property value ∧ observation value) ↔
      ∃ point, property point ∧ observation (encode point) := by
  constructor
  · rintro ⟨value, ⟨point, inside, same⟩, observed⟩
    exact ⟨point, inside, same ▸ observed⟩
  · rintro ⟨point, inside, observed⟩
    exact ⟨encode point, ⟨point, inside, rfl⟩, observed⟩

theorem erased_guard_false :
    (∃ _value : {value : Raw A // Admitted (fun _ => False) value}, True) ∧
      ¬ (∃ value : {value : Raw A // Admitted (fun _ => False) value},
        Present (fun _ => False) value.val) :=
  ⟨⟨embed (fun _ => False) .none, trivial⟩, false_has_no_present⟩

theorem two_distinct_present :
    Present (fun _ : Bool => True) (encode false) ∧
      Present (fun _ : Bool => True) (encode true) ∧ encode false ≠ encode true := by
  refine ⟨⟨false, trivial, rfl⟩, ⟨true, trivial, rfl⟩, ?_⟩
  intro same
  have impossible : false = true := encode_injective same
  cases impossible


namespace Controls
open HenkinModel.ModelPropertyCanary

def emptyValuation : (booleanBaseModel).Valuation [] := fun impossible => nomatch impossible

def emptyProperty : ClosedTerm (NoConstants Unit) ((Ty.base ()) ⇒ .prop) :=
  falseProperty (.base ())

noncomputable def emptyDenotationEquivalence :=
  denotationEquivalence booleanBaseModel booleanBaseModel_fullDomains
    emptyProperty emptyValuation

theorem empty_admitted_denotation :
    ((booleanBaseModel).denote (admitted emptyProperty (none (.base ()))) emptyValuation).down ↔
      Admitted (fun _ : LiftedBool => False) (absent LiftedBool) :=
  denote_admitted booleanBaseModel booleanBaseModel_fullDomains
    emptyProperty (none (.base ())) emptyValuation

end Controls

#print axioms denote_predicate
#print axioms denotationEquivalence
#print axioms guarded_forall
#print axioms guarded_exists
#print axioms erased_guard_false
#print axioms two_distinct_present

#print axioms encode_ne_absent
#print axioms encode_injective
#print axioms equivalence
#print axioms false_has_no_present
#print axioms denote_some
#print axioms denote_present
#print axioms denote_admitted
end Mettapedia.Logic.HOL.PointedPredicate.Semantics
