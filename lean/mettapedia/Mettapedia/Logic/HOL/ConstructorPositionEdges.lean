import Mettapedia.Logic.HOL.ConstructorPositionPrograms

/-!
# Root-index checks for data-dependent positions

The position relation supplies the child index consumed by the shared root
predicate. Constructor data and payload agreement are retained. The curried
programs preserve the original parameter context and expose activity, child
index and edge checks without imposing a constant recursive arity.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding CurriedPredicates ConstructorPrograms
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
variable {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)
variable {space : Ty Base}
  (construct : Term Const Γ (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))

def edgeGuard (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) : Formula Const Γ :=
  let rho : Subst Const Γ (constructors.index :: Γ) := fun index => .var (.vs index)
  .ex (.and ((positions.subst rho).childGuard (HOL.subst rho payload) (HOL.subst rho slot) (.var .vz))
    ((constructors.subst rho).rootIndex (HOL.subst rho construct) (HOL.subst rho child) (.var .vz)))

variable (model : HenkinModel.{u,v,w} Base Const)

def edgeMeaning (values : model.Valuation Γ)
    (payload : Ty.denote model.Carrier (payloadType constructors.fields))
    (slot : Ty.denote model.Carrier constructors.number) (child : Ty.denote model.Carrier space) : Prop :=
  ∃ data : constructors.Data model, constructors.dataAllowed model values data ∧
    payloadEquivalence model constructors.fields payload =
      TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) constructors.fields data ∧
    ∃ index, positions.related model values data slot index ∧
      constructors.rootMeaning construct model values child index

variable (full : model.FullDomains)
include full

theorem edgeGuard_denote (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (values : model.Valuation Γ) :
    (model.denote (positions.edgeGuard construct payload slot child) values).down ↔
      positions.edgeMeaning construct model values (model.denote payload values)
        (model.denote slot values) (model.denote child values) := by
  let rho : Subst Const Γ (constructors.index :: Γ) := fun index => .var (.vs index)
  have localMeaning (index : Ty.denote model.Carrier constructors.index) :
      (model.denote ((positions.subst rho).childGuard (HOL.subst rho payload) (HOL.subst rho slot) (.var .vz))
        (model.extend values index)).down ∧
      (model.denote ((constructors.subst rho).rootIndex (HOL.subst rho construct) (HOL.subst rho child) (.var .vz))
        (model.extend values index)).down ↔
      (∃ data : constructors.Data model, (constructors.dataAllowed model values data ∧
        positions.related model values data (model.denote slot values) index) ∧
        constructors.payloadMatches model values payload data) ∧
      constructors.rootMeaning construct model values (model.denote child values) index := by
    rw [(positions.subst rho).childGuard_denote model full,
      (constructors.subst rho).rootIndex_denote _ model full]
    simp only [rho, rootMeaning, resultValue, packedData, dataAllowed, payloadMatches, related,
      PositionPrograms.subst, ConstructorPrograms.subst, holds, Soundness.denote_subst,
      HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
    rfl
  change (∃ index, model.adm _ index ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨index, _, parent, child⟩
    obtain ⟨⟨data, ⟨allowed, relation⟩, agrees⟩, root⟩ := (localMeaning index).mp ⟨parent, child⟩
    exact ⟨data, allowed, agrees, index, relation, root⟩
  · rintro ⟨data, allowed, agrees, index, relation, root⟩
    exact ⟨index, full _ _, (localMeaning index).mpr ⟨⟨data, ⟨allowed, relation⟩, agrees⟩, root⟩⟩

theorem edge_implies_active (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) (values : model.Valuation Γ)
    (valid : (model.denote (positions.edgeGuard construct payload slot child) values).down) :
    (model.denote (positions.activeGuard payload slot) values).down := by
  obtain ⟨data, allowed, agrees, index, relation, _⟩ :=
    (positions.edgeGuard_denote construct model full payload slot child values).mp valid
  exact (positions.activeGuard_denote model full payload slot values).mpr
    ⟨data, ⟨allowed, index, relation⟩, agrees⟩

omit full in
def activeProgram : Term Const Γ (payloadType constructors.fields ⇒ constructors.number ⇒ .prop) :=
  .lam (.lam ((positions.subst beneathTwo).activeGuard (.var (.vs .vz)) (.var .vz)))

omit full in
def childProgram : Term Const Γ
    (payloadType constructors.fields ⇒ constructors.number ⇒ constructors.index ⇒ .prop) :=
  .lam (.lam (.lam ((positions.subst beneathThree).childGuard
    (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

omit full in
def edgeProgram : Term Const Γ
    (payloadType constructors.fields ⇒ constructors.number ⇒ space ⇒ .prop) :=
  .lam (.lam (.lam ((positions.subst beneathThree).edgeGuard
    (HOL.subst beneathThree construct) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

theorem activeProgram_denote (values : model.Valuation Γ)
    (payload : Ty.denote model.Carrier (payloadType constructors.fields))
    (slot : Ty.denote model.Carrier constructors.number) :
    (model.denote positions.activeProgram values payload slot).down ↔
      ∃ data : constructors.Data model, (constructors.dataAllowed model values data ∧
        ∃ index, positions.related model values data slot index) ∧
        payloadEquivalence model constructors.fields payload =
          TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) constructors.fields data := by
  change (model.denote ((positions.subst beneathTwo).activeGuard (.var (.vs .vz)) (.var .vz))
    (model.extend (model.extend values payload) slot)).down ↔ _
  rw [(positions.subst beneathTwo).activeGuard_denote model full]
  simp only [dataAllowed, payloadMatches, related, PositionPrograms.subst, ConstructorPrograms.subst,
    holds, Soundness.denote_subst, HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
  rfl

theorem childProgram_denote (values : model.Valuation Γ)
    (payload : Ty.denote model.Carrier (payloadType constructors.fields))
    (slot : Ty.denote model.Carrier constructors.number) (index : Ty.denote model.Carrier constructors.index) :
    (model.denote positions.childProgram values payload slot index).down ↔
      ∃ data : constructors.Data model, (constructors.dataAllowed model values data ∧
        positions.related model values data slot index) ∧
        payloadEquivalence model constructors.fields payload =
          TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) constructors.fields data := by
  change (model.denote ((positions.subst beneathThree).childGuard
    (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
      (model.extend (model.extend (model.extend values payload) slot) index)).down ↔ _
  rw [(positions.subst beneathThree).childGuard_denote model full]
  simp only [dataAllowed, payloadMatches, related, PositionPrograms.subst, ConstructorPrograms.subst,
    holds, Soundness.denote_subst, HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
  rfl

theorem edgeProgram_denote (values : model.Valuation Γ)
    (payload : Ty.denote model.Carrier (payloadType constructors.fields))
    (slot : Ty.denote model.Carrier constructors.number) (child : Ty.denote model.Carrier space) :
    (model.denote (positions.edgeProgram construct) values payload slot child).down ↔
      positions.edgeMeaning construct model values payload slot child := by
  change (model.denote ((positions.subst beneathThree).edgeGuard (HOL.subst beneathThree construct)
    (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
      (model.extend (model.extend (model.extend values payload) slot) child)).down ↔ _
  rw [(positions.subst beneathThree).edgeGuard_denote _ model full]
  simp only [edgeMeaning, rootMeaning, resultValue, packedData, dataAllowed, related,
    PositionPrograms.subst, ConstructorPrograms.subst, holds, Soundness.denote_subst,
    HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
  rfl

#print axioms edgeGuard_denote
#print axioms edge_implies_active
#print axioms activeProgram_denote
#print axioms childProgram_denote
#print axioms edgeProgram_denote
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
