import Mettapedia.Ethics.Theory

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u v w

abbrev TranslationRel (S1 : Type u) (S2 : Type v) : Type (max u v) :=
  S1 -> S2 -> Prop

def Translates {S1 : Type u} {S2 : Type v}
    (R : TranslationRel S1 S2) (s : S1) : Prop :=
  Exists (fun t : S2 => R s t)

abbrev Witnessed {S1 : Type u} {S2 : Type v}
    (R : TranslationRel S1 S2) (s : S1) :=
  PSigma (fun t : S2 => R s t)

theorem witnessed_to_translates {S1 : Type u} {S2 : Type v}
    {R : TranslationRel S1 S2} {s : S1} :
    Witnessed R s -> Translates R s := by
  intro h
  exact ⟨h.fst, h.snd⟩

def TranslationComp {S1 : Type u} {S2 : Type v} {S3 : Type w}
    (R1 : TranslationRel S1 S2) (R2 : TranslationRel S2 S3) :
    TranslationRel S1 S3 :=
  fun s t => Exists (fun m => R1 s m ∧ R2 m t)

theorem translation_comp_translates {S1 : Type u} {S2 : Type v} {S3 : Type w}
    {R1 : TranslationRel S1 S2} {R2 : TranslationRel S2 S3}
    {s : S1} (h1 : Translates R1 s)
    (h2 : forall m, R1 s m -> Translates R2 m) :
    Translates (TranslationComp R1 R2) s := by
  obtain ⟨m, hm⟩ := h1
  obtain ⟨t, ht⟩ := h2 m hm
  exact ⟨t, m, hm, ht⟩

def TranslationId {S : Type u} : TranslationRel S S :=
  fun s t => s = t

theorem translation_id_translates {S : Type u} (s : S) :
    Translates (TranslationId (S := S)) s :=
  ⟨s, rfl⟩

theorem translation_comp_id_left {S1 : Type u} {S2 : Type v}
    (R : TranslationRel S1 S2) (s : S1) (t : S2) :
    TranslationComp (TranslationId (S := S1)) R s t <-> R s t := by
  simp [TranslationComp, TranslationId]

theorem translation_comp_id_right {S1 : Type u} {S2 : Type v}
    (R : TranslationRel S1 S2) (s : S1) (t : S2) :
    TranslationComp R (TranslationId (S := S2)) s t <-> R s t := by
  simp [TranslationComp, TranslationId]

def translation_comp_witnessed {S1 : Type u} {S2 : Type v} {S3 : Type w}
    {R1 : TranslationRel S1 S2} {R2 : TranslationRel S2 S3} {s : S1}
    (h1 : Witnessed R1 s) (h2 : Witnessed R2 h1.fst) :
    Witnessed (TranslationComp R1 R2) s :=
  ⟨h2.fst, h1.fst, h1.snd, h2.snd⟩

end Mettapedia.Ethics