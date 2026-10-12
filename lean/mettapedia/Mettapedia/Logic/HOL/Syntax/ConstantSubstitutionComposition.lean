import Mettapedia.Logic.HOL.Syntax.ConstMap
import Mettapedia.Logic.HOL.Syntax.TypeSubstitution

/-!
# Composition of closed constant interpretations

These laws concern actual typed terms, including terms under binders. Closed
images may be compound terms. Composing interpretations expands those images,
rather than choosing a replacement constant or changing variable ownership.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}
  {Const' : Ty Base → Type w} {Const'' : Ty Base → Type x}

@[simp] theorem substConst_weakenCtx
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (context : Ctx Base) {type : Ty Base} (term : ClosedTerm Const type) :
    substConst images (weakenCtx context term) =
      weakenCtx context (substConst images term) := by
  induction context with
  | nil => rfl
  | cons head tail ih => rw [weakenCtx_cons, substConst_weaken, ih]; rfl

@[simp] theorem mapConst_weakenCtx
    (images : ∀ {type}, Const type → Const' type)
    (context : Ctx Base) {type : Ty Base} (term : ClosedTerm Const type) :
    mapConst images (weakenCtx context term) =
      weakenCtx context (mapConst images term) := by
  induction context with
  | nil => rfl
  | cons head tail ih => rw [weakenCtx_cons, mapConst_weaken, ih]; rfl

@[simp] theorem substConst_id {context : Ctx Base} {type : Ty Base}
    (term : Term Const context type) :
    substConst (fun constant => .const constant) term = term := by
  induction term <;> simp_all [substConst]

theorem substConst_comp
    (first : ∀ {type}, Const type → ClosedTerm Const' type)
    (second : ∀ {type}, Const' type → ClosedTerm Const'' type)
    {context : Ctx Base} {type : Ty Base} (term : Term Const context type) :
    substConst second (substConst first term) =
      substConst (fun constant => substConst second (first constant)) term := by
  induction term <;> simp_all [substConst]

theorem substConst_mapConst
    (constants : ∀ {type}, Const type → Const' type)
    (images : ∀ {type}, Const' type → ClosedTerm Const'' type)
    {context : Ctx Base} {type : Ty Base} (term : Term Const context type) :
    substConst images (mapConst constants term) =
      substConst (fun constant => images (constants constant)) term := by
  induction term <;> simp_all [mapConst, substConst]

theorem mapConst_substConst
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (constants : ∀ {type}, Const' type → Const'' type)
    {context : Ctx Base} {type : Ty Base} (term : Term Const context type) :
    mapConst constants (substConst images term) =
      substConst (fun constant => mapConst constants (images constant)) term := by
  induction term <;> simp_all [mapConst, substConst]

theorem substConst_ext
    {first second : ∀ {type}, Const type → ClosedTerm Const' type}
    (equal : ∀ {type} (constant : Const type), first constant = second constant)
    {context : Ctx Base} {type : Ty Base} (term : Term Const context type) :
    substConst first term = substConst second term := by
  induction term <;> simp_all [substConst]

theorem substConst_constant_images
    (constants : ∀ {type}, Const type → Const' type)
    {context : Ctx Base} {type : Ty Base} (term : Term Const context type) :
    substConst (fun constant => .const (constants constant)) term = mapConst constants term := by
  induction term <;> simp_all only [substConst, mapConst, weakenCtx_const]

section TypeInstantiation

universe u' v' w'

variable {Base' : Type u'} {InstConst : Ty Base' → Type v'}
  {InstExpanded : Ty Base' → Type w'}

/-- Retyping a closed replacement and weakening it commute, including when
a base type is replaced by a compound function type. -/
@[simp] theorem mapTypes_weakenCtx
    (substitution : Base → Ty Base')
    (symbols : ∀ {type}, Const type → InstConst (Ty.substitute substitution type))
    (context : Ctx Base) {type : Ty Base} (term : ClosedTerm Const type) :
    mapTypes substitution symbols (weakenCtx context term) =
      weakenCtx (context.map (Ty.substitute substitution))
        (mapTypes substitution symbols term) := by
  induction context with
  | nil => rfl
  | cons head tail ih =>
      simp only [weakenCtx_cons, mapTypes_weaken, ih]
      rfl

/-- Type instantiation commutes with closed-term constant interpretation
when the actual symbol images commute. Neither the type map nor the symbol
maps need to be injective. -/
theorem mapTypes_substConst
    (substitution : Base → Ty Base')
    (sourceSymbols : ∀ {type}, Const type → InstConst (Ty.substitute substitution type))
    (targetSymbols : ∀ {type}, Const' type → InstExpanded (Ty.substitute substitution type))
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (instantiatedImages : ∀ {type}, InstConst type → ClosedTerm InstExpanded type)
    (commutes : ∀ {type} (constant : Const type),
      instantiatedImages (sourceSymbols constant) =
        mapTypes substitution targetSymbols (images constant))
    {context : Ctx Base} {type : Ty Base} (term : Term Const context type) :
    mapTypes substitution targetSymbols (substConst images term) =
      substConst instantiatedImages (mapTypes substitution sourceSymbols term) := by
  induction term with
  | const constant =>
      simp only [mapTypes, substConst, mapTypes_weakenCtx]
      rw [commutes]
  | _ =>
      simp_all only [mapTypes, substConst] <;> rfl

end TypeInstantiation

end Mettapedia.Logic.HOL
