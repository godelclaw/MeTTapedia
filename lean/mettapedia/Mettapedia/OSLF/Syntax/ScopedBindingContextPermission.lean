import Mettapedia.OSLF.Syntax.ScopedBindingContextComparison
import Mettapedia.CategoryTheory.GroundPathFramePermissionRPO

/-!
# Actual positional permission for binder contexts

An authored permission chooses operator slots at their actual variable
contexts. It selects holes, rather than forbidding the stored sibling
terms. Complete path permissions construct a category whose inclusion
retains every binder prefix, variable position and sibling.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout

variable (S : Binding.Signature)

local instance : Quiver (Scope S) := bindingFrameQuiver S

abbrev SlotPermission := (context : Binding.Ctx S) → (sort : S.Srt) →
  (operator : S.Op sort) → Fin (S.arity operator).length → Prop

def framePermission (permission : SlotPermission S) :
    @FramePermission.Permission (Scope S) (bindingFrameQuiver S) :=
  fun frame => match frame with
  | .slot context sort operator position _ => permission context sort operator position

abbrev PermittedContextObject (permission : SlotPermission S) :=
  @FramePermission.Object (Scope S) (bindingFrameQuiver S) (framePermission S permission) (bindingAction S)

def permittedOrigin (permission : SlotPermission S) : PermittedContextObject S permission :=
  FramePermission.origin (framePermission S permission) (bindingAction S)

def permittedInterface (permission : SlotPermission S) (scope : Scope S) :
    PermittedContextObject S permission :=
  FramePermission.interface (framePermission S permission) (bindingAction S) scope

def permissionInclusion (permission : SlotPermission S) :
    PermittedContextObject S permission ⥤ BindingContextObject S :=
  FramePermission.inclusion (framePermission S permission) (bindingAction S)

instance permissionInclusion_faithful (permission : SlotPermission S) :
    (permissionInclusion S permission).Faithful :=
  FramePermission.inclusion_faithful (framePermission S permission) (bindingAction S)

variable {S}

def permittedTermArrow {permission : SlotPermission S} {scope : Scope S}
    (supplied : Binding.Term S scope.1 scope.2) :
    permittedOrigin S permission ⟶ permittedInterface S permission scope :=
  FramePermission.value (framePermission S permission) (bindingAction S) supplied

def permittedContextArrow {permission : SlotPermission S} {source target : Scope S}
    (path : BindingContext S source target)
    (allowed : FramePermission.PermittedPath (framePermission S permission) path) :
    permittedInterface S permission source ⟶ permittedInterface S permission target :=
  FramePermission.context (framePermission S permission) (bindingAction S) path allowed

theorem permitted_redex_relativePushouts {permission : SlotPermission S} {first second : Scope S}
    (agent : Binding.Term S first.1 first.2) (redex : Binding.Term S second.1 second.2) :
    HasRelativePushouts (permittedTermArrow (permission := permission) agent)
      (permittedTermArrow (permission := permission) redex) :=
  FramePermission.redex_relativePushouts (framePermission S permission) (bindingAction S) agent redex

theorem permitted_relativePushout_iff {permission : SlotPermission S} {first second : Scope S}
    {target : PermittedContextObject S permission}
    {agent : Binding.Term S first.1 first.2} {redex : Binding.Term S second.1 second.2}
    {left : permittedInterface S permission first ⟶ target}
    {right : permittedInterface S permission second ⟶ target}
    (candidate : Candidate (permittedTermArrow agent) (permittedTermArrow redex) left right) :
    IsRelativePushout candidate ↔ IsRelativePushout (mapCandidate (permissionInclusion S permission) candidate) :=
  FramePermission.relativePushout_iff (framePermission S permission) (bindingAction S) candidate

end Mettapedia.OSLF.Binding.ScopedEncoding
