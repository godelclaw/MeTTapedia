import Mettapedia.CategoryTheory.GroundPathFramePermission

/-!+# Permission readout of a complete extended path

The actual inductive permission witness decomposes into the entire preceding
path and its final frame. This generic readout avoids making dependent
elimination depend on a computed source or intermediate endpoint.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundPath.FramePermission

universe u v
variable {V : Type u} [Quiver.{v} V]

theorem permittedPath_cons_iff (permission : Permission V) {source middle target : V}
    (previous : Quiver.Path source middle) (frame : middle ⟶ target) :
    PermittedPath permission (previous.cons frame) ↔
      PermittedPath permission previous ∧ permission frame := by
  constructor
  · intro given
    cases given with
    | cons inner last => exact ⟨inner, last⟩
  · rintro ⟨inner, last⟩
    exact .cons inner last

end Mettapedia.CategoryTheory.GroundPath.FramePermission
