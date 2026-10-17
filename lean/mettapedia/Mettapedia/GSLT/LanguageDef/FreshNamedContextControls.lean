import Mettapedia.GSLT.LanguageDef.FreshNamedContext

namespace Mettapedia.GSLT.LanguageDef.NamedFreeContext.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

theorem fresh_names_admitted : admitNames
    [("cesta_local_0", .base "Expr"), ("cesta_local_1", .base "Expr")]
    ["value", "result"] = true := by decide +kernel

theorem free_name_collision_refused : admitNames
    [("value", .base "Expr"), ("cesta_local_1", .base "Expr")]
    ["value", "result"] = false := by decide +kernel

theorem duplicate_name_across_sorts_refused : admitNames
    [("same", .base "Expr"), ("same", .base "Statement")] [] = false := by decide +kernel

theorem two_binders_preserve_old_reference : lookupPosition?
    [("cesta_local_0", .base "Expr"), ("cesta_local_1", .base "Expr"), ("value", .base "Expr")]
    "value" (.base "Expr") = some (Var.succ (Var.succ Var.zero)) := by
  simp [lookupPosition?]; rfl

theorem generated_reference_resolves_to_its_binder : lookupPosition?
    [("cesta_local_0", .base "Expr"), ("cesta_local_1", .base "Expr"), ("value", .base "Expr")]
    "cesta_local_1" (.base "Expr") = some (Var.succ Var.zero) := by
  simp [lookupPosition?]; rfl

theorem unfresh_frame_captures_reference : lookupPosition?
    [("value", .base "Expr"), ("value", .base "Expr")]
    "value" (.base "Expr") = some Var.zero := by
  simp [lookupPosition?]; rfl

end Mettapedia.GSLT.LanguageDef.NamedFreeContext.Controls
