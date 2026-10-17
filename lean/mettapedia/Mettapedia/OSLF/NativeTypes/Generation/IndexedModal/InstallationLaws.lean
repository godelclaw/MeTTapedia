import Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline

/-! # Source preservation of successful operational installation -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal

theorem installed_generated {authored : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    {generated : Generated} {logic : NativeLogic.Fragment} {installed : BindingPipeline.Installed}
    (checked : BindingPipeline.installGenerated authored generated logic = .ok installed) :
    installed.generated = generated := by
  unfold BindingPipeline.installGenerated at checked
  repeat' first
    | split at checked
    | dsimp only [Except.bind, Except.pure] at checked
    | cases checked
  all_goals rfl

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal
