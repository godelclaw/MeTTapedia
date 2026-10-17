import Mettapedia.GSLT.LanguageDef.ModuleFormat.DependencyAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable

/-!
# Structured module-format integration with coGSLT layers

The public `module/1` envelope is connected to compositional declaration
elaboration, compatible catalog assembly, ordered qualified exports and
snapshot-dependent dependency admission. Export specifications remain whole
and opaque. Canonical portable text uses the verified MeTTa reader and a
complete five-field presentation codec, with explicitly serializable dependent
layers. It is distinct from the historical BNFC and upstream Rust `.module`
grammars. No cryptographic verification or runtime refinement is asserted.
-/
