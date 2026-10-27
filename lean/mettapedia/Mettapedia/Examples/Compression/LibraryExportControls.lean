import Mettapedia.Algorithms.Compression.ValueArguments
import Mettapedia.Algorithms.Compression.TemplateExport
import Mettapedia.Algorithms.Compression.LocalFrames

/-! Logical dependencies of the helper-port compiler and argument-sharing
laws. Source-reader, primitive-head admission, LC1 byte correspondence and
emitted-library execution are qualified separately through the native gate. -/

open Mettapedia.Algorithms.Compression

#print axioms ValueArguments.collect
#print axioms ValueArguments.collect_pure
#print axioms ValueArguments.strictApply
#print axioms ValueArguments.strictApply_ready
#print axioms ValueArguments.Controls.sharing_changes_choice_multiplicity
#print axioms ValueArguments.Controls.eager_unused_failure_loses_the_answer
#print axioms ValueArguments.Controls.eager_unused_effect_is_observable
#print axioms ValueArguments.Controls.ready_arguments_preserve_an_effectful_context
#print axioms TemplateExport.body
#print axioms TemplateExport.bodies
#print axioms TemplateExport.arguments
#print axioms TemplateExport.expand_body
#print axioms TemplateExport.parameters
#print axioms TemplateExport.expansion_preserved
#print axioms TemplateExport.matched_source_reconstructed
#print axioms TemplateExport.parameter_indices_distinct
#print axioms TemplateExport.code_and_value_ports_remain_distinct
#print axioms TemplateExport.omitting_a_parameter_loses_reconstruction

#print axioms LocalFrames.substitute
#print axioms LocalFrames.substitute_rename
#print axioms LocalFrames.compile
#print axioms LocalFrames.expand
#print axioms LocalFrames.interpret
#print axioms LocalFrames.image_port
#print axioms LocalFrames.image_local
#print axioms LocalFrames.expand_compile
#print axioms LocalFrames.address_injective
#print axioms LocalFrames.argument_avoids_locals
#print axioms LocalFrames.unshifted_names_capture
