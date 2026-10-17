import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.PolicyControls

/-! Runtime controls for joined indexed modal formation and receipts. -/

open Mettapedia.OSLF.NativeTypes.Generation
open IndexedModal

#eval do
  JoinedRuntime.receipts BindingPipeline.Controls.originalLambda [] "Term" BindingPipeline.Controls.lambdaSource.term 2000
  JoinedRuntime.receipts BindingPipeline.Controls.originalLambda [] "Term" Consumers.underBinderSource 2000
  JoinedRuntime.receipts BindingPipeline.Controls.originalLambda [] "Term" Consumers.relySource 2000
  JoinedRuntime.receipts BindingPipeline.Controls.originalLetCase [] "Computation" BindingPipeline.Controls.letCaseSource.term 2000
  JoinedRuntime.receipts BindingPipeline.Controls.originalMachine [] "Cfg" BindingPipeline.Controls.machineSource.term 500
  JoinedRuntime.receipts Consumers.sharedLanguage [] "Program" Consumers.sharedSource 500

#eval JoinedRuntime.binderFocus
#eval JoinedRuntime.duplicateOrigins
