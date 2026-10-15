import Mettapedia.OSLF.NativeTypes.Runtime.Interface
import Mettapedia.OSLF.NativeTypes.Decision.Profiles

open Mettapedia.OSLF.Framework

/-!
# Installed original rho and authored lambda execution

The installed runtime retains the generated presentation and its proved
native leaf meanings. It consumes the original suspended operational jobs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.Profiles

open Mettapedia.OSLF.Binding LambdaContextualRung
open Mettapedia.OSLF.NativeTypes.Runtime

def rhoRuntime (configuration : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Configuration) :
    Engine (Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.driver configuration) where
  cursor := Mettapedia.OSLF.NativeTypes.Decision.Profiles.rho
  leaves := Mettapedia.OSLF.NativeTypes.Decision.Profiles.rhoLeaves configuration
  leaf_meaning := Mettapedia.OSLF.NativeTypes.Decision.Profiles.rho_leaf_meaning configuration

def lambdaRuntime (configuration : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration) (context : Ctx sig) :
    Engine (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.driver configuration context) where
  cursor := Mettapedia.OSLF.NativeTypes.Decision.Profiles.lambda configuration.rules context
  leaves := Mettapedia.OSLF.NativeTypes.Decision.Profiles.lambdaLeaves configuration context
  leaf_meaning := Mettapedia.OSLF.NativeTypes.Decision.Profiles.lambda_leaf_meaning configuration context

def rho (configuration : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Configuration) : Installed :=
  ⟨Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.driver configuration, rhoRuntime configuration⟩

def lambda (configuration : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration) (context : Ctx sig) : Installed :=
  ⟨Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.driver configuration context, lambdaRuntime configuration context⟩

theorem rho_original (configuration : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Configuration) :
    (rho configuration).native.generated.snapshot.language =
      Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc := Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.driver_original_language configuration

theorem lambda_original (configuration : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration) (context : Ctx sig) :
    (lambda configuration context).native.generated.snapshot.language =
      LambdaAuthoredFullRuleProfile.language := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.driver_original_language configuration context

end Mettapedia.OSLF.NativeTypes.Runtime.Profiles
