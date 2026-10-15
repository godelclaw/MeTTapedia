import Mettapedia.GSLT.Weighting.ConfiguredFundingControls
import Mettapedia.GSLT.Weighting.OutcomeFibreRateControls
import Mettapedia.GSLT.Scope.ConversionRateControls
import Mettapedia.GSLT.Scope.MonoidalConversionControls
import Mettapedia.GSLT.Causality.ResourceReservationControls
import Mettapedia.GSLT.Causality.ResourceCurrencyControls
import Mettapedia.OSLF.Syntax.RhoScopedEventPriceControls

/-!
# Configured coefficients, preaccepted histories and currency conversion

The entry point joins actual event funding at evolving weight maps, ordered
charge words and prefix-safe reservations, connected conversion graphs and
their normalized monoidal common measures, permitted batch exchanges, and
event-sensitive prices under capture-avoiding substitution.

The finite outcome-fibre comparison requires fractional coefficients and a
price which descends to outcomes. The reservation comparison retains supplied
resource histories. Common measures do not supply exchange permissions or
certificates, and these interfaces do not identify a complete process runtime
or a stochastic normalization.
-/
