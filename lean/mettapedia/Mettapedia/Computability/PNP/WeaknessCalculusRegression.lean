import Mettapedia.Computability.PNP.WeaknessCalculus

/-!
# Regression checks for the finite weakness calculus

These checks keep the finite spectrum/gap and no-threading bridge visible in
the PNP regression target.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check WeaknessTask.spectrum_mono
#check spectrumGap_nonneg
#check spectrumGap_eq_zero_iff_domination
#check spectrumGap_eq_zero_iff_flat
#check spectrumGap_mono_polyBudget
#check spectrum_dataProcessing
#check noThreading_general
#check spectrumGap_pos_of_noThreading
#check spectrumGap_zero_of_starSWDomination
#check toyWeakness_noThreading_forces_gap

#print axioms WeaknessTask.spectrum_mono
#print axioms spectrumGap_eq_zero_iff_domination
#print axioms spectrum_dataProcessing
#print axioms noThreading_general
#print axioms spectrumGap_pos_of_noThreading
#print axioms spectrumGap_zero_of_starSWDomination
#print axioms toyWeakness_noThreading_forces_gap

end Mettapedia.Computability.PNP
