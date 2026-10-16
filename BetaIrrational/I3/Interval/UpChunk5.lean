/-
# I3 contour certificate: upper polyline, chunk 5 (PROOF_BETA §6.3, (S2), (S4))

Kernel checks (`decide +kernel`) on the segments of `upA5, upC5` (`PolyDataI3.lean`):
* `chk_up5`: `Re f ≤ T0` on every segment (`polyChk`, second-order Taylor bound per segment);
* `chk_sec_up5`: `|α_i| ≥ 1/1000`, `|arg α_i| ≤ 2.76` for every factor and `Re z > -1/2`
  (`polySectorQ`).

Combined with the other chunks in `ContourI3.lean`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Interval.PolyDataI3

namespace BetaIrr.I3.Interval

open BetaIrr.Interval BetaIrr.Fam.Interval

lemma chk_up5 : polyChk 40 16 facI3 T0 upA5 upC5 = true := by decide +kernel

lemma chk_sec_up5 : polySectorQ 40 16 amin Amax facI3 upA5 upC5 = true := by decide +kernel

end BetaIrr.I3.Interval
