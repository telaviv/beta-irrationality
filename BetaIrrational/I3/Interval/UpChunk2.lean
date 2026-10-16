/-
# I3 contour certificate: upper polyline, chunk 2 (PROOF_BETA §6.3, (S2), (S4))

Kernel checks (`decide +kernel`) on the segments of `upA2, upC2` (`PolyDataI3.lean`):
* `chk_up2`: `Re f ≤ T0` on every segment (`polyChk`, second-order Taylor bound per segment);
* `chk_sec_up2`: `|α_i| ≥ 1/1000`, `|arg α_i| ≤ 2.76` for every factor and `Re z > -1/2`
  (`polySectorQ`).

Combined with the other chunks in `ContourI3.lean`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Interval.PolyDataI3

namespace BetaIrr.I3.Interval

open BetaIrr.Interval BetaIrr.Fam.Interval

lemma chk_up2 : polyChk 40 16 facI3 T0 upA2 upC2 = true := by decide +kernel

lemma chk_sec_up2 : polySectorQ 40 16 amin Amax facI3 upA2 upC2 = true := by decide +kernel

end BetaIrr.I3.Interval
