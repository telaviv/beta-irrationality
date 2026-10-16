/-
# I3 contour certificate: lower polyline (PROOF_BETA §6.3, (S2), (S4), (S5))

Kernel checks (`decide +kernel`) on the segments of `dnStart, dnPts` (`PolyDataI3.lean`), from
`x₀ - ρ d` down to the real point `x_c`:
* `chk_dn`: `Re f ≤ T0` on every segment (`polyChk`);
* `chk_sec_dn`: `|α_i| ≥ 1/1000`, `|arg α_i| ≤ 2.76` for every factor and `Re z > -1/2`
  (`polySectorQ`).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Interval.PolyDataI3

namespace BetaIrr.I3.Interval

open BetaIrr.Interval BetaIrr.Fam.Interval

lemma chk_dn : polyChk 40 16 facI3 T0 dnStart dnPts = true := by decide +kernel

lemma chk_sec_dn : polySectorQ 40 16 amin Amax facI3 dnStart dnPts = true := by decide +kernel

end BetaIrr.I3.Interval
