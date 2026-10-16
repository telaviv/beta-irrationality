/-
# Connector, disc and first-segment box checks for the I3 contour (PROOF_BETA §6.3)

Small kernel checks that depend only on the contour data (`PolyDataI3.lean`), kept apart from the
saddle files so that they build in parallel:
* `chk_cup`, `chk_cdn` (`ballOK`): `Re f ≤ T0` on the discs of radius `10⁻⁹` around `upStart`,
  `dnStart` (these contain the connectors `[x₀ ± ρ d, upStart/dnStart]`);
* `chk_sec_cup`, `chk_sec_cdn`, `chk_sec_disc` (`sectorQ`): the sector condition of (S4) on the
  connector boxes and on the box `c0 ± (ρ + R0)` containing the Taylor disc (`c0`, `ρ = 1/250`,
  `R0 = 10⁻¹²` written as literals; they are identified with the definitions of `SaddleI3.lean`
  in `ContourI3.lean`);
* the first segment `[x_c, firstB]` widened by `δ0 = 10⁻⁷` (`firstBox`): slit-plane condition,
  sector condition, and `|Ψ' - 2πi| δ0 ≤ 10⁻⁵` (`chk_first_G`), used for the moved start point
  (field `S2_first` of `SaddleData`).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Interval.PolyDataI3

namespace BetaIrr.I3.Interval

open BetaIrr.Interval BetaIrr.Interval.IV BetaIrr.Fam.Interval

/-! ## Connectors and the Taylor disc box -/

lemma chk_cup : ballOK 40 16 facI3 T0 upStart (1 / 10 ^ 9) = true := by decide +kernel
lemma chk_cdn : ballOK 40 16 facI3 T0 dnStart (1 / 10 ^ 9) = true := by decide +kernel

lemma chk_sec_cup :
    sectorQ 40 16 amin Amax facI3 (CB.ofQRad upStart.1 upStart.2 (1 / 10 ^ 9)) = true := by
  decide +kernel
lemma chk_sec_cdn :
    sectorQ 40 16 amin Amax facI3 (CB.ofQRad dnStart.1 dnStart.2 (1 / 10 ^ 9)) = true := by
  decide +kernel

lemma chk_sec_disc_lit : sectorQ 40 16 amin Amax facI3
    (CB.ofQRad (11719231074608510827430178 / 10 ^ 25) (99732253713548444658806 / 10 ^ 25)
      (1 / 250 + 1 / 10 ^ 12)) = true := by
  decide +kernel

/-! ## The first segment, widened -/

def δ0 : ℚ := 1 / 10 ^ 7

def firstA : ℚ × ℚ := (xc, 0)

/-- The bounding box of `[x_c, firstB]` widened by `δ0`. -/
def firstBox : CB :=
  ⟨ival (min firstA.1 firstB.1 - δ0) (max firstA.1 firstB.1 + δ0),
   ival (min firstA.2 firstB.2 - δ0) (max firstA.2 firstB.2 + δ0)⟩

def firstG : CB := (dpsiB 40 16 facI3 firstBox).sub twoPiIB

lemma chk_first_good : goodB facI3 firstBox = true := by decide +kernel
lemma chk_first_sec : sectorQ 40 16 amin Amax facI3 firstBox = true := by decide +kernel
lemma chk_first_G : (absHi firstG.re + absHi firstG.im) * δ0 ≤ 1 / 10 ^ 5 := by decide +kernel
lemma chk_first_re : firstG.re ≠ top ∧ firstG.im ≠ top := by decide +kernel

end BetaIrr.I3.Interval
