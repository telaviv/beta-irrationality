/-
# Instance I3: one of β(4), β(6), …, β(36) is irrational, given the A-certificate sum

All inputs of `oneOfBeta4To36_of_parts` (`I3/Glue/Main.lean`) are discharged except the single
computational fact `CertA.UnitsFact`: the rounded body sum `bodyUnits 400` equals the value printed
by the independent Python implementation `d30_certA_exact.py` for the I3 blocks.
* Lemma 6(i): `size_I3` (`I3/Size/Main.lean`, real-axis bound `V_cert = -29.76`);
* Lemma 6(ii): `nonvan_of_saddleData` (`I3/Analytic/NonvanI3.lean`) applied to the kernel-checked
  certificate `I3_saddleData` (`I3/Interval/SaddleDataI3.lean`).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Glue.Main
import BetaIrrational.I3.Size.Main
import BetaIrrational.I3.Analytic.NonvanI3
import BetaIrrational.I3.Interval.SaddleDataI3

namespace BetaIrr.I3

/-- **Lemma 6(ii) for I3, unconditional.** -/
theorem nonvan_I3 : Filter.Frequently (fun m => L m ≠ 0) Filter.atTop :=
  Analytic.nonvan_of_saddleData Interval.I3_saddleData

/-- **Main theorem for I3, conditional on the A-certificate computation.** -/
theorem oneOfBeta4To36_of_certUnits (h : CertA.UnitsFact) : OneOfBeta4To36 :=
  oneOfBeta4To36_of_parts (CertA.certFact_of_units h) εL εL_lim size_I3 nonvan_I3

end BetaIrr.I3
