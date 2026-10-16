import BetaIrrational

/-! # Axiom audit

Run with `lake env lean Axioms.lean` (after `lake build`). Every line should print only Lean's three
standard axioms `[propext, Classical.choice, Quot.sound]`. A `sorryAx` would indicate a gap, and a
`Lean.ofReduceBool` / `*.native_decide.ax_*` entry would indicate trust in the compiler. -/

-- The main theorem
#print axioms BetaIrr.I3.oneOfBeta4To36

-- Its main ingredients
#print axioms BetaIrr.I3.expansion_I3             -- Lemma 3: L_n ∈ ℚ + ℚβ(4) + … + ℚβ(36)
#print axioms BetaIrr.I3.Arith.int_rho_I3         -- Lemma 4: common denominator
#print axioms BetaIrr.I3.oneOfBeta4To36_of_parts  -- Lemmas 4–5 + assembly
#print axioms BetaIrr.I3.CertA.bodyUnits_400      -- (H2) the A-certificate computation
#print axioms BetaIrr.I3.size_I3                  -- Lemma 6(i): size of L_n
#print axioms BetaIrr.I3.Analytic.nonvan_of_saddleData  -- Lemma 6(ii) from saddle data
#print axioms BetaIrr.I3.Interval.I3_saddleData   -- the kernel-checked saddle certificate

-- Shared infrastructure
#print axioms BetaIrr.exists_irrational_of_small_forms  -- the irrationality criterion
#print axioms BetaIrr.PFData.tsum_alt_R2_even           -- Lemmas 1–3 for partial-fraction data
#print axioms BetaIrr.PNT.theta_div_tendsto             -- prime number theorem (ported)
#print axioms BetaIrr.Stirling.stirling_scaled          -- complex Stirling
