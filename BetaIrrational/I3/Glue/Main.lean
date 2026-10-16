/-
# Glue (I3): Lemmas 3, 4, 5 discharged — `oneOfBeta4To36_of_parts`

`I3.Hyp` (`FamilyI3.lean`) is built from:
* Lemma 3 (`expansion`): `expansion_I3` (`I3/Concrete/Expansion.lean`), with `ρ = (pf m).rho`,
  `τ m j = (pf m).tau (2j-2)`;
* Lemma 4 (`D`, `D_pos`, `int_ρ`, `int_τ`): `Arith.D`, `D_pos_I3`, `int_rho_I3`, `int_tau_I3`
  (`I3/Arith/Lemma4.lean`; Lemma C via `pf_R2_inner_zero`);
* Lemmas 4–5 (`arith`, with `A = Acert`): `arith_I3`, from the split `Arith.log_D_sub_le`
  (`20 n log 2 + o(n)` + the sharp sum) and `sharp_I3` (PNT step `sharp_of_pointwise` with the
  CertA data: pointwise bound, step function on the events of `[1, 400]`, tail `44 + G{y}`);
* (H2): the single computational fact `hcert : CertA.ABody 400 + CertA.tail 400 ≤ Acert`
  (`= CertA.CertFact`, `I3/CertA/Cert.lean`), taken as a hypothesis;
* Lemma 6(i) (`size`) and 6(ii) (`nonvan`): hypotheses, discharged in `I3/MainCond.lean`
  (`I3/Size`, `I3/Analytic`, `I3/Interval`).

Main result: `oneOfBeta4To36_of_parts (hcert) (εL) (hεL) (hsize) (hnon) : OneOfBeta4To36`.

Status: complete (no `sorry`). PROOF_BETA §3–§5, §7, §9 (I3 column).
-/
import BetaIrrational.I3.Glue.CertInst
import BetaIrrational.I3.CertA.Cert
import BetaIrrational.I3.Arith.Lemma4
import BetaIrrational.I3.Concrete.Expansion
import BetaIrrational.FamilyI3

namespace BetaIrr.I3

open Filter Topology Finset

/-- (c) of `sharp_of_pointwise` for the CertA data: `A_body + 44/400 + G/(2·399) ≤ Acert`. -/
lemma cert_I3 (hcert : CertA.ABody 400 + CertA.tail 400 ≤ Acert) :
    ∑ i ∈ range (LL (CertA.events 400)),
      uL (CertA.events 400) i * (1 / xL (CertA.events 400) i - 1 / xL (CertA.events 400) (i + 1))
      + 44 / ((400 : ℕ) : ℝ) + (G : ℝ) / (2 * (((400 : ℕ) : ℝ) - 1)) ≤ (Acert : ℝ) := by
  rw [← pairSum_cast_eq]
  have h := hcert
  unfold CertA.tail CertA.ABody at h
  generalize CertA.pairSum (fun a b => CertA.eStar ((a + b) / 2) * (1 / a - 1 / b))
    (CertA.events 400) = P at h ⊢
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h' ⊢
  linarith

/-- **Lemma 5 for I3** (given (H2)). `Σ_{√𝒩 < p ≤ n} (E_p - G⌊n/p⌋) log p ≤ n (Acert + o(1))`. -/
theorem sharp_I3 (hcert : CertA.ABody 400 + CertA.tail 400 ≤ Acert) :
    ∃ εS : ℕ → ℝ, Tendsto εS atTop (𝓝 0) ∧
    ∀ᶠ m in atTop,
      ∑ p ∈ (Arith.primesD m).filter (fun p => p ≤ nOf m ∧ Arith.NN m < p ^ 2),
          ((Arith.Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)) * Real.log p
        ≤ (nOf m : ℝ) * ((Acert : ℝ) + εS m) :=
  sharp_of_pointwise (fun q => ((CertA.eStar q : ℚ) : ℝ))
    (Eventually.of_forall fun m p hp hpn hN => Esharp_sub_le_eStar m p hp hpn hN)
    (xL (CertA.events 400)) (uL (CertA.events 400)) (LL (CertA.events 400)) 400 (by norm_num)
    (xL_zero evs_pairwise evs_bounds one_mem_evs four_hundred_mem_evs) (xL_lt evs_pairwise)
    (xL_LL evs_pairwise evs_bounds one_mem_evs four_hundred_mem_evs) cell_le_evs 44 (by norm_num)
    tail_le
    (Acert : ℝ) (cert_I3 hcert)

/-- **Lemmas 4–5 for I3** (given (H2)):
`log D_n ≤ G log n! + n (Acert + 20 log 2 + εA)` with `εA → 0`. -/
theorem arith_I3 (hcert : CertA.ABody 400 + CertA.tail 400 ≤ Acert) :
    ∃ εA : ℕ → ℝ, Tendsto εA atTop (𝓝 0) ∧
    ∀ᶠ m in atTop, Real.log ((Arith.D m : ℚ) : ℝ)
      ≤ (G : ℝ) * Real.log ((nOf m).factorial : ℝ)
        + (nOf m : ℝ) * ((Acert : ℝ) + 20 * Real.log 2 + εA m) := by
  obtain ⟨εS, hεS, hsharp⟩ := sharp_I3 hcert
  refine ⟨fun m => εS m + (40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1)) * Real.log 2 / nOf m
      + 312 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m, ?_, ?_⟩
  · have := (hεS.add tendsto_err1).add tendsto_err2
    rw [add_zero, add_zero] at this
    exact this
  · filter_upwards [hsharp] with m hm
    have hsplit := Arith.log_D_sub_le m
    have hn := nOf_pos m
    have e1 : (nOf m : ℝ) * ((40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1)) * Real.log 2 / nOf m)
        = (40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1)) * Real.log 2 := by
      field_simp
    have e2 : (nOf m : ℝ) * (312 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m)
        = 312 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) := by
      field_simp
    have e3 : (nOf m : ℝ) * ((Acert : ℝ) + 20 * Real.log 2 + (εS m
        + (40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1)) * Real.log 2 / nOf m
        + 312 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m))
        = (nOf m : ℝ) * ((Acert : ℝ) + εS m) + 20 * (nOf m : ℝ) * Real.log 2
          + (nOf m : ℝ) * ((40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1)) * Real.log 2 / nOf m)
          + (nOf m : ℝ) * (312 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m) := by
      ring
    rw [e3, e1, e2]
    linarith

/-- `I3.Hyp` from the parts: (H2) `hcert`, Lemma 6(i) `hsize`, Lemma 6(ii) `hnon`. -/
noncomputable def hypOfParts (hcert : CertA.ABody 400 + CertA.tail 400 ≤ Acert)
    (εL : ℕ → ℝ) (hεL : Tendsto εL atTop (𝓝 0))
    (hsize : ∀ m, L m ≠ 0 → Real.log |L m| ≤
      -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * ((Vcert : ℝ) + εL m))
    (hnon : ∃ᶠ m in atTop, L m ≠ 0) : Hyp where
  ρ := fun m => (pf m).rho
  τ := fun m j => (pf m).tau (2 * j - 2)
  expansion := expansion_I3
  D := Arith.D
  D_pos := Arith.D_pos_I3
  int_ρ := Arith.int_rho_I3
  int_τ := Arith.int_tau_I3
  A := Acert
  hA := le_rfl
  εA := (arith_I3 hcert).choose
  εA_lim := (arith_I3 hcert).choose_spec.1
  arith := (arith_I3 hcert).choose_spec.2
  εL := εL
  εL_lim := hεL
  size := Eventually.of_forall hsize
  nonvan := hnon

/-- **Main theorem for I3 from the parts.** Given the single computational fact
(H2) `hcert`, Lemma 6(i) (`hsize`, with `V_cert = -29.76`) and Lemma 6(ii) (`hnon`), one of
`β(4), β(6), …, β(36)` is irrational. -/
theorem oneOfBeta4To36_of_parts (hcert : CertA.ABody 400 + CertA.tail 400 ≤ Acert)
    (εL : ℕ → ℝ) (hεL : Tendsto εL atTop (𝓝 0))
    (hsize : ∀ m, L m ≠ 0 → Real.log |L m| ≤
      -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * ((Vcert : ℝ) + εL m))
    (hnon : ∃ᶠ m in atTop, L m ≠ 0) : OneOfBeta4To36 :=
  oneOfBeta4To36_of_hyp (hypOfParts hcert εL hεL hsize hnon)

end BetaIrr.I3
