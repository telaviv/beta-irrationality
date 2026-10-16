/-
# The A-certificate for instance I3: the isolated computational fact and its reductions

PROOF_BETA §5.4 / (H2) for I3. This file contains *no* computation. It isolates the single
computational fact of the I3 A-certificate as a `Prop`:

* `CertFact : Prop := ABody 400 + tail 400 ≤ Acert` — **(H2) for I3**, the hypothesis `hcert` of
  `I3.oneOfBeta4To36_of_parts` (`I3/Glue/Main.lean`);
* `UnitsFact : Prop := bodyUnits 400 = 1243345293752876677540040193981` — the rounded-body form
  (proved in `I3/CertAK/CertCompute.lean`);
* `certFact_of_units : UnitsFact → CertFact` (proved here; exact rational arithmetic).

Numbers (`d30_certA_exact.py`, re-run 2026-10-15 on `r = 7/6`, `X = 400`, blocks
PROOF_BETA §9): `bodyUnits 400 = 1243345293752876677540040193981` (units of
`2^-96`; the Python's `body_units`), `A_body ≤ 15.6932239…`, `tail 400 = 44/400 + G/798 = 1321/9975`,
and `bodyUnits/2^96 + tail = Acert = 12507029707866288048422972493354331/790300921079786767495600904601600`
exactly (`≈ 15.8256550`). The Python counts 62,965 events (each chunk's endpoints counted twice).

`e*` is the computable `eStar` (`I3/CertA/Defs.lean`); `I3/CertA/Sound.lean` proves `f x y ≤ eStar x`.

Status: complete (no `sorry`). `CertFact` itself is proved from `UnitsFact` here, and `UnitsFact` in
`I3/CertAK/CertCompute.lean`.
-/
import BetaIrrational.I3.CertA.Sound

namespace BetaIrr.I3.CertA

/-- Each exact term is at most its rounded-up value. -/
lemma pairSum_le_units :
    ∀ l : List ℚ, pairSum (fun a b => eStar ((a + b) / 2) * (1 / a - 1 / b)) l ≤
      ((pairSum termUnits l : ℤ) : ℚ) / 2 ^ 96
  | [] => by simp [pairSum]
  | [_] => by simp [pairSum]
  | a :: b :: l => by
    have ih := pairSum_le_units (b :: l)
    have h96 : (0 : ℚ) < 2 ^ 96 := by positivity
    have hterm : eStar ((a + b) / 2) * (1 / a - 1 / b) ≤ ((termUnits a b : ℤ) : ℚ) / 2 ^ 96 := by
      rw [le_div_iff₀ h96]; exact Int.le_ceil _
    show eStar ((a + b) / 2) * (1 / a - 1 / b) +
        pairSum (fun a b => eStar ((a + b) / 2) * (1 / a - 1 / b)) (b :: l) ≤
      ((termUnits a b + pairSum termUnits (b :: l) : ℤ) : ℚ) / 2 ^ 96
    rw [Int.cast_add, add_div ((termUnits a b : ℤ) : ℚ) ((pairSum termUnits (b :: l) : ℤ) : ℚ)]
    linarith

lemma ABody_le_units (X : ℕ) : ABody X ≤ ((bodyUnits X : ℤ) : ℚ) / 2 ^ 96 :=
  pairSum_le_units (events X)

/-- **The isolated computational fact (H2) for I3**: `A_body + E_tail/X + G/(2(X-1)) ≤ Acert`
with `X = 400`, `E_tail = S + 9 = 44`, where `A_body = Σ_ℓ e*(mid_ℓ)(1/x_{ℓ-1} - 1/x_ℓ)` over the
event intervals in `[1, 400]`. -/
def CertFact : Prop := ABody 400 + tail 400 ≤ Acert

/-- The rounded-body form of the computation (value from `d30_certA_exact.py`). -/
def UnitsFact : Prop := bodyUnits 400 = 1243345293752876677540040193981

/-- The rounded body value and the tail add up to `Acert` exactly. -/
lemma units_add_tail_eq :
    ((1243345293752876677540040193981 : ℤ) : ℚ) / 2 ^ 96 + tail 400 = Acert := by
  norm_num [tail, G, Acert]

/-- `UnitsFact` implies `CertFact`. -/
theorem certFact_of_units (h : UnitsFact) : CertFact := by
  have h1 := ABody_le_units 400
  rw [show bodyUnits 400 = 1243345293752876677540040193981 from h] at h1
  have h2 := units_add_tail_eq
  unfold CertFact
  linarith

end BetaIrr.I3.CertA
