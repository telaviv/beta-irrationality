/-
# The A-certificate for instance I3: definitions


`PROOF_BETA.md` §5.1 and `d30_certA_exact.py`.

Instance I3: `μ_in = 3`, one zero run `[-(1+r), r]` (in units of `n`) of multiplicity 3, `r = 7/6`,
blocks `δ_j = k_j/160` from `BetaIrr.I3.blocks`, `G = 179/10`.

This file contains
* the **specification** `f x y` of PROOF_BETA §5.1 for `x ≥ 1` (for `x < 1` it is `0`, since
  `μ_in = 3`), written with the exact floor conventions (including the out-of-block indicator
  `[δ x - y ∈ ℤ]`, encoded as `Int.fract (δ x - y) = 0`);
* the **floor-data form** `Phi`: `f x y` only depends on the floors and ceilings of `y - c` for the
  finitely many offsets `c = σ/480 · x + τ/2` listed in `offsets`;
* the **computable** `eStar x` (an integer-scaled sup over the breakpoints, proved equal to
  `sup_{0 ≤ y ≤ x} f x y` in `CertA/Sound.lean`);
* the **event points** in `[1, X]` (same set as `d30_certA_exact.py`: chunk cuts, integers, and
  crossings `(t₂ - t₁ + m)/(s₁ - s₂)` of the breakpoint line families);
* the rounded body sum `bodyUnits` (each term rounded *up* to a multiple of `2^-96`, as in the
  Python).

Everything here is a definition; no proofs.

Status: complete (definitions only, no `sorry`).
-/
import BetaIrrational.FamilyI3

namespace BetaIrr.I3.CertA

open Finset

/-! ## Specification (PROOF_BETA §5.1) -/

/-- `δ = d/160`. -/
def dlt (d : ℕ) : ℚ := (d : ℚ) / 160

/-- `r = 7/6`. -/
def rr : ℚ := 7 / 6

/-- `S(y) = Σ_j m_j [δ_j x ≤ y ≤ (1-δ_j) x]`. -/
def Sfun (x y : ℚ) : ℕ :=
  (blocks.map fun b => if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then b.2 else 0).sum

/-- The number of odd integers in the half-open interval `(u, v]`. -/
def oddCount (u v : ℚ) : ℕ := ((Ioc ⌊u⌋ ⌊v⌋).filter Odd).card

/-- `c(y) = μ · #{odd o ∈ (2y + 2Ax, 2y + 2Bx]}` for the single run `[A, B] = [-(1+r), r]`,
`μ = 3`. -/
def cfun (x y : ℚ) : ℕ := 3 * oddCount (2 * y + 2 * (-(1 + rr)) * x) (2 * y + 2 * rr * x)

/-- `P_j(y)` of §5.1 (for `x ≥ 1`), with the out-of-block indicator terms. -/
def Pfun (d : ℕ) (x y : ℚ) : ℤ :=
  if dlt d * x ≤ y ∧ y ≤ (1 - dlt d) * x then
    ⌊y - dlt d * x⌋ + ⌊(1 - dlt d) * x - y⌋
  else if y < dlt d * x then
    ⌊(1 - dlt d) * x - y⌋ - ⌊dlt d * x - y⌋ + (if Int.fract (dlt d * x - y) = 0 then 1 else 0)
  else
    ⌊y - dlt d * x⌋ - ⌊y - (1 - dlt d) * x⌋ + (if Int.fract (y - (1 - dlt d) * x) = 0 then 1 else 0)

/-- `f(x, y)` of PROOF_BETA §5.1 for I3: for `x ≥ 1`,
`S + 2 - c + Σ_j m_j P_j - G ⌊x⌋`; for `x < 1` it is `0` (`μ_in = 3`).
(The restriction "where `S(y) > 0`" is automatic for I3 on `0 ≤ y ≤ x`: the block `δ = 0`
covers `[0, x]`.) -/
def f (x y : ℚ) : ℚ :=
  if 1 ≤ x then
    (Sfun x y : ℚ) + 2 - cfun x y + (((blocks.map fun b => (b.2 : ℤ) * Pfun b.1 x y).sum : ℤ) : ℚ)
      - G * ⌊x⌋
  else 0

/-! ## Offsets and the floor-data form -/

/-- An offset `(σ, τ)` stands for the breakpoint family `y = σ/480 · x + τ/2 + j`, `j ∈ ℤ`. -/
def offVal (x : ℚ) (o : ℤ × ℤ) : ℚ := (o.1 : ℚ) / 480 * x + (o.2 : ℚ) / 2

/-- Left block end `δ x`: `σ = 3d`. -/
def aOff (d : ℕ) : ℤ × ℤ := (3 * (d : ℤ), 0)
/-- Right block end `(1-δ) x`: `σ = 480 - 3d`. -/
def bOff (d : ℕ) : ℤ × ℤ := (480 - 3 * (d : ℤ), 0)
/-- `-r x - 1/2`: `(v+1)/2 = y - this` for `v = 2y + 2rx`. -/
def c1Off : ℤ × ℤ := (-560, -1)
/-- `(1+r) x - 1/2`: `(u+1)/2 = y - this` for `u = 2y - 2(1+r)x`. -/
def c2Off : ℤ × ℤ := (1040, -1)

/-- All offsets on which `f x ·` depends. -/
def offsets : List (ℤ × ℤ) :=
  c1Off :: c2Off :: blocks.flatMap fun b => [aOff b.1, bOff b.1]

/-- One block's contribution `(m [in block], m P_j)` from the floor/ceiling data
`Fa = ⌊y - δx⌋`, `Ca = ⌈y - δx⌉`, `Fb = ⌊y - (1-δ)x⌋`, `Cb = ⌈y - (1-δ)x⌉`. -/
def blockVal (m Fa Ca Fb Cb : ℤ) : ℤ :=
  if 0 ≤ Fa ∧ Cb ≤ 0 then m + m * (Fa - Cb)
  else if Fa < 0 then m * (Ca - Cb + if Fa = Ca then 1 else 0)
  else m * (Fa - Fb + if Fb = Cb then 1 else 0)

/-- `S + 2 - c + Σ m_j P_j` as a function of floor data `F o = ⌊y - c_o⌋`, `C o = ⌈y - c_o⌉`. -/
def Phi (F C : ℤ × ℤ → ℤ) : ℤ :=
  (blocks.map fun b =>
      blockVal b.2 (F (aOff b.1)) (C (aOff b.1)) (F (bOff b.1)) (C (bOff b.1))).sum
    + 2 - 3 * (F c1Off - F c2Off)

/-! ## The computable `e*` (integer scaling) -/

/-- For `x = P/Q` and `M = 960 Q`, the scaled offset `M · offVal x o = 2σP + 480τQ`, split as
`q M + r` with `0 ≤ r < M`. -/
def qrOf (P Q : ℤ) (o : ℤ × ℤ) : ℤ × ℤ :=
  let B := 2 * o.1 * P + 480 * o.2 * Q
  (B / (960 * Q), B % (960 * Q))

/-- Floor of `y - c_l` at the candidate `y = k + r_i/M`, where `c_l` has data `(q_l, r_l)`. -/
def flAt (k ri : ℤ) (ql : ℤ × ℤ) : ℤ := k - ql.1 - (if ri < ql.2 then 1 else 0)

/-- Ceiling of `y - c_l` at `y = k + r_i/M` (`right = false`) or the floor-plus-one of the
right limit `y + 0` (`right = true`). -/
def clAt (k ri : ℤ) (right : Bool) (ql : ℤ × ℤ) : ℤ :=
  if right then flAt k ri ql + 1 else flAt k ri ql + (if ri = ql.2 then 0 else 1)

/-- Precomputed per-block data for `x = P/Q`. -/
def preOf (P Q : ℤ) : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ)) :=
  blocks.map fun b => ((b.2 : ℤ), qrOf P Q (aOff b.1), qrOf P Q (bOff b.1))

/-- `Phi` at a candidate, from precomputed data. -/
def phiAt (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) (k ri : ℤ) (right : Bool) : ℤ :=
  (pre.map fun e => blockVal e.1 (flAt k ri e.2.1) (clAt k ri right e.2.1)
      (flAt k ri e.2.2) (clAt k ri right e.2.2)).sum
    + 2 - 3 * (flAt k ri q1 - flAt k ri q2)

/-- Validity of the candidate `y = k + r_i/M`: `0 ≤ y ≤ x` (for the value at `y`, `right = false`)
or `0 ≤ y < x` (for the right-limit value, `right = true`), where `960 P = qX M + rX`. -/
def valid (qX rX ri k : ℤ) (right : Bool) : Bool :=
  decide (0 ≤ k) && (decide (k < qX) || (decide (k = qX) &&
    (if right then decide (ri < rX) else decide (ri ≤ rX))))

/-- The values of `k` at which some block changes case, for fixed `r_i` (plus `0`). Between
consecutive thresholds `phiAt · r_i right` is constant in `k`. -/
def thresholds (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (ri : ℤ) (right : Bool) : List ℤ :=
  0 :: pre.flatMap fun e =>
    [e.2.1.1 + (if ri < e.2.1.2 then 1 else 0),
     e.2.2.1 + (if ri < e.2.2.2 then 1 else 0) + 1 -
       (if right then 1 else if ri = e.2.2.2 then 0 else 1)]

/-- Fold step: include candidate `(k, r_i, right)` if valid. -/
def candStep (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (q1 q2 : ℤ × ℤ) (qX rX ri : ℤ) (right : Bool)
    (acc k : ℤ) : ℤ :=
  if valid qX rX ri k right then max acc (phiAt pre q1 q2 k ri right) else acc

/-- `max_{0 ≤ y ≤ x} (S + 2 - c + Σ m_j P_j)` (an integer), computed over the breakpoints
`y = k + r_i/M` and their right limits, where for each offset only the thresholds in `k` are
visited. The initial value is the value at `y = 0`. -/
def eStarInt (x : ℚ) : ℤ :=
  let P := x.num
  let Q : ℤ := x.den
  let pre := preOf P Q
  let q1 := qrOf P Q c1Off
  let q2 := qrOf P Q c2Off
  let qX := P / Q
  let rX := 960 * (P % Q)
  offsets.foldl (fun acc o =>
      let ri := (qrOf P Q o).2
      let acc := (thresholds pre ri false).foldl (candStep pre q1 q2 qX rX ri false) acc
      (thresholds pre ri true).foldl (candStep pre q1 q2 qX rX ri true) acc)
    (phiAt pre q1 q2 0 0 false)

/-- `e*(x) = sup_{0 ≤ y ≤ x} f(x, y)` (computable; see `CertA/Sound.lean` for the proof that it is
the supremum, for `x ≥ 1`). For `x < 1` it is `0`. -/
def eStar (x : ℚ) : ℚ := if 1 ≤ x then (eStarInt x : ℚ) - G * ⌊x⌋ else 0

/-! ## Event points -/

/-- The breakpoint line families `(s, t)` of `d30_certA_exact.py`: `y = s x + t + j`. -/
def fams : List (ℚ × ℚ) :=
  (([((13 : ℚ) / 6, -1 / 2), (-7 / 6, -1 / 2)] : List (ℚ × ℚ)) ++
    blocks.flatMap (fun b : ℕ × ℕ => ([(dlt b.1, 0), (1 - dlt b.1, 0)] : List (ℚ × ℚ))) ++
    ([(0, 0), (0, 1 / 2), (1, 0)] : List (ℚ × ℚ))).dedup

/-- Crossings in `(lo, hi)` of the families `(s₁,t₁)`, `(s₂,t₂)` with `s₁ > s₂`:
`x = (t₂ - t₁ + m) / (s₁ - s₂)`. -/
def crossPair (lo hi : ℚ) (p₁ p₂ : ℚ × ℚ) : List ℚ :=
  if p₂.1 < p₁.1 then
    let ds := p₁.1 - p₂.1
    let dt := p₂.2 - p₁.2
    let m0 := ⌊lo * ds - dt⌋
    let m1 := ⌈hi * ds - dt⌉
    ((List.range ((m1 - m0).toNat + 1)).map fun i : ℕ => (dt + ((m0 + (i : ℤ) : ℤ) : ℚ)) / ds).filter
      fun v => lo < v ∧ v < hi
  else []

/-- All crossings in `(lo, hi)`. -/
def crossings (lo hi : ℚ) : List ℚ :=
  fams.flatMap fun p₁ => fams.flatMap fun p₂ => crossPair lo hi p₁ p₂

/-- The chunk cuts of `d30_certA_exact.py`: `1 + j/20` (`j < 40`) and `3 + j/2`
(`0 ≤ j ≤ 2(X-3)`). They include every integer in `[1, X]`. -/
def cuts (X : ℕ) : List ℚ :=
  (List.range 40).map (fun j : ℕ => 1 + (j : ℚ) / 20) ++
    (List.range (2 * (X - 3) + 1)).map (fun j : ℕ => 3 + (j : ℚ) / 2)

/-- Remove adjacent duplicates. -/
def dedupAdj : List ℚ → List ℚ
  | a :: b :: l => if a = b then dedupAdj (b :: l) else a :: dedupAdj (b :: l)
  | l => l

/-- The sorted event points in `[1, X]`. -/
def events (X : ℕ) : List ℚ :=
  dedupAdj ((cuts X ++ crossings 1 X).mergeSort (fun a b => decide (a ≤ b)))

/-! ## The certificate sums -/

/-- Sum of `g a b` over consecutive pairs `(a, b)` of a list. -/
def pairSum {β : Type} [AddCommMonoid β] (g : ℚ → ℚ → β) : List ℚ → β
  | a :: b :: l => g a b + pairSum g (b :: l)
  | _ => 0

/-- The exact body `A_body = Σ_ℓ e*(mid_ℓ) (1/x_{ℓ-1} - 1/x_ℓ)`. -/
def ABody (X : ℕ) : ℚ := pairSum (fun a b => eStar ((a + b) / 2) * (1 / a - 1 / b)) (events X)

/-- One term rounded up to a multiple of `2^-96` (in units of `2^-96`). -/
def termUnits (a b : ℚ) : ℤ := ⌈eStar ((a + b) / 2) * (1 / a - 1 / b) * 2 ^ 96⌉

/-- The rounded body, in units of `2^-96`. -/
def bodyUnits (X : ℕ) : ℤ := pairSum termUnits (events X)

/-- `E_tail = S + 9 = 44`; tail bound `E_tail/X + G/(2(X-1))`. -/
def tail (X : ℕ) : ℚ := 44 / X + G / (2 * ((X : ℚ) - 1))

end BetaIrr.I3.CertA
