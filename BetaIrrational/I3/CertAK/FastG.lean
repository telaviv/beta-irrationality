/-
# The A-certificate for I3: a faster form of `e*` (kernel cost ÷ 2–4)

Refines `eStarIntF` (`I3/CertAK/Fast.lean`) for kernel evaluation:
* the `right = true` values are never larger than the `right = false` ones (`phiN_true_le`), so
  only `right = false` is evaluated;
* the running maximum is kept as a pair `(p, n)` of naturals standing for `p - n` (`bestStep`), so
  the kernel does no `Int` arithmetic per candidate; the constant `K` is added once at the end;
* the candidate residues are read off `rsOf` (`offsets_residues`) instead of being recomputed.

Main results: `eStarInt_eq_G`, `termUnits_eq_G : termUnits = termUnitsG`.
-/
import BetaIrrational.I3.CertAK.Fast

namespace BetaIrr.I3.CertA

/-- Reference implementation of `gAccF` (used only by the compiler, e.g. for `#eval`). -/
def gAccFImpl (ri1 ri : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ × ℕ
  | [], p, n => (p, n)
  | e :: l, p, n => gAccFImpl ri1 ri l (p + if ri1 ≤ e.2.2 then e.1 else 0)
      (n + ((if ri1 ≤ e.2.1 then e.1 else 0) + if ri = e.2.2 then 0 else e.1))

/-- `gAcc ri false`, with `ri1 = ri + 1` precomputed (`gAccF_eq`). -/
@[implemented_by gAccFImpl]
noncomputable def gAccF (ri1 ri : ℕ) (l : List (ℕ × ℕ × ℕ)) : ℕ → ℕ → ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ × ℕ) (fun p n => (p, n))
    (fun e _ ih p n => ih (Nat.add p (cond (Nat.ble ri1 e.2.2) e.1 0))
      (Nat.add n (Nat.add (cond (Nat.ble ri1 e.2.1) e.1 0) (cond (Nat.beq ri e.2.2) 0 e.1)))) l

/-- Keep the pair with the larger `p - n`. -/
def bestStep (acc g : ℕ × ℕ) : ℕ × ℕ :=
  cond (Nat.ble (Nat.add acc.1 g.2) (Nat.add g.1 acc.2)) g acc

/-- The value `p - n` of a pair. -/
def pval (g : ℕ × ℕ) : ℤ := (g.1 : ℤ) - (g.2 : ℤ)

/-- Faster `eStarInt` (equal to it for `x ≥ 1`, `eStarInt_eq_G`). -/
def eStarIntG (x : ℚ) : ℤ :=
  let P := x.num
  let Q : ℤ := x.den
  let pre := preOf P Q
  let q1 := qrOf P Q c1Off
  let q2 := qrOf P Q c2Off
  let rs := rsOf pre
  let r1 := q1.2.toNat
  let r2 := q2.2.toNat
  let gF := fun ri : ℕ =>
    gAccF (Nat.succ ri) ri rs (cond (Nat.blt ri r1) 3 0) (cond (Nat.blt ri r2) 3 0)
  let best := (r1 :: r2 :: rs.flatMap (fun e => [e.2.1, e.2.2])).foldl
    (fun acc ri => bestStep acc (gF ri)) (gF 0)
  Kof pre q1 q2 + pval best

/-- Faster `eStar`. -/
def eStarG (x : ℚ) : ℚ := if 1 ≤ x then (eStarIntG x : ℚ) - G * ⌊x⌋ else 0

/-- Faster `termUnits`. -/
def termUnitsG (a b : ℚ) : ℤ := ⌈eStarG ((a + b) / 2) * (1 / a - 1 / b) * 2 ^ 96⌉

/-! ## Proofs -/

lemma gAccF_eq (ri : ℕ) : ∀ (l : List (ℕ × ℕ × ℕ)) (p n : ℕ),
    gAccF (Nat.succ ri) ri l p n = gAcc ri false l p n
  | [], _, _ => rfl
  | _ :: l, _, _ => gAccF_eq ri l _ _

lemma phiN_true_le (K : ℤ) (rs : List (ℕ × ℕ × ℕ)) (r1 r2 ri : ℕ) :
    phiN K rs r1 r2 ri true ≤ phiN K rs r1 r2 ri false := by
  simp only [phiN, gAcc_spec]
  have : ∀ l : List (ℕ × ℕ × ℕ),
      (l.map fun e => (if ri < e.2.1 then e.1 else 0) + ebN ri e.2.2 false e.1).sum ≤
        (l.map fun e => (if ri < e.2.1 then e.1 else 0) + ebN ri e.2.2 true e.1).sum := by
    intro l
    induction l with
    | nil => simp
    | cons e l ih =>
      simp only [List.map_cons, List.sum_cons]
      have : ebN ri e.2.2 false e.1 ≤ ebN ri e.2.2 true e.1 := by
        unfold ebN; simp only [Bool.false_eq_true, ite_false, ite_true]; split_ifs <;> omega
      omega
  have h := this rs
  omega

lemma pval_bestStep (acc g : ℕ × ℕ) : pval (bestStep acc g) = max (pval acc) (pval g) := by
  unfold bestStep pval
  have hb : Nat.ble (Nat.add acc.1 g.2) (Nat.add g.1 acc.2) =
      decide (acc.1 + g.2 ≤ g.1 + acc.2) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]; rfl
  rw [hb]
  by_cases h : acc.1 + g.2 ≤ g.1 + acc.2 <;> simp [h] <;> omega

lemma foldl_best {α : Type} (K : ℤ) (gF : α → ℕ × ℕ) :
    ∀ (l : List α) (a : ℕ × ℕ),
      l.foldl (fun acc ri => max acc (K + pval (gF ri))) (K + pval a) =
        K + pval (l.foldl (fun acc ri => bestStep acc (gF ri)) a)
  | [], _ => rfl
  | r :: l, a => by
    rw [List.foldl_cons, List.foldl_cons, ← foldl_best K gF l (bestStep a (gF r)), pval_bestStep,
      max_add_add_left]

lemma offsets_residues (P Q : ℤ) :
    offsets.map (fun o => (qrOf P Q o).2.toNat) =
      (qrOf P Q c1Off).2.toNat :: (qrOf P Q c2Off).2.toNat ::
        (rsOf (preOf P Q)).flatMap (fun e => [e.2.1, e.2.2]) := by
  simp [offsets, rsOf, preOf, List.map_flatMap, List.flatMap_map]

lemma phiN_false_eq (K : ℤ) (rs : List (ℕ × ℕ × ℕ)) (r1 r2 ri : ℕ) :
    phiN K rs r1 r2 ri false =
      K + pval (gAccF (Nat.succ ri) ri rs (cond (Nat.blt ri r1) 3 0)
        (cond (Nat.blt ri r2) 3 0)) := by
  rw [gAccF_eq]; unfold phiN pval; ring

theorem eStarIntF_eq_G (x : ℚ) : eStarIntF x = eStarIntG x := by
  unfold eStarIntF eStarIntG
  simp only
  rw [← offsets_residues, List.foldl_map, phiN_false_eq, ← foldl_best]
  apply List.foldl_ext
  intro acc o _
  rw [max_eq_left (le_trans (phiN_true_le _ _ _ _ _) (le_max_right _ _)), phiN_false_eq]

theorem eStarInt_eq_G (x : ℚ) (hx : 1 ≤ x) : eStarInt x = eStarIntG x :=
  (eStarInt_eq_F x hx).trans (eStarIntF_eq_G x)

theorem eStar_eq_G (x : ℚ) : eStar x = eStarG x := by
  unfold eStar eStarG
  split_ifs with h
  · rw [eStarInt_eq_G x h]
  · rfl

theorem termUnits_eq_G : termUnits = termUnitsG := by
  funext a b
  unfold termUnits termUnitsG
  rw [eStar_eq_G]

end BetaIrr.I3.CertA
