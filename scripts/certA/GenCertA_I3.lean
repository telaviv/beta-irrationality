/-
# Generator for the A-certificate data files (`BetaIrrational/CertA/Ev*.lean`).

Run from `lean_beta/`: `lake env lean scripts/certA/GenCertA.lean` (writes `scripts/certA/gen_I3.txt`,
~30 s), then `python scripts/certA/gen_certA_files.py`. The output is untrusted: every claim in the
generated files is re-checked by `decide +kernel`.
-/
import BetaIrrational.I3.CertAK.Windows
import BetaIrrational.I3.CertAK.FastG
namespace BetaIrr.I3.CertA

def chunksOf (n : ℕ) : ℕ → List ℚ → List (List ℚ)
  | 0, _ => []
  | _, [] => []
  | f + 1, l => l.take n :: chunksOf n f (l.drop n)

def qs (q : ℚ) : String := if q.den = 1 then s!"{q.num}" else s!"{q.num}/{q.den}"

def genOut : IO Unit := do
  let h ← IO.FS.Handle.mk "scripts/certA/gen_I3.txt" IO.FS.Mode.write
  let mut tot : ℤ := 0
  for j in List.range 133 do
    let l := win j
    let cs := chunksOf 32 1000 l
    h.putStrLn s!"W {j} {l.length} {(l.head? == some (bnd j))}"
    let nk := cs.length
    for k in List.range nk do
      let c := cs.getD k []
      let nxt := if k + 1 < nk then (cs.getD (k+1) []).headD 0 else bnd (j + 1)
      let v := pairSum termUnitsG (c ++ [nxt])
      tot := tot + v
      h.putStrLn s!"C {v} {String.intercalate " " (c.map qs)}"
  h.putStrLn s!"T {tot}"
  h.flush

#eval genOut
end BetaIrr.I3.CertA
