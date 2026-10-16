# What you have to trust

## Axioms

`lake env lean Axioms.lean` prints, for the main theorem and each of its main ingredients,

```
'BetaIrr.I3.oneOfBeta4To36' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms, the same ones Mathlib uses. The project contains no `sorry`, no `axiom`
declaration and no `native_decide`, so nothing relies on the compiler.
- The A-certificate and the saddle-point certificate are decidable statements about rational data, proved by
  `decide +kernel`.
- The 58 logarithm enclosures of the real-axis bound (`I3/Size/PhiNum.lean`) are proved by `norm_num` from Mathlib's
  series bounds for `log`.

Every proof is checked by the kernel.

One caveat. Two helper functions in the A-certificate code (`gAcc`, `gAccF`) carry `@[implemented_by …]` attributes.
These affect compiled code only, i.e. the `#eval` generator scripts. The kernel never uses them, and they add no axiom.

## The statement

The kernel checks the proof. It cannot check that the statement means what we claim, so read these definitions yourself:

| file | definition |
|---|---|
| `BetaIrrational/Defs.lean` | `dirichletBeta s := ∑' m : ℕ, (-1)^m / (2m+1)^s`, with `summable_betaTerm` for `s ≥ 2`. The `tsum` is therefore the genuine sum of the series. |
| `BetaIrrational/Statement.lean` | `OneOfBeta4To36 := ∃ j ∈ Finset.Icc 2 18, Irrational (dirichletBeta (2 * j))`, i.e. one of β(4), β(6), …, β(36) |

`Irrational` is Mathlib's (`x ∉ Set.range ((↑) : ℚ → ℝ)`).

## Generated files

Some Lean files contain large literal data produced by scripts: event lists, polyline vertices and rational
enclosures. The scripts and their output are **untrusted inputs**. Every claim about the data is re-proved by the
kernel, so a wrong value makes the build fail; it cannot make a false theorem true.

| data | Lean files | generator |
|---|---|---|
| A-certificate (62,132 event points, 62,131 intervals, 1,995 chunks) | `I3/CertAK/EvData.lean`, `EvWin*.lean`, `EvSorted.lean`, `EvSum*.lean`, `CertCompute.lean` | `scripts/certA/GenCertA_I3.lean` (`#eval`) + `scripts/certA/gen_certA_files.py` |
| Φ enclosures on the real axis | `I3/Size/PhiNum.lean` | `scripts/size/gen_phinum_I3.py` |
| steepest-descent polyline, saddle boxes | `I3/Interval/PolyDataI3.lean`, `SaddleI3.lean`, `UpChunk*.lean`, … | ad hoc Python (RK4 trace + simplification), not included |

## How the A-certificate is kernel-checked

The specification (`I3/CertA/Defs.lean`: `eStar`, and `events` built with `List.mergeSort`) is what the soundness proofs
use. The kernel cannot evaluate it directly: `List.mergeSort` is well-founded recursion, and the naive `eStar` costs
seconds per point. So the proof goes through equivalent forms, each with a general proof:

| step | file | statement |
|---|---|---|
| fast e* | `I3/CertAK/Fast.lean`, `FastG.lean` | `termUnits = termUnitsG`: e* is a max of closed forms using only `Nat` arithmetic. Each I3 point takes about 0.15 s in the kernel. |
| sort | `I3/CertAK/EvSort.lean` | `msort`, a structural merge sort that permutes its input whatever the comparator |
| windows | `I3/CertAK/Windows.lean` | if each window's sort equals a literal list and their concatenation is strictly increasing, that concatenation is `events 400` |
| chunks | `I3/CertAK/Windows.lean` | `pairSum` over concatenated chunks equals the sum of the chunk sums |

The generated files then check, by `decide +kernel`:
- each window;
- the monotonicity of the concatenation;
- each chunk sum.

`CertCompute.lean` assembles these into `bodyUnits 400 = N`.

## Cross-checks outside Lean

These are not needed for correctness, but they agree:

- **A-certificate.** The value `bodyUnits 400 = 1243345293752876677540040193981` (units of 2⁻⁹⁶) agrees exactly with an
  independent exact-rational Python implementation.
- **Saddle certificate.** The certified saddle value Re Ω ∈ [−29.7790173, −29.7790172] agrees with two independent Arb
  (ball-arithmetic) implementations.

## Cost

- A cold `lake build` takes more than an hour on a desktop with 16+ GB of RAM. The A-certificate dominates:
  - about 2.6 CPU-hours of chunk sums plus about 1 CPU-hour of window checks;
  - run as three parallel import chains, with up to about 4 GB resident per process.
- The interval certificate takes about 30 CPU-minutes.
