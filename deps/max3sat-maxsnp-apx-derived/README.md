# MaxSNP-completeness and APX-completeness of MAX-3-SAT and 3-OCCURRENCE MAX-3-SAT (the PCP theorem and hardness of approximation) in Lean 4

A Lean 4 proof of the classical hardness-of-approximation results that follow from the PCP
theorem, together with the PCP theorem itself in a witness-recovering form, for an explicit
Turing-machine model. The statement is the self-contained `Challenge.lean` (Lean core only,
at most 1,000 lines and 100 KiB), the proof is `Solution.lean`, and `comparator.json` tells
Comparator to check that they agree. The proof depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`; nothing is assumed as a hypothesis.

## What it proves

`Challenge.lean` states nine theorems (namespace `Complexity`):

```lean
theorem pcp_gap : ∃ num den : Nat, 0 < num ∧
    ∀ L : Language, InNP L → ∃ g : Word → SAT.CNF, GapReduction num den L g
theorem pcp_theorem (L : Language) : InNP L ↔ ∃ c q, InPCP c q L
theorem npo_maxSNP0 (ga sa : List Nat) (k : Nat) (φ : QF) : NPO (maxSNP0 ga sa k φ)
theorem maxSNPHard_no_ptas {P : OptProblem} (hP : MaxSNPHard P)
    (h : ∀ k, P.ApproximableWithin (k + 2) (k + 1)) : PEqNP
theorem maxSNPHard_not_hasPTAS {P : OptProblem} (hP : MaxSNPHard P) (h : P.HasPTAS) : PEqNP
theorem max3SAT_maxSNPComplete : MaxSNPComplete max3SAT
theorem max3SAT3_maxSNPComplete : MaxSNPComplete max3SAT3
theorem max3SAT_apxComplete : APXComplete max3SAT
theorem max3SAT3_apxComplete : APXComplete max3SAT3
```

In words:

1. **PCP theorem, gap form** (ANONYMIZED–ANONYMIZED–ANONYMIZED–ANONYMIZED–ANONYMIZED): for a fixed fraction
   `num / den > 0`, every NP language reduces in polynomial time to 3-SAT so that members give
   satisfiable formulas and non-members give formulas of which every assignment leaves at
   least the fraction `num / den` of the clauses unsatisfied.
2. **PCP theorem, verifier form** (ANONYMIZED–ANONYMIZED; ALMSS): `NP = PCP(O(log n), O(1))`.
3. **The problems of the syntactic class MaxSNP₀ are in NPO** (a check on the definition:
   solutions are polynomially bounded, and feasibility and value are polynomial-time).
4. **MaxSNP-hard problems have no PTAS unless P = NP**, in two forms: no family of
   polynomial-time algorithms achieving every ratio `1 + 1/(k+1)` (one algorithm per `k` is
   allowed), and no uniform approximation scheme.
5. **MAX-3-SAT and 3-OCCURRENCE MAX-3-SAT are MaxSNP-complete** (ANONYMIZED–ANONYMIZED 1991;
   ANONYMIZED 1994, Thm 13.10), MaxSNP being the class of NPO problems L-reducible to a
   problem of the syntactic class MaxSNP₀.
6. **Both are APX-complete**, APX-hardness being with respect to PTAS-reductions
   (ANONYMIZED–ANONYMIZED).

The definitions, all in `Challenge.lean` with docstrings:

* **Machines, P, NP** (reused verbatim from the NP-completeness foundation `NPCompleteness-Lean4`,
  commit `3e603e795b44fedcf7d6dd65b7d1e30547ead925`):
  deterministic single-tape Turing machines over {blank, 0, 1, separator}, time = number of
  steps, polynomial bounds `c * (n + 1) ^ k`, `PolyTime f`, `InP`, `InNP` by verifiers and
  polynomially bounded certificates; `PEqNP` means every NP language is in P.
* **Formulas**: CNF formulas over natural-number variables, coded by `SAT.encode` with unary
  indices; `SAT.satCount a f` counts satisfied clauses; `SAT.assignmentOf y` reads a word as an
  assignment.
* **PCP**: `GapReduction num den L g`; `InPCP c q L` — a polynomial-time non-adaptive verifier
  that maps the input and a random string of `c * log₂(|x| + 2)` bits to a CNF formula over at
  most `q` proof bits, with perfect completeness and soundness `1/2`.
* **Optimization**: `OptProblem` (a direction and a relation `Sol x y v`), `IsOpt`,
  `ApproximableWithin a b`, `HasPTAS`, `NPO`, `LReducible`, quantifier-free formulas `QF`,
  structures of a signature (`Relations.Fits n ar`: one relation per arity in `ar`, each a list
  of distinct tuples of that arity over the universe `{0, …, n - 1}`), well-formed formulas
  (`QF.WellFormed ga sa k`), the syntactic class `maxSNP0 ga sa k φ` (instances: structures of
  the input signature `ga`; solutions: structures of the solution signature `sa` on the same
  universe), `InMaxSNP` (NPO problems L-reducible to `maxSNP0 ga sa k φ` for a well-formed `φ`),
  `MaxSNPHard`, `MaxSNPComplete`, `InAPX`, `PTASReducible`, `APXHard`, `APXComplete`, and the
  problems `max3SAT` and `max3SAT3`.

`formalization.yaml` (`fidelity.divergences`) lists every convention a reader should know.

## How the proof goes

| Part | Directory | Lines |
| --- | --- | --- |
| Machine model, ANONYMIZED–ANONYMIZED, register programs, witness extraction, statement definitions | `Complexity/` | 20,200 |
| OpenAI's gap amplification, expanders and their machines (adapted from ANONYMIZED) | `OAI/` | 75,600 |
| Simulation of Mathlib's multi-stack machines by the single-tape model | `Bridge/` | 1,150 |
| A framework for polynomial time on coded data (`PT f`, with `fun_prop`) | `PT/` | 3,800 |
| The PCP, MaxSNP and APX results | `Hardness/` | 13,100 |

* **Gap form.** The ANONYMIZED–ANONYMIZED reduction (`Complexity/`) is composed with the 3-CNF gap map of
  the Lean formalization of the Unique Games theorem in the
  [OpenAI mathematics repository](https://github.com/openai/math) (`OAI/`, OpenAI's gap
  amplification), whose polynomial time is proved there for Mathlib's multi-stack machines and
  carried over by `Bridge.stack_of_tm2`; encoding converters glue the two formula
  representations (`Hardness/GapPCP.lean`, `Hardness/Final/`).
* **Verifier form.** The verifier samples `2·den` clauses of the gap formula with `O(log n)`
  random bits; conversely a PCP verifier is checked deterministically over all random strings
  (`Hardness/Verifier/`).
* **No PTAS.** MAX-3-SAT L-reduces to every MaxSNP-hard problem, L-reductions transfer
  approximation schemes, and an approximation scheme for MAX-3-SAT decides the gap
  (`Hardness/MaxSNP/`).
* **MaxSNP₀ is in NPO.** A lenient polynomial-time parser for codes of relations, a check of
  the signatures, and a size bound for structures of a fixed signature
  (`Hardness/MaxSNP/NPO.lean`).
* **MaxSNP-completeness.** An explicit quantifier-free formula puts MAX-3-SAT in MaxSNP₀, and
  every MaxSNP₀ problem L-reduces to it by one clause per falsifying pattern of the atoms,
  split into 3-clauses, with an averaging bound; an assignment is mapped back to the structure
  of the solution signature that it writes (`Hardness/MaxSNP/Hard/`). For 3-OCCURRENCE
  MAX-3-SAT, copies of each variable are linked along an explicit constant-degree expander and
  then by a torus gadget of implications (`Hardness/Occ/`, `Hardness/Expander/`).
* **APX-completeness.** APX-hardness needs the PCP theorem with *witness recovery*. This is
  proved here: an explicit deterministic decoder for the gap map (`Hardness/Decode/`), written as
  list programs and shown polynomial-time (`Hardness/DecodeList/`, `Hardness/Witness/`), turns
  every assignment satisfying more than the fraction `1 - num/den` of the clauses back into an
  NP certificate. Every APX problem then PTAS-reduces to MAX-3-SAT by a threshold construction
  (`Hardness/APX/`), and APX-hardness passes to 3-OCCURRENCE MAX-3-SAT along the L-reduction.

## Reused code and licences

* `OAI/Computability/UniqueGames/` (194 files) is adapted from
  [openai/math](https://github.com/openai/math) at commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (Apache-2.0, licence in `OAI/LICENSE`). Every file
  starts with a comment naming its source file and listing the changes: conversion to the Lean
  module system (`module`, `public import`, `@[expose] public section`, `private` removed),
  a few proof adjustments for the module system and Lean v4.35.0-rc2, a count-form restatement
  of one theorem, and an opaque wrapper for one large constant (`RoundTables.sizeFactor`) so that
  the NanoDa checker does not try to unfold it. `PCP/GapTheorem.lean` is new, extracted from the
  upstream `TableGapReductionLemmas.lean`. Only the files needed for the gap map are included.
* `Complexity/` contains the part of the `Complexity` library of the NP-completeness
  foundation `NPCompleteness-Lean4` (Apache-2.0, commit
  `3e603e795b44fedcf7d6dd65b7d1e30547ead925`) needed for the ANONYMIZED–ANONYMIZED reduction: 75 files,
  byte-identical to that commit, plus new modules `Complexity/Reg/`, `Complexity/Witness/`,
  `Complexity/PCP/`, `Complexity/Approx/`. In this derived packaging (`DERIVED.md`) the 75
  files are provided by that package and the new modules are under `ComplexityExt/`.
* [`docs/PROVENANCE.md`](docs/PROVENANCE.md) lists the origin of every Lean file: 194 adapted
  from openai/math (with their upstream paths and changes), 75 taken unchanged from
  NPCompleteness-Lean4, and 108 written for this project.

## Checking it

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get        # Mathlib v4.35.0-rc2 build cache
lake build                # Solution and everything it imports (about 25 minutes on 2 cores)
python3 scripts/generate_challenge.py
lake build Challenge
lake comparator --config comparator.json --paranoid   # needs bubblewrap
```

`scripts/verify_all.sh` runs the same steps after the repository checks
(`scripts/check_repository.py`: layout, `module` headers, at most 10,000 lines per file, no
`sorry`, `admit`, `native_decide` or `axiom` outside the Challenge, the Challenge's limits and
imports, `comparator.json` and `formalization.yaml`); `scripts/generate_challenge.py --check`
confirms that `Challenge.lean` is generated from the library's own declarations. Files
importing much of `OAI/` need up to about 5 GB of memory each. `docs/VERIFICATION.md` records
the runs. On GitHub, `.github/workflows/verify.yml` repeats these steps.
