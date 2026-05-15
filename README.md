# Byzantine-tolerant causality detection in Isabelle/HOL

Mechanisation of the impossibility results of

> Anshuman Misra and Ajay D. Kshemkalyani,
> **Byzantine-tolerant detection of causality: There is no holy grail.**
> *Parallel Computing* 124 (2025) 103136.
> https://doi.org/10.1016/j.parco.2025.103136

A local copy of the paper is in
[`paper/`](paper/Misra-Kshemkalyani-2025-Byzantine-tolerant-detection-of-causality.pdf).
The article is open access under CC-BY 4.0; the file is redistributed
here under the same license.

## Status of this branch

This (`main`) is the baseline for the formalisation work: the original
mission brief in [`MISSION.md`](MISSION.md) and the source paper.
The actual Isabelle/HOL development lives on a feature branch and is
proposed for merge via pull request.

See [`MISSION.md`](MISSION.md) for:

- The exact scope of the formalisation (Theorems 3, 4, 5 as the
  minimum viable result; out-of-scope items deferred).
- The proof strategy (the paper's two-step reduction
  `Consensus ⪯ Black_Box ⪯ CD` plus FLP).
- The foundation it builds on (AFP entry
  [`FLP`](https://www.isa-afp.org/entries/FLP.html)).
- The working method, declarative-Isar style requirements, and
  definitions of done.

## Licence

BSD-3-Clause (matching the AFP `FLP` entry the development builds
on).  The source paper is open access under CC-BY 4.0 and
redistributed here under that license.
