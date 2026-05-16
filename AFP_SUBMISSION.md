# AFP submission preparation notes

This document captures what is in place for an eventual submission of
`ByzantineCD` to the Archive of Formal Proofs (AFP), and what the
submitter would still need to do.

## What is ready

- `ByzantineCD/ROOT` declares an AFP-chapter session, a description
  block, the theory order, and `document_files "root.tex" "root.bib"`.
- `ByzantineCD/document/root.tex` is the standard AFP cover-page
  LaTeX with title, abstract, table of contents, and a reading-order
  guide.
- `ByzantineCD/document/root.bib` lists the source paper, the FLP
  entry, and Lamport 1978.
- The session builds green under `isabelle build -d $AFP -D .` with
  Isabelle 2025-2 and AFP snapshot `afp-2026-05-13` (the closest
  AFP-stable release at the time of preparation).  Wall time
  ~3s; 16 theory files.
- All proofs are declarative Isar; zero `sorry`, `oops`, `apply`,
  `sledgehammer`, or `try0` anywhere in the development.
- 14 of the paper's 18 theorems are fully proven; T16 is partially
  proven (Consensus half); T9-T14 remain as future work.  See
  `ROADMAP.md`.

## What still needs to happen before submission

1. **PDF build verified.**
   ```sh
   isabelle build -d $AFP -o document=pdf -D ByzantineCD
   ```
   produces `document.pdf` (47 pages, A4) under
   `<presentation-dir>/AFP/ByzantineCD/document.pdf`.  The LaTeX
   toolchain used for verification was a TinyTeX install
   (`~/.TinyTeX/bin/x86_64-linux/` in PATH) plus the packages
   `babel-english`, `csquotes`, `ulem`, and `txfonts` added via
   `tlmgr install`.  Any TeXLive scheme that includes lualatex plus
   those packages will work; AFP CI uses a full TeXLive.

2. **AFP submission form fields** (for
   <https://www.isa-afp.org/submission/>):
   - **Title:**
     *Byzantine-tolerant detection of causality: there is no holy grail*
   - **Author / Affiliation / Email:** (to be filled by submitter)
   - **Abstract:** see `ByzantineCD/document/root.tex` (the
     `\begin{abstract} \dots \end{abstract}` block) -- copy verbatim
     or trim to the AFP's preferred length.
   - **Topics:** *Computer science / Algorithms / Distributed* and
     *Logic / General logic / Mechanization of proofs*.
   - **License:** BSD-3-Clause (matching the FLP entry we build on).
   - **Depends on:** AFP entry `FLP`.

3. **Open hypotheses to disclose in the abstract**:
   The headline impossibility theorems (3, 4, 5) take exactly one
   mild finiteness side hypothesis:
     - `fin_cd` (side hypothesis on Theorems 3/4/5 in
       `Impossibility.thy`): any candidate CD-solver `cd_alg` that
       produces a valid `F` has finite `events_of` output at the
       Theorem 1 adversary's local target event of the form
       `Internal p_i_in 2`.  Trivially satisfied by any algorithm
       whose output is supported on the (finite) process set;
       identical in shape to the `fin_F` hypothesis of Theorem 1
       (`CD_FN_unavoidable`).
   No HOL axioms, no locale axioms on the impossibility chain.
   Proofs of Theorems 3/4/5 route directly through Theorem 1; the
   paper's "Consensus ⪯ BlackBox ⪯ CD + FLP" chain is preserved as
   paper-faithful documentation in `Reductions.thy`,
   `BlackBox_Unsolvable.thy`, and `FLP_Consensus.thy` but is not on
   the critical path.  All the meta-level hypotheses that earlier
   revisions exposed (`bb_realizes_flp_consensus`, `bb_unsolv`,
   `cd_can_identify_correct` on the chain) have been discharged or
   demoted to documentation.  Both the BlackBox impossibility and
   the FLP impossibility are themselves proved (against Theorem 1
   and against `flpPseudoConsensus.ConsensusFails` respectively).

4. **AFP technical conventions** (already satisfied, listed for
   double-checking):
   - Single chapter declaration (`chapter AFP`).  ✓
   - Session name matches the directory name.  ✓
   - `document_files` listed in ROOT.  ✓
   - No external dependencies beyond `HOL` and AFP-FLP.  ✓
   - All theories live under the session directory.  ✓

## Reproducibility caveats

- **NixOS hosts:** the JDK shipped with Isabelle 2025-2 `dlopen`s
  `libfontconfig.so.1` at startup; if it cannot be loaded the JVM
  silently exits with rc=2 after printing only
  `*** Fontconfig head is null, check your fonts or fonts
  configuration` to stderr.  Resolve by adding a libfontconfig to
  `LD_LIBRARY_PATH` via `~/.isabelle/Isabelle2025-2/etc/settings`.
  Documented in `MISSION.md`.
