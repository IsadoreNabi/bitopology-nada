# Bitopological Spaces from Directed Graphs

Reproducibility repository for the paper
*Bitopological Spaces from Directed Graphs: Extending the Nada
Construction to Capture Temporal Irreversibility*
(José Mauricio Gómez Julián, 2026).

## Contents

- `paper/directed_nada_bitopology.tex` — LaTeX source of the paper.
- `paper/directed_nada_bitopology.pdf` — Compiled PDF.
- `paper/reproducibility.Rmd` — R Markdown document that regenerates
  Table 1 of the paper from the FRED series `GDPC1` using the
  [`topologyR`](https://github.com/IsadoreNabi/topologyR) package.
- `paper/GDPC1_snapshot.csv` — Frozen snapshot of the FRED `GDPC1`
  series used in the paper, so the results are bit-exact reproducible
  under later BEA revisions.
- `BitopologyNada/` — Lean 4 formalization of the main theorems
  against `mathlib4`, built as a Lake project rooted at this directory.
- `lakefile.toml`, `lean-toolchain`, `BitopologyNada.lean` — Lake /
  Lean configuration.

## Reproducing the paper

### PDF of the paper
```bash
cd paper
pdflatex directed_nada_bitopology.tex
pdflatex directed_nada_bitopology.tex
pdflatex directed_nada_bitopology.tex
```

### Empirical results (Table 1)
Requires R ≥ 4.0 and the `topologyR` package:
```r
# install.packages("remotes")
remotes::install_github("IsadoreNabi/topologyR")
```
Then:
```bash
cd paper
Rscript -e 'rmarkdown::render("reproducibility.Rmd")'
```
The Rmd uses the local `GDPC1_snapshot.csv` to guarantee bit-exact
reproduction of the paper's Table 1. If the snapshot is removed, the
Rmd falls back to a live FRED download.

### Formal proofs
Requires Lean 4 (via `elan`) and a `mathlib4` cache:
```bash
lake exe cache get   # optional but much faster
lake build
```
Mathlib pin: `v4.29.0`.

## Citation

If you use this work, please cite the paper (BibTeX entry to appear
upon publication) and the `topologyR` package.

## License

Code is released under the MIT License (see `LICENSE`). The paper
itself (LaTeX source and PDF) is distributed under CC BY 4.0.
