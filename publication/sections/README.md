# Publication sections

The `Qxxx.tex` files are generated from the audited Markdown answers by
`publication/build_sections.py`; do not edit them by hand. Run
`python3 proof_pipeline.py render` to regenerate the verified set and the master
document. The generator supplies the informal verdict and the exact Lean scope
recorded in `pipeline.json`; `main.tex` supplies section headings and evidence links.
