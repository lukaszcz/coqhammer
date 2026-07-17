# Extraction confirmation artifacts

No confirmation metrics for the current source tree are committed here. Run
`../../evaluate.sh confirmation` from `eval/` to generate `summary.tsv`,
`analysis.md`, and `provenance.env` after a complete run.

The generated provenance records the current repository commit, configuration
manifest, corpora, scripts, and timeout settings. Treat summaries as valid only
together with that provenance file.
