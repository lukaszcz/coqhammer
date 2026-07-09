# External Program/Equations-heavy corpus selection

Candidates considered for the Phase 6 dependent/external evaluation slice:

- **Coq-Equations** (`mattam82/Coq-Equations`) — canonical Equations-heavy
  development, LGPL-2.1-compatible, actively maintained for recent Rocq
  releases. It stresses dependent pattern matching, generated elimination
  principles, Program/WF obligations, and equation lemmas.
- **Interaction Trees** (`DeepSpec/InteractionTrees`) — large and actively used,
  but the dependency stack is substantially heavier and less suitable as the
  first critical-path harness port.
- **std++** (`coq-stdpp`) — license-compatible and broad, but it is less focused
  on Program/Equations-generated definitions than the extraction plan requires.

Choice: **Coq-Equations**. The harness adapter accepts a local checkout via
`./prepare-corpus.sh external-equations --source /path/to/Coq-Equations` and
copies its `.v` files into `eval/problems` for the standard `hammer_hook` flow.
The committed `sample/` file is a small Program/WF smoke test used when a local
checkout is not available; it keeps dry-runs reproducible in minimal CI images
while preserving the same harness path.
