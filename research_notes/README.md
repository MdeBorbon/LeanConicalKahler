# Research notes

Mathematical notes that are **not** Lean proofs. Nothing here is kernel-checked. Nothing here
should be cited as a formalised result.

| File | Content |
|---|---|
| `PROPOSITION_2_5_AUDIT.md` | Audit of Proposition 2.5 (interior `L²` Hessian bound) of de Borbon–Edwards, arXiv:2002.07668v1, by M. de Borbon with ChatGPT. It covers the missing boundary term, the `W^{2,2}` issue, a localised Bochner repair, and the proof obligations. |
| `prop_2_5_checks.py` | Independent symbolic checks (sympy) of the audit's computations. Run `python3 -I research_notes/prop_2_5_checks.py`. |

The verified conclusions are recorded in `../PAPER_REVIEW.md`: V9 and V10 (confirmed errors in the
arXiv proof), S1 (remaining gaps) and §C (the proposed repair, not established). That file also
records the points where this review adds to the audit.
