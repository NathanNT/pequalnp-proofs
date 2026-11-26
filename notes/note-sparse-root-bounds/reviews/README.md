# Review record

The note was reviewed twice by AI systems acting as critical referees. These are not academic peer reviews, and no
human mathematician took part.

| round | version reviewed | referee | verdict | files |
|---|---|---|---|---|
| 1 | version 1 | OpenAI GPT-6 Astra (`gpt-6-astra`), reasoning effort xhigh | minor revision | `round1-report-gpt-6-astra.md`, `round1-response.md` |
| 2 | version 2 | OpenAI GPT-6.2 Astra (`gpt-6.2-astra`), reasoning effort xhigh | major revisions required | `round2-report-gpt-6.2-astra.md`, `round2-response.md` |
| 2, confirmation | version 3 | the same referee, same session | minor revisions required | `round2-confirmation-gpt-6.2-astra.md`, `round2-confirmation-response.md` |

In both rounds the referee worked in a copy of the submission (manuscript, Lean files, the eighteen repository files,
programs and data) with access to Lean, Python and the web, and was asked to check every statement independently and
to look for errors, unsupported claims, missing or wrong credit, and defects of exposition. In round 2 it was also
asked for simpler proofs where they exist and for a recommended text for the post proposing the note.

The reports are reproduced verbatim, except that in the round 2 report three passages about the content of the
supplementary files, which have no mathematical content, are omitted and marked as such, and the address of the
hosting repository is replaced by a placeholder. The instructions given to the referee are not reproduced.

Statement numbers changed between versions. The round 1 report refers to version 1 (sections 0 to 9, items N1 to
N7), its reply to version 2, and the round 2 report to version 2. The published note is version 3 with the
corrections of the confirmation pass; in it the disclosure of AI involvement was moved from the paper to the
README of this directory and to the post proposing the note, and the paper was reformatted.

What the two rounds verified independently of the author's programs: the sign patterns of the three-cube, four-cube
and five-cube examples in exact arithmetic; the gluing lemma; the moment formulas and the identity of order 9; the
compilation of the Lean files; and the computation behind Proposition 13. For that computation, round 1
independently checked the cases with at most two linked pairs and reran the supplied program for the cases with
three; round 2 independently checked all 4,179,296 triples, including those with three linked pairs. What the
reviews changed: see the replies. After the reply to round 2, the referee of round 2 examined version 3 in a
confirmation pass (`round2-confirmation-gpt-6.2-astra.md`); its verdict was "minor revisions required", and the
remaining corrections it lists were made (`round2-confirmation-response.md`).
