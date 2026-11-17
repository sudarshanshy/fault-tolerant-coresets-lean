# Authoritative source

**Fault Tolerant Coresets**, Milind Prabhu, Chris Schwiegelshohn, Sudarshan Shyam.

The included `coreset_notes.pdf` is a byte-for-byte copy of the attachment
`coreset_notes (29).pdf` supplied in the referenced conversation (39 pages).

SHA-256:

```
64ea6452deb990517e2e33f0133a90761956ba10692dfda35090cdc15186b6d9
```

Relevant pages in the PDF:

- Page 5: model, nonnegative weighted losses, Definition 2.1.
- Pages 6–7: Lemma 3.2, Algorithm 1, Theorem 3.1 and its proof.
- Page 8: Theorem 4.1 and the constrained finite-metric reduction; Theorem 4.2
  and its conditional sensitivity-approximation hardness statement.
- Page 16: Theorem A.1 and the proxy-sampling entry bound.
- Pages 17–18: Claim A.2 and the proof of Theorem 3.4.
- Page 19: Definition B.1 and the added-point metric reduction proving
  Theorem 4.2.

Theorem 4.2 is formalized as a conditional hardness transfer with the base
gap-k-means hardness as an explicit premise. The cited external hardness
theorem of Guha and Khuller is not reproved. See the README for the exact
bit-cost model used by the complexity statements. No results from a different
paper revision are used.
