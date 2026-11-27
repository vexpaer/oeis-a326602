# OEIS A326602 — Independent Lean 4 formalization

**Author:** Ximing Wang · 27 November 2026

[Original manuscript PDF (Nov 27; superseded by revised source)](paper/oeis_a326602_paper.pdf) · [Revised LaTeX source (Nov 28)](paper/oeis_a326602_paper.tex) · [Original source bundle](original/oeis-a326602-lean.zip)

## Result

Paul D. Hanna conjectured in 2019 that the coefficients of [OEIS A326602](https://oeis.org/A326602) are odd precisely at square indices. Let

$$A(x)=\sum_{n\ge0}\frac{(x^{2n}+x)^n}{(1+x^{2n+1})^{n+1}}\in\mathbb Z[[x]],\qquad a(n)=[x^{2n}]A(x).$$

The supplied proof establishes the signed multinomial triple-sum identity, evenness of the series, and `Odd (a n) ↔ ∃ b : ℕ, n = b ^ 2`. The argument pairs triples under the involution swapping the first and third coordinates; nonzero diagonal terms are even by the central binomial coefficient identity.

The supplied manuscript reports a successful Lean 4.33.1 build and standard axioms only. Independent CI reproduction is separate from that report; see [Actions](https://github.com/vexpaer/oeis-a326602/actions). No claim of independently established priority or peer review is made. This work was developed with AI assistance.

## Reproduce

The original ZIP contains the exact 781-line source. The readable source at `FormalConjectures/OEIS/326602.lean` is a whitespace-normalized copy from the supplied Google Docs file. The verification script compares the two ignoring blank lines and surrounding whitespace and uses the exact ZIP source.

```sh
bash scripts/verify.sh
```

The script checks out Formal Conjectures at `f606af160664c5a10952e9a957b100a1cd45bbeb` (Lean 4.33.1), builds the module and prints the axioms of the five central theorems and four initial-value checks. No changes are pushed to upstream.

## Prior proof and contribution

The mathematical proof was previously published on November 1, 2026 in [trureturing Issue #25051](https://github.com/the-omega-institute/trureturing/issues/25051). That proof already contains the multinomial expansion, symmetry involution, central-binomial parity argument and evenness. The present project was developed separately and credits that prior proof; its contribution is a Lean formalization of the defining power series and the resulting coefficient and parity identities. No mathematical or formalization priority is claimed. Generative AI was used substantially in proof development, Lean implementation, manuscript drafting and the subsequent literature review.

## Related work and citation

- [OEIS A326602](https://oeis.org/A326602), Hanna (2019).
- [OEIS A323557](https://oeis.org/A323557), a related series; [AlphaProof Nexus Lean proof](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/OEIS/oeis_323557_conjecture_0.lean) for its distinct pronic-index parity implication uses a related involution argument.
- [Citation metadata](CITATION.cff). Cite the version-specific Zenodo DOI when available.

## License

Lean source retains its Apache-2.0 notice; see [LICENSE](LICENSE). Original manuscript materials are available under [CC BY 4.0](LICENSE-PAPER). Third-party dependencies retain their own licenses.
