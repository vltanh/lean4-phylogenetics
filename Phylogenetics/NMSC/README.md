# The quartet concordance factors of a cycle under the NMSC

This directory defines nothing new: it proves, from the definition of the network multispecies
coalescent (NMSC) on metric level-1 networks in [`Phylogenetics/Defs.lean`](../Defs.lean), the
quartet concordance factors (CFs) that the NMSC gives to the components of a cycle
([`Phylogenetics.nmsc_quartetCF`](Cycle.lean#L743)). They are the CFs of the induced metric
quarnets (Baños 2019). The property [`Phylogenetics.NMSCQuartetCF`](../Defs.lean#L362) of a family
of CFs says that it is given by these formulas; `Phylogenetics.nmsc_quartetCF` proves this property
for the cycles of every well-formed network, so a result stated under the property holds for them.

## Sources

- H. Baños, *Identifying species network features from gene tree quartets under the coalescent
  model*, Bull. Math. Biol. 81 (2019) 494–534: under the NMSC, the distribution of the unrooted
  gene tree on four taxa depends only on the induced metric quarnet; the CFs of a level-1 4-cycle
  quarnet are the formulas of the second case of the [statement](#statement) below.
- The quartet-tree CFs of the multispecies coalescent: the quartet tree with internal edge of
  length `t` has CFs `1 - (2/3)e^{-t}`, `(1/3)e^{-t}`, `(1/3)e^{-t}`; see e.g.
  E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from the
  distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011) 833–862,
  Section 4.1.
- The NMSC itself: Nakhleh (2011); Yu, Degnan, Nakhleh (2012). Kingman's coalescent on forests of
  gene lineages, with its transition probabilities as a matrix exponential and its absorption above
  the root, is defined in [`Phylogenetics/MSC/Defs.lean`](../MSC/Defs.lean).

## The model

The definitions are in the block of [`Phylogenetics/Defs.lean`](../Defs.lean) between its marker
comments. The block is self-contained, given Mathlib and the block of
[`Phylogenetics/MSC/Defs.lean`](../MSC/Defs.lean), so that a project's `Challenge.lean` can copy
both verbatim (Comparator needs the same constants in the Challenge and the Solution).

- **Networks.** `Phylogenetics.Net X` (with `Phylogenetics.Side X`) describes a rooted binary
  level-1 network recursively from its root: a leaf, a tree node on no cycle, or the top node of a
  cycle with its two sides, which lead to the hybrid node. Every binary rooted level-1 network has
  such a description, and every well-formed description with at least two leaves is one
  ([`Phylogenetics.MetricDigraph.isNetwork_iff_exists_net`](../Graph/Correspondence.lean#L29), in
  [`Phylogenetics/Graph/`](../Graph)). [`Net.WellFormed`](../Defs.lean#L138): positive edge
  lengths, inheritance probabilities in `(0, 1)`, no cycle of two edges, distinct leaf labels.
- **The NMSC.** `Net.forestDist s N` is the distribution of the forest of gene lineages at the root
  of `N` (the lineage `l` is sampled from the taxon `s l`). Along every edge the lineages coalesce
  by Kingman's coalescent; at a tree node and at a node of a side, independent forests form one
  forest; at a hybrid node every lineage independently takes the hybrid edge of `γ` with
  probability `γ`. [`Net.geneTreeDist`](../Defs.lean#L208) adds the population above the root,
  of infinite length.
- **Quartet CFs.** `Net.quartetCF N a b c e` samples one lineage from each of the four taxa and
  is the probability that the unrooted gene tree has the split `ab|ce`. Gene trees in practice have
  all the taxa; the restriction of such a gene tree to four taxa has the distribution of the gene
  tree of four lineages (sampling consistency of the coalescent,
  [`Phylogenetics.Net.geneTreeDist_restrict`](Consistency.lean#L537)), so the CF is the
  probability that the gene tree on all the taxa displays `ab|ce`
  ([`Phylogenetics.quartetCF_eq_displays`](Displays.lean#L148)).
- **Cycles.** `Net.Cycle N` is a cycle of `N` (its top node's subnetwork among `N.subnets`), with
  its components in their cyclic order around the cycle (`Ω.component i`, `C₀` hybrid, `C₁` on the
  side of `γ`), its size `d = Ω.size` (the number of components), and the lengths `Ω.edgeLen m` of
  its edges in the semi-directed network (where the root, if it is the top node of the cycle, is
  suppressed).

## Statement

[`Phylogenetics.nmsc_quartetCF`](Cycle.lean#L743): for a well-formed network `N`, a cycle `Ω` of
size `d`, the metric cycle `M` with the inheritance probability and edge lengths of `Ω`, a labelling
`ord` of the components and a choice `x` of one taxon in each, the component CFs
`N.componentCF x a b c e = N.quartetCF (x a) (x b) (x c) (x e)` of distinct labels are
`cycleCF M` at the positions of the components:

- if `C₀` is not among them: the CF of the quartet tree obtained by opening the cycle at the
  hybrid node, the four components hanging from the path `C₁ — ⋯ — C_{d-1}` (a tree quarnet);
- otherwise: `γ` times the CF of the displayed tree in which `C₀` hangs next to `C₁`, plus
  `1 - γ` times the CF of the displayed tree in which `C₀` hangs next to `C_{d-1}` (a network
  quarnet).

## The proof

| File | Content |
| --- | --- |
| [`Basic.lean`](Basic.lean) | Good (binary) forests; adding an independent forest; Kingman facts (rows are distributions on good forests containing the start; relabelling; one root stays; two roots merge with probability `1 - e^{-t}`); the score of a forest of four lineages |
| [`Process.lean`](Process.lean) | The coalescent with given forests at the leaves; substitution of networks for leaves; relabelling; support and total mass; a network with at most one sampled lineage returns it; at a hybrid node one lineage takes the side of `γ` with probability `γ` |
| [`Symmetry.lean`](Symmetry.lean) | Nice kernels; the expected score is invariant from three lineages on (persistence of coalesced pairs, symmetry under relabellings of the uncoalesced lineages) |
| [`Context.lean`](Context.lean) | The rest of the network around a cycle is a network with one hole; its kernel, followed by the population above the root, is nice; so the quartet CF is the expected score of the forest at the top node of the cycle |
| [`Arms.lean`](Arms.lean) | The displayed tree: two arms of a path meeting at the top node; the expected score at the top node is the quartet-tree CF of the induced positions (the node where the third lineage joins; the pairs that may coalesce before it) |
| [`Cycle.lean`](Cycle.lean) | The components and edges of the cycle as positions on the arms; the two placements of the hybrid lineage; [`Phylogenetics.nmsc_quartetCF`](Cycle.lean#L743) |
| [`Consistency.lean`](Consistency.lean) | Sampling consistency: restricting the coalescent to a subset of the lineages gives the coalescent of that subset (Kingman's lumpability, [`Phylogenetics.kingmanTransition_lump`](../MSC/Marginal.lean#L381); at a hybrid node the choices of the other lineages sum out) |
| [`Displays.lean`](Displays.lean) | The quartet CF is the probability that the gene tree on all the lineages displays the quartet, for any assignment of the lineages to taxa ([`Phylogenetics.quartetCF_eq_displays_sample`](Displays.lean#L109); one lineage per taxon: [`Phylogenetics.quartetCF_eq_displays`](Displays.lean#L148)) |
| [`GeneTrees.lean`](GeneTrees.lean) | The gene trees of the NMSC: a probability distribution ([`Phylogenetics.Net.sum_geneTreeDist`](GeneTrees.lean#L113)), so the quartet CFs lie in `[0, 1]`; every gene tree in its support is a hierarchy ([`Phylogenetics.geneTreeDist_isHierarchy`](GeneTrees.lean#L148)), whose displayed quartets are transitive |
| [`Sampling.lean`](Sampling.lean) | Gene trees drawn from the NMSC: the probability that one displays a quartet of taxa from four distinct components is their component CF, and i.i.d. gene trees are identically distributed (for estimating CFs from a sample of gene trees) |
| [`Instance.lean`](Instance.lean) | The formulas themselves satisfy [`Phylogenetics.NMSCQuartetCF`](../Defs.lean#L362), so a result stated under the property applies to the formulas of an explicit metric cycle |

The argument is the usual one for the coalescent: lineages of a component other than the root's
reach the cycle one at a time; once three lineages are together and uncoalesced, the rest of the
network treats them alike, so each of the three splits has probability `1/3`; before that point
only pairs can coalesce, with probability `1 - e^{-t}` along a path of length `t`.
