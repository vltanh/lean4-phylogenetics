# Phylogenetics: phylogenetic trees and networks, the coalescent, and concordance factors, in Lean 4

[![CI](https://github.com/vltanh/lean4-phylogenetics/actions/workflows/ci.yml/badge.svg)](https://github.com/vltanh/lean4-phylogenetics/actions/workflows/ci.yml)

`Phylogenetics` is a Lean 4 library of mathematical phylogenetics on top of Mathlib:

- rooted species trees, Kingman's coalescent on forests of gene lineages, and the multispecies
  coalescent, with its marginalization, coalescent histories and a verified computation of gene
  tree distributions;
- the combinatorics of rooted and unrooted trees, and Steel's theorem that an unrooted tree is
  determined by its quartets;
- rooted metric level-1 networks, as terms and as directed graphs, and the network multispecies
  coalescent: a probability distribution on gene trees, whose quartet concordance factors for the
  components of a cycle are those of the induced metric quarnets (Baños 2019);
- gene trees, the quartets they display, anchor nodes, metric cycles and cyclic orders.

Its declarations live in the namespace `Phylogenetics`. Every declaration depends only on Lean's
standard axioms; there is no `sorry`.

## Using it

Require it in the project's `lakefile.toml`:

```toml
[[require]]
name = "Phylogenetics"
git = "https://github.com/vltanh/lean4-phylogenetics"
rev = "main"            # or a commit hash
```

and import only the modules you use, for example:

```lean
import Phylogenetics.NMSC.Cycle    -- the quartet concordance factors of a cycle of a network
import Phylogenetics.MSC.Marginal  -- marginalization of the multispecies coalescent
```

Lake builds only the imported modules and the modules they import. No module imports all of
Mathlib: each imports the Mathlib modules that it uses. `import Phylogenetics` imports every
module. The library is on Lean `v4.35.0-rc4` and the Mathlib release of the same name.

## Contents

| Directory or module | Content |
| --- | --- |
| [`Phylogenetics.MSC.Defs`](Phylogenetics/MSC/Defs.lean), [`Phylogenetics.MSC.Notions`](Phylogenetics/MSC/Notions.lean) | Rooted species trees with edge lengths (`Phylogenetics.SpeciesTree`, as hierarchies), Kingman's coalescent on forests of gene lineages (`Phylogenetics.kingmanGenerator`, `Phylogenetics.kingmanTransition`, `Phylogenetics.kingmanAbsorption`), the multispecies coalescent and its rooted and unrooted gene tree distributions (`Phylogenetics.SpeciesTree.rootedDist`, `Phylogenetics.SpeciesTree.unrootedDist`); restrictions, induced species trees, rooted triples, and the coalescence probabilities `g_ij(t)`. |
| [`Phylogenetics/Coalescent/`](Phylogenetics/Coalescent) | Forests of gene lineages; the jump chain and the factorization of Kingman's coalescent; Tavaré's formula for the number of lineages (`Phylogenetics.deathProb_eq_tavare`); the population above the root; the unrooted gene tree it produces. |
| [`Phylogenetics/MSC/`](Phylogenetics/MSC) | The multispecies coalescent: basic properties, relabelling taxa, marginalization (`Phylogenetics.SpeciesTree.rootedDist_restrict`), contracting edges of length zero and continuity, several lineages per taxon, coalescent histories. |
| [`Phylogenetics/Hierarchy/`](Phylogenetics/Hierarchy) | Rooted trees as hierarchies: their combinatorics, counts of rooted and unrooted trees, unrooted trees on four and five taxa and their rootings, the location of the root, rooted tree shapes, small species trees; unrooted trees are determined by their quartets (Steel; `Phylogenetics.mem_unroot_iff_quartets`). |
| [`Phylogenetics/Computation/`](Phylogenetics/Computation) | A verified computation of gene tree distributions of small species trees (bitmask codes, an engine checked against the definitions), with the distributions of all species trees on three, four and five taxa. |
| [`Phylogenetics.Defs`](Phylogenetics/Defs.lean) | Rooted metric level-1 networks (`Phylogenetics.Net`, `Phylogenetics.Side`, `Phylogenetics.Net.WellFormed`), described recursively from the root, and their cycles and components (`Phylogenetics.Net.Cycle`); the network multispecies coalescent (`Phylogenetics.Net.forestDist`, `Phylogenetics.Net.geneTreeDist`); quartet and component concordance factors (`Phylogenetics.Net.quartetCF`, `Phylogenetics.Net.componentCF`); whether a gene tree displays a quartet (`Phylogenetics.geneTreeDisplays`); the metric cycle and the CFs of its induced metric quarnets (`Phylogenetics.MetricCycle`, `Phylogenetics.cycleCF`, `Phylogenetics.NMSCQuartetCF`); cyclic orders (`Phylogenetics.SameCyclicOrder`). |
| [`Phylogenetics/NMSC/`](Phylogenetics/NMSC) | The network multispecies coalescent is a probability distribution on gene trees, which are hierarchies (`Phylogenetics.Net.sum_geneTreeDist`, `Phylogenetics.geneTreeDist_isHierarchy`); the quartet concordance factors of the components of a cycle are those of the induced metric quarnets (`Phylogenetics.nmsc_quartetCF`; Baños 2019), and the probabilities that the gene trees on all the taxa display the quartets (`Phylogenetics.quartetCF_eq_displays`); gene trees drawn from it ([README](Phylogenetics/NMSC/README.md)). |
| [`Phylogenetics/Cycle/`](Phylogenetics/Cycle) | The CF formulas of a metric cycle, its mirror image, edge lengths with rational attenuations, and the realization of every metric cycle by a network (`Phylogenetics.MetricCycle.exists_net`). |
| [`Phylogenetics/Graph/`](Phylogenetics/Graph) | Networks as directed graphs: a graph is a rooted binary metric level-1 network iff it is isomorphic to the graph of a well-formed network term (`Phylogenetics.MetricDigraph.isNetwork_iff_exists_net`); every cycle has exactly one hybrid node. |
| [`Phylogenetics/Tree/`](Phylogenetics/Tree) | Rooted binary gene trees as an inductive type, their clusters and displayed quartets; anchor nodes (`Phylogenetics.GeneTree.countP_isAnchor`); annotated trees. |
| [`Phylogenetics.CyclicOrder`](Phylogenetics/CyclicOrder.lean) | Sorting and cyclic orders. |

The definitions in the modules `Phylogenetics.MSC.Defs`, `Phylogenetics.Defs`,
`Phylogenetics.Graph.Defs` and `Phylogenetics.Graph.OfNet` sit between marker comments, so that a
formalization's `Challenge.lean` can copy them word for word. Within one module Lean shares the auxiliary
definitions of identical pattern matches; this is why `Phylogenetics.Defs` stays one module, and
why the definitions of `Phylogenetics.Graph.OfNet` list the cases of networks in reverse
constructor order.

## Checks

`lake build`, then `lake env lean scripts/Audit.lean`, which checks that every declaration
(4271, private and auxiliary ones included) depends only on `propext`, `Classical.choice` and
`Quot.sound`. CI runs both, and checks that the audit imports every module.

## Credits

- **Maintainer:** The-Anh Vu-Le.
- **Formalization:** Claude Opus 5.5 (`claude-opus-5-5`, Anthropic), in Claude Code.
- **Review:** no person has reviewed the proofs; Lean's kernel checks them.

License: Apache-2.0.
