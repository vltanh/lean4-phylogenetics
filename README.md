# Phylogenetics: phylogenetic trees and networks, the coalescent, and concordance factors, in Lean 4

[![CI](https://github.com/vltanh/lean4-phylogenetics/actions/workflows/ci.yml/badge.svg)](https://github.com/vltanh/lean4-phylogenetics/actions/workflows/ci.yml)

`Phylogenetics` is a Lean 4 library of mathematical phylogenetics on top of Mathlib:

- rooted trees as hierarchies and unrooted trees as split families, with their combinatorics, quartets
  and tree metrics;
- rooted phylogenetic networks on arbitrary vertex and arc types, as directed multigraphs: cut edges,
  blobs, induced networks and the tree of blobs; and level-1 networks, as terms and as directed graphs;
- Kingman's coalescent on forests of gene lineages, the multispecies coalescent on species trees, and
  the network multispecies coalescent, with correlated inheritance on general networks and in the
  term-based form on level-1 networks;
- quartet concordance factors and the displayed tree model;
- neighbor joining, Buneman's four-point theorem and the ASTRAL dynamic program.

It holds definitions and general results, each acknowledged to its source. It does not formalize any one
paper as a whole: a formalization of a paper belongs in a project that depends on this library.

Its declarations live in the namespace `Phylogenetics`. The general results of
[`Phylogenetics/ForMathlib/`](Phylogenetics/ForMathlib) use Mathlib's namespaces. Every declaration
depends only on Lean's standard axioms; there is no `sorry`.

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
import Phylogenetics.NMSC.Exchangeability  -- exchangeability across a cut edge of a general network
import Phylogenetics.MSC.Marginal          -- marginalization of the multispecies coalescent
```

Lake builds only the imported modules and the modules they import. No module imports all of
Mathlib: each imports the Mathlib modules that it uses. `import Phylogenetics` imports every
module. The library is on Lean `v4.36.0-rc1` and the Mathlib release of the same name. Earlier module
paths and names are listed in the [changelog](CHANGELOG.md).

## Contents

In each directory, `Defs` has the definitions when there is such a module, and the other modules have
the theory.

| Directory | Content |
| --- | --- |
| [`Phylogenetics/ForMathlib/`](Phylogenetics/ForMathlib) | Analysis that does not mention phylogenetics: the entries of `exp (t • A)` are entire; preimages of null sets under maps of Haar measures. |
| [`Phylogenetics/Graph/`](Phylogenetics/Graph) | Directed multigraphs with individually named arcs (`Phylogenetics.DirectedMultigraph`), linked to Mathlib's `Graph`: connectivity and bridges, degrees, the uniqueness of a cut bipartition, the laminarity of cuts, the quotient by bridge components, blobs and trees (`DirectedMultigraph.isBlob_iff`, `DirectedMultigraph.bridgeQuotient_isTree`), linked to `SimpleGraph.IsTree` |
| [`Phylogenetics/Hierarchy/`](Phylogenetics/Hierarchy) | Rooted trees as hierarchies (`Phylogenetics.IsHierarchy`, `childClusters`, `unroot`, `restrictClusters`): their combinatorics, counts of rooted and unrooted trees, unrooted trees on four and five taxa and their rootings, the location of the root, rooted tree shapes, small species trees. Rooted species trees with edge lengths (`Phylogenetics.SpeciesTree`) and their induced subtrees. Unrooted trees are determined by their quartets (Steel; `Phylogenetics.mem_unroot_iff_quartets`). |
| [`Phylogenetics/Tree/`](Phylogenetics/Tree) | Unrooted trees as split families (`Phylogenetics.IsUnrootedTree`, characterized by compatibility in `isUnrootedTree_iff`) and quartet trees (`Phylogenetics.QuartetTree`, `Displays`): vertex partitions, splicing, detaching and reattaching, counts and probabilities of displayed quartet trees (`quartetCount`, `displayCF`), the Maximum Quartet Support objective, tree metrics and the four-point expression (`TreeMetric.eq_of_treeMetric_eq`); neighbor joining (`NJ.isExactBuilder_nj`); Buneman's four-point theorem (`FourPoint.isFourPoint_iff`); the ASTRAL dynamic program (`astralTree_isAstralOptimal`). [`Tree/GeneTree/`](Phylogenetics/Tree/GeneTree): rooted binary gene trees as an inductive type (`Phylogenetics.GeneTree`), their clusters and displayed quartets, anchor nodes (`GeneTree.countP_isAnchor`), annotated trees. |
| [`Phylogenetics/Network/`](Phylogenetics/Network) | Rooted networks on arbitrary vertex and arc types (`Phylogenetics.RootedNetwork`, `IsPhylogenetic`, `IsMetric`), with parallel arcs and vertices of any degree allowed: cuts through domination, the ancestral restriction, deleted arcs, the induced network by the least stable ancestor and suppression (`inducedNetwork`), the graph of a hierarchy, the hierarchy of a network's cuts, and the tree of blobs as a graph (`treeOfBlobs`, `isUnrootedTree_treeOfBlobs`). The level of a network through its blobs (`RootedNetwork.IsLevelOne`). Parameters of the induced network (`Network/InducedMetric`). |
| [`Phylogenetics/Network/Level1/`](Phylogenetics/Network/Level1) | Rooted binary metric level-1 networks described recursively from the root (`Phylogenetics.Net`, `Side`, `Net.WellFormed`, `Net.Cycle`), and as directed graphs (`Phylogenetics.MetricDigraph`): a graph is such a network iff it is isomorphic to the graph of a well-formed term (`MetricDigraph.isNetwork_iff_exists_net`); every cycle has exactly one hybrid node; the map to rooted networks (`MetricDigraph.toRootedNetwork`, `Net.toRootedNetwork`), which are level-1 in the sense of their blobs (`MetricDigraph.isLevelOne_ofBinary`); cyclic orders. |
| [`Phylogenetics/Coalescent/`](Phylogenetics/Coalescent) | Kingman's coalescent on forests (`Phylogenetics.kingmanGenerator`, `kingmanTransition`, `kingmanAbsorption`): the jump chain and the factorization; Tavaré's formula for the number of lineages (`deathProb_eq_tavare`); the population above the root; binary forests; `PMF` forms; relabelling; lumpability, by restricting to a set of lineages or along an embedding; the unrooted gene tree it produces. |
| [`Phylogenetics/MSC/`](Phylogenetics/MSC) | The multispecies coalescent on species trees (`SpeciesTree.rootedDist`, `SpeciesTree.unrootedDist`): basic properties, relabelling taxa, marginalization (`SpeciesTree.rootedDist_restrict`), contracting edges of length zero and continuity, several lineages per taxon, coalescent histories. |
| [`Phylogenetics/NMSC/`](Phylogenetics/NMSC) | The network multispecies coalescent on `RootedNetwork`, with an inheritance correlation (`Phylogenetics.geneTreeDist`, `nmscCF`): the Pólya urn at a reticulation; a probability distribution positive on all binary trees (`sum_geneTreeDist`, `geneTreeDist_pos`); sampling consistency; symmetry; the Markov property at an arc; exchangeability across a cut edge (`NMSC.exchangeability`); the strict dominance of the split of a fork (`NMSC.nmscCF_lt_of_fork`); concordance factors at boundary parameters; analyticity in the parameters (`analyticOnNhd_nmscCF_coordMetric`); passing to the induced network (`NMSC.nmscCF_inducedNetwork`); the displayed tree model and the mixture at `ρ = 1`, with its bound on concordance factors (`RootedNetwork.nmscCF_rho_one`, `RootedNetwork.one_sub_exp_le_sub_nmscCF_rho_one`); gluing a network from pieces (`NMSC.IsGlued.rootDist_eq`); and the multispecies coalescent as the case of a tree (`SpeciesTree.rootedDist_eq_geneTreeDist`). |
| [`Phylogenetics/NMSC/Level1/`](Phylogenetics/NMSC/Level1) | The coalescent on the terms `Net`, with independent inheritance (`Net.forestDist`, `Net.geneTreeDist`, `Net.quartetCF`): a probability distribution on hierarchies (`Net.sum_geneTreeDist`, `geneTreeDist_isHierarchy`); the quartet concordance factors of the components of a cycle are those of the induced metric quarnets (`nmsc_quartetCF`; Baños 2019), and the probabilities that gene trees on all the taxa display the quartets (`quartetCF_eq_displays`); metric cycles (`MetricCycle`, `MetricCycle.exists_net`) ([README](Phylogenetics/NMSC/Level1/README.md)); these are the general coalescent at correlation `0` (`Net.geneTreeDist_toRootedNetwork`, `Net.nmscCF_toRootedNetwork`). |
| [`Phylogenetics/Computation/`](Phylogenetics/Computation) | A verified computation of gene tree distributions of small species trees (bitmask codes, an engine checked against the definitions), with the distributions of all species trees on three, four and five taxa. |

## What is connected, and what is not yet

The library has several representations of a concept, because each has theorems that the other does
not. These are connected:

- **Level-1 terms and digraphs.** `MetricDigraph.isNetwork_iff_exists_net`: up to isomorphism, the
  graphs of well-formed terms with at least two leaves are exactly the networks.
- **Level-1 digraphs and general networks.** `MetricDigraph.toRootedNetwork` and `Net.toRootedNetwork`
  keep the vertices, arcs, lengths and inheritance probabilities; the result is phylogenetic and binary,
  with valid parameters (`toRootedNetwork_isPhylogenetic`, `toRootedNetwork_isBinary`,
  `toRootedNetwork_isMetric`).
- **Graphs and split families.** `hierarchyNetwork` is the graph of a hierarchy, whose labelled cuts are
  `unroot H` (`hierarchyNetwork_hasCutSplit_iff`); the cuts of a network form a hierarchy
  (`cutHierarchy_isHierarchy`), and `treeOfBlobs` is the split family of the graph obtained by contracting
  the blobs (`mem_treeOfBlobs_iff_blobTree`). `hasCutSplitOn_iff_inducedNetwork_hasCutSplit` does the same
  for induced networks.
- **Gene trees.** The inductive `GeneTree` and hierarchies, through `GeneTree.clusters`; a displayed
  quartet, in all three forms (`GeneTree.displays_iff_geneTreeDisplays`,
  `displays_unroot_quartetTree_iff`). Binary trees: `isBinaryHierarchy_iff_card_childClusters`,
  `isBinaryTree_iff`, `SpeciesTree.isBinary_iff_isBinaryHierarchy`.
- **Kingman's coalescent.** There is one implementation. `MSC`, `NMSC` and `NMSC.Level1` all use
  `kingmanTransition` and `kingmanAbsorption`. The two forms of lumpability follow from one argument
  (`sum_kingmanTransition_comp`), and `image_map_restrictForest` relates their restrictions.

- **The coalescents.** `Net.geneTreeDist_toRootedNetwork`: `Net.geneTreeDist` of a well-formed term is
  `Phylogenetics.geneTreeDist` of `Net.toRootedNetwork` at inheritance correlation `0`. So
  `Net.nmscCF_toRootedNetwork` gives the concordance factors of `nmsc_quartetCF` as `nmscCF`, and the
  theorems of `NMSC` apply to `Net.geneTreeDist`. `SpeciesTree.rootedDist_eq_geneTreeDist`:
  `SpeciesTree.rootedDist` is `geneTreeDist` of the graph of the hierarchy, for every `ρ ≥ 0`, also with
  several lineages per taxon (`SpeciesTree.rootedDist_eq_geneTreeDist_sample`).
- **Steel's theorem.** `mem_unroot_iff_quartets` on species trees is `mem_of_forall_displays` on split
  families.

- **Level-1.** `MetricDigraph.isLevelOne_ofBinary`: on a binary digraph with labelled leaves, if no two cycles
  share an edge then every blob has level at most one. So `Net.isLevelOne_toRootedNetwork` and
  `MetricDigraph.IsNetwork.isLevelOne_toRootedNetwork` make the theorems on `IsLevelOne` apply to terms and
  digraphs. Off binary networks this fails: two cycles through one vertex share no edge, and are one blob with
  two reticulations. On binary networks the bridges of the two graphs are the same
  (`MetricDigraph.isBridge_iff_undirected_isBridge`).

What is not connected:

- **Level-1, the converse.** That a binary digraph whose rooted network is `IsLevelOne` has `IsLevel1` is not in
  the library.
- **Induced networks.** `inducedNetwork` cuts at the least stable ancestor. Allman et al. 2023 keep what lies above
  it. `NMSC.nmscCF_inducedNetwork` passes that part on the concordance factors, but a second induced network is not
  defined.

## Checks

`lake build`, then `lake env lean scripts/Audit.lean`, which checks that every declaration
(about 7100, private and auxiliary ones included) depends only on `propext`, `Classical.choice` and
`Quot.sound`. CI runs both, and checks that the audit imports every module.

## Credits

- **Maintainer:** The-Anh Vu-Le.
- **Formalization:** Claude Opus 5.5 (`claude-opus-5-5`, Anthropic), in Claude Code; the first versions of
  the directed multigraphs and rooted networks, by Codex (GPT-6 family).
- **Review:** no person has reviewed the proofs; Lean's kernel checks them.

License: Apache-2.0.
