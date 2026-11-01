module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that the proofs are visible to the axiom
-- check (the module system hides them from a plain `import`). Generate the lines with
--   (echo Phylogenetics.lean; find Phylogenetics -name '*.lean') | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all Phylogenetics
import all Phylogenetics.Coalescent.Absorption
import all Phylogenetics.Coalescent.BinaryForest
import all Phylogenetics.Coalescent.Defs
import all Phylogenetics.Coalescent.Factorization
import all Phylogenetics.Coalescent.Forest
import all Phylogenetics.Coalescent.Lump
import all Phylogenetics.Coalescent.Outcome
import all Phylogenetics.Coalescent.PMF
import all Phylogenetics.Coalescent.Relabel
import all Phylogenetics.Coalescent.Tavare
import all Phylogenetics.Coalescent.Trace
import all Phylogenetics.Computation.Caterpillar5
import all Phylogenetics.Computation.Codes
import all Phylogenetics.Computation.Engine
import all Phylogenetics.Computation.FiveTaxa
import all Phylogenetics.Computation.FourTaxa
import all Phylogenetics.Computation.ThreeTaxa
import all Phylogenetics.Computation.Toolkit
import all Phylogenetics.ForMathlib.Analysis.MatrixExponential
import all Phylogenetics.ForMathlib.MeasureTheory.HaarPreimage
import all Phylogenetics.Graph.Basic
import all Phylogenetics.Graph.Blobs
import all Phylogenetics.Graph.BridgeCutLaminar
import all Phylogenetics.Graph.Connectivity
import all Phylogenetics.Graph.CutUniqueness
import all Phylogenetics.Graph.Defs
import all Phylogenetics.Graph.Degree
import all Phylogenetics.Graph.Tree
import all Phylogenetics.Hierarchy.Basic
import all Phylogenetics.Hierarchy.Classify
import all Phylogenetics.Hierarchy.Counts
import all Phylogenetics.Hierarchy.Defs
import all Phylogenetics.Hierarchy.Quartets
import all Phylogenetics.Hierarchy.RootLocation
import all Phylogenetics.Hierarchy.Shapes
import all Phylogenetics.Hierarchy.Small
import all Phylogenetics.Hierarchy.SpeciesTree
import all Phylogenetics.MSC.Basic
import all Phylogenetics.MSC.Contract
import all Phylogenetics.MSC.Defs
import all Phylogenetics.MSC.History
import all Phylogenetics.MSC.Marginal
import all Phylogenetics.MSC.MultiSample
import all Phylogenetics.MSC.Relabel
import all Phylogenetics.NMSC.Analytic
import all Phylogenetics.NMSC.Basic
import all Phylogenetics.NMSC.Defs
import all Phylogenetics.NMSC.DisplayedTreeModel
import all Phylogenetics.NMSC.Exchangeability
import all Phylogenetics.NMSC.Factor
import all Phylogenetics.NMSC.Glue
import all Phylogenetics.NMSC.History
import all Phylogenetics.NMSC.Induced
import all Phylogenetics.NMSC.InducedAbove
import all Phylogenetics.NMSC.InducedParams
import all Phylogenetics.NMSC.InducedRestrict
import all Phylogenetics.NMSC.InducedSuppress
import all Phylogenetics.NMSC.Inheritance
import all Phylogenetics.NMSC.Level1.Arms
import all Phylogenetics.NMSC.Level1.Basic
import all Phylogenetics.NMSC.Level1.Consistency
import all Phylogenetics.NMSC.Level1.Context
import all Phylogenetics.NMSC.Level1.Cycle
import all Phylogenetics.NMSC.Level1.Defs
import all Phylogenetics.NMSC.Level1.Displays
import all Phylogenetics.NMSC.Level1.GeneTrees
import all Phylogenetics.NMSC.Level1.General
import all Phylogenetics.NMSC.Level1.MetricCycle.Basic
import all Phylogenetics.NMSC.Level1.MetricCycle.Instance
import all Phylogenetics.NMSC.Level1.MetricCycle.RationalLengths
import all Phylogenetics.NMSC.Level1.MetricCycle.Realization
import all Phylogenetics.NMSC.Level1.MetricCycle.Reflection
import all Phylogenetics.NMSC.Level1.Process
import all Phylogenetics.NMSC.Level1.Sampling
import all Phylogenetics.NMSC.Level1.Symmetry
import all Phylogenetics.NMSC.Marginal
import all Phylogenetics.NMSC.SpeciesTree
import all Phylogenetics.NMSC.Symmetry
import all Phylogenetics.NMSC.TreeCF
import all Phylogenetics.NMSC.Witness
import all Phylogenetics.Network.AncestralRestriction
import all Phylogenetics.Network.Basic
import all Phylogenetics.Network.CutHierarchy
import all Phylogenetics.Network.Cuts
import all Phylogenetics.Network.Defs
import all Phylogenetics.Network.DeletedArcs
import all Phylogenetics.Network.Induced
import all Phylogenetics.Network.InducedMetric
import all Phylogenetics.Network.Level1.CyclicOrder
import all Phylogenetics.Network.Level1.Defs
import all Phylogenetics.Network.Level1.Digraph.Basic
import all Phylogenetics.Network.Level1.Digraph.Complete
import all Phylogenetics.Network.Level1.Digraph.CompleteCycle
import all Phylogenetics.Network.Level1.Digraph.CompleteDesc
import all Phylogenetics.Network.Level1.Digraph.CompleteEmbed
import all Phylogenetics.Network.Level1.Digraph.Correspondence
import all Phylogenetics.Network.Level1.Digraph.CycleHybrid
import all Phylogenetics.Network.Level1.Digraph.Defs
import all Phylogenetics.Network.Level1.Digraph.Invariance
import all Phylogenetics.Network.Level1.Digraph.Invariant
import all Phylogenetics.Network.Level1.Digraph.InvariantCycle
import all Phylogenetics.Network.Level1.Digraph.InvariantSide
import all Phylogenetics.Network.Level1.Digraph.InvariantTree
import all Phylogenetics.Network.Level1.Digraph.OfNet
import all Phylogenetics.Network.Level1.Digraph.Sound
import all Phylogenetics.Network.Level1.LevelOne
import all Phylogenetics.Network.Level1.ToRootedNetwork
import all Phylogenetics.Network.OfHierarchy
import all Phylogenetics.Network.PendantCuts
import all Phylogenetics.Network.Quartets
import all Phylogenetics.Network.TreeOfBlobs
import all Phylogenetics.Tree.AstralDP
import all Phylogenetics.Tree.Defs
import all Phylogenetics.Tree.Detach
import all Phylogenetics.Tree.FourPoint
import all Phylogenetics.Tree.GeneTree.AnchorNode
import all Phylogenetics.Tree.GeneTree.Annotate
import all Phylogenetics.Tree.GeneTree.Basic
import all Phylogenetics.Tree.Metric
import all Phylogenetics.Tree.NeighborJoining
import all Phylogenetics.Tree.Splice
import all Phylogenetics.Tree.Splits

/-!
# Axiom audit of the library `Phylogenetics`

`lake env lean scripts/Audit.lean` (in `Phylogenetics/`, or `lake env lean Phylogenetics/scripts/Audit.lean` from
a project that requires `Phylogenetics`) checks that every declaration of the library, private and
auxiliary ones included, depends only on Lean's standard axioms `propext`, `Classical.choice` and
`Quot.sound` (a `sorry` would show up as the axiom `sorryAx`), and lists the axioms of its main
theorems. Declarations of the library in Mathlib's namespaces are covered too: the check goes through
modules, not namespaces.
-/

open Lean Elab Command

namespace PhyloAudit

/-- The main theorems of the library, with a short label. -/
meta def mainResults : List (String × Name) :=
  [("Tavaré's formula for the number of lineages", ``Phylogenetics.deathProb_eq_tavare),
   ("Marginalization of the multispecies coalescent", ``Phylogenetics.SpeciesTree.rootedDist_restrict),
   ("Unrooted trees are determined by their quartets", ``Phylogenetics.mem_unroot_iff_quartets),
   ("NMSC quartet CFs of the components of a cycle", ``Phylogenetics.nmsc_quartetCF),
   ("Sampling consistency: CFs of gene trees on all the taxa", ``Phylogenetics.quartetCF_eq_displays),
   ("Every metric cycle is the cycle of a network", ``Phylogenetics.MetricCycle.exists_net_nmscQuartetCF),
   ("Networks as directed graphs", ``Phylogenetics.MetricDigraph.isNetwork_iff_exists_net),
   ("One hybrid node per cycle", ``Phylogenetics.MetricDigraph.IsNetwork.existsUnique_isHybrid),
   ("Anchor nodes of a quartet", ``Phylogenetics.GeneTree.countP_isAnchor),
   ("The NMSC is a probability distribution on gene trees", ``Phylogenetics.Net.sum_geneTreeDist),
   ("The gene trees of the NMSC are hierarchies", ``Phylogenetics.geneTreeDist_isHierarchy),
   ("Contracting the blobs of a connected graph gives a tree",
    ``Phylogenetics.DirectedMultigraph.bridgeQuotient_isTree),
   ("The tree of blobs is an unrooted tree", ``Phylogenetics.RootedNetwork.isUnrootedTree_treeOfBlobs),
   ("Cut splits on a set of taxa are those of the induced network",
    ``Phylogenetics.RootedNetwork.hasCutSplitOn_iff_inducedNetwork_hasCutSplit),
   ("A level-1 digraph is a phylogenetic rooted network",
    ``Phylogenetics.MetricDigraph.toRootedNetwork_isPhylogenetic),
   ("Unrooted trees are the compatible split families", ``Phylogenetics.isUnrootedTree_iff),
   ("A tree metric determines the tree and the weights",
    ``Phylogenetics.TreeMetric.eq_of_treeMetric_eq),
   ("The general NMSC is a probability distribution on gene trees", ``Phylogenetics.sum_geneTreeDist),
   ("Sampling consistency of the general NMSC", ``Phylogenetics.NMSC.sum_injDist_trace),
   ("Exchangeability across a cut edge", ``Phylogenetics.NMSC.exchangeability),
   ("The split of a fork has the largest concordance factor", ``Phylogenetics.NMSC.nmscCF_lt_of_fork),
   ("Concordance factors are entire in the parameters",
    ``Phylogenetics.analyticOnNhd_nmscCF_coordMetric),
   ("The term-based coalescent is the general one at correlation 0",
    ``Phylogenetics.Net.geneTreeDist_toRootedNetwork),
   ("The multispecies coalescent is the general one on a tree",
    ``Phylogenetics.SpeciesTree.rootedDist_eq_geneTreeDist),
   ("Concordance factors of the induced network", ``Phylogenetics.NMSC.nmscCF_inducedNetwork),
   ("Neighbor joining is exact on tree metrics", ``Phylogenetics.NJ.isExactBuilder_nj),
   ("Buneman's four-point theorem", ``Phylogenetics.FourPoint.isFourPoint_iff),
   ("The optimum of the ASTRAL dynamic program", ``Phylogenetics.astralTree_isAstralOptimal),
   ("At rho = 1, the mixture over the displayed trees", ``Phylogenetics.RootedNetwork.nmscCF_rho_one),
   ("At rho = 1, a bound on concordance factors from an arc separating a cherry",
    ``Phylogenetics.RootedNetwork.one_sub_exp_le_sub_nmscCF_rho_one),
   ("Binary digraphs with edge-disjoint cycles are level-1 in their blobs",
    ``Phylogenetics.MetricDigraph.isLevelOne_ofBinary)]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#audit_phylo" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut rows : Array String := #["| Result | Lean | Axioms |", "| --- | --- | --- |"]
  for (label, n) in mainResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    rows := rows.push s!"| {label} | `{n}` | {", ".intercalate (axs.toList.map toString)} |"
  let mut count := 0
  for m in env.header.moduleNames, d in env.header.moduleData do
    if (`Phylogenetics).isPrefixOf m then
      for c in d.constNames do
        count := count + 1
        let axs ← liftCoreM <| collectAxioms c
        if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {count} declarations of Phylogenetics: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end PhyloAudit

#audit_phylo
