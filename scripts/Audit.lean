module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that the proofs are visible to the axiom
-- check (the module system hides them from a plain `import`). Generate the lines with
--   (echo Phylogenetics.lean; find Phylogenetics -name '*.lean') | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all Phylogenetics
import all Phylogenetics.Coalescent.Absorption
import all Phylogenetics.Coalescent.Factorization
import all Phylogenetics.Coalescent.Forest
import all Phylogenetics.Coalescent.Outcome
import all Phylogenetics.Coalescent.Tavare
import all Phylogenetics.Computation.Caterpillar5
import all Phylogenetics.Computation.Codes
import all Phylogenetics.Computation.Engine
import all Phylogenetics.Computation.FiveTaxa
import all Phylogenetics.Computation.FourTaxa
import all Phylogenetics.Computation.ThreeTaxa
import all Phylogenetics.Computation.Toolkit
import all Phylogenetics.Cycle.Basic
import all Phylogenetics.Cycle.RationalLengths
import all Phylogenetics.Cycle.Realization
import all Phylogenetics.Cycle.Reflection
import all Phylogenetics.CyclicOrder
import all Phylogenetics.Defs
import all Phylogenetics.Graph.Basic
import all Phylogenetics.Graph.Complete
import all Phylogenetics.Graph.CompleteCycle
import all Phylogenetics.Graph.CompleteDesc
import all Phylogenetics.Graph.CompleteEmbed
import all Phylogenetics.Graph.Correspondence
import all Phylogenetics.Graph.CycleHybrid
import all Phylogenetics.Graph.Defs
import all Phylogenetics.Graph.Invariance
import all Phylogenetics.Graph.Invariant
import all Phylogenetics.Graph.InvariantCycle
import all Phylogenetics.Graph.InvariantSide
import all Phylogenetics.Graph.InvariantTree
import all Phylogenetics.Graph.OfNet
import all Phylogenetics.Graph.Sound
import all Phylogenetics.Hierarchy.Basic
import all Phylogenetics.Hierarchy.Classify
import all Phylogenetics.Hierarchy.Counts
import all Phylogenetics.Hierarchy.Quartets
import all Phylogenetics.Hierarchy.RootLocation
import all Phylogenetics.Hierarchy.Shapes
import all Phylogenetics.Hierarchy.Small
import all Phylogenetics.MSC.Basic
import all Phylogenetics.MSC.Contract
import all Phylogenetics.MSC.Defs
import all Phylogenetics.MSC.History
import all Phylogenetics.MSC.Marginal
import all Phylogenetics.MSC.MultiSample
import all Phylogenetics.MSC.Notions
import all Phylogenetics.MSC.Relabel
import all Phylogenetics.NMSC.Arms
import all Phylogenetics.NMSC.Basic
import all Phylogenetics.NMSC.Consistency
import all Phylogenetics.NMSC.Context
import all Phylogenetics.NMSC.Cycle
import all Phylogenetics.NMSC.Displays
import all Phylogenetics.NMSC.GeneTrees
import all Phylogenetics.NMSC.Instance
import all Phylogenetics.NMSC.Process
import all Phylogenetics.NMSC.Sampling
import all Phylogenetics.NMSC.Symmetry
import all Phylogenetics.Tree.AnchorNode
import all Phylogenetics.Tree.Annotate
import all Phylogenetics.Tree.Basic

/-!
# Axiom audit of the library `Phylogenetics`

`lake env lean scripts/Audit.lean` (in `Phylogenetics/`, or `lake env lean Phylogenetics/scripts/Audit.lean` from
a project that requires `Phylogenetics`) checks that every declaration of the library, private and
auxiliary ones included, depends only on Lean's standard axioms `propext`, `Classical.choice` and
`Quot.sound` (a `sorry` would show up as the axiom `sorryAx`), and lists the axioms of its main
theorems.
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
   ("The gene trees of the NMSC are hierarchies", ``Phylogenetics.geneTreeDist_isHierarchy)]

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
