module

public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Relation

/-!
# Directed multigraphs: definitions

A directed multigraph on given vertex and arc types, in which every element of the arc type is an
actual arc, so parallel arcs remain distinct.

* `DirectedMultigraph V E`, with `source` and `target`.
* `DirectedMultigraph.Adj`, `Reaches`, `IsAcyclic`: directed adjacency, reachability, acyclicity.
* `DirectedMultigraph.indegree`, `outdegree`: degrees, which count parallel arcs separately.
* `DirectedMultigraph.Crosses e S`: the arc `e` crosses the vertex bipartition `S | Sᶜ`.

No finiteness, connectivity or network assumption is built into the data. The theory is in the other
modules of `Phylogenetics.Graph`.
-/

@[expose] public section

namespace Phylogenetics

/-- A directed multigraph on given vertex and arc types. Every element of the arc type is an actual
arc; parallel arcs remain distinct. -/
structure DirectedMultigraph (V E : Type*) where
  /-- The vertex that an arc leaves. -/
  source : E → V
  /-- The vertex that an arc enters. -/
  target : E → V

namespace DirectedMultigraph

variable {V E : Type*} (G : DirectedMultigraph V E)

/-- Directed adjacency. -/
def Adj (u v : V) : Prop := ∃ e, G.source e = u ∧ G.target e = v

/-- Directed reachability; the empty path is allowed. -/
def Reaches : V → V → Prop := Relation.ReflTransGen G.Adj

/-- No nonempty directed closed path. -/
def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen G.Adj v v

/-- The number of arcs entering a vertex, counting parallel arcs separately. -/
noncomputable def indegree (v : V) : ℕ := {e | G.target e = v}.ncard

/-- The number of arcs leaving a vertex, counting parallel arcs separately. -/
noncomputable def outdegree (v : V) : ℕ := {e | G.source e = v}.ncard

/-- An arc crosses a vertex bipartition, in either orientation. -/
def Crosses (e : E) (S : Set V) : Prop :=
  (G.source e ∈ S ∧ G.target e ∉ S) ∨ (G.target e ∈ S ∧ G.source e ∉ S)

end DirectedMultigraph

end Phylogenetics
