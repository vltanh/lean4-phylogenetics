module

public import Phylogenetics.Tree.Basic

/-!
# Annotated trees

A rooted binary tree with a value at every node (`Phylogenetics.AnnotatedTree`), and the annotation
of a gene tree by a function of the subtrees below its nodes (`Phylogenetics.GeneTree.annotate`),
with its value at the root and its internal nodes. Algorithms on gene trees that store a table at
every node compute such annotations. -/

@[expose] public section

namespace Phylogenetics

universe u v

/-- A rooted binary tree with a value of type `α` at every node: `leaf a`, or `node a l r` with the
subtrees `l, r` below its two children. -/
inductive AnnotatedTree (α : Type u) where
  | leaf (a : α)
  | node (a : α) (l r : AnnotatedTree α)

namespace AnnotatedTree

variable {α : Type u}

/-- The value at the root. -/
def val : AnnotatedTree α → α
  | leaf a => a
  | node a _ _ => a

/-- The internal nodes in postorder (the root last), each given by its value and the values at its
two children. -/
def internalNodes : AnnotatedTree α → List (α × α × α)
  | leaf _ => []
  | node a l r => l.internalNodes ++ r.internalNodes ++ [(a, l.val, r.val)]

end AnnotatedTree

/-- The gene tree with each node annotated by the value of `f` at the subtree below it. -/
def GeneTree.annotate {X : Type u} {α : Type v} (f : GeneTree X → α) :
    GeneTree X → AnnotatedTree α
  | .leaf x => .leaf (f (.leaf x))
  | .node l r => .node (f (.node l r)) (l.annotate f) (r.annotate f)

/-- The value at the root of an annotated gene tree is the annotation of the whole tree. -/
theorem GeneTree.val_annotate {X : Type u} {α : Type v} (f : GeneTree X → α) (s : GeneTree X) :
    (s.annotate f).val = f s := by
  cases s <;> rfl

/-- The internal nodes of an annotated gene tree, with their annotations and those of their
children. -/
theorem GeneTree.internalNodes_annotate {X : Type u} {α : Type v} (f : GeneTree X → α)
    (s : GeneTree X) :
    (s.annotate f).internalNodes =
      s.internalNodes.map fun v => (f (.node v.1 v.2), f v.1, f v.2) := by
  induction s with
  | leaf x => rfl
  | node l r ihl ihr =>
    simp only [GeneTree.annotate, AnnotatedTree.internalNodes, ihl, ihr, GeneTree.internalNodes,
      List.map_append, List.map_cons, List.map_nil, GeneTree.val_annotate]

end Phylogenetics
