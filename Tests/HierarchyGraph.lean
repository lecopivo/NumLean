module

public import NumLean.Interfaces.Algebra.Field.Lawful

@[expose] public section

open NumLean.HierarchyGraph

@[hierarchy_graph test_tag_a test_tag_b test_tag_c]
class MultiTaggedHierarchyGraphClass where
  value : Nat

/--
error: hierarchy_graph tags are only allowed on class declarations; use bare @[hierarchy_graph] for instances
-/
#guard_msgs in
@[hierarchy_graph instance_tag]
instance : MultiTaggedHierarchyGraphClass where
  value := 0

#hierarchy_graph_json algebra_ops algebra_lawful

#hierarchy_graph_json test_tag_a test_tag_c
