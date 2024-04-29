//https://github.com/vmware-labs/verified-betrfs/blob/d13ee563391daf84ff03db9a6b1986b4c072b0b3/examples/circular_list.dfy#L47


function IndexOf(s: seq<Node>, e: Node) : int
  requires e in s
  requires NoDupes(s)
  ensures 0 <= IndexOf(s,e) < |s|
  ensures s[IndexOf(s,e)] == e
{
  var i :| 0 <= i < |s| && s[i] == e;
  i
}

class Node {
  var prev: Node
  var next:  Node
  ghost var nodes: seq<Node>

  constructor()
    ensures Valid(this)
    ensures this == this.nodes[0]
    ensures Singleton(this)
  {
    prev := this;
    next := this;
    nodes := [ this ];
  }
}

// implies that this node is not connected to any other nodes.
predicate Singleton(n: Node)
  requires Valid(n)
  ensures Singleton(n) ==> n.nodes == [ n ]
  reads n, n.nodes
{
  ghost var i := IndexOf(n.nodes, n);
  assert n.next == n.nodes[(i + 1) % |n.nodes|];
  n.prev == n.next == n
}

predicate NoDupes(a: seq<Node>) {
  (forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j])
}

// Validity of a link in a cicular linked list
ghost predicate Valid(node: Node)
  reads node
  reads node.nodes
{
  var nodes := node.nodes;

  && |nodes| > 0
  && (node in multiset(nodes)) // self is present in the set of nodes
  && (forall node' :: node' in nodes ==> node'.nodes == nodes) // all nodes are same in the chain
  && NoDupes(nodes) // no duplicates in the chain (they are pointers)
  && (forall i :: 0 <= i < |nodes| - 1 ==> nodes[i].next == nodes[i+1]) // assert that every next pointer is in the next index
  && nodes[|nodes|-1].next == nodes[0] // except the very last one that wraps to the first one
  && (forall i :: 1 <= i < |nodes| ==> nodes[i].prev == nodes[i-1]) // assert that every prev pointer is in the prev index
  && nodes[0].prev == nodes[|nodes|-1] // except the very first one that wraps to the last one
}

// analogue to __list_add
method internal_list_add(new_node: Node, prev: Node, next: Node)
  requires Valid(new_node) && Valid(prev) && Valid(next) // must be valid nodes
  requires Singleton(new_node) // must be a new node
  requires new_node != prev && new_node != next // all are different nodes
  requires prev.nodes == next.nodes // same linked list
  requires prev.next == next // next should be immediately after
  modifies next, prev, new_node, multiset(prev.nodes)
  ensures Valid(new_node)
  ensures Valid(prev)
  ensures Valid(next)
  ensures prev.nodes == next.nodes == new_node.nodes
  ensures |prev.nodes| == |old(prev.nodes)|+1
{
  next.prev := new_node;
  new_node.next := next;
  new_node.prev := prev;
  prev.next := new_node;

  // Proof of the above
  // Consider 2 cases - when prev is the very last node, and when it isn't, to handle appending the node correctly
  // NOTE: the nodes object is shared so directly modifying it will affect everyone. Be careful!

  assert prev.nodes[IndexOf(prev.nodes, prev)] == prev;
  assert next.nodes[IndexOf(next.nodes, next)] == next;
  var prev_idx := IndexOf(prev.nodes, prev);

  if prev_idx == |prev.nodes|-1 {
    assert prev.nodes[0] == next;
    ghost var new_nodes := prev.nodes + [new_node];
    forall a' | a' in new_nodes {
      a'.nodes := new_nodes;
    }
  } else {
    assert prev.nodes[prev_idx+1] == next;
    ghost var new_nodes := prev.nodes[..(prev_idx+1)] + [new_node] + prev.nodes[(prev_idx+1)..];
    prev.nodes := new_nodes; // not sure why this is needed
    forall a' | a' in new_nodes {
      a'.nodes := new_nodes;
    }
  }
}

method list_add(new_node: Node, head: Node)
  requires Valid(new_node)
  requires Valid(head)
  requires Singleton(new_node)
  requires new_node !in head.nodes
  modifies new_node, head, multiset(head.nodes)
{
  assert head.nodes[(IndexOf(head.nodes, head)+1) % |head.nodes|] == head.next;
  internal_list_add(new_node, head, head.next);
}