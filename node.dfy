include "utils.dfy"

class Node {
  var prev: Node
  var next:  Node
  ghost var nodes: seq<Node>
  // int nat seq<Node> map<node> set<Node>
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

// Validity of a link in a cicular linked list
ghost predicate Valid(node: Node)
  reads node
  reads node.nodes
{
  var nodes := node.nodes;

  && |nodes| > 0
  && (node in multiset(nodes)) // self is present in the set of nodes
  && (forall node' {:trigger node'.nodes == nodes} :: node' in nodes ==>  node'.nodes == nodes) // all nodes are same in the chain
  && NoDupes(nodes) // no duplicates in the chain (they are pointers)
  && (forall i :: 0 <= i < |nodes| - 1 ==> nodes[i].next == nodes[i+1]) // assert that every next pointer is in the next index
  && nodes[|nodes|-1].next == nodes[0] // except the very last one that wraps to the first one
  && (forall i :: 1 <= i < |nodes| ==> nodes[i].prev == nodes[i-1]) // assert that every prev pointer is in the prev index
  && nodes[0].prev == nodes[|nodes|-1] // except the very first one that wraps to the last one
}
