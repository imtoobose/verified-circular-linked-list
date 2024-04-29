include "utils.dfy"
include "Node.dfy"


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

method list_add_tail(new_node: Node, head: Node)
  requires Valid(new_node)
  requires Valid(head)
  requires Singleton(new_node)
  requires new_node !in head.nodes
  modifies new_node, head, multiset(head.nodes)
{
  assert head.nodes[(IndexOf(head.nodes, head)+|head.nodes|-1) % |head.nodes|] == head.prev;
  internal_list_add(new_node, head.prev, head);
}

method internal_list_del(prev: Node, next: Node)
  requires Valid(prev) && Valid(next) && Valid(prev.next)
  requires prev.next.next == next
  requires prev != prev.next && prev.next != next
  requires prev.nodes == next.nodes == prev.next.nodes
  modifies prev, next, prev.next, multiset(prev.nodes)
  ensures Valid(prev)
  ensures Valid(next)
  ensures prev.next == next
  ensures next.prev == prev
  ensures prev.nodes == next.nodes
  ensures |prev.nodes| == |old(prev.nodes)| - 1
  ensures old(prev.next) !in prev.nodes && old(next.prev) !in next.nodes
  // ensures multiset(prev.nodes) == multiset(old(prev.nodes)) - multiset{old(prev.next)}
{
  var prev_next := prev.next; // maintain reference to removed node
  next.prev := prev;
  prev.next := next;

  ghost var prev_idx := IndexOf(prev.nodes, prev);
  ghost var removed_idx := IndexOf(prev.nodes, prev_next);
  ghost var next_idx := IndexOf(prev.nodes, next);

  // 3 cases - prev is the last node, the second last node, or any other node
  // in each assert the position of prev_next and next, then proceed to remove prev_next from the list
  if prev_idx == |prev.nodes| - 1 {
    assert prev.nodes[0] == prev_next;
    assert prev.nodes[1] == next;

    var new_nodes := prev.nodes[1..];
    prev.nodes := new_nodes;
    forall a' | a' in new_nodes {
      a'.nodes := new_nodes;
    }
    assert prev.nodes[0] == next;
  } else if prev_idx == |prev.nodes| - 2 {
    assert prev.nodes[0] == next;
    assert prev.nodes[|prev.nodes|-1] == prev_next;

    var new_nodes := prev.nodes[..prev_idx+1];
    forall a' | a' in new_nodes {
      a'.nodes := new_nodes;
    }
  } else {
    assert prev.nodes[prev_idx+1] == prev_next;
    assert prev.nodes[prev_idx+2] == next;
    assert next_idx == prev_idx+2;

    var splice_till_prev := prev.nodes[..prev_idx+1];
    var splice_from_next := prev.nodes[next_idx..];
    var new_nodes := splice_till_prev + splice_from_next;
    assert |new_nodes| >= 2;
    prev.nodes := new_nodes;
    forall a' | a' in new_nodes {
      a'.nodes := new_nodes;
    }
  }
}

// method list_del_entry(entry: Node)
// requires Valid(entry) && Valid(entry.prev) && Valid(entry.next) 
// requires entry != entry.prev && entry != entry.next
// requires entry.next.nodes == entry.prev.nodes == entry.nodes
// modifies entry, entry.prev, entry.next, multiset(entry.nodes), multiset(entry.prev.nodes)
// ensures Valid(entry.prev)
// ensures Valid(entry.next)
// {
//   var entry_next := entry.next;
//   var entry_prev := entry.prev;

//   // assert entry != entry.prev && entry != entry.next  ==> |entry.nodes| >= 2;
//   assert entry.nodes[get_prev_seq_idx(entry.nodes, IndexOf(entry.nodes, entry))] == entry.prev;
//   assert entry.nodes[get_next_seq_idx(entry.nodes, IndexOf(entry.nodes, entry))] == entry.next;
  
//   assert Valid(entry) && entry != entry.prev ==> |entry.nodes| >= 2;
//   // assert Valid(entry.prev) && Valid(entry) && entry.nodes == entry.prev.nodes ==> entry.prev.next == entry;
//   // assert Valid(entry.next) && Valid(entry) && entry.nodes == entry.next.nodes ==> entry.next.prev == entry;
//   // assert entry.prev.next.next == entry.next;
//   // assert entry.next.prev.prev == entry.prev;

//   internal_list_del(entry.prev, entry.next); 

//   assert |entry.prev.nodes| == |entry.nodes| - 1;
// }