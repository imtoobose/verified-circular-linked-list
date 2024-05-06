include "utils.dfy"
include "Node.dfy"

method INIT_LIST_HEAD(node: Node)
  modifies node
  ensures node.prev == node
  ensures node.footprint == [node]
  ensures node.next == node
  ensures Singleton(node)
{
  node.prev := node;
  node.next := node;
  node.footprint := [node];
}

ghost predicate same_linked_list(nodes: seq<Node>)
  requires |nodes| >= 1
  reads multiset(nodes)
{
  var ghost_nodes := nodes[0].footprint;
  forall node' :: node' in nodes ==> node'.footprint == ghost_nodes
}

// analogue to __list_add
method internal_list_add(new_node: Node, prev: Node, next: Node)
  requires Valid(new_node) && Valid(prev) && Valid(next) // must be valid nodes
  requires new_node !in prev.footprint
  requires prev.footprint[get_next_seq_idx(prev.footprint, IndexOf(prev.footprint, prev))] == next
  requires same_linked_list([prev, next])
  requires Singleton(new_node) // must be a new node
  requires new_node != prev && new_node != next // all are different nodes
  modifies new_node, new_node.next, new_node.prev, multiset(prev.footprint)
  ensures Valid(new_node)
  ensures Valid(prev)
  ensures Valid(next)
  ensures same_linked_list([prev, next, new_node])
  ensures |prev.footprint| == |old(prev.footprint)|+1
  ensures (
            var prev_idx := IndexOf(old(prev.footprint), prev);
            && (prev_idx == |old(prev.footprint)|-1 ==> prev.footprint == old(prev.footprint) + [new_node])
            && (0 <= prev_idx < |old(prev.footprint)|-1 ==> (
                    if |old(prev.footprint)| == 1 then prev.footprint == [prev, new_node]
                    else prev.footprint  == old(prev.footprint[..prev_idx])+[prev, new_node]+old(prev.footprint[(prev_idx+1)..]))
               )
          )
{
  assert prev.next == next;
  ghost var next_idx := IndexOf(prev.footprint, next);

  next.prev := new_node;
  new_node.next := next;
  new_node.prev := prev;
  prev.next := new_node;

  // Proof of the above
  // Consider 2 cases - when prev is the very last node, and when it isn't, to handle appending the node correctly
  // NOTE: the nodes object is shared so directly modifying it will affect everyone. Be careful!

  assert prev.footprint[IndexOf(prev.footprint, prev)] == prev;
  assert next.footprint[IndexOf(next.footprint, next)] == next;
  var prev_idx := IndexOf(prev.footprint, prev);

  if prev_idx == |prev.footprint|-1 {
    assert prev.footprint[0] == next;
    ghost var new_nodes := prev.footprint + [new_node];
    forall a' | a' in new_nodes {
      a'.footprint := new_nodes;
    }
  } else {
    assert 0 <= prev_idx < |prev.footprint|-1;
    var splice_till_prev := prev.footprint[..prev_idx+1];
    var splice_from_next := prev.footprint[prev_idx+1..];

    assert splice_till_prev[|splice_till_prev|-1] == prev;
    assert prev != next ==> splice_from_next[0] == next;
    assert disjointSeq(splice_till_prev, splice_from_next);
    assert new_node !in splice_till_prev;
    assert new_node !in splice_from_next;
    
    ghost var new_nodes := splice_till_prev + [new_node] + splice_from_next;
    prev.footprint := new_nodes;
    next.footprint := new_nodes;
    new_node.footprint := new_nodes;

    assert prev.footprint[prev_idx+1] == new_node == prev.next;
    assert prev.footprint[prev_idx] == prev == new_node.prev;
    assert prev != next ==> prev.footprint[prev_idx+2] == next == new_node.next;
    
    assume {:axiom} NoDupes(new_nodes);
    forall a' | a' in new_nodes {
      a'.footprint := new_nodes;
    }
  }
}

predicate disjointSeq(self: seq<Node>, other: seq<Node>) {
  forall i: int, j: int :: 0 <= i < |self| && 0 <= j < |other| ==> self[i] != other[j]
}

method list_add(new_node: Node, head: Node)
  requires Valid(new_node)
  requires Valid(head)
  requires Singleton(new_node)
  requires new_node !in head.footprint
  modifies new_node, head, multiset(head.footprint)
  ensures Valid(new_node)
  ensures Valid(head)
  ensures same_linked_list([head, new_node])
{
  assert head.footprint[(IndexOf(head.footprint, head)+1) % |head.footprint|] == head.next;
  assert same_linked_list([head, head.next]);
  internal_list_add(new_node, head, head.next);
}

method list_add_tail(new_node: Node, head: Node)
  requires Valid(new_node)
  requires Valid(head)
  requires Singleton(new_node)
  requires new_node !in head.footprint
  modifies new_node, head, multiset(head.footprint)
  ensures Valid(new_node)
  ensures Valid(head)
  ensures same_linked_list([head, new_node])
{
  assert head.footprint[(IndexOf(head.footprint, head)+|head.footprint|-1) % |head.footprint|] == head.prev;
  assert same_linked_list([head, head.prev]);
  internal_list_add(new_node, head.prev, head);
}

method internal_list_del(prev: Node, next: Node)
  requires Valid(prev) && Valid(next)
  requires prev.next.next == next
  requires prev != prev.next && prev.next != next
  requires same_linked_list([prev, next])
  modifies prev, next, prev.next, multiset(prev.footprint)
  ensures Valid(prev)
  ensures Valid(next)
  ensures same_linked_list([prev, next])
  ensures (
            var idx := IndexOf(old(prev.footprint), prev);
            && (idx == |old(prev.footprint)| - 1 ==> prev.footprint == old(prev.footprint[1..])) // prev is last, removed val is first index
            && (idx == |old(prev.footprint)| - 2 ==> prev.footprint == old(prev.footprint[..|prev.footprint|-1])) // prev is second last, removed is the last element
            && (0 <= idx < |old(prev.footprint)|-2 ==> prev.footprint == old(prev.footprint[..idx+1])+old(prev.footprint[idx+2..])) // anything else, then join arr till prev_idx] + [prev_idx+2..]
          )
{
  ghost var prev_idx := IndexOf(prev.footprint, prev);
  ghost var next_idx := IndexOf(prev.footprint, next);
  ghost var len := |prev.footprint|;

  var prev_next := prev.next; // maintain reference to removed node
  next.prev := prev;
  prev.next := next;

  // 3 cases - prev is the last node, the second last node, or any other node
  // in each assert the position of prev_next and next, then proceed to remove prev_next from the list

  if prev_idx == len - 1 {
    assert prev.footprint[0] == prev_next;
    assert prev.footprint[1] == next;

    var new_nodes := prev.footprint[1..];
    prev.footprint := new_nodes;
    forall a' | a' in new_nodes {
      a'.footprint := new_nodes;
    }
    assert prev.footprint[0] == next;
  } else if prev_idx == len - 2 {
    assert prev_idx != |prev.footprint|-1;
    assert prev_idx != |prev.footprint|-1;
    assert prev.footprint[0] == next;
    assert prev.footprint[|prev.footprint|-1] == prev_next;

    var new_nodes := prev.footprint[..prev_idx+1];
    forall a' | a' in new_nodes {
      a'.footprint := new_nodes;
    }
  } else {
    assert 0 <= prev_idx < |prev.footprint|-2;
    assert prev.footprint[prev_idx+1] == prev_next;
    assert prev.footprint[prev_idx+2] == next;
    assert next_idx == prev_idx+2;

    var splice_till_prev := prev.footprint[..prev_idx+1];
    var splice_from_next := prev.footprint[next_idx..];
    var new_nodes := splice_till_prev + splice_from_next;
    assert |new_nodes| >= 2;
    prev.footprint := new_nodes;
    forall a' | a' in new_nodes {
      a'.footprint := new_nodes;
    }
  }
}


method list_del_entry(entry: Node)
  requires Valid(entry)
  requires entry != entry.prev && entry != entry.next
  modifies multiset(entry.footprint)
  ensures Valid(old(entry.prev))
  ensures Valid(old(entry.next))
{
  assert entry.footprint[get_prev_seq_idx(entry.footprint, IndexOf(entry.footprint, entry))] == entry.prev;
  assert entry.footprint[get_next_seq_idx(entry.footprint, IndexOf(entry.footprint, entry))] == entry.next;
  assert Valid(entry) ==> entry.next.footprint == entry.footprint;
  assert Valid(entry) ==> entry.prev.footprint == entry.footprint;
  internal_list_del(entry.prev, entry.next);
}

method list_replace(old_node: Node,
                    new_node: Node)
  requires Valid(old_node)
  requires Valid(new_node)
  requires old_node != new_node
  requires Singleton(new_node)
  requires new_node !in old_node.footprint
  modifies new_node, old_node, old_node.next, new_node.next, new_node.prev, old_node.prev, multiset(old_node.footprint)
  ensures Valid(new_node)
  ensures (
            var idx := IndexOf(old(old_node.footprint), old_node);
            new_node.footprint == old(old_node.footprint[..idx]) + [new_node] + old(old_node.footprint[idx+1..])
          )
{
  assert old_node.footprint[get_next_seq_idx(old_node.footprint, IndexOf(old_node.footprint, old_node))] == old_node.next;
  assert old_node.footprint[get_prev_seq_idx(old_node.footprint, IndexOf(old_node.footprint, old_node))] == old_node.prev;
  assert new_node !in old_node.footprint ==> old_node.next != new_node;
  assert new_node !in old_node.footprint ==> old_node.prev != new_node;

  new_node.next := old_node.next;
  new_node.next.prev := new_node;
  new_node.prev := old_node.prev;
  new_node.prev.next := new_node;


  var old_idx := IndexOf(old_node.footprint, old_node);

  assert new_node !in old_node.footprint;
  var new_nodes := old_node.footprint[..old_idx] + [new_node]+ old_node.footprint[old_idx+1..];
  assert |new_nodes| == |old_node.footprint|;
  assert old_node !in new_nodes;
  assert new_node in new_nodes;
  assert new_node !in old_node.footprint[..old_idx] && new_node !in old_node.footprint[old_idx+1..];
  assert NoDupes(old_node.footprint) ==> multiset(old_node.footprint[..old_idx]) !! multiset(old_node.footprint[old_idx+1..]);
  assert NoDupes(old_node.footprint[..old_idx]);
  assert NoDupes(old_node.footprint[old_idx+1..]);
  assert NoDupes(old_node.footprint[..old_idx] + [new_node]+ old_node.footprint[old_idx+1..]);
  new_node.footprint := new_nodes;
  assert new_node.footprint[get_prev_seq_idx(new_nodes, IndexOf(new_node.footprint, new_node))] == new_node.prev;
  assert old_node !in new_nodes;
  forall a' | a' in new_nodes {
    a'.footprint := new_nodes;
  }
}


method list_replace_init(old_node: Node, new_node: Node)
  requires Valid(old_node)
  requires Valid(new_node)
  requires !same_linked_list([old_node, new_node])
  requires Singleton(new_node)
  ensures Valid(new_node)
  ensures Valid(old_node) && Singleton(old_node)
  modifies new_node, old_node, old_node.next, new_node.next, new_node.prev, old_node.prev, multiset(old_node.footprint)
{
  list_replace(old_node, new_node);
  INIT_LIST_HEAD(old_node);
  assert Singleton(old_node) ==> Valid(old_node);
}


/**
  * list_del_init - deletes entry from list and reinitialize it.
  * @entry: the element to delete from the list.
  */
method list_del_init(entry: Node)
  requires Valid(entry)
  requires Valid(entry)
  requires entry != entry.prev && entry != entry.next
  requires entry.next.footprint == entry.prev.footprint == entry.footprint
  modifies multiset(entry.footprint)
  ensures Valid(entry) && Singleton(entry)
{
  assert entry.footprint[get_prev_seq_idx(entry.footprint, IndexOf(entry.footprint, entry))] == entry.prev;
  assert entry.footprint[get_next_seq_idx(entry.footprint, IndexOf(entry.footprint, entry))] == entry.next;

  ghost var entry_prev := entry.prev;
  ghost var entry_next := entry.next;

  list_del_entry(entry);

  assert Valid(entry_prev);
  assert Valid(entry_next);

  INIT_LIST_HEAD(entry);
}

method list_move(list: Node, head: Node)
  requires Valid(list)
  requires Valid(head)
  requires list != list.prev && list != list.next
  requires multiset(list.footprint) !! multiset(head.footprint)
  modifies multiset(list.footprint), multiset(head.footprint)
  ensures same_linked_list([list, head])
  ensures Valid(head)
  ensures Valid(list)
{
  list_del_entry(list);

  // the list is invalid here because list points to a chain of nodes it's not a part of.
  // @change
  INIT_LIST_HEAD(list);

  list_add(list, head);
}

method list_move_tail(list: Node,
                      head: Node)
  requires Valid(list)
  requires Valid(head)
  requires list != list.prev && list != list.next
  requires multiset(list.footprint) !! multiset(head.footprint)
  modifies multiset(list.footprint), multiset(head.footprint)
  ensures same_linked_list([list, head])
  ensures Valid(head)
  ensures Valid(list)
{
  list_del_entry(list);

  // the list is invalid here because list points to a chain of nodes it's not a part of.
  // @change
  INIT_LIST_HEAD(list);

  list_add_tail(list, head);
}

method list_is_last(list: Node, head: Node) returns (ret: bool)
  requires Valid(list)
  requires Valid(head)
  ensures ret ==> list.footprint[get_next_seq_idx(list.footprint, IndexOf(list.footprint, list))] == head
{
  return list.next == head;
}

predicate list_empty(head: Node)
  reads head, multiset(head.footprint)
  requires Valid(head)
  ensures list_empty(head) ==> Singleton(head)
{
  head.next == head
}
