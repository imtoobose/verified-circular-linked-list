include "Node.dfy"

function IndexOf(s: seq<Node>, e: Node) : int
  requires e in s
  requires NoDupes(s)
  ensures 0 <= IndexOf(s,e) < |s|
  ensures s[IndexOf(s,e)] == e
{
  var i :| 0 <= i < |s| && s[i] == e;
  i
}

function get_next_seq_idx(s: seq<Node>, i: int): int
  requires 0 <= i < |s|
  requires NoDupes(s)
  ensures 0 <= get_next_seq_idx(s,i) < |s|
{
  if |s| == 1 then 0
  else
    (i+1) % |s|
}

function get_prev_seq_idx(s: seq<Node>, i: int): int
  requires 0 <= i < |s|
  requires NoDupes(s)
  ensures 0 <= get_prev_seq_idx(s, i) < |s|
{
  if |s| == 1 then 0
  else
    (i+|s|-1) % |s|
}

predicate  NoDupes(a: seq<Node>)
 {
  (forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j])
  // for any integer in existence := i, j -> constraint => 0 <= i < len(a), j I!=J => A[I] = A[J]
  // while loop => recursion / forall lemma
}
