module list

sig Node {}

one sig TrashBin {
  var removed: set Node -- removed nodes
}

one sig List {
  var head: one Node,
  var tail: one Node,
  var nxt: Node -> Node,
  var prv: Node -> Node,
  var nodes: set Node -- list content
} {
  nodes = head.*nxt
  some nodes => one tail
  no ^nxt & iden -- no cycles
  nxt = ~prv     -- symmetric
  no prv[head]   -- head is a head
  no nxt[tail]   -- tail is a tail
  head.^nxt = Node.^nxt -- reachability
}

fun getnxt : Node->Node { List.nxt }
fun getprv : Node->Node { List.prv }
fun getHead  : one Node { List.head }
fun getTail  : one Node { List.tail }

pred pop_back {
  --prereq
    #nodes > 2

  --action
    TrashBin.removed' = TrashBin.removed + getTail
    List.nodes' = List.nodes - getTail
  -- rebinding
    getTail' = getTail.getprv
    getTail'.getprv' = getTail'.getprv
    no getTail'.getnxt'

  --postreq
    no getTail.getnxt'
    no getTail.getprv'
    getHead' = getHead
    all i: Node - getTail - getTail' {i.getnxt' = i.getnxt && i.getprv' = i.getprv}
}

pred push_back[new: Node] {
  --prereq
    new in TrashBin.removed

  --action
    TrashBin.removed' = TrashBin.removed - new
    List.nodes' = List.nodes + new
    -- rebinding
    getTail' = new
    getTail'.getprv' = getTail
    getTail.getnxt' = getTail'

  --postreq
    no getTail'.getnxt'
    getTail.getprv' = getTail.getprv
    getHead' = getHead
    all i: Node - getTail - getTail' {i.getnxt' = i.getnxt && i.getprv' = i.getprv}
}

pred pop_front {
  --prereq
    #nodes > 2

  --action
    TrashBin.removed' = TrashBin.removed + getHead
    List.nodes' = List.nodes - getHead
    getHead' = getHead.getnxt
    getHead'.getnxt' = getHead'.getnxt
    no getHead'.getprv'

  --postreq
    no getHead.getprv'
    no getHead.getnxt'
    getTail' = getTail
    all i: Node - getHead - getHead' {i.getnxt' = i.getnxt && i.getprv' = i.getprv}
}

pred push_front[e: Node] {
  --prereq
    e in TrashBin.removed

  --action
    TrashBin.removed' = TrashBin.removed - e
    List.nodes' = List.nodes + e
    getHead' = e
    getHead'.getnxt' = getHead
    getHead.getprv' = getHead'

  --postreq
    no getHead'.getprv'
    getHead.getnxt' = getHead.getnxt
    getTail' = getTail
    all i: Node - getHead - getHead' {i.getnxt' = i.getnxt && i.getprv' = i.getprv}
}

pred clear{
  --prereq

  --action
    all i: Node - getTail - getHead | i in TrashBin.removed'
    TrashBin.removed' = Node - getTail - getHead
    List.nodes' = getTail + getHead

  --postreq
    all i : TrashBin.removed' | no i.getnxt' && no i.getprv'
    getTail' = getTail
    getHead' = getHead
    getHead'.getnxt' = getTail'
    getTail'.getprv' = getHead'
    no getHead'.getprv'
    no getTail'.getnxt'
}

// no-op
pred noChange {
  all i:Node {
    i.getnxt' = i.getnxt &&
    i.getprv' = i.getprv &&
    TrashBin.removed'=TrashBin.removed &&
    List.nodes' = List.nodes &&
    getHead' = getHead &&
    getTail' = getTail
  }
}

pred transitions {
  // all possible actions with a List
  pop_back or
  (some elem: Node | push_back[elem]) or
  pop_front or
  (some elem: Node | push_front[elem]) or
  clear or
  noChange
}

// validity check
pred ListIsValid {
  #List.nodes > 1

  // Head in nodes
  getHead in List.nodes

  // Tail in nodes
  getTail in List.nodes

  // Removed nodes are disconnected
  all i: TrashBin.removed | no i.getnxt
  // Each removed node does not lie in List
  all i: TrashBin.removed | i not in List.nodes
  //  Each node either inside list or in removed
  all i: Node | i in List.nodes or i in TrashBin.removed
  // Each node from list does not lie in trash bin
  all i: List.nodes | i not in TrashBin.removed
  all disj i,j: List.nodes | i.getnxt != j.getnxt
}

fact "init" {
  #Node > 4
  #List.nodes > 3
  ListIsValid
}

run {
  always transitions
  // eventually !ListIsValid
} for 5 but 1..2 steps

// Sanity checks

// Push check
pred sc1 [] {
  eventually some elem: Node {
    elem in TrashBin.removed
    elem in List.nodes'
  }
}

// Pop check
pred sc2 [] {
  eventually some elem: Node {
    elem in List.nodes
    elem in TrashBin.removed'
    #List.nodes > 2
  }
}
