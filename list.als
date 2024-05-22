module list

sig Node {}

one sig TrashBin {
  removed: set Node -- removed nodes
}

one sig List {
  head: lone Node,
  tail: lone Node,
  next: Node -> lone Node,
  prev: Node -> lone Node,
  nodes: set Node -- list content
} {
  nodes = head.*next
  some nodes => one tail
  no ^next & iden -- no cycles
  next = ~prev     -- symmetric
  no prev[head]   -- head is a head
  no next[tail]   -- tail is a tail
  head.^next = Node.^next -- reachability
}

fun getNext : Node->Node { List.next }
fun getPrev : Node->Node { List.prev }
fun getHead  : one Node { List.head }
fun getTail  : one Node { List.tail }

pred pop_back {
  --prereq
    #nodes > 2

  --action
    TrashBin.removed' = TrashBin.removed + getTail
    List.nodes' = List.nodes - getTail
  -- rebinding
    getTail' = getTail.getPrev
    getTail'.getPrev' = getTail'.getPrev
    no getTail'.getNext'

  --postreq
    no getTail.getNext'
    no getTail.getPrev'
    getHead' = getHead
    all i: Node - getTail - getTail' {i.getNext' = i.getNext && i.getPrev' = i.getPrev}
}

pred push_back[new: Node] {
  --prereq
    new in TrashBin.removed

  --action
    TrashBin.removed' = TrashBin.removed - new
    List.nodes' = List.nodes + new
    -- rebinding
    getTail' = new
    getTail'.getPrev' = getTail
    getTail.getNext' = getTail'

  --postreq
    no getTail'.getNext'
    getTail.getPrev' = getTail.getPrev
    getHead' = getHead
    all i: Node - getTail - getTail' {i.getNext' = i.getNext && i.getPrev' = i.getPrev}
}

pred pop_front {
	--prereq
		#nodes > 2

	--action
		TrashBin.removed' = TrashBin.removed + getHead
		List.nodes' = List.nodes - getHead
		getHead' = getHead.getNext
		getHead'.getNext' = getHead'.getNext
		no getHead'.getPrev'

	--postreq
		no getHead.getPrev'
		no getHead.getNext'
		getTail' = getTail
		all i: Node - getHead - getHead' {i.getNext' = i.getNext && i.getPrev' = i.getPrev}
}

pred push_front[e: item] {
	--prereq
		e in TrashBin.removed

	--action
		TrashBin.removed' = TrashBin.removed - e
		List.nodes' = List.nodes + e
		getHead' = e
		getHead'.getNext' = getHead
		getHead.getPrev' = getHead'

	--postreq
		no getHead'.getPrev'
		getHead.getNext' = getHead.getNext
		getTail' = getTail
		all i: Node - getHead - getHead' {i.getNext' = i.getNext && i.getPrev' = i.getPrev}
}

pred clear{
	--prereq

	--action
		all i: item - getTail - getHead | i in TrashBin.removed'
		TrashBin.removed' = item - getTail - getHead
		List.nodes' = getTail + getHead

	--postreq
		all i : TrashBin.removed' | no i.getNext' && no i.getPrev'
		getTail' = getTail
		getHead' = getHead
		getHead'.getNext' = getTail'
		getTail'.getPrev' = getHead'
		no getHead'.getPrev'
		no getTail'.getNext'
}

pred noChange { all i:item {i.getNext' = i.getNext && i.getPrev' = i.getPrev && TrashBin.removed'=TrashBin.removed && List.nodes' = List.nodes && getHead' = getHead && getTail' = getTail} }

pred transitions { -- all possible actions with a List
	pop_back or
	(some e: item | push_back[e]) or
	pop_front or
	(some e: item | push_front[e]) or
	clear or
	noChange
}

pred ListIsValid {
	#List.nodes > 1
	getHead in List.nodes -- L has the Head
	getTail in List.nodes -- L has the Tail
	getHead != getTail -- Acyclicity
	getPrev = ~getNext -- Double Linkage
	no getTail.getNext -- Last is a Tail
	no getHead.getPrev -- First is a Head
	all i: item | i in List.nodes or i in TrashBin.removed -- The union of nodes and removed is a complete set
	all i: List.nodes | i not in TrashBin.removed -- nodes and removed are non-crossing sets
	all i: TrashBin.removed | i not in List.nodes -- nodes and removed are non-crossing sets
	all i: TrashBin.removed | no i.getNext -- Unconnectivity of removed
	all i: List.nodes - List.Last  | i.getNext != i -- Acyclicity
	all i: List.nodes - List.Last  | one i.getNext -- Connectivity
	all i: List.nodes - List.Last  | i.getNext not in TrashBin.removed -- Connectivity
	all i: List.nodes - List.Last  | List.Last in i.^getNext	-- Connectivity
	all disj i,j: List.nodes | i.getNext != j.getNext -- Linearity
}

fact "init" {
	#item > 4
	#List.nodes > 3
	ListIsValid
}

run {

	 always transitions

	---------------------------
	 -- eventually !ListIsValid -- invariant check !SHOULD RETURN "NO INSTANCE FOUND"!
	---------------------------

	-- uncomment any of sanity-check predicates to check it
	---------------------------
	-- sc1 -- deleting is possible
	-- sc2 -- full list is possible
	-- sc3 -- push happens
	-- sc4 -- pop happens
	---------------------------

} for 5 but 1..2 steps

---------------------------
-- Sanity-check predicates
---------------------------

pred sc1 [] {
	-- deleting is possible
	eventually some removed
}
pred sc2 [] {
	-- full list is possible
	eventually no removed
}
pred sc3 [] {
	-- push happens
	eventually some e: item {
		e in TrashBin.removed
		e in List.nodes'
	}
}
pred sc4 [] {
	-- pop happens
	eventually some e: item {
		e in List.nodes
		e in TrashBin.removed'
		#List.nodes > 2
	}
}
