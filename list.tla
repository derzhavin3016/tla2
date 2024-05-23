------------------------ MODULE list ------------------------
EXTENDS Naturals

CONSTANTS Node

VARIABLES removed, head, tail, nxt, prv, nodes, popLock, pushLock

List ==
    /\ nodes = head @@ (nxt [nodes])
    /\ \E n \in nodes : tail = n
    /\ \A n \in nodes : ~(nxt[n] = n)
    /\ nxt = [n \in nodes |-> prv[n]]
    /\ ~(prv[head] \in nodes)
    /\ ~(nxt[tail] \in nodes)
    /\ head @@ (nxt [head]) = Node @@ (nxt [Node])

getnxt == nxt
getprv == prv
getHead == head
getTail == tail

pop_back ==
    /\ Cardinality(nodes) > 2
    /\ removed' = removed \cup {tail}
    /\ nodes' = nodes \ {tail}
    /\ tail' = prv[tail]
    /\ prv[tail']' = prv[tail']
    /\ ~(nxt[prv[tail']]')
    /\ popLock' = FALSE

push_back(new) ==
    /\ new \in removed
    /\ removed' = removed \ {new}
    /\ nodes' = nodes \cup {new}
    /\ tail' = new
    /\ prv[tail']' = tail
    /\ nxt[tail] = tail'
    /\ pushLock' = FALSE

pop_front ==
    /\ Cardinality(nodes) > 2
    /\ removed' = removed \cup {head}
    /\ nodes' = nodes \ {head}
    /\ head' = nxt[head]
    /\ nxt[head']' = nxt[head']
    /\ ~(prv[nxt[head']])
    /\ popLock' = FALSE

push_front(e) ==
    /\ e \in removed
    /\ removed' = removed \ {e}
    /\ nodes' = nodes \cup {e}
    /\ head' = e
    /\ nxt[head']' = head
    /\ prv[head] = head'
    /\ pushLock' = FALSE

clear ==
    /\ \A i \in nodes : i \notin {tail, head} => i \in removed'
    /\ removed' = Node \ {tail, head}
    /\ nodes' = tail @@ head
    /\ \A i \in removed' : ~(nxt[i]') /\ ~(prv[i]')
    /\ tail' = tail
    /\ head' = head
    /\ nxt[head']' = tail'
    /\ prv[tail']' = head'
    /\ ~(prv[head'])
    /\ popLock' = FALSE
    /\ pushLock' = FALSE

noChange ==
    \A i \in Node : i.nxt' = i.nxt
                  /\ i.prv' = i.prv
                  /\ removed' = removed
                  /\ nodes' = nodes
                  /\ head' = head
                  /\ tail' = tail
                  /\ popLock' = FALSE
                  /\ pushLock' = FALSE

transitions ==
    \/ pop_back
    \/ (\E elem \in Node : push_back(elem))
    \/ pop_front
    \/ (\E elem \in Node : push_front(elem))
    \/ clear
    \/ noChange

ListIsValid ==
    Cardinality(nodes) > 1
    /\ head \in nodes
    /\ tail \in nodes
    /\ \A i \in removed : ~(nxt[i])
    /\ \A i \in removed : i \notin nodes
    /\ \A i \in Node : (i \in nodes \/ i \in removed)
    /\ \A i \in nodes : i \notin removed

Init ==
  Cardinality(Node) > 4
  /\ Cardinality(nodes) > 3
  /\ ListIsValid
  /\ popLock = FALSE
  /\ pushLock = FALSE

Next == transitions

Spec == Init /\ [][Next]_<<removed, head, tail, nxt, prv, nodes, popLock, pushLock>>

THEOREM Spec => []<><<removed, head, tail, nxt, prv, nodes, popLock, pushLock>>_<<removed', head', tail', nxt', prv', nodes', popLock', pushLock'>>
