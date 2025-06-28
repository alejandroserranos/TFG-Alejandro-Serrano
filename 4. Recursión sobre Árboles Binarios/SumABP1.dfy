datatype Tree =
    Leaf| 
    Node(value: int, left: Tree, right: Tree)

function Sum(t: Tree): int
    ensures (t == Leaf) ==> Sum(t) == 0
    ensures forall v, l, r :: t == Node(v, l, r) ==> Sum(t) == v + Sum(l) + Sum(r)
{
    match t 
    case Leaf => 0
    case Node(v, l, r) => v + Sum(l) + Sum(r)
}
