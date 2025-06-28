datatype Tree =
    Leaf |
    Node(value: int, left: Tree, right: Tree)

function Sum(t: Tree): int
    ensures Sum(t) >= 0 || exists v: int :: v < 0 && v in t
{
    match t 
    case Leaf => 0
    case Node(v, l, r) => v + Sum(l) + Sum(r)
}
