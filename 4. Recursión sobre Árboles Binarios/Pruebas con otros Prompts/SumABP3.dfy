// Declaración del tipo de árbol binario
datatype Tree =
    Leaf
  | Node(value: int, left: Tree, right: Tree)

// Función recursiva que suma todos los valores del árbol
function Sum(t: Tree): int
  decreases t  // Asegura que la recursión termina
{
  match t 
  case Leaf => 0
  case Node(v, l, r) => v + Sum(l) + Sum(r)
}
