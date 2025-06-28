from dataclasses import dataclass
from typing import Union

# Definición del tipo Tree
class Tree:
    pass

@dataclass
class Leaf(Tree):
    pass

@dataclass
class Node(Tree):
    value: int
    left: Tree
    right: Tree

# Función recursiva Sum
def Sum(t: Tree) -> int:
    if isinstance(t, Leaf):
        return 0
    elif isinstance(t, Node):
        return t.value + Sum(t.left) + Sum(t.right)
    else:
        raise TypeError("Tipo de árbol no reconocido")