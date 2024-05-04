# Dafny program list.dfy compiled into Python
import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

from module_ import Node, default__
import _dafny

nodeCtr = 0
nodeMap = {}

def createNewNode()-> Node:
    global nodeCtr
    newNode = Node()
    newNode.ctor__()
    nodeMap[id(newNode)] = nodeCtr
    nodeCtr += 1
    return newNode


dll = createNewNode()
new_dll = createNewNode()
print(id(dll))
print(id(dll.next))
print(id(dll.prev))
print(id(new_dll))
default__.list__add(new_dll, dll)
print(id(new_dll.next))
print(id(dll.next))