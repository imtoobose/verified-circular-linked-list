# Dafny program list.dfy compiled into Python
import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

from module_ import Node, default__
import _dafny

nodeCtr = 0
nodeMap = {}

def getSize(head: Node) -> int:
    tempNode = head
    size = 1
    while tempNode.next != head:
        size += 1
        tempNode = tempNode.next
    return size

def printList(head: Node):
    tempNode = head
    printStr = str(nodeMap[head])
    while tempNode.next != head:
        tempNode = tempNode.next
        printStr += " ⇋ " + str(nodeMap[tempNode])
    print(printStr)

def createNewNode() -> Node:
    global nodeCtr
    newNode = Node()
    newNode.ctor__()
    nodeMap[newNode] = nodeCtr
    nodeCtr += 1
    return newNode

def singletonTest(head: Node):
    print("Checking if the given node is a singleton...")
    if head == head.next == head.prev:
        print("Node is a singleton")
    else:
        print("Node is not a singleton, it has other nodes attached")

def listAddTailTest(newNode: Node, head: Node):
    print("Printing Linked List before list__add__tail:")
    printList(head)
    default__.list__add__tail(newNode, head)
    print("Printing Linked List after list__add__tail:")
    printList(head)

def listAddTest(newNode: Node, head: Node):
    print("Printing Linked List before list__add:")
    printList(head)
    default__.list__add(newNode, head)
    print("Printing Linked List after list__add:")
    printList(head)
    


dll = createNewNode()
singletonTest(dll)
new_dll = createNewNode()
new_dll2 = createNewNode()
new_dll3 = createNewNode()

default__.list__add(new_dll, dll)

print(getSize(dll))
print(nodeMap[dll])
printList(dll)
singletonTest(dll)
listAddTest(new_dll2, dll)
listAddTailTest(new_dll3, dll)

