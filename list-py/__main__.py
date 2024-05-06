# Dafny program list.dfy compiled into Python
import sys
import random
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
        printStr += " <-> " + str(nodeMap[tempNode])
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
    print("Printing List before list__add__tail:")
    printList(head)
    default__.list__add__tail(newNode, head)
    print("Printing List after list__add__tail:")
    printList(head)

def listAddTest(newNode: Node, head: Node):
    print("Printing List before list__add:")
    printList(head)
    default__.list__add(newNode, head)
    print("Printing List after list__add:")
    printList(head)

def delNodeInitTest(entry: Node):
    print("Printing List before list__del__entry:")
    printList(entry)
    temp = entry.next
    default__.list__del__int(entry)
    print("Printing List after list__del__entry:")
    printList(temp)

def replaceInitTest(head: Node):
    newNode = createNewNode()
    print("Id of New Node: " + str(nodeMap[newNode]))
    for i in range(3):
        temp = createNewNode()
        default__.list__add(temp, head)
    print("Printing List before Replacement")
    printList(head)
    nodeToBeReplaced = head.next
    print("Replacing Node with Id " + str(nodeMap[nodeToBeReplaced]) + " in the list with Node with Id " + str(nodeMap[newNode]))
    default__.list__replace__init(nodeToBeReplaced, newNode)
    printList(head)

def listIsLastTest(head: Node):
    size = getSize(head)
    temp = head
    for i in range(size - 1):
        temp = temp.next
    print("List: ")
    printList(head)
    print("Checking if Node with Val " + str(nodeMap[temp]) + " is the last node")
    print(default__.list__is__last(temp, head))

def listEmpty(head: Node):
    print("List: ")
    printList(head)
    print("Checking if the list has only one node")
    print(default__.list__empty(head))



def randomCheck():
    nodeMap.clear()
    global nodeCtr
    nodeCtr = 0
    node0 = createNewNode()
    node1 = createNewNode()
    node2 = createNewNode()
    default__.list__add__tail(node1, node0)
    default__.list__add__tail(node2, node0)
    print("Initial List: ")
    printList(node0)

    for i in range(10):
        listSize = getSize(node0)
        if listSize == 1:
             randomOp = random.choice([1, 2])
        else:
            randomOp = random.randrange(0, 4)
        
        if randomOp == 0:   # Delete Operation
            randomNode = random.randrange(1, listSize)
            temp = node0
            for hops in range(randomNode):
                temp = temp.next
            print("Printing List before deleting node in position " + str(randomNode + 1))
            printList(node0)
            default__.list__del__init(temp)
            print("Printing List after deleting node")
            printList(node0)
        
        elif randomOp == 1:   # list__add Operation
            numNodes = random.randrange(1, 4)
            temp = node0
            print("Printing List before adding " + str(numNodes) + " node(s) after head")
            printList(node0)
            for hops in range(numNodes):
                temp = createNewNode()
                default__.list__add(temp, node0)
            print("Printing List after adding " + str(numNodes) + " node(s) after head")
            printList(node0)
        
        elif randomOp == 2:   # list__add__tail Operation
            numNodes = random.randrange(1, 4)
            temp = node0
            print("Printing List before adding " + str(numNodes) + " node(s) to the tail")
            printList(node0)
            for hops in range(numNodes):
                temp = createNewNode()
                default__.list__add__tail(temp, node0)
            print("Printing List after adding " + str(numNodes) + " node(s) to the tail")
            printList(node0)

        elif randomOp == 3: #list
            size = getSize(node0)
            newNode = createNewNode()
            print("Id of New Node: " + str(nodeMap[newNode]) + ", list of nodes before replacement: ")
            printList(node0)
            randNode = random.randrange(1, size)
            temp = node0
            for i in range(randNode):
                temp = temp.next
            print("Replacing Node " + str(randNode + 1) + "(Id: " + str(nodeMap[temp]) + ") with Node of Id: " + str(nodeMap[newNode]))
            default__.list__replace__init(temp, newNode)
            printList(node0)
            


dll = createNewNode()
singletonTest(dll)
listEmpty(dll)
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
listIsLastTest(dll)
replaceInitTest(dll)
print("\nStart of Random Tests")
randomCheck()
# print(nodeMap)
