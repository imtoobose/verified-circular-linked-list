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

# Auxilary Functions
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

# Functions used for Sanity Testing
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

def listEmptyTest(head: Node):
    print("List: ")
    printList(head)
    print("Checking if the list has only one node")
    print(default__.list__empty(head))

def listMoveTest(head: Node):
    print("Current List: ")
    printList(head)
    newList = createNewNode()
    default__.list__add__tail(createNewNode() ,newList)
    default__.list__add__tail(createNewNode() ,newList)
    print("List whose head is to be Added after 1st Node: ")
    printList(newList)
    default__.list__move(newList, head)
    print("List: ")
    printList(head)

def listMoveTailTest(head: Node):
    print("Current List: ")
    printList(head)
    newList = createNewNode()
    default__.list__add__tail(createNewNode() ,newList)
    default__.list__add__tail(createNewNode() ,newList)
    print("List whose head is to be Added at the tail of prev list: ")
    printList(newList)
    default__.list__move__tail(newList, head)
    print("List: ")
    printList(head)


# This function calls any of the functions defined in module_.py randomly for a total of 10 times
# It shows the list before the function is called and after the operation is performed
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
            randomOp = random.randrange(2, 5)
        else:
            randomOp = random.randrange(0, 5)
        
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
        
        elif randomOp == 1: # list__replace__init Operation
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
        
        elif randomOp == 2:   # list__add Operation
            numNodes = random.randrange(1, 4)
            temp = node0
            print("Printing List before adding " + str(numNodes) + " node(s) after head")
            printList(node0)
            for hops in range(numNodes):
                temp = createNewNode()
                default__.list__add(temp, node0)
            print("Printing List after adding " + str(numNodes) + " node(s) after head")
            printList(node0)
        
        elif randomOp == 3:   # list__add__tail Operation
            numNodes = random.randrange(1, 4)
            temp = node0
            print("Printing List before adding " + str(numNodes) + " node(s) to the tail")
            printList(node0)
            for hops in range(numNodes):
                temp = createNewNode()
                default__.list__add__tail(temp, node0)
            print("Printing List after adding " + str(numNodes) + " node(s) to the tail")
            printList(node0)
        
        elif randomOp == 4: # list__replace__init Operation
            newList = createNewNode()
            for i in range(random.randrange(0, 2)):
                default__.list__add__tail(createNewNode() ,newList)
            print("List whose head is to be Added at the tail of prev list: ")
            printList(newList)
            default__.list__move__tail(newList, node0)
            print("List: ")
            printList(node0)

# Create a node and test if it is a single Node
# It can be done by using either singletonTest() or listEmptyTest()
dll = createNewNode()
singletonTest(dll)
listEmptyTest(dll)

# Create 3 more nodes that can be used as we please
new_dll = createNewNode()
new_dll2 = createNewNode()
new_dll3 = createNewNode()

# Add a new node to the head
default__.list__add(new_dll, dll)

# Start Other Sanity Tests
listAddTest(new_dll2, dll)
listAddTailTest(new_dll3, dll)
listIsLastTest(dll)
replaceInitTest(dll)
listMoveTest(dll)
listMoveTailTest(dll)

# Run Random Tests to Check output
print("\nStart of Random Tests")
randomCheck()
