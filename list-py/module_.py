import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def INIT__LIST__HEAD(node):
        (node).prev = node
        (node).next = node

    @staticmethod
    def internal__list__add(new__node, prev, next):
        (next).prev = new__node
        (new__node).next = next
        (new__node).prev = prev
        (prev).next = new__node

    @staticmethod
    def list__add(new__node, head):
        default__.internal__list__add(new__node, head, head.next)

    @staticmethod
    def list__add__tail(new__node, head):
        default__.internal__list__add(new__node, head.prev, head)
        
    @staticmethod
    def internal__list__del(prev, next):
        d_0_prev__next_: Node
        d_0_prev__next_ = prev.next
        (next).prev = prev
        (prev).next = next

    @staticmethod
    def list__del__entry(entry):
        default__.internal__list__del(entry.prev, entry.next)

    @staticmethod
    def list__replace(old__node, new__node):
        (new__node).next = old__node.next
        obj0_ = new__node.next
        obj0_.prev = new__node
        (new__node).prev = old__node.prev
        obj1_ = new__node.prev
        obj1_.next = new__node

    @staticmethod
    def list__replace__init(old__node, new__node):
        default__.list__replace(old__node, new__node)
        default__.INIT__LIST__HEAD(old__node)

    @staticmethod
    def list__del__init(entry):
        default__.list__del__entry(entry)
        default__.INIT__LIST__HEAD(entry)

    @staticmethod
    def list__is__last(list, head):
        ret: bool = False
        ret = (list.next) == (head)
        return ret

    @staticmethod
    def list__empty(head):
        return (head.next) == (head)

    @staticmethod
    def Singleton(n):
        return ((n.prev) == (n.next)) and ((n.next) == (n))

    @staticmethod
    def IndexOf(s, e):
        def iife0_(_let_dummy_0):
            d_1_i_: int = None
            with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                assign_such_that_0_: int
                for assign_such_that_0_ in _dafny.IntegerRange(0, len(s)):
                    d_1_i_ = assign_such_that_0_
                    if (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) and (((s)[d_1_i_]) == (e)):
                        raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                raise Exception("assign-such-that search produced no value (line 9)")
                pass
            return d_1_i_
        return iife0_(0)
        

    @staticmethod
    def get__next__seq__idx(s, i):
        if (len(s)) == (1):
            return 0
        elif True:
            return _dafny.euclidian_modulus((i) + (1), len(s))

    @staticmethod
    def get__prev__seq__idx(s, i):
        if (len(s)) == (1):
            return 0
        elif True:
            return _dafny.euclidian_modulus(((i) + (len(s))) - (1), len(s))

    @staticmethod
    def NoDupes(a):
        def lambda0_(forall_var_0_):
            def lambda1_(forall_var_1_):
                d_3_j_: int = forall_var_1_
                return not (((((0) <= (d_2_i_)) and ((d_2_i_) < (len(a)))) and (((0) <= (d_3_j_)) and ((d_3_j_) < (len(a))))) and ((d_2_i_) != (d_3_j_))) or (((a)[d_2_i_]) != ((a)[d_3_j_]))

            d_2_i_: int = forall_var_0_
            return _dafny.quantifier(_dafny.IntegerRange(0, len(a)), True, lambda1_)

        return _dafny.quantifier(_dafny.IntegerRange(0, len(a)), True, lambda0_)


class Node:
    def  __init__(self):
        self.prev: Node = None
        self.next: Node = None
        pass

    def __dafnystr__(self) -> str:
        return "_module.Node"
    def ctor__(self):
        (self).prev = self
        (self).next = self

