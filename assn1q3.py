#!/usr/bin/env python

import argparse
from contextlib import contextmanager
import sys, os

parser = argparse.ArgumentParser()
parser.add_argument('sequent', help = 'dd', type = str)

args = parser.parse_args()


def proving(sequent):
    flag = False
    if not sequent:
        flag = True
        return flag
    else:
        left, right = sequent_slicing(sequent)
    if all(atomic(x) for x in left) and all(atomic(x) for x in right):
        if set(left) & set(right):
            flag = True
        print('{:<50} Rule 1'.format(sequent))
        return flag
    else:
        while not (all(atomic(x) for x in left) and all(atomic(x) for x in right)):                
            if any(x[ : 3] == 'neg' for x in left) or any(x[ : 3] == 'neg' for x in right):
                sequent1 = P2(left, right)
                left, right = sequent_slicing(sequent1)
                if all(atomic(x) for x in left) and all(atomic(x) for x in right):
                    print('{:<50} Rule 1'.format(sequent1))
                    return True
            else:
                sequent1 = ''
            if any(and_slicing(arg) for arg in right):
                sequent2, sequent3 = P3a(left, right)
            else:
                sequent2, sequent3 = '', ''
                
            if any(and_slicing(arg) for arg in left):
                sequent4 = P3b(left, right)
            else:
                sequent4 = ''
            if any(or_slicing(arg) for arg in right):
                sequent5 = P4a(left, right)
            else:
                sequent5 = ''
            if any(or_slicing(arg) for arg in left):
                sequent6, sequent7 = P4b(left, right)
            else:
                sequent6, sequent7 = '', ''
            if any(imp_slicing(arg) for arg in right):
                sequent8 = P5a(left, right)
            else:
                sequent8 = ''
            if any(imp_slicing(arg) for arg in left):
                sequent9, sequent10 = P5b(left, right)
            else:
                sequent9, sequent10 = '', ''
            if any(iff_slicing(arg) for arg in right):
                sequent11, sequent12 = P6a(left, right)
            else:
                sequent11, sequent12 = '', ''
            if any(iff_slicing(arg) for arg in left):
                sequent13, sequent14 = P6b(left, right)
            else:
                sequent13, sequent14 = '', ''

            flag = (proving(sequent1) and proving(sequent2) and
                    proving(sequent3) and proving(sequent4) and
                    proving(sequent5) and proving(sequent6) and
                    proving(sequent7) and proving(sequent8) and
                    proving(sequent9) and proving(sequent10) and
                    proving(sequent11) and proving(sequent12) and
                    proving(sequent13) and proving(sequent14))
    return flag

## slice the sequent into two formulae, left and right
def sequent_slicing(sequent):
    left = sequent.split(' seq ')[0][1 : -1]
    right = sequent.split(' seq ')[1][1 : -1]
    if sequent.split(' seq ')[0][1 : -1]:
        left = sequent.split(' seq ')[0][1 : -1].split(', ')
    else:
        left = []
    if sequent.split(' seq ')[1][1 : -1]:
        right = sequent.split(' seq ')[1][1 : -1].split(', ')
    else:
        right = []
    return left, right

## an expression is atomic if contains only symbols but no connectives or brackets
def atomic(x):
    if 'neg' in x or 'and' in x or 'or' in x or 'imp' in x or 'iff' in x or '(' in x or ')' in x:
        return False
    return True


## a string is balanced if it has the same number of opening and closing brackets
def balanced(x):
    stack = []
    Flag = False
    for token in x:
        if token == '(':
            stack.append(token)
        if token == ')':
            stack.pop()
        if len(stack) == 0:
            Flag = True
        else:
            Flag = False
    return Flag


## depending on whether an expression is atomic, and remove the 'neg' connective accordingly.
def neg_removing(x):
    if atomic(x[4 : ]):
        output = x[4 : ]
    else:
        output = x[5 : -1]
    return output


## for each formula with a 'neg' connective, remove the 'neg' and then move the formula to the other side,
## and construct a new sequent
def P2(left, right):
    new_left = []
    new_right = []
    for x in left:
        if x[ : 3] == 'neg':
            new_right.append(neg_removing(x))
        else:
            new_left.append(x)
    for x in right:
        if x[ : 3] == 'neg':
            new_left.append(neg_removing(x))
        else:
            new_right.append(x)
    if len(new_left) > 1:
        l = ', '.join(new_left)
    else:
        l = ''.join(new_left)
    if len(new_right) > 1:
        r = ', '.join(new_right)
    else:
        r = ''.join(new_right)
        
    sequent = '[' + l + '] seq [' + r + ']'
    if sequent:
        print('{:<50} Rule P2'.format(sequent))
    return sequent


## if 'and' exists in a formula and the expression on both sides are balanced, splits the formula into two
def and_slicing(x):
    and_indices = [i for i in range(len(x)) if x[i : i + 3] == 'and']
    if not and_indices:
        return None
    for index in and_indices:
        if balanced(x[ : index - 1]) and balanced(x[index + 4 : ]):
            if atomic(x[ : index - 1]):
                arg1 = x[ : index - 1]
            else:
                arg1 = x[1 : index - 2]
            if atomic(x[index + 4 : ]):
                arg2 = x[index + 4 : ]
            else:               
                arg2 = x[index + 5 : -1]
            return arg1, arg2


## if 'or' exists in a formula and the expression on both sides are balanced, splits the formula into two
def or_slicing(x):
    or_indices = [i for i in range(len(x)) if x[i : i + 2] == 'or']
    if not or_indices:
        return None
    for index in or_indices:
        if balanced(x[ : index - 1]) and balanced(x[index + 3 : ]):
            if atomic(x[ : index - 1]):
                arg1 = x[ : index - 1]
            else:
                arg1 = x[1 : index - 2]
            if atomic(x[index + 3 : ]):
                arg2 = x[index + 3 : ]
            else:
                arg2 = x[index + 4 : -1]
            return arg1, arg2


## if 'imp' exists in a formula and the expression on both sides are balanced, splits the formula into two
def imp_slicing(x):
    imp_indices = [i for i in range(len(x)) if x[i : i + 3] == 'imp']
    if not imp_indices:
        return None
    for index in imp_indices:
        if balanced(x[ : index - 1]) and balanced(x[index + 4 : ]):
            if atomic(x[ : index - 1]):
                arg1 = x[ : index - 1]
            else:
                arg1 = x[1 : index - 2]
            if atomic(x[index + 4 : ]):
                arg2 = x[index + 4 : ]
            else:               
                arg2 = x[index + 5 : -1]
            return arg1, arg2
        else:
            return None


## if 'iff' exists in a formula and the expression on both sides are balanced, splits the formula into two
def iff_slicing(x):
    iff_indices = [i for i in range(len(x)) if x[i : i + 3] == 'iff']
    if not iff_indices:
        return None
    for index in iff_indices:
        if balanced(x[ : index - 1]) and balanced(x[index + 4 : ]):
            if atomic(x[ : index - 1]):
                arg1 = x[ : index - 1]
            else:
                arg1 = x[1 : index - 2]
            if atomic(x[index + 4 : ]):
                arg2 = x[index + 4 : ]
            else:               
                arg2 = x[index + 5 : -1]
            return arg1, arg2

        
## for each formula with an 'and' connective the right, slice it into two formulae,
## and construct two sequents accordingly.
def P3a(left, right):
    for arg in right:
        if and_slicing(arg):
            arg1, arg2 = and_slicing(arg)
            right.remove(arg)
            if len(right) == 0:
                sequent1 = '[' + ', '.join(left) + '] seq [' + arg1 + ']'
                sequent2 = '[' + ', '.join(left) + '] seq [' + arg2 + ']'
            else:
                sequent1 = '[' + ', '.join(left) + '] seq [' + ', '.join(right) + ', ' + arg1 + ']'
                sequent2 = '[' + ', '.join(left) + '] seq [' + ', '.join(right) + ', ' + arg2 + ']'
        else:
            continue
    if sequent1:
        print('{:<50} Rule P3a'.format(sequent1))
    if sequent2:
        print('{:<50} Rule P3a'.format(sequent2))
    return sequent1, sequent2


## for each formula with an 'and' connective the left, slice it into two formula to put them back to the left side.
## and and construct a new sequent.
def P3b(left, right):
    for arg in left:
        if and_slicing(arg):
            arg1, arg2 = and_slicing(arg)
            left.append(arg1)
            left.append(arg2)
            left.remove(arg)
        else:
            continue        
    sequent = '[' + ', '.join(left) + '] seq [' + ', '.join(right) + ']'
    if sequent:
        print('{:<50} Rule P3b'.format(sequent))
    return sequent


## for each formula with an 'or' connective the right, slice it into two formula to put them back to the right side.
## and and construct a new sequent.
def P4a(left, right):
    for arg in right:
        if or_slicing(arg):
            arg1, arg2 = or_slicing(arg)
            right.append(arg1)
            right.append(arg2)
            right.remove(arg)
        else:
            continue
    sequent = '[' + ', '.join(left) + '] seq [' + ', '.join(right) + ']'
    if sequent:
        print('{:<50} Rule P4a'.format(sequent))
    return sequent


## for each formula with an 'or' connective the right, slice it into two formulae,
## and construct two sequents accordingly.
def P4b(left, right):
    for arg in left:
        if or_slicing(arg):
            arg1, arg2 = or_slicing(arg)
            left.remove(arg)
            if len(left) == 0:
                sequent1 = '[' + arg1 + '] seq [' + ', '.join(right) + ']'
                sequent2 = '[' + arg2 + '] seq [' + ', '.join(right) + ']'
            else:
                sequent1 = '[' + ', '.join(left) + ', ' + arg1 + '] seq [' + ', '.join(right) + ']'
                sequent2 = '[' + ', '.join(left) + ', ' + arg2 + '] seq [' + ', '.join(right) + ']'
        else:
            continue
    if sequent1:
        print('{:<50} Rule P4b'.format(sequent1))
    if sequent2:
        print('{:<50} Rule P4b'.format(sequent2))
    return sequent1, sequent2


## for each formula with an 'imp' connective the right, slice it into two formulae and put them back to the left and right side accordingly.
## and and construct a new sequent.
def P5a(left, right):
    for arg in right:
        if imp_slicing(arg):
            arg1, arg2 = imp_slicing(arg)
            left.append(arg1)
            right.append(arg2)
            right.remove(arg)
        else:
            continue
    sequent = '[' + ', '.join(left) + '] seq [' + ', '.join(right) + ']'
    if sequent:
        print('{:<50} Rule P5a'.format(sequent))
    return sequent           


## for each formula with an 'imp' connective the left, slice it into two formulae,
## and construct two sequents accordingly.
def P5b(left, right):
    for arg in left:
        if imp_slicing(arg):
            arg1, arg2 = imp_slicing(arg)
            left.remove(arg)
            
            if len(left) == 0:
                sequent1 = '[' + arg2 + '] seq [' + ', '.join(right) + ']'
            else:
                sequent1 = '[' + ', '.join(left) + ', ' + arg2 + '] seq [' + ', '.join(right) + ']'
            if len(right) == 0:
                sequent2 = '[' + '] seq [' + arg1 + ']'
            else:
                sequent2 = '[' + ', '.join(left) + '] seq [' + ', '.join(right) + ', ' + arg1 + ']'
                
        else:
            continue
    if sequent1:
        print('{:<50} Rule P5b'.format(sequent1))
    if sequent2:
        print('{:<50} Rule P5b'.format(sequent2))
    return sequent1, sequent2


## for each formula with an 'iff' connective the right, slice it into two formulae,
## and construct two sequents accordingly.
def P6a(left, right):
    for arg in right:
        if iff_slicing(arg):
            arg1, arg2 = iff_slicing(arg)
            right.remove(arg)
            if len(right) == 0:
                sequent1 = '[' + ', '.join(left) + ', ' + arg1 + '] seq [' + arg2 + ']'
                sequent2 = '[' + ', '.join(left) + ', ' + arg2 + '] seq [' + arg1 + ']'
            else:
                sequent1 = '[' + ', '.join(left) + ', ' + arg2 + '] seq [' + ', '.join(right) + ', ' + arg1 + ']'
                sequent2 = '[' + ', '.join(left) + ', ' + arg1 + '] seq [' + ', '.join(right) + ', ' + arg2 + ']'
        else:
            continue
    if sequent1:
        print('{:<50} Rule P6a'.format(sequent1))
    if sequent2:
        print('{:<50} Rule P6a'.format(sequent2))
    return sequent1, sequent2


## for each formula with an 'iff' connective the left, slice it into two formulae,
## and construct two sequents accordingly.
def P6b(left, right):
    for arg in left:
        if iff_slicing(arg):
            arg1, arg2 = iff_slicing(arg)
            left.remove(arg)
            if len(left) == 0:
                sequent1 = '[' + arg2 + '] seq [' + ', '.join(right) + ', ' + arg1 + ']'
                sequent2 = '[' + arg1 + '] seq [' + ', '.join(right) + ', ' + arg2 + ']'
            else:
                sequent1 = '[' + ', '.join(left) + ', ' + arg2 + '] seq [' + ', '.join(right) + ', ' + arg1 + ']'
                sequent2 = '[' + ', '.join(left) + ', ' + arg1 + '] seq [' + ', '.join(right) + ', ' + arg2 + ']'
        else:
            continue
    if sequent1:
        print('{:<50} Rule P6b'.format(sequent1))
    if sequent2:
        print('{:<50} Rule P6b'.format(sequent2))
    return sequent1, sequent2


## disable the printing function while returing the returing the result of the proof
@contextmanager
def suppress_stdout():
    with open(os.devnull, "w") as devnull:
        old_stdout = sys.stdout
        sys.stdout = devnull
        try:  
            yield
        finally:
            sys.stdout = old_stdout

            

if __name__ == '__main__':
    with suppress_stdout():
        flag = proving(args.sequent)        
    print(flag)
    flag = proving(args.sequent)
    print('QED.')
