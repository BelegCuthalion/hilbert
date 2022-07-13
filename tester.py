#!/usr/bin/python3

import sys

atoms = ['p', 'q', 'r', 's', 'a', 'b', 'c', 'd']

class Node:
  def __init__(self, left, right):
    self.left = left
    self.right = right
    self.label = ''
  
  def __repr__(self):
    if self.comp():
      return "(" + str(self.left) + ">" + str(self.right) + ")"
    else:
      return self.label

  def __eq__(self, o):
    if o == None:
      return False

    if self.comp() and o.comp():
      return self.left == o.left and self.right == o.right
    else:
      return self.label == o.label

  def comp(self):
    if self.left != None and self.right != None:
      return True
    elif self.left == None and self.right == None:
      return False
    else:
      raise Exception


def parse(string):
  node = Node(None, None)
  stack = [node]
  for c in string:
    if c == '(':
      node.left = Node(None, None)
      stack.append(node)
      node = node.left
    elif c in atoms:
      node.label = c
      node = stack.pop()
    elif c == '>':
      node.label = c
      node.right = Node(None, None)
      stack.append(node)
      node = node.right
    elif c == ')':
      node = stack.pop()

  return node

def isA1(prop : Node):
  return  (prop.comp() and
          prop.right.comp() and
          prop.left == prop.right.right)


def isA2(prop : Node):
  return  (prop.comp() and
          prop.left.comp() and
          prop.left.right.comp() and
          prop.right.comp() and
          prop.right.left.comp() and
          prop.right.right.comp() and
          prop.left.left == prop.right.left.left and
          prop.left.right.left == prop.right.left.right and
          prop.left.right.right == prop.right.right.right)


def check(proof):
  conclusion = parse(proof[-1][0])
  r = proof[-1][1]
  if r == "A1":
    return isA1(conclusion)

  if r == "A2":
    return isA2(conclusion)

  #FINALLY
  k, j = [int(i) for i in r.split(',')]
  pj = parse(proof[j-1][0])
  pk = parse(proof[k-1][0])
  if pk.comp() and pk.left == pj and pk.right == conclusion:
    return check(proof[:k]) and check(proof[:j])
  else:
    print("ERROR:", len(proof), str(pk), str(pj), str(conclusion), "MP", str(k), str(j))
    return False
  
  

p = [l.split() for l in open(sys.argv[1]).read().splitlines()]

proof = [None] * len(p)
for x in p:
  if(len(proof) < int(x[0])):
    print("You have an extra line! " + int(x[0]))
  else:
    proof[int(x[0])-1] = x[1:]

print(check(proof))