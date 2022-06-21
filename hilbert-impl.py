#!/usr/bin/python3

import sys
import copy

DEBUG = False

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


class ProofStep:
  def __init__(self, context : [Node], node : Node):
    self.context = context
    self.node = node
    self.position = 0

  def __eq__(self, o):
    return self.node == o.node

  def __repr__(self):
    return str(self.position) + "\t" + str(self.node) + "\t?"


class ContextFree(ProofStep):
  pass


class A1(ContextFree): # a -> (b -> a)
  def __init__(self, context : [Node], a : Node, b : Node):
    self.node = Node(a , Node(b, a))
    self.context = context
    self.position = 0

  def __repr__(self):
    return str(self.position) + "\t" + str(self.node) + "\tA1"


class A2(ContextFree): # (a -> (b -> c)) -> ((a -> b) -> (a -> c))
  def __init__(self, context : [Node], a : Node, b : Node, c : Node):
    self.node = Node(Node(a, Node(b, c)), Node(Node(a, b), Node(a, c)))
    self.context = context
    self.position = 0

  def __repr__(self):
    return str(self.position) + "\t" + str(self.node) + "\tA2"


class MP(ProofStep): # A, A -> B / B
  def __init__(self, context : [Node], implication : ProofStep, antecedent : ProofStep):
    if context != implication.context or context != antecedent.context:
      raise Exception

    if not implication.node.comp() or implication.node.left != antecedent.node:
      raise Exception

    self.node = implication.node.right
    self.context = context
    self.implication = implication
    self.antecedent = antecedent
    self.position = 0

  def __repr__(self):
    return str(self.position) + "\t" + str(self.node) + "\t" + str(self.implication.position) + "," + str(self.antecedent.position)


class Member(ContextFree):
  def __init__(self, context : [Node], index : int):
    if index < 0 or index >= len(context):
      raise Exception

    self.node = context[index]
    self.index = index
    self.context = context
    self.position = 0

  def __repr__(self):
    return str(self.position) + "\t" + str(self.node) + "\tAssumption " + str(self.index + 1)


class TopMember(ProofStep):
  def __init__(self, context : [Node]):
    self.node = context[-1]
    self.context = context
    self.position = 0

  def __repr__(self):
    return str(self.position) + "\t" + str(self.node) + "\tLast Assumption " + str(len(self.context))


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


def findImplication(context : [Node], prop : Node):
  for i in context:
    if i.comp():
      if i.right == prop:
        return i


def hilbert(context : [Node], prop : Node):
  if DEBUG: print("<<: " + str(context) + " ⊢ " + str(prop))
  if isA1(prop):
    return A1(context, prop.left, prop.right.left)

  if isA2(prop):
    return A2(context, prop.left.left, prop.left.right.left, prop.left.right.right)

  if len(context) > 0 and prop in context[:-1]:
    return Member(context, context.index(prop))

  if len(context) > 0 and prop == context[-1]:
    return TopMember(context)

  for k in range(len(context)):
    if context[k].right == prop:
      for j in range(len(context)):
        if context[k].left == context[j]:
          pk = Member(context, k) if k < len(context) - 1 else TopMember(context)
          pj = Member(context, j) if j < len(context) - 1 else TopMember(context)
          return MP(context, pk, pj)

  if prop.left != None:
    newContext = context + [prop.left]
    proof = hilbert(newContext, prop.right)
    if DEBUG: print(">>: " + str(newContext) + " ⊢ " + str(proof))
    return transform(newContext, proof)

  # FINALLY
  print("<<" + str(context) + " ⊢ X")
  print("<<" + str(context) + " ⊢ (X>" + str(prop) + ")")
  print("X?", end=' ')
  x = parse(input())
  p1 = hilbert(context, x)
  if DEBUG: print(">>: " + str(context) + " ⊢ " + str(p1))
  p2 = hilbert(context, Node(x, prop))
  if DEBUG: print(">>: " + str(context) + " ⊢ " + str(p2))
  return MP(context, p2, p1)


def transform(context: [Node], proof : ProofStep): # Γ,a ⊢ b  =>  Γ ⊢ a->b
  if DEBUG: print("<>: " + str(context) + " ⊢ " + str(proof))
  if len(context) == 0:
    raise Exception

  newContext = copy.deepcopy(context)[:-1]
  a = context[-1]
  b = proof.node
  resultNode = Node(a, b)

  if isA1(resultNode):
    return A1(newContext, a, b.left)
  
  if isA2(resultNode):
    return A2(newContext, a.left, a.right.left, a.right.right)

  result = None
  if isinstance(proof, ContextFree):
    i = A1(newContext, b, a)
    newProof = None
    if isinstance(proof, A1):
      newProof = A1(newContext, b.left, b.right.left)
    elif isinstance(proof, A2):
      newProof = A2(newContext, b.left.left, b.left.right.left, b.left.right.right)
    elif isinstance(proof, Member):
      if proof.index == len(newContext) - 1:
        newProof = TopMember(newContext)
      else:
        newProof = Member(newContext, proof.index)
    result = MP(newContext, i, newProof)
  elif isinstance(proof, TopMember):
    p1 = A2(newContext, b, Node(b, b), b)
    p2 = A1(newContext, b, Node(b, b))
    p3 = MP(newContext, p1, p2)
    p4 = A1(newContext, b, b)
    result = MP(newContext, p3, p4)
  elif isinstance(proof, MP):
    p1 = transform(context, proof.implication)
    p2 = transform(context, proof.antecedent)
    p3 = A2(newContext, a, proof.antecedent.node, b)
    p4 = MP(newContext, p3, p1)
    result = MP(newContext, p4, p2)

  return result


def serialize(proof : ProofStep):
  proof.position += 1
  seq = [proof]
  if isinstance(proof, MP):
    proof.antecedent.position += proof.position
    seq += serialize(proof.antecedent)
    proof.implication.position += proof.position + len(seq) - 1
    seq += serialize(proof.implication)

  return seq


# try:
proof = hilbert([], parse(sys.argv[1]))
if DEBUG: print(">>: ⊢ " + str(proof))
proofSequence = serialize(proof)
for i in range(len(proofSequence)):
  proofSequence[i].position = len(proofSequence) - i
for p in proofSequence:
  print(str(p))
  # print(str(p.context) + " ⊢ " + str(p))
# except:
  # print("reject")