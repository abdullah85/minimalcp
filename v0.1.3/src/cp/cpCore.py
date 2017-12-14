'''
cp is a tool for modeling, verifying card protocols.
This file, cpCore.py, contains the core engine for making 
inferences and interacting with the Z3 SAT Solver.
It constructs the formulae when provided with the input
of the distribution type alongwith the list of agents.
'''

from z3 import *

def Equiv(a,b):
  return And(Implies(a,b), Implies(b,a))

def ExactlyK(fList, k):
  argList = [] # To avoid side effects
  for f in fList:
    argList.append(f)
  argList.append(k) # Append the value of k
  expr2 = AtLeast(argList)
  expr1 = AtMost(argList)
  return And(expr1,expr2)

def AtMostK(fList, k):
  argList = []
  for f in fList:
    argList.append(f)
  argList.append(k)
  return AtMost(argList)

class CP:
  """
  For any p,q \in Agts and i \in cards, we have the following propositions,
  a) p__i    - denoting that p has i
  b) Kpq__i  - denoting that p knows that q has i
  c) KpNq__i - denoting that p knows that q does not have i
  """
  def __init__(self, distrLst, agtList):
    """
    Let the distribution type be of the form <s_1, ... s_n>
    where n is the number of agents. Then, the only data structures 
    maintained in the CP class are

    a) self.dType  -- a dictionary associating an agent to s_i
    b) self.agents -- the list of agents ([a_1, ..., a_n])
    c) self.dList  -- the distribution as a list ([s_1, s_2 ... s_n])
    d) self.nCards -- sum(self.dList)
    e) self.cards  -- range(0,self.nCards)

    The propositional formulae can be constructed using the above data.
    """
    if len(distrLst) != len(agtList):
      raise RuntimeError('Distribution type does not match the agent list.')
    self.dList  = distrLst
    self.agents = agtList
    self.dType  = {}
    i = 0
    while i < len(agtList) :
      agt  = self.agents[i]
      nAgt = self.dList[i]
      self.dType[agt] = nAgt
      i = i + 1
    self.nCards = sum(distrLst)    
    self.cards  = range(0, self.nCards)

  def getProp(self, p, i): # Corresponds to the p__i
    return Bool(p + '__'+str(i))

  def getPropList(self, p):
    return BoolVector(p, self.nCards)

  def getKProp(self, p, q, i):
    return Bool('K'+p+q+'__'+str(i))

  def getKNProp(self, p, q, i):
    return Bool('K'+p+'N'+q+'__'+str(i))

  def getKList(self, p, q):
    '''
    >>> sadi234 = CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> p1, p2  = sadi234.getKList('a', 'b')[0], sadi234.getKProp('a', 'b', 0)
    >>> p1.sexpr() == p2.sexpr()
    True
    '''
    return BoolVector('K'+p+q,self.nCards)

  def getKNList(self, p, q):
    '''
    >>> sadi234 = CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> q1, q2  = sadi234.getKNList('a', 'b')[0], sadi234.getKNProp('a', 'b', 0)
    >>> q1.sexpr() == q2.sexpr()
    True
    '''
    return BoolVector('K'+p+'N'+q,self.nCards)

  #TODO :  Better and more succinct examples for all the invariants.
  def validDeal(self) :
    """
    Returns a formula that enforces a valid deal to all 
    propositional variables of the form p__i for all 
    p \in Agts and all i \in Cards.

    >>> s, sadi234 = Solver(), CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> s.add(sadi234.validDeal())
    >>> s.add(And( Bool('a__0'), Bool('a__1'), Bool('a__2')))
    >>> s.check()
    unsat
    """
    cList = []
    for agt in self.agents:
      nAgt = self.dType[agt]
      aL = self.getPropList(agt)
      cList.append(ExactlyK(aL, nAgt))
    return And(And(cList), self.ownership())

  def ownership(self):
    """
    Encodes the constraint that every card is assigned to exactly one agent

    >>> s, sadi234 = Solver(), CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> s.push()
    >>> s.add(sadi234.ownership())

    Having added the ownership formula check the following :

    a) The same card cannot be assigned to different agents,

    >>> s.push()
    >>> s.add(And(Bool('a__0'), Bool('b__0')))
    >>> s.check()
    unsat
    >>> s.pop() 

    b) Every card (here '7') has to be assigned to some agent,

    >>> s.push()
    >>> s.add( And(Not(Bool('a__7')), Not(Bool('b__7')), \
                    Not(Bool('c__7')), Not(Bool('e__7'))) )
    >>> s.check()
    unsat
    """
    exprL = []
    for card in self.cards:
      cList = []
      for agt in self.agents:
        aCard = self.getProp(agt, card)
        cList.append(aCard)
      exprL.append( ExactlyK(cList, 1) )
    return (And(exprL))

  def hand2K(self):
    """
    Expresses the fact that if any agent has a particular card,
    then, he knows nobody else has it.

    >>> s, sadi234 = Solver(), CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> s.push()
    >>> s.add(sadi234.hand2K())
    >>> s.add( And(Bool('a__0'), Not(Bool('KaNb__0'))) )
    >>> s.check()
    unsat
    """
    exprL = []
    for card in self.cards:
      cList = []
      for p in self.agents:
        ante = self.getProp(p, card)
        conseqList = []
        for q in self.agents:
          if p != q:
            conseqList.append( self.getKNProp(p, q, card) )
        conseq = And(conseqList)
        exprL.append( Implies(ante, conseq) )
    return (And(exprL))

  def kConsistency(self):
    """
    Encodes the constraint that either Not(Kab[i]) or Not(KaNb[i]) 
    is true for every agent a,b and every card 'i'

    >>> s, sadi234 = Solver(), CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> s.push()
    >>> s.add(sadi234.kConsistency())
    >>> s.add(And(Bool('Kab__0'), Bool('KaNb__0')) )
    >>> s.check()
    unsat
    """
    exprL = []
    for p in self.agents:
      for card in self.cards:
        for q in self.agents:
          if p != q:
            Kijc  = self.getKProp(p, q, card)
            KiNjc = self.getKNProp(p, q, card)
            exprL.append(Or(Not(Kijc), Not(KiNjc)))
    return (And(exprL))

  def ownershipK(self): # Knowledge version of ownership()
    """
    This is the knowledge version of ownership. By this, we ensure that all knowledge 
    variables of the form Kpq are consistent with the requirements of ownership. 
    That is, every agent *knows* that each card belongs to exactly one agent.

    >>> s, sadi234 = Solver(), CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> s.add(sadi234.ownershipK())
    >>> s.add(sadi234.kConsistency()) # Needs kConsistency to work correctly

    >>> s.push()
    >>> s.add(And(Bool('Kab__0'), Bool('Kac__0')) )
    >>> s.check()
    unsat
    >>> s.pop()

    >>> s.push()
    >>> s.add(And(Not(Bool('a__7')), Bool('KaNb__7'), \
                     (Bool('KaNc__7')), Bool('KaNe__7')))
    >>> s.check()
    unsat
    """
    exprL = []
    for p in self.agents:
      for c in self.cards:
        for q in self.agents:
          if p != q:
            cOwner = self.getKProp(p, q, c)
            cList  = []
            for agt3 in self.agents:
              if agt3 == p :
                aC = self.getProp(p, c)
                cList.append( Not(aC) )
              elif agt3 != q :
                # p's knowledge that agt3 does not have c
                #  (viz., KiNkc for k!=j and k != i)
                k1N3c = self.getKNProp(p, agt3, c)
                cList.append(k1N3c)
            exprL.append(Equiv(cOwner, And(cList)))
    return (And(exprL))

  def dealK(self):
    """
    Each agent knows the distribution type.

    >>> s, sadi234 = Solver(), CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> s.add(sadi234.dealK())
    >>> bL = BoolVector('KaNb', 9)
    >>> s.add( And(bL) )
    >>> s.check()
    unsat
    """
    exprL=[]
    for p in self.agents:
      for q in self.agents:
        if p != q:
          K12  = self.getKList(p, q)
          K1N2 = self.getKNList(p, q)
          n1   = self.dType[q]
          n2   = self.nCards - n1
          exprL.append(AtMostK(  K12, n1))
          exprL.append(AtMostK( K1N2, n2))
          posKComplete = ExactlyK(  K12, n1)
          negKComplete = ExactlyK( K1N2, n2)
          exprL.append(Equiv(posKComplete, negKComplete))
    return And(exprL)

  def initK(self):
    """
    If an agent doesn't have a particular card ,then, he does'nt know whether any
    other agent has it or not. This is true only initially and assumes that there
    are at least 3 agents.

    >>> s, sadi234 = Solver(), CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> s.add(sadi234.initK())
    >>> s.add( And(Not(Bool('a__3')), Or(Bool('Kab__3'), Bool('KaNb__3'))) )
    >>> s.check()
    unsat
    """
    exprL  = []
    for p in self.agents:
      for card in self.cards:
        antecedent = Not( self.getProp(p, card) )
        cList = []
        for q in self.agents:
          if p != q:
            kp  = self.getKProp(p, q, card)
            kNp = self.getKNProp(p, q, card)
            cList.append(Not(kp))
            cList.append(Not(kNp))
        initExpr = Implies(antecedent, And(cList))
        exprL.append(initExpr)
    return (And(exprL))

  def getSolver(self):
    '''
    Return an appropriate solver object with required constraints added.
    The constraints are 1) validDeal 2) hand2K 3) kConsistency
    4) ownershipK and 5) dealK.

    >>> sadi234 = CP([2,3,4,0], ['a', 'b', 'c', 'e'])
    >>> solvR   = sadi234.getSolver()
    >>> solvR.push()
    >>> solvR.add(And(Bool('Kab__0'), Bool('KaNb__0')))
    >>> solvR.check()
    unsat
    '''
    solvR = Solver()
    solvR.push()
    vD, oW, hK = self.validDeal(),    self.ownership(),  self.hand2K()
    kC, oK, dK = self.kConsistency(), self.ownershipK(), self.dealK()
    solvR.add(vD)
    solvR.add(oW)
    solvR.add(hK)
    solvR.add(kC)
    solvR.add(oK)
    solvR.add(dK)
    solvR.push()
    return solvR

  def infFml(self, agt):
    exprL = []
    for card in self.cards:
      for agt1 in self.agents:
        if agt1 != agt:
          kProp = self.getKProp(agt, agt1, card)
          prop = self.getProp(agt1, card)
          exprL.append( Equiv(kProp, prop) )
    return And(exprL)

  def getInvariants(self):
    vD, oW, hK = self.validDeal(),    self.ownership(),  self.hand2K()
    kC, oK, dK = self.kConsistency(), self.ownershipK(), self.dealK()
    return And(vD, oW, hK, kC, oK, dK)

  def val2Fml(self, val):
    cList = []
    if val == []:
      return True
    for pName in val:
      p = Bool(pName)
      cList.append(p)
    return And(cList)    

################################################################
#      Documentation (with actual code snippets for doctest)
################################################################

'''
To take note of.
'''
  
# Testing the above functionality using doctest module of python.
__test__ = {
  'solver' :
  '''
  >>> s = Solver()
  >>> sadi234 = CP([2,3,4,0], ['a', 'b', 'c', 'e'])
  >>> s.add(sadi234.validDeal())
  >>> s.add(sadi234.ownership())
  >>> s.add(sadi234.hand2K())
  >>> s.add(sadi234.kConsistency())
  >>> s.add(sadi234.ownershipK())
  >>> s.add(sadi234.dealK())
  '''
}
