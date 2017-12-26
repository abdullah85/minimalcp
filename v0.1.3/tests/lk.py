import cpState as cps;
import cpUtil as ut;
import pickle as pk;
import time
import random as rand
import z3

def addToSolver(solvR, Lst, debug):
  solvR.push()
  for f in Lst:
    if debug:
      solvR.push()
    solvR.add(f)
  solvR.push()
  return solvR

Bool         = z3.Bool
Not, And, Or = z3.Not, z3.And, z3.Or
Implies      = z3.Implies
AtLeast, AtMost = z3.AtLeast, z3.AtMost
a,b,c,e  = ['a', 'b', 'c', 'e']

class Leakage:
  ################################################################
  #          Various types of solvers relevant 
  #      to searching as well as verifying protocols.
  ################################################################
  def vanillaSolver():
    return z3.Solver()

  def kEavesSolver(self, debug):
    posKL = self.eavesKFml.children()
    negKL = self.eavesKNFml.children()
    fLst = posKL + negKL
    solver = z3.Solver()
    solver = addToSolver(solver, fLst, debug)    
    return (solver, fLst)

  def pEavesSolver(self, debug):
    (solver, fL1) = self.kEavesSolver(debug)
    wL, pL = [], []
    if not self.wComputed:
      self.pEWitnessesAll()
    if not self.pComputed:
      self.pEaves()
    pL = self.pEavesFml.children()
    wL = self.pEWitnessesFml.children()
    fL = pL+wL
    solver = addToSolver(solver, fL, debug)
    fL = fL1 + fL
    return (solver, fL)

  def eavesKNIgnorant(self):
    nK = []
    for agt in self.agents:
      nK = nK + map(Not, self.keN[agt])
    return And(nK)

  def eavesIgnorant(self):
    KL = []
    for c in self.cards:
      for agt in self.agents:
        KL.append(Not(self.ke[agt][c]))
    kFml = And(KL)
    return kFml

  def safetySolver(self, debug):
    '''
    Basically for searching for safe runs
    '''
    (solver, fL1) = self.pEavesSolver(debug)
    kFml = self.eavesIgnorant()
    solver.add(kFml)
    fLst = fL1 + [kFml]
    return (solver, fLst)

  def safetySynthSolver(self, debug):
    '''
    For synthesis of safe runs (and protocols)
    We need to add self.soInformative() separately
    and add it to the solver.
    '''
    solver, fL = self.safetySolver(debug)
    da = self.deal2AnnAll() #Truthfulness    
    ad = self.ann2Deals()
    dealFLst = da + ad
    solver = addToSolver(solver, dealFLst, debug)
    fL = fL + dealFLst
    return (solver, fL)

  def synthesizer(self, debug):
    solver, fL1 = self.safetySynthSolver(debug)
    sInf = self.soInformative()
    solver = addToSolver(solver, sInf, debug)
    fLst = fL1 + sInf
    return solver, fLst

  ################################################################
  #     Solvers are defined. Now initializing the class
  ################################################################
  def __init__(self, hSize):
    '''
    Agents are ['a', 'b', 'c', 'e']
    '''
    self.agents = [a,b,c] # Eaves is outside the system
    self.hSize = hSize
    i = hSize
    dLst = [i, i, i, 0]
    deal = ut.minDeal(dLst, [a,b,c,e], range(3*i))
    s0 = cps.cpState(dLst, [a,b,c,e], deal, [a,b,c], e)
    self.cards = range(3*i)
    # Knowledge/Possibility formula for Eaves.
    self.pe  = {}
    self.peN = {}
    self.ke  = {}
    self.keN = {}
    nCards = len(self.cards)
    # Initialize all propositions with respect to each agent
    for agt in ['a','b','c']:
      self.pe[agt] = z3.BoolVector ('Pe'+agt,  nCards)
      self.peN[agt] = z3.BoolVector('PeN'+agt, nCards)
      self.ke[agt] = z3.BoolVector ('Ke'+agt,  nCards)
      self.keN[agt] = z3.BoolVector('KeN'+agt, nCards)
    self.keFml  = {}
    self.keNFml = {}
    eavesKL  = []
    eavesKNL = []
    for agt in [a,b,c]:
      self.keFml[agt]  = self.eavesK(agt)
      self.keNFml[agt] = self.eavesKN(agt)
      eavesKL.append ( And(self.keFml[agt]) )
      eavesKNL.append( And(self.keNFml[agt]))
    self.eavesKFml  = And(eavesKL)
    self.eavesKNFml = And(eavesKNL)
    self.initializedHands = False
    self.initializedDeals = False
    self.initializedAnn   = False
    self.wComputed = False
    self.pComputed = False
    self.ann2D = False
    self.d2Ann = False

  def initHands(self):
    self.initializedHands = True
    hSize = self.hSize
    self.handList = ut.allHands(hSize, self.cards)    

  def initDeals(self):
    self.initializedDeals = True
    # set of all possible deals[B
    i = self.hSize
    dType = [i, i, i] # Ignore (for now) that eaves has no card. 
    self.deals = ut.allDeals(dType, [a,b,c], self.cards)
    # Now the possible deals models if  (after a run) the 
    #     deal is possible or not.
    self.possibleDeals = z3.BoolVector('d', len(self.deals))

  ################################################################
  #    Formulae relevant to eavesdroppers' knowledge.
  ################################################################
  def eavesK(self, agt):
    '''
    The +ve knowledge version of what Eaves knows about agt
    '''
    eKP = []
    for c in self.cards:
      f = self.ke[agt][c]
      g = Not(self.peN[agt][c])
      f1 = Implies(f, g)
      f2 = Implies(g, f)
      eKP.append(And(f1, f2))
    return eKP

  def eavesKN(self, agt):
    '''
    The -ve knowledge version of what Eaves knows
    '''
    eKN = []
    for c in self.cards:
      f  = self.keN[agt][c]
      g  = Not(self.pe[agt][c])
      f1 = Implies(f, g)
      f2 = Implies(g, f)
      eKN.append(And(f1, f2))
    return eKN

  def pEWitnessesAll(self):
    fLst = []
    for agt in self.agents:
      pAgt = self.pEWitnesses(agt)
      fLst = fLst + pAgt
    self.pEWitnessesFml = And(fLst)
    self.wComputed = True
    return fLst

  def pEWitnesses(self, agt):
    '''
    For any agt, say a,
    a) Ensure that if pea__i is true then a corresponding
        deal d_k is true such that a has i in d_k
    b) Ensure that if peNa__i is true then a corresponding
        deal d_k is true such that a does not have i in d_k
    '''
    # Currently we need the explicit list of hands as well as 
    #    deals for a given hand size. Check ways to avoid
    #    explicitly constructing these sets in future.
    if not self.initializedHands:
      self.initHands()
    if not self.initializedDeals:
      self.initDeals()
    fmlLst = []
    hLst   = self.handList
    dLst   = self.deals
    dBL    = self.possibleDeals
    for c in self.cards:
      head1 = self.pe[agt][c]
      head2 = self.peN[agt][c]
      body1 = []
      body2 = []
      for j in range(len(dLst)):
        currDeal  = dLst[j] # The actual deal.
        currDealB = dBL[j]  # The boolean representing possibility.
        if c in currDeal[agt]:
          body1.append(currDealB)
        else:
          body2.append(currDealB)
      if body1 == []:
        body1 = True
      if body2 == []:
        body2 = True
      body1 = Or(body1)
      body2 = Or(body2)
      f1 = Implies(head1, body1)
      f2 = Implies(head2, body2)
      fmlLst.append(f1)
      fmlLst.append(f2)
    return fmlLst

  def pEaves(self):
    '''
    The formulation of what eaves thinks 
    possible given a valuation to a set of deals.
    '''
    if not self.initializedHands:
      self.initHands()
    if not self.initializedDeals:
      self.initDeals()
    eP = []
    for i in range(len(self.deals)):
      currDeal = self.deals[i]
      head = self.possibleDeals[i]
      body = []
      # Now, get the signature for currDeal
      for agt in self.agents:
        for c in self.cards:
          if c in currDeal[agt]:
            body.append(self.pe[agt][c])
          else:
            body.append(self.peN[agt][c])
      body = And(body)
      f1 = Implies(head, body)
      #      f2 = Implies(body, head)
      #      fml = And(f1, f2)
      fml = f1
      eP.append(fml)
    self.pEavesFml = And(eP)
    self.pComputed = True
    return eP

  ################################################################
  #     Code relevant for announcements, informativity
  ################################################################
  def getImplIndices(self, fml):
    hIdx = int(fml.children()[0].sexpr().split('__')[-1])
    bIL  = []
    sIL  = fml.children()[1].children()
    for f in sIL:
      idx = int(f.sexpr().split(')')[0].split('__')[-1])
      bIL.append(idx)
    return bIL

  def sInf(self, i):
    dLst = self.deals
    dBls = self.possibleDeals
    nDeals = len(dLst)
    currDeal = dLst[i]
    head     = dBls[i]
    body     = []
    for agt in self.agents:
      currHand = currDeal[agt]
      for j in range(nDeals):
        altDeal = dLst[j]
        altHand = altDeal[agt]
        altBool = dBls[j]
        if (i != j) and (currHand == altHand):
          body.append( Not(altBool) )
    if body == []:
      body = True
    body = And(body)
    fml = Implies(head, body)
    return fml

  def soInformative(self):
    '''
    formula encoding second order informativity for [a,b,c].
    Currently explicit as we encode it as a property of the
    possible deals.
    '''
    fLst = []
    if not self.initializedDeals:
      self.initDeals()
    dLst = self.deals
    dBls = self.possibleDeals
    nDeals = len(dLst)
    for agt in self.agents:
      fLst = fLst + self.sInf4Agt(agt)
    return fLst

  def sInf4AgtAt(self, agt, i):
      currDeal = self.deals[i]
      currHand = currDeal[agt]
      head = self.possibleDeals[i]
      body = []
      for j in range(len(self.deals)):
        altDeal = self.deals[j]
        altHand = altDeal[agt]
        altBool = self.possibleDeals[j]
        if (i != j and currHand == altHand):
          body.append( Not(altBool) )
      if body == []:
        body = True
      body = And(body)
      fml = Implies(head, body)
      return fml

  def sInf4Agt(self, agt):
    fLst = []
    nDeals = len(self.deals)
    for i in range(nDeals):
      fml = self.sInf4AgtAt(agt, i)
      fLst.append(fml)
    return fLst

  def sInf4AgtOpt(self, agt):
    '''
    Optimizing sInf4Agt
    '''
    eqClasses = []
    dProps = []
    for prop in self.possibleDeals:
      dProps.append(prop)    

    currDeal = self.deals[i]
    currHand = currDeal[agt]
    head = self.possibleDeals[i]
    body = []
    for j in range(len(self.deals)):
      altDeal = self.deals[j]
      altHand = altDeal[agt]
      altBool = self.possibleDeals[j]
      if (i != j and currHand == altHand):
        body.append( Not(altBool) )
    if body == []:
      body = True
    body = And(body)
    fml = Implies(head, body)
    
    nDeals = len(self.deals)
    for i in range(nDeals):
      fml = self.sInf4AgtAt(agt, i)
      fLst.append(fml)
    return fLst

  def initAnn(self, nRounds):
    '''
    initialize boolean variables denoting possible announcements by 
    each agent for nRounds. At each round, every agent essentially 
    announces a subset of self.handList.
    '''
    self.initializedAnn = True
    self.ann = {}
    for agt in self.agents:
      self.ann[agt] = []
    if not self.initializedHands:
      self.initHands()
    handLst = self.handList
    nHands  = len(handLst)
    for agt in self.agents:
      for r in range(nRounds):
        # Due to the symmetric nature of [i,i,i] 
        #   no need to look at actual dType currently.        
        self.ann[agt].append(z3.BoolVector(agt+str(r), nHands))
    self.nRounds = nRounds

  def dealsBL(self, dListI):
    '''
    A list of propositions corresponding to indices dListI
    '''
    bL = []
    for i in dListI:
      bL.append(self.possibleDeals[i])
    return bL

  def annBL(self, agt, rnd, aLstI):
    '''
    A list of propositions corresponding to the indices aLstI 
              for agt's announcement at rnd
    '''
    bL = []
    annList = self.ann[agt][rnd]
    for i in aLstI:
      bL.append(annList[i])
    return bL

  def deal2Ann(self, agt, rnd):
    '''
    When deal is true how should ann variables (of agt at rnd) be set.
    Basically ensure that *truthfulness* of the announcement is maintained
    because when deal is true then it is a possible deal.
    '''
    if not self.initializedHands:
      self.initHands()
    if not self.initializedDeals:
      self.initDeals()
    if not self.initializedAnn:
      self.initAnn(1) # default is at least one round
    fLst = []
    dLst = self.deals
    handLst = self.handList
    nHands = len(handLst)
    for i in range(len(dLst)):
      currDeal = dLst[i]
      dealB    = self.possibleDeals[i]
      currHand = currDeal[agt]
      j = handLst.index(currHand)
      annB = self.ann[agt][rnd][j]
      fml = Implies(dealB, annB)
      fLst.append(fml)
    return fLst

  def deal2Ann4Round(self, rnd):
    '''
    See deal2Ann
    '''    
    fLst = []
    for agt in self.agents:
      agtL = self.deal2Ann(agt, rnd)
      fLst  = fLst + agtL
    return fLst

  def deal2AnnAll(self):
    fLst = []
    if not self.initializedHands:
      self.initHands()
    if not self.initializedDeals:
      self.initDeals()
    if not self.initializedAnn:
      self.initAnn(1) # default is at least one round    
    self.d2Ann = True
    # Onto actual code for generation
    dLst = self.deals
    handLst = self.handList
    for i in range(len(dLst)):
      currDeal = dLst[i]
      head = self.possibleDeals[i]
      body = []
      for agt in self.agents:
        idx = handLst.index(currDeal[agt])
        for j in range(self.nRounds):  
          body.append(self.ann[agt][j][idx])
      fml  = Implies(head, And(body))
      fLst.append(fml)
    self.da = fLst
    return fLst

  def ann2Deals(self):
    '''
    Ensures that if a deal is possible due to announcements
    then it is enforced to be true. This is to ensure search 
    for second order informative runs.
    '''
    if not self.initializedHands:
      self.initHands()
    if not self.initializedDeals:
      self.initDeals()
    if not self.initializedAnn:
      self.initAnn(1)
    self.ann2D = True
    fLst = []
    dLst = self.deals
    hLst = self.handList
    for i in range(len(dLst)):
      currDeal = dLst[i]
      targetB  = self.possibleDeals[i]
      head = []
      for agt in self.agents:
        agtHand = currDeal[agt]
        idx = hLst.index(agtHand)
        for j in range(self.nRounds): 
          # the idx variable must be set 
          #      at every round for agt
          aBool = self.ann[agt][j][idx]
          head.append(aBool)
      # Now, head has been constructed
      head = And(head)
      fml =  Implies(head, targetB)
      fLst.append(fml)
    self.ad = fLst
    return fLst

  ################################################################
  #    Obtaining models and results of the same
  ################################################################
  def obtainAnnSet(self, solver, cutOff):
    '''
    Keep getting newer and newer announcements upto cutoff.
    Return the updated solver (blocking all announcements found
    so far) alongwith the actual models obtained.
    '''
    i = 0
    mLst = []
    res = solver.check()
    while i < cutOff and res == z3.sat:
      m   = solver.model()
      mLst.append(m)
      fml = Not(And(self.getAnnPropsAll(m)))
      solver.add(fml)
      res = solver.check()
      i = i + 1
    return (solver, mLst)

  def obtainDealSet(self, solver, cutOff):
    '''
    Keep getting newer and newer deals obtained as a result of announcements.
    Return the updated solver (blocking all deals sets obtained thus far) 
    alongwith the set of models obtained.
    Note that this is stronger than obtaining different announcement
    sets as having a different set of deals reached entails a different 
    set of announcements to be made but not vice versa.
    '''
    i = 0

    res = solver.check()
    while i < cutOff and res == z3.sat:
      m   = solver.model()
      mLst.append(m)
      dL  = self.Deals2Fml(m)
      fml = Not(And(dL))
      solver.add(fml)
      res = solver.check()
      i = i + 1
    return (solver, mLst)

  ################################################################
  #    Processing the models obtained
  ################################################################    
  def sortIndices(self, decLst):
    dL = decLst
    extendedL = []
    for d in dL:
      val = d.name().split('__')
      val[-1] = int(val[-1])
      extendedL.append((val, d))
    extendedL.sort()
    sortedLst = []
    for triple in extendedL:
      sortedLst.append(triple[-1])
    return sortedLst

  def fLgetIndices(self, fL):
    '''
    Given a list of formulae, obtain the indices of each formula.
    We assume that each formula has only one occurrence of '__'
    '''
    iL = []
    for f in fL:
      idx = int(f.sexpr().split(')')[0].split('__')[-1])
      iL.append(idx)
    return iL

  def getIndices(self, decL):
    idL = []
    for d in decL:
      idx = int(d.name().split('__')[-1])
      idL.append(idx)
    return idL

  def getAllPropsPrefixedBy(self, m, pref):
    dL = m.decls()
    dealsSet = []
    for d in dL:
      if d.name().startswith(pref):
        dealsSet.append(d)
    return dealsSet

  def getTruePropsPrefixedBy(self, m, pref):
    dL = m.decls()
    indicesSet = []
    for d in dL:
      if d.name().startswith(pref):
        if m[d].sexpr() == 'true' :        
          indicesSet.append(d)
    return indicesSet

  def getAnnIL(self, m, agt, rnd):
    '''
    Get the announcement indices for agt at round rnd.
    '''
    pL = self.getTruePropsPrefixedBy(m, agt+str(rnd))
    iL = self.getIndices(pL)
    return iL  

  def hand2DIL(self, agt, hand):
    '''
    return deal indices such that agt has hand
    '''
    dL = []
    for i in range(len(self.deals)):
      currDeal = self.deals[i]
      if hand in currDeal[agt]:
        dL.append(i)
    return dL    

  def hand2DPL(self, agt, hand):
    '''
    return deal indices (as propositions) wherein agt has hand
    '''
    dL = []
    for i in range(len(self.deals)):
      currDeal = self.deals[i]
      if hand in currDeal[agt]:
        dL.append(self.possibleDeals[i])
    return dL    

  def iL2PropL(self, agt, rnd, iL):
    pL = []
    for i in iL:
      pL.append(self.ann[agt][rnd][i])
    return pL
    
  def iL2AnnL(self, iL):
    annL = []
    iL.sort()
    for i in iL:
      annL.append(self.handList[i])
    return annL

  def iL2Deals(self, iL):
    deals = []
    for i in iL:
      deals.append(self.deals[i])
    return deals

  def annL2iL(self, agt, annL):
    iL = []
    for disj in annL:
      idx = self.handList.index(disj)
      iL.append(idx)
    return iL

  def getAnnList(self, m, agt, rnd):
    '''
    Return the announcement made by agt at round rnd (as a list of disjuncts)
    '''
    iL = self.getAnnIL(m, agt, rnd)
    iL.sort()
    annL = []    
    for i in iL:
      annL.append(self.handLLList[i])
    return annL    
    
  def getAnnProps(self, m, agt, rnd):
    '''
    Return the set of announcement propositions set for agt
    '''
    iL = self.getAnnIL(m, agt, rnd)
    pL = []
    for i in iL:
      pL.append(self.ann[agt][rnd][i])
    return pL

  def getAnnPropsAll(self, m):
    pL = []
    for agt in self.agents:
      for i in range(self.nRounds):
        aP = self.getAnnProps(m, agt, i)
      pL.append(aP)
    return pL

  def getTrueDealIndices(self, m):
    dL = self.getTruePropsPrefixedBy(m, 'd')
    dealsSet = self.getIndices(dL)
    return dealsSet

  def Deals2Fml(self, m):
    '''
    Return the list of deal propositions set 
    '''
    dealsSet = self.getTrueDealIndices(m)
    pL = []
    for i in dealsSet:
      pL.append(self.deals[i])
    return pL

  def genSaveSInfFml(self, agt):
    '''
    Generate and save sInf Fml.
    '''
    i = self.hSize
    aName = agt.upper()
    fName = 'optimized/' + str(i) + '-sInf' + aName + '.txt'
    fml = And(self.sInf4Agt(agt))
    expr = fml.sexpr()
    f = open(fName, 'w')
    pk.dump(expr, f)
    f.close()

  def rSInf4Agt(self, fName):
    f = open(fName)
    sExpr = pk.load(f)
    f.close()
    sExpL = sExpr.splitlines()
    fLst  = []
    body = []
    for l in sExpL:
      if '=' in l:
        if body != []:
          fLst.append(Implies(head, And(body)))
        headI = int(l.split('__')[-1].split(')')[0])
        head  = self.possibleDeals[headI]
        body  = []
      else:
        idx = int(l.split('__')[-1].split(')')[0])
        body.append( Not(self.possibleDeals[idx]) )
    return fLst

  def readSInfFml(self, folder):
    if not self.initializedHands:
      self.initHands()
    if not self.initializedDeals:
      self.initDeals()
    if not self.initializedAnn:
      self.initAnn(1)
    fLst = []
    nDeals = len(self.deals)
    for i in range(nDeals):
      f = open(folder+'/'+'d-'+str(i)+'.txt', 'r')
      expr  = pk.load(f)
      f.close()
      exprL = expr.split('(=>')[1:][0].split('\n')[1:]
      head  = self.possibleDeals[i]
      body  = []
      for e in exprL:
        idx = int( e.split(')')[0].split('__')[-1] )
        dB  = self.possibleDeals[idx]
        body.append(Not(dB))
      f = Implies( head, And(body) )
      fLst.append(f)
    return fLst

  ################################################################
  ####    Latest additions
  ################################################################
  def getAnnFml(self, agt, rnd, annIL):
    '''
    Get an appropriate formula encoding the exact formula
    to add to solver for the announcement consisting of disjuncts
    encoding by indices in annIL.
    '''
    notAnnL = []
    for i in range(len(self.handList)) :
      if not i in annIL :
        notAnnL.append(i)
    annProps = self.iL2PropL(agt, rnd, annIL)
    notAnnProps = self.iL2PropL(agt, rnd, notAnnL)
    annFL = []
    for p in annProps :
      annFL.append(p)
    for p in notAnnProps :
      annFL.append(Not(p))
    annFml   = And(annFL)
    return annFml

  def restrictWidthRound(self, agt, rnd, w):
    pL = self.ann[agt][rnd]
    fL = []
    for p in pL:
      fL.append(p)
    fL.append(w)
    fml = Or(AtMost(fL), And(pL))
    # Either all true (corresponding to pass) or width constraint enforced
    return fml

  def restrictWidth(self, agt, w):
    '''
    Return a fml restricting the number of valid disjuncts in any announcement to w.
    That is, the total number of disjuncts announced in any formula is at most w
    (or pass which is equivalent to true). Hopefully, this aids in extracting the strategy.
    '''
    resFml = []
    for i in range(self.nRounds):
      fml = self.restrictWidthRound(agt, i, w)
      resFml.append(fml)
    return resFml

  def restrictWidthAll(self, w):
    fL = []
    for agt in self.agents:
      fL.append(self.restrictWidth(agt, w))
    return And(fL)

  def extractDealsProps(self, fml):
    '''
    Obtain the set of deals enforced by fml as a set of propositions.
    Typically fml is an announcement or a sequence of announcements and
    we would like to obtain the set of deals satisfying them.
    '''
    solver = z3.Solver()
    if not self.ann2D :  ad = self.ann2Deals()
    else:                ad = self.ad
    solver.add(ad)
    solver.add(fml)
    dL  = []
    res = solver.check()
    if res == z3.sat:
      m  = solver.model()
      dL = self.getTruePropsPrefixedBy(m, 'd')
      dL = self.sortIndices(dL)
    return dL

  # TODO
  def obtainSolns(self, synth, fixedFml, dList):
    '''
    fixedFml is usually ann
    '''
    synth.push()
    synth.add(fixedFml)
    synth.push()
    mLst = []
    i = 0
    res = z3.sat
    while i <len(dList) and res == z3.sat:
      d = dList[i]
      synth.push()
      synth.add(d)
      res = synth.check()
      if res == z3.sat:
        m = synth.model()
        mLst.append(m)
      synth.pop()
      i = i + 1
    return mLst

  def isFirstAnnTheSame(self, mLst):
    firstAnnSame = True
    i = 0
    while firstAnnSame and i < len(dL1):
      la = self.getIndices(self.getTruePropsPrefixedBy(m, a))
      la.sort()
      cEq1 = (la == s1A)
      firstAnnSame = firstAnnSame and cEq1
      i = i + 1
    return fistAnnSame

  def getAnnBC(self, mLst):
    annL = []
    for i in range(len(mLst)):
      m = mLst[i]
      bP = self.getIndices(self.getTruePropsPrefixedBy(m, 'b'))
      cP = self.getIndices(self.getTruePropsPrefixedBy(m, 'c'))
      currAnnL = [bP, cP] #Note the order
      annL.append(currAnnL)
    return annL

  def compAgtDeals4(self, fml, agt, rnd, iL):
    '''
    What does agt know for each hand indexed in iL with fml before
    '''
    agtDeals = []
    for i in iL:
      agtHand = self.handList[i]
      agtHFml = getAnnFml(agt, rnd, [i])
      aD = extractDealsProps(And(fml, agtHFml))
      agtDeals.append(aD)
    return agtDeals
