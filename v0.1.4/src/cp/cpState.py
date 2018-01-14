'''
Stores the state and relevant methods for updating it.
'''
from cpCore import *
import cpUtil as cpUtil

class cpState:
  '''
  Store the relevant code for maintaining the state as
  a list of announcements encoded into formulae involving 
  knowledge propositions of each agent.

  More concretely, given the distribution type as well
  as the list of agents and an initial deal, this class 
  stores the following
  a) An appropriate object of CP class
  b) The knowledge base for each agent which is essentially
      a DNF formula encoding the announcement into
      an equivalent formula over knowledge propositions.
  c) The actual initial deal.
  '''
  def __init__(self, distrLst, agtLst, deal, infAgts, eaves):
    self.cp     = CP(distrLst, agtLst)
    self.cards  = self.cp.cards
    self.nCards = self.cp.nCards
    self.agents = self.cp.agents
    self.agents.sort()
    self.dList  = self.cp.dList
    self.dType  = self.cp.dType
    self.knowledge = {}
    for agt in agtLst:
      self.knowledge[agt] = []
# Every state has to have some initial deal.
    self.initDeal(deal) 
    self.infAgts = infAgts
    self.eaves   = eaves

  def initK(self, deal):
    '''
    initializes the knowledge using function from cpUtil
    '''
    initialK = {}
    dAgts = deal.keys()
    dAgts.sort()
    if dAgts != self.agents:
      raise Exception('Given deal incompatible with agent list, '+str(self.agents))
    for agt in deal.keys():
      initL   = cpUtil.hand2KLst(deal, agt)
      initFml = And(initL)
      if initL == []:
        initFml = And(BoolVal(True))
      initialK[agt] = [initFml]
    return initialK

  def initDeal(self, deal):
    '''
    Given a deal as a dictionary mapping the agents
    to the cards they have received, initDeal appropriately
    initializes the valuations of each agent.
    '''
    self.deal = deal
    self.knowledge = self.initK(deal)

  def newState(self):
    st = cpState(self.dList, self.agents, self.deal, self.infAgts, self.eaves)
    for agt in self.agents:
      annKL = self.knowledge[agt][1:]
      for fml in annKL:
        st.knowledge[agt].append(fml)
    return st

  def updateAnn(self, ann):
    succState  = self.newState()
    spkr, annL = ann
    for agt1 in self.agents:
      if agt1 != spkr:
        annK = cpUtil.ann2K(agt1, spkr, annL)
        succState.knowledge[agt1].append(annK)
    return succState

  def execRun(self, run):
    currState  = self.newState()
    for ann in run:
      currState = currState.updateAnn(ann)
    return currState

####################################################################
# Code for querying for validity of propositions.
#####################################################################
  def knowsProp(self, agt1, neg, agt2, card):
    '''
    Check if agt1 knows that agt2 has card if neg is False
    and check if agt1 knows that agt2 does not have card
    if neg is True.
    '''
    cp = self.cp
    if not neg:
      prop = cp.getKProp(agt1, agt2, card)
    else:
      prop = cp.getKNProp(agt1, agt2, card)
    agt1K = And(self.knowledge[agt1])    
    solver = cp.getSolver()
    solver.push()
    solver.add(agt1K)
    solver.add( Not(prop) )
    res = solver.check()
    solver.pop()
    if res == unsat: 
# Assuming self.knowledge[agt1] is consistent 
#  (which it should if all announcements are truthful)
      return True
    return False

  def getPosK(self, agt):
    '''
    Obtain the set of positive knowledge propositions agt 
    knows in this state. Note that the queries we make
    are dependent on the actual deal.     
    '''
    deal,cp = self.deal, self.cp
    resL = []
    for agt1 in self.agents:
      if agt1 != agt and deal[agt1] != []:
        aCards = deal[agt1]
        for card in aCards:
          if self.knowsProp(agt, False, agt1, card) :
            prop = cp.getKProp(agt, agt1, card)
            resL.append(prop.sexpr())
    resL.sort()
    return resL

  def getCards(self, agt):
    cardsK = []
    learnt = self.getPosK(agt)
    for c in self.deal[agt]:
      cardsK.append(c)
    for pName in learnt:
      card = int(pName.split('__')[1])
      cardsK.append(card)
    cardsK.sort()
    return cardsK

  def getNegK(self, agt):
    '''
    Obtain the set of negative knowledge propositions agt 
    knows in this state. Note that the queries we make
    are dependent on the actual deal.     
    '''
    deal,cp = self.deal, self.cp
    resL = []
    for agt1 in self.agents:
      if agt1 != agt and deal[agt1] != []:
        aCards = set(deal[agt1])
        remCards = list(set(self.cards).difference(aCards))
        for card in remCards:
          if self.knowsProp(agt, True, agt1, card) :
            prop = cp.getKNProp(agt, agt1, card)
            resL.append(prop.sexpr())
    resL.sort()
    return resL

  def infFormula(self, agt):
    '''
    Encodes the list of propositions that agt needs to know.
    '''
    deal,cp = self.deal, self.cp
    reqL =[]
    for agt1 in self.agents:
      if agt1 != agt:
        aCards = deal[agt1]
        for card in aCards:
          prop = cp.getKProp(agt, agt1, card)
          reqL.append(prop)
    return reqL

  def isInfAgt(self, agt):
    '''
    Is the current state informative for agt. Here, we 
    check informativity with a single SAT call. Another 
    way to do it is with getPosK.
    '''
    deal,cp = self.deal, self.cp
    reqL = self.infFormula(agt)
# kDeal encodes that agt knows all positive propositions of other agents.
    kDeal  = And(reqL)  
    cp = self.cp
    agtK = And(self.knowledge[agt])
    solver = cp.getSolver()
    solver.push()
    solver.add(agtK)
    solver.add( Not(kDeal) )
    res = solver.check()
    solver.pop()
    if res == unsat:
      return True
    return False

  def isInformative(self, infAgts):
    '''
    Is the current state informative for infAgts
    '''
    for agt in infAgts:
      if not (self.isInfAgt(agt)):
        return False
    return True

  def getInfo(self):
    '''
    Returns the set of agents  for which this 
    state is informative. The set of agents are 
    returned as a list in sorted order.
    '''
    returnCode=-1
    infAgts, eaves = self.infAgts, self.eaves
    infFor, nonInf = [], []
    for ag in self.agents:      # Unoptimized  but simple informativity checks.
      if (self.isInfAgt(ag)):
        infFor.append(ag)
      else:
        nonInf.append(ag)
    checkLst = [eaves] + infAgts
    if set(checkLst).issubset(set(infFor)):    # Unsafe (and inf for infAgts)
      rCode = 0 
    elif eaves in infFor:                      # Unsafe (but not inf)
      rCode = -1 
    elif (set(infAgts).issubset(set(infFor))): # (deal-)Safe and inf
      rCode = 1 
    else :                                     # Partially Inf and (deal-)safe.
      rCode = 2 
    infFor.sort()
    return (rCode,infFor, nonInf)

  def extractPosFor(self, agt):
    r,infL,nInfL = self.getInfo()
    posL = self.getPosK(agt)
    return (posL, infL, nInfL)

  def extractAllPos(self):
    '''
    Return a summary involving all positive propositions
    for all agents whether it knows the complete deal or
    otherwise. Slightly optimized compared to computing
    getPosK() for each agent especially if many agents
    know the deal.
    '''
    r,infL,nInfL = self.getInfo()
    summary = {}
    for agt in infL:
      reqL  = self.infFormula(agt)
      propL = []
      for prop in reqL:
        propL.append(prop.sexpr())
      summary[agt] = propL
    for agt in nInfL:
      posL = self.getPosK(agt)
      summary[agt] = posL
    return (summary, infL, nInfL)

  def extractAllNeg(self):
    '''
    Return a summary involving all negative propositions
    for all agents whether it knows the complete deal or
    otherwise. Should be optimized further.
    '''
    summary = {}
    for agt in self.agents:
      negL = self.getNegK(agt)
      summary[agt] = negL
    return summary

# Generalize above functions to a set of deals for a particular run.
  def getInfo4Deals(self, run, dList):
    infL = []
    for d in dList:
      s0 = cpState(self.dList, self.agents, d, self.infAgts, self.eaves)
      sF = s0.execRun(run)
      info = sF.getInfo()
      infL.append(info)
    return infL    

  def getPosK4Deals(self, agt, run, dList):
    posL = []
    for d in dList:
      s0   = cpState(self.dList, self.agents, d, self.infAgts, self.eaves)
      sF   = s0.execRun(run)
      posK = sF.getPosK(agt)
      posL.append(posK)
    return posL

  def getCards4Deals(self, agt, run, dList):
    cardL = []
    for d in dList:
      s0   = cpState(self.dList, self.agents, d, self.infAgts, self.eaves)
      sF   = s0.execRun(run)
      cL   = sF.getCards(agt)
      cardL.append(cL)
    return cardL

  def getNegK4Deals(self, agt, run, dList):
    negL = []
    for d in dList:
      s0   = cpState(self.dList, self.agents, d, self.infAgts, self.eaves)
      sF   = s0.execRun(run)
      negK = sF.getNegK(agt)
      negL.append(negK)
    return negL

  def getAllPosK4Deals(self, run, dList):
    summary = {}
    for ag in self.agents:
      agL = self.getPosK4Deals(ag, run, dList)
      summary[ag] = agL
    return summary

  def getAllCards4Deals(self, run, dList):
    summary = {}
    for ag in self.agents:
      cL = self.getCards4Deals(ag, run, dList)
      summary[ag] = cL
    return summary

  def getAllNegK4Deals(self, run, dList):
    summary = {}
    for ag in self.agents:
      agL = self.getNegK4Deals(ag, run, dList)
      summary[ag] = agL
    return summary

  def getCards4Runs(self, rList, dList):
    summary={}
    for a in self.agents:
      summary[a] = []
    for r in rList:
      res = self.getAllCards4Deals(r, dList)
      for a in self.agents:
        summary[a].append(res[a])
    return summary

################################################################
#    Code related to second order safety
################################################################
  def getAgtFml(self, agt):
    '''
    The formula encoding the constraints on the deals from perspective of agt.
    '''
    kList = [] # The converted formulae
    kAgt  = self.knowledge[agt][1:] # The list of announcements
    agtH  = self.deal[agt]
    handK = []
    for card in agtH:
      handK.append( cpUtil.getProp(agt, card) )
    if handK != []:
      kList.append( And(handK) )
    for kItem in kAgt:
      (spkr,ann) = cpUtil.k2Ann(agt, kItem)
      aF = cpUtil.ann2DealFml(spkr, ann)
      kList.append(aF)
    return And(kList)

  def getAltDeal(self, agt):
    '''
    Returns an alternate deal as a dictionary compatible with agt knowledge
    if one exists else return an empty dictionary.

    >>> a,b,c,e = 'a', 'b', 'c', 'e'
    >>> deal = {a : [0, 1, 2, 3], b:[4, 5, 6, 7], c:[8, 9, 10, 11], e:[]}
    >>> ann1 = (a, [[0, 1, 2, 3], [4, 5, 6, 7]]); ann2 = (b, [[4, 5, 6, 7], [0, 1, 2, 3]])
    >>> run  = [ann1, ann2]
    >>> infAgts, eaves = ['a', 'b', 'c'], 'e'
    >>> s0 = cpState([4, 4, 4, 0], [a, b, c, e], deal, infAgts, eaves)
    >>> sF = s0.execRun(run)
    >>> aD = sF.getAltDeal(eaves)
    >>> aD[a]
    [4, 5, 6, 7]
    >>> aD[b]
    [0, 1, 2, 3]
    >>> run.append((b,[[4, 5, 6, 7]]))
    >>> tF = s0.execRun(run)
    >>> tF.getAltDeal(eaves)
    {}
    '''
    agts, cards = self.agents, self.cards
    eFml  = self.getAgtFml(agt)
    solvR = self.cp.getSolver()
    dealFml = cpUtil.deal2Fml(self.deal)
    solvR.push()
    solvR.add(Not(dealFml))
    solvR.add(eFml)
    res = solvR.check()
    solvR.pop()
    if res == unsat:
      return {}
    m = solvR.model()
    resDeal = cpUtil.model2Deal(m, agts, cards)
    return resDeal

  def fml2Deals(self, fml):
    '''
    Returns all deals consistent with fml 
        (ideally involves only deal variables)
    '''
    dList = []
    solvR = self.cp.getSolver()
    solvR.push()
    solvR.add(fml)
    res = solvR.check()
    while res != unsat :
      m = solvR.model()
      nextDeal = cpUtil.model2Deal(m, self.agents, self.cards)
      dList.append(nextDeal)
      dealFml  = cpUtil.deal2Fml(nextDeal)
      solvR.add(Not(dealFml))
      res = solvR.check()
    solvR.pop()
    return dList

  def run2Deals(self, run):
    '''
    Given an announcement sequence run, return all deals compatible with it.
    '''
    fmlList = []
    for ann in run:
      s, a = ann
      fml  = cpUtil.ann2DealFml(s,a)
      fmlList.append(fml)
    return self.fml2Deals( And(fmlList) )

  def getAgtDeals(self, agt):
    '''
    Returns all deals that are consistent with agt's knowledge.
    '''
    agtFml = self.getAgtFml(agt)
    agts, cards = self.agents, self.cards
    return self.fml2Deals(agtFml)

  def getEavesFml(self):
    '''
    The formula encoding the constraints on the deals from Eaves perspective.    
    '''
    return self.getAgtFml(self.eaves)

  def getEavesDeals(self):
    '''
    Returns all deals that are consistent with Eaves knowledge.

    >>> a,b,c,e = 'a', 'b', 'c', 'e'
    >>> deal = {a : [0, 1, 2, 3], b:[4, 5, 6, 7], c:[8, 9, 10, 11], e:[]}
    >>> ann1 = (a, [[0, 1, 2, 3], [4, 5, 6, 7]]); ann2 = (b, [[4, 5, 6, 7], [0, 1, 2, 3]])
    >>> run  = [ann1, ann2]
    >>> infAgts, eaves = ['a', 'b', 'c'], 'e'
    >>> s0 = cpState([4, 4, 4, 0], [a, b, c, e], deal, infAgts, eaves)
    >>> sF = s0.execRun(run)
    >>> dL = sF.getEavesDeals()
    >>> import cpUtil as ut
    >>> dL = ut.sortDeals(dL)
    >>> dL[0][a], dL[0][b], dL[0][c]
    ([0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11])
    >>> dL[1][a], dL[1][b], dL[1][c]
    ([4, 5, 6, 7], [0, 1, 2, 3], [8, 9, 10, 11])
    '''
    return self.getAgtDeals(self.eaves)

  def deals2State(self, dList, actualDeal):
    '''
    Return a state denoting local knowledge of each agent
    when the possible worlds model consists of dList and
    actual world is actualDeal.
    '''
    if dList == []:
      raise Exception('Empty set of deals')
    st = cpState(self.dList, self.agents, actualDeal, self.infAgts, self.eaves)    
    for ag in self.agents:
      dlFml = cpUtil.deals2KAgt(dList, ag)
      st.knowledge[ag].append(dlFml)
    return st

  def getInfDeals(self, run):
    '''
    Obtain the set of all informative deals for run 
    compatible with Eaves knowledge, if self.deal is informative 
    for run and return [] otherwise.
    '''
    st = cpState(self.dList, self.agents, self.deal, self.infAgts, self.eaves)
    finalSt = st.execRun(run)
    (code, infL, nonInf) = finalSt.getInfo()
    if infL != self.infAgts:
      return []
    resDeals = [finalSt.deal]
    allDeals = finalSt.getEavesDeals() # to remove self.deal
    for deal in allDeals:
      st = cpState(self.dList, self.agents, deal, self.infAgts, self.eaves)
      finalSt = st.execRun(run)
      (code, infL, nonInf) = finalSt.getInfo()
      if infL == self.infAgts:
        resDeals.append(deal)
    return resDeals

################################################################
#    Random generation of Announcements
################################################################
  def genAnn(self, agt, cWidth, dWidth):
    '''
    Generate a random truthful announcement 
    such that each conjunct is of cWidth while
    the number of disjuncts is dWidth.
    '''
    import random
    if cWidth > self.dType[agt]:
      cWidth = self.dType[agt]
    annL = []
    rangeL = range(0, self.dType[agt])
    currDisj = []
    for j in range(0, cWidth):
      rI = random.randint(0, len(rangeL)-1)
      rIndex = rangeL[rI]
      rangeL.remove(rIndex) 
#     Above Avoids repetition
      randCard = self.deal[agt][rIndex]
      currDisj.append(randCard)
    currDisj.sort()
    annL.append(currDisj)
#   Truthful disjunct generated.
    for i in range(0, dWidth-1):
      currDisj = []
      rangeL = range(0, self.nCards)
      for j in range(0, cWidth):
        rI = random.randint(0, len(rangeL)-1)
        rIndex = rangeL[rI]
        rangeL.remove(rIndex)
        randCard = self.cards[rIndex]
        currDisj.append(randCard)
      currDisj.sort()
      annL.append(currDisj)
    return (agt, annL)

  def genAnnFullHand(self, agt, dWidth):
    '''
    Generate random full hand truthful announcements with dWidth disjuncts.
    '''
    agtW = self.dType[agt]
    return self.genAnn(agt, agtW, dWidth)    

  def genRunFH(self, dWidth, length):
    run = []
    for idx in range(0,length):
      agtIndex = idx % (len(self.agents) - 1)
      agt = self.agents[agtIndex]
      ann = self.genAnnFullHand(agt, dWidth)
      run.append(ann)
    return run

  def genRun(self, hSize, annLen, runLen):
    run = []
    for idx in range(0, runLen):
      agtIndex = idx % (len(self.agents) - 1)
      agt = self.agents[agtIndex]
      ann = self.genAnn(agt, hSize, annLen)
      run.append(ann)
    return run

################################################################
#      Documentation (with actual code snippets for doctest)
################################################################
__test__ = {
  'sadi234' :
  '''
  >>> a,b,c,e = 'a', 'b', 'c', 'e'
  >>> deal = {a : [0,1], b:[2,3,4], c:[5,6,7,8], e:[]}
  >>> ann1 = (a, [[0,1], [0,2], [1,2]]); ann2 = (b, [[2,3,4], [0,5,6], [1,7,8]])
  >>> run  = [ann1, ann2]
  >>> infAgts, eaves = ['a', 'b', 'c'], 'e'
  >>> s0 = cpState([2,3,4,0], [a, b, c, e], deal, infAgts, eaves)
  >>> s1 = s0.updateAnn(ann1)
  >>> s2 = s1.updateAnn(ann2)

  >>> s0.getPosK(b)
  []
  >>> s1.getPosK(b)
  ['Kba__0', 'Kba__1', 'Kbc__5', 'Kbc__6', 'Kbc__7', 'Kbc__8']
  >>> s2.getPosK(b)
  ['Kba__0', 'Kba__1', 'Kbc__5', 'Kbc__6', 'Kbc__7', 'Kbc__8']

  >>> s0.getNegK(a)
  ['KaNb__0', 'KaNb__1', 'KaNc__0', 'KaNc__1']
  >>> s1.getNegK(a)
  ['KaNb__0', 'KaNb__1', 'KaNc__0', 'KaNc__1']
  >>> s2.getNegK(a)
  ['KaNb__0', 'KaNb__1', 'KaNb__5', 'KaNb__6', 'KaNb__7', 'KaNb__8', 'KaNc__0', 'KaNc__1', 'KaNc__2', 'KaNc__3', 'KaNc__4']

  >>> s1.isInfAgt(b)
  True
  >>> s1.isInfAgt(c)
  False
  >>> s1.isInformative([a,b,c])
  False
  >>> s2.isInformative([a,b,c])
  True
  ''',

  'testInit' :
  '''
  >>> deal = {'a' : [0,1], 'b':[2,3,4], 'c':[5,6,7,8], 'e':[]}
  >>> infAgts, eaves = ['a', 'b', 'c'], 'e'
  >>> s = cpState([2,3,4,0], ['a', 'b', 'c', 'e'], deal, infAgts, eaves)
  >>> s.knowledge['a'] #doctest: +NORMALIZE_WHITESPACE
  [And(KaNb__0, KaNb__1, KaNc__0, KaNc__1)]
  '''
}
