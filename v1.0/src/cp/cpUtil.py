import z3 as z3

################################################################
#                 Utility Functions 
#   (Converting to formulae from deals and vice versa)
################################################################
def getKProp(p, q, i):
  return z3.Bool('K'+p+q+'__'+str(i))

def getKNProp(p, q, i):
  return z3.Bool('K'+p+'N'+q+'__'+str(i))

def getProp(p, i):
  return z3.Bool(p+'__'+str(i))

def ann2K(listener, spkr, ann):
  '''
  >>> fml = ann2K('b', 'a', [[0,1], [0,2], [1,2]])
  >>> fC = fml.children()
  >>> len(fC)
  3
  >>> fml.sexpr()
  '(or (and Kba__0 Kba__1) (and Kba__0 Kba__2) (and Kba__1 Kba__2))'
  '''
  exprL = []
  for cnj in ann:
    cList = []
    for card in cnj:
      prop = getKProp(listener, spkr, card)
      cList.append(prop)
    exprL.append(z3.And(cList))
  return z3.Or(exprL)

def k2Ann(listener, fml):
  '''
  Basically, the inverse of ann2K.
  Produces the spkr as well as the announcement.
  Assuming correctness of ann2K, the following example should work,

  >>> fml = ann2K('b', 'a', [[0,1], [0,2], [1,2]])
  >>> k2Ann('b', fml)
  ('a', [[0, 1], [0, 2], [1, 2]])
  '''
  kPre  = 'K'+listener
  disjL = fml.children()
  spkr  = ''
  if len(disjL) > 0:
    d0 = disjL[0]
    c0 = d0.children()
    p0 = c0[0].sexpr()
    pref,card = p0.split('__')
    spkr = pref.strip(kPre)
  resAnn = []
  for d in disjL:
    conjL    = d.children()
    currDisj = []
    for prop in conjL:
      propStr   = prop.sexpr()
      propL     = propStr.split('__')
      pref,card = propL[0], propL[1]
      currSpkr  = pref.strip(kPre)
      if spkr != currSpkr:
       return ('',[[]])
      else:
        currDisj.append(int(card))
    resAnn.append(currDisj)
  return (spkr, resAnn)

def ann2DealFml(spkr, ann):
  '''
  Returns the announcement converted into
  a formula involving the deal variables.

  >>> ann = [[0, 1], [0, 2], [1, 2]]
  >>> fml = ann2DealFml('a', ann)
  >>> fC = fml.children()
  >>> len(fC)
  3
  >>> fml.sexpr()
  '(or (and a__0 a__1) (and a__0 a__2) (and a__1 a__2))'
  '''
  disjList = ann
  resFml = []
  for disj in disjList:
    cList = []
    for card in disj:
      cList.append(getProp(spkr, card))
    resFml.append(z3.And(cList))
  return z3.Or(resFml)

def model2Deal(model, agents, cards):
  '''
  Given a model involving the propositional variables,
  extract the deal and return as a dictionary of hands
  for each agent.
  '''
  deal = {}
  for agt in agents:
    agtHand = []
    for card in cards:
      prop = getProp(agt, card)
      val  = model[prop].sexpr()
      if val == 'true':
        agtHand.append(card)
    deal[agt] = agtHand
  return deal

def deal2Fml(deal):
  '''
  Converts the deal into a formula involving deal variables
  '''
  cList = []
  agts  = deal.keys()
  for agt in agts:
    agtHand = deal[agt]
    for card in agtHand:
      prop = getProp(agt, card)
      cList.append(prop)
  return z3.And(cList)

def deal2Key(deal):
  '''
  Convert the deal into a (unique) string 
  that can be used as a key for a dictionary.
  '''
  agtLst = deal.keys()
  agtLst.sort()
  resKey = "< "
  for agt in agtLst:
    h = deal[agt]
    h.sort()
    hStr = str(h)[1:-1]
    resKey = resKey+hStr
    if agt != agtLst[-1]:
      resKey = resKey +" | "
  resKey = resKey +" >"
  return resKey

def deals2Fml(dList):
  '''
  Convert dList to a formula (using deal variables)
  specifying the constraints that are satisfied by
  deals in dList (currently the encoding is exhaustive).
  '''
  fList = []
  for d in dList:
    fList.append(deal2Fml(d))
  return z3.Or(fList)

def hand2KLst(deal, agent):
  '''
  Given deal, encode the fact that
  for any other agent (that has at least one card)
  he does not have the card that agent has.
  '''
  fList   = []
  agtLst  = deal.keys()
  agtHand = deal[agent]
  for ag in agtLst:
    if ag != agent and deal[ag] != []:
      for card in agtHand :
        prop = getKNProp(agent, ag, card)
        fList.append(getKNProp(agent, ag, card))
  return fList

def deal2KAgt(deal, agt):
  '''
  Returns a formula that encodes the deal for agt.
  '''
  cList = []
  agts  = deal.keys()
  for ag in agts:
    if ag  != agt and deal[ag] != []:
      agtHand = deal[ag]
      for card in agtHand:
        prop = getKProp(agt, ag, card)
        cList.append(prop)
  return z3.And(cList)

def deals2KAgt(dList, agt):
  '''
  Convert the set of deals into a formula involving 
  K_{agt} propositions (similar in spirit to 
  deals2Fml).
  '''
  fList = []
  for d in dList:
    fList.append(deal2KAgt(d, agt))
  return z3.Or(fList)

def deals2KAgt_atDeal(dList, actualDeal, agt):
  '''
  Return two formulae. The first represents the knowledge
  of agt due to the hand he has in actualDeal while the
  second formula summarizes the global dList.
  '''
  initFml = hand2KLst(actualDeal, agt)
  kFml    = deals2KAgt(dList, agt)
  return initFml, kFml

def k2Fml(kFml, agt):
  '''
  Converts a formula involving K_agt propositions
  to another formula where the K_agt propositions 
  are converted by removing the prefix.

  >>> f = k2Fml(z3.Or(z3.Bool('KaNb__0'), z3.Bool('Kac__0')), 'a')
  >>> f.sexpr()
  '(or (not b__0) c__0)'
  '''
  if kFml.num_args() == 0:
    propName = kFml.sexpr()
    kPre = 'K'+agt
    if not (propName.startswith(kPre)):
      return kFml
    propName = propName.strip(kPre)
    if propName.startswith('N'):
      propName = propName.strip('N')
      return z3.Not(z3.Bool(propName))
    return z3.Bool(propName)
  fmlExpr = kFml.sexpr()
  fLst = []
  if fmlExpr.startswith('(not'):
    return z3.Not( k2Fml(kFml.arg(0), agt) )
  for f in kFml.children():
    fLst.append( k2Fml(f, agt) )
  if fmlExpr.startswith('(or'):
    return z3.Or(fLst)
  return z3.And(fLst)

################################################################
#   Code related to navigation between the deals
################################################################
def limitHand(maximize, hSize, cardList):
  '''
  Returns a tuple of limit hand followed by the remaining cards
  of cardList. The limit had is either the minimum or maximum hand 
  of hSize from cardList depending on the value of the boolen maximize. 
  If maximize is true, return the maximum hand else return the minimum.
  P.S :- cardList is not assumed to be sorted.
  '''
  cardList.sort()
  if maximize:
    cardList.reverse()
  limitH = []
  remList = []
  i = 0
  while i < hSize:
    limitH.append(cardList[i])
    i = i + 1
  while i < len(cardList):
    remList.append(cardList[i])
    i = i + 1
  if maximize:
    limitH.reverse()
  return limitH, remList

def minHand(hSize, cardList):
  return limitHand(False, hSize, cardList)

def maxHand(hSize, cardList):
  return limitHand(True,  hSize, cardList)

def minDeal(dLst, agtLst, cardLst):
  minD = {}
  remC = cardLst
  i = 0
  while i < len(agtLst):
    mH, remC = minHand(dLst[i], remC)
    minD[agtLst[i]] = mH
    i = i + 1
  return minD

def succHand(hand, remList):
  '''
  INput :  hand, remList as two sorted lists
            such that their intersection is empty.
  Return a tuple such that the first element is 
  the sucessor of hand and the second element is the
  list of remaining cards in sorted order.
  If hand is already maximal, then return [],(hand+remList).
  '''
  if hand == []:
    return ([], remList)
  hMin, hMax = hand[0], hand[-1]
  rMin, rMax = remList[0], remList[-1]
  succH , resList  = [], []
  if hMin > rMax:
    remList = remList + hand
    return [], remList
  i = 0
  # Obtain the maximal card of hand that is less than rMax
  while (i+1 < len(hand)) and (hand[i+1] < rMax) :
    succH.append(hand[i])
    i = i + 1
  maxCard = hand[i] # The card that needs to be changed
  j = 0
  while (maxCard > remList[j]) :
    resList.append(remList[j])
    j = j + 1
  succH.append(remList[j])
  resList.append(maxCard)
  i,j = i+1, j+1
  hSize = len(hand[i:])
  cardsLst = hand[i:] + remList[j:]
  remH, remL = minHand(hSize, cardsLst)
  succH = succH + remH
  resList = resList + remL
  return succH, resList

def succDeal_byLst(deal, agtLst):
  '''
  SuccDeal according to the ordering defined
  by agtLst and return [] if deal is the maximal
  according to this ordering.
  '''
  if not set(agtLst).issubset(set(deal.keys())):
    raise Exception('agtLst is not a subset of deal.keys().')
  i = 1
  agtLst.reverse()
  while i < len(agtLst):
    remCards = []
    prevAgts = agtLst[:i]
    for ag in prevAgts:
      remCards = remCards + deal[ag]
    remCards.sort()
    currAgt = agtLst[i]
    agtHand = deal[currAgt]
    succH, remCards = succHand(agtHand, remCards)
    if (succH != []):
      laterAgts = agtLst[(i+1):]
      succDeal = {}
      for ag in laterAgts:
        succDeal[ag] = deal[ag]
      succDeal[currAgt] = succH
      j = i - 1
      while j >= 0:
        currAgt = agtLst[j]
        nHand = len(deal[currAgt])
        succDeal[currAgt] = remCards[:nHand]
        remCards = remCards[nHand:]
        j = j - 1
      return succDeal
    i = i + 1
  return []

def succDeal(deal):
  agtLst = deal.keys()
  agtLst.sort()
  return succDeal_byLst(deal, agtLst)

def allHands(hSize, cardList):
  nH,rC = minHand(hSize, cardList)
  if rC == []:
    return [nH]
  resL = []
  while nH != []:
    resL.append(nH)
    nH, rC = succHand(nH, rC)
  return resL

def allDeals(dLst, agents, cardLst):
  resDeals = []
  nD = minDeal(dLst, agents, cardLst)
  while nD != []:
    resDeals.append(nD)
    agtLst = []
    for ag in agents:
      agtLst.append(ag)
    nD = succDeal_byLst(nD, agtLst)
  return resDeals

def ann2Str(annList):
  resL = []
  for x in annList:
    resL.append(str(x))
  return resL

def annIntersection(ann1, ann2):
  ann1S, ann2S = ann2Str(ann1), ann2Str(ann2)
  setAnn1, setAnn2 = set(ann1S), set(ann2S)
  resSet = setAnn1.intersection(setAnn2)
  resL = list(resSet)
  resAnn = S2Ann(resL)
  return resAnn

def S2Ann(annS):
  resAnn = []
  annS.sort()
  for x in annS:
    resAnn.append(eval(x))
  return resAnn

################################################################
#  Code related to sorting and helping visualize deal lists.
################################################################
def LE_byLst(d1, d2, agtLst):
  '''
  Return True iff d1 <= d2 under lexicographic ordering for agtLst. 
  Furthermore, the sequence of agtLst denotes the ordering of the
  agents to consider for ordering.
  '''
  if agtLst == []: # d1 == d2 (for agtLst == [])
    return True
  agtSet = set(agtLst)
  if (not agtSet.issubset(set(d1))) or (not agtSet.issubset(set(d2))):
    raise Exception('agtList not compatible with one of the deals')  
  agents = agtLst
  ag = agents[0]
  d1[ag].sort()
  d2[ag].sort()
  if d1[ag] == d2[ag]:
    agents = agents[1:]
    return LE_byLst(d1, d2, agents)
  i = 0
  while (i < len(d1[ag])) and (i < len(d2[ag])) and (d1[ag][i] == d2[ag][i]):
    i = i + 1
  if (i > len(d1[ag])) or (d1[ag][i] < d2[ag][i]) :
    return True
  return False

def LE(d1,d2):
  if set(d1.keys()) != set(d2.keys()):
    raise Exception('keys of the input deals are not compatible')
  agtLst = d1.keys()
  agtLst.sort()
  return LE_byLst(d1, d2, agtLst)

def sortDeals_byLst(dList, agtLst):
  '''
  sort Deals according to ordering defined in agtLst
  '''
  resL  = [dList[0]]
  dList = dList[1:]  
  for d in dList:
    l1 = []
    i = 0
    while i < len(resL) and LE_byLst(resL[i], d, agtLst) :
      l1.append(resL[i])
      i = i + 1
    l2 = [d] + (resL[i:])
    resL = l1 + l2
  return resL

def lexSort(annLst):
  '''
  Sort a disjunction of hands lexicographically.
  '''
  resL = []
  for a in annList:
    l1 = []
    i  = 0
    a.sort()
    while i < len(resL) and resL[i] <= a:
      l1.append(resL[i])
      i = i + 1
    l2 = [a] + resL[i:]
    resL = l1 + l2
  return resL

def crossProduct(l1, l2, options):
  '''
  Obtain crossproduct of l1, l2 
  '''
  resL = []
  if options == 'd' or options == '': # default
    for x in l1:
      for y in l2:
        resL.append(x + y)
  elif options == 'o' : # Otherwise
    for y in l2:
      for x in l1:
        resL.append(y+x)
  return resL

def crossProd(l1, l2):
  return crossProduct(l1, l2, '')

def annSort(ann):
  annS = ann2Str(ann)
  annS.sort()
  resAnn = S2Ann(annS)
  return resAnn

def annCrossCList(ann, cList):
  '''
  returns a sequence of announcements extending the
  input announcement ann with conjuncts from cList.
  '''
  newCList = []
  for conj in cList:
    newCList.append([conj])
  return crossProduct([ann], newCList, '')

def filterBy(annL, cardList, contains):
  resAnn = []
  cSet = set(cardList)
  for conj in annL:
    conjSet = set(conj)  
    if not (conjSet.isdisjoint(cSet)) and contains :
      resAnn.append(conj)
    elif conjSet.isdisjoint(cSet) and not contains:
      resAnn.append(conj)
  return resAnn

def sortDeals(dList):
  '''
  Return the sorted lexicographic ordering of dList
  '''
  d = dList[0]
  agents = d.keys()
  agents.sort()
  resL = sortDeals_byLst(dList, agents)
  return resL

def printDeal(deal, agtLst):
  print '<',
  i = 0
  while i < len(agtLst):
    agt = agtLst[i]
    print deal[agt],
    i = i + 1
    if i < len(agtLst):
      print ', ',
  print '>'

def printBy(dList, agtLst):
  for d in dList:
    printDeal(d, agtLst)
  print
  print 'Order : ', agtLst

def printAnnL(annL, perLine):
  n = len(annL)
  l = perLine
  for i in range(n):
    print annL[i], '\t',
    if (i%l == l-1) and (i+1 < n):
      print
