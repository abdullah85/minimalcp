import cpState as cps
import cpUtil as ut; 
import pickle as pk;
import time
import random as rand
import z3

def getRun(sNo, state, deal, agt1):
  '''
  agt is the agt who makes the first announcement
  '''
  runL = []
  if sNo == 1:
    runL = run1(state, deal, agt1)
  elif sNo == 2:
    runL = run2(state, deal, agt1)
  return runL

def displayHands(hLst, k):
  for i in range(len(hLst)/k):
    for d in hLst[(k*i) : (k*i) + k]:
      print d,
    print

def filterHands(origLst, cLst):
  resLst = []
  for d in origLst:
    extend = True
    for c in cLst:
      if not c in d:
        extend = False
    if extend:
      resLst.append(d)
  return resLst

def filterDeals(dLst, agt, cLst):          
  resLst = []
  for d in dLst:
    if d[agt] in cLst:
      resLst.append(d)
  return resLst

def experimentRange(sNo, r1, r2):
  '''
  sNo denotes the strategy number to use
  '''
  a,b,c,e = 'a', 'b', 'c', 'e'
  st = cps.cpState
  agtL = [a, b, c, e]
  runL,posL,negL,nDeals = [], [] ,[] ,[]
  for i in range(r1,r2):
    dLst, cards = [i, i, i, 0], range(3*i);
    dl = ut.minDeal(dLst, agtL, cards);
    r0 = st(dLst, agtL, dl, [a,b,c], e)
    rn1 = getRun(sNo, r0, dl, a)    
    runL.append(rn1)
    r1 = r0.execRun(rn1)
    posL.append(r1.getPosK(e))
    negL.append(r1.getNegK(e))
    nDeals.append(r1.getAgtDeals(e))
  return (runL, posL, negL, nDeals)

def tabulateRange(res):
  '''
  Tabulate the result of experimentRange
  '''
  runL,posL, negL, nDeals = res[0], res[1], res[2], res[3]
  rows = ['', '' ,'' ,'']
  for i in range(len(runL)):
    fAnnLst = runL[i][0][1]
    if i != 0:
      for j in range(4):
        rows[j] = rows[j] + '&'
    rows[0] = rows[0] + (str(len(fAnnLst) - 1 ) +'\t')
    rows[1] = rows[1] + (str(len(posL[i]))       +'\t')
    rows[2] = rows[2] + (str(len(negL[i]))       +'\t')    
    rows[3] = rows[3] + (str(len(nDeals[i]))     +'\t')
  for i in range(len(rows)):
    rows[i] = rows[i]+'\n'
    print rows[i]
  return rows

def run1(state, deal, agt1):
  fAnn,x = firstAnn(state, deal, agt1)
  sAnn = secondAnn1(state, deal, fAnn)
  return [fAnn, sAnn]

def run2(state, deal, agt1):
  fAnn,x = firstAnn(state, deal, agt1)
  sAnn   = secondAnn2(state, deal, fAnn)
  return [fAnn, sAnn]

def firstAnn(state, deal, agt):
  hand = deal[agt]
  uSet = set(state.cards)
  restCards = list(uSet.difference(set(hand)))
  unkIdx = rand.randint(0, len(restCards)-1)
  unknownCard = restCards[unkIdx]
  dList = [hand]
  for i in range(len(hand)):
    disj = []
    for j in range(len(hand)):
      disj.append(hand[j])
    disj[i] = unknownCard
    disj.sort()
    dList.append(disj)
  dList.sort()
  ann = (agt, dList)
  return ann, unknownCard

def secondAnn2(state, deal, firstAnn):
  xCard = getStrategy1(deal, firstAnn)
  a,b,c,e = 'a', 'b', 'c', 'e'
  agt2,agt3 = 'b', 'c'
  if xCard in deal['c']:
    agt2, agt3 = 'c', 'b'
  pairList = []
  dList = [deal[agt2]]
  idL = range(len(deal[agt3]))
  for c in deal[a]:
    idx = rand.randint(0, len(idL)-1)
    cId = idL.pop(idx) # the chosen index
    card = deal[agt3][cId]
    pairList.append((c, card))
  for i in range(len(pairList)):
    p1,p2 = pairList[i]
    disj = [p1]
    if i == 0 :
      for c in deal[agt3]:
        if c != p2:
          disj.append(c)
      pairList[1] = (pairList[1][0], p2)
    else:
      disj.append(p2)
      choiceLst = []
      for x in (deal[agt2] + deal[agt3]):
        if (x != p2) and (x != xCard):
          choiceLst.append(x)
      idL = range(len(choiceLst))
      while len(disj) != len(deal[agt2]):
        idx = rand.randint(0, len(idL) - 1)
        cId = idL.pop(idx)
        card = choiceLst[cId]
        disj.append(card)
    dList.append(disj)
  return (agt2, dList)

def secondAnn1(state, deal, firstAnn):
  '''
  Generate basically 3 disjuncts including own hand,
  while other two disjuncts are such that each disjunct
  has at least one card of the other two players.
  '''
  agt1 = firstAnn[0]
  dList = firstAnn[1]
  hand1 = deal[agt1] 
  altDisj = dList[0]
  if hand1 == dList[0]:
    altDisj = dList[1]
  xCard = -1
  for i in range(len(hand1)):
    if hand1[i] != altDisj[i]:
      xCard = altDisj[i]
  agt2,agt3 = 'b','c'      
  if xCard in deal['c']:
    agt2,agt3 = 'c','b'
  hand2,hand3 = deal[agt2], deal[agt3]
  disjL = [hand2] # The announcer's hand.
  # Get all indices first
  h1L,h2L,h3L = range(len(hand1)), range(len(hand2)), range(len(hand3))
  i1 = rand.randint(0, h1L[-1])
  h1L.remove(i1)
  i2 = rand.randint(0, h1L[-1])
  a1 = hand1[i1]
  a2 = hand1[i2]
  # Obtained a1,a2
  idx = rand.randint(0, h3L[-1])
  x1 = hand3[idx]
  Y  = hand3[:idx] + hand3[(idx+1):] # H_P' \ x1
  YL = []
  i = 0
  while i < (len(hand2)) -1 and i < len(Y):
    YL.append(Y[i])
    i = i + 1    
  j = 0
  while i< len(hand2)-1:
    if hand2[j] == xCard:
      j = j + 1
    YL.append(hand2[j])
    i = i + 1
  ch = rand.randint(0,1)
  if ch == 0: # Choose some cards from other players hand.
    X = []
    X = YL
  else : # Choose from own hand
    X = []
    for c in hand2:
      if c != xCard:
        X.append(c)
  D1 = [a1] + YL
  D2 = [a2] + X
  dList = [deal[agt2], D1, D2]
  dList.sort()
  return (agt2, dList)

def getStrategy1(deal, firstAnn):
  agt = firstAnn[0]
  aHand = deal[agt]
  dList = firstAnn[1]
  nonHand = dList[0]
  if aHand == dList[0]:
    nonHand = dList[1]
  xCard = nonHand[0]
  i = 0
  while xCard in aHand:
    xCard = nonHand[i]
    i = i + 1
  return xCard

def getStrategy2(deal, secondAnn):
  agt = secondAnn[agt]

################################################################

def filterHands(origLst, cLst):
  resLst = []
  for d in origLst:
    extend = True
    for c in cLst:
      if not c in d:
        extend = False
    if extend:
      resLst.append(d)
  return resLst

def filterDeals(dLst, agt, cLst):
  resLst = []
  for d in dLst:
    if d[agt] in cLst:
      resLst.append(d)
  return resLst

################################################################

def nonIntersectingHands(h, l):
  niL = []
  refSet = set(h)
  for i in range(len(l)):
    currHand = l[i]
    currSet = set(currHand)
    diffSet = currSet.difference(refSet)
    if diffSet == currSet:
      niL.append(i)
  return niL

def getWitnessL(src, pairLst, annL):
  resL = []
  x = 'x'
  for (l0, l1) in pairLst:
    l0Witness = True
    for c in annL:
      if c in l0 and c != src:
        l0Witness = False
    if l0Witness:
      resL.append(0)
    else:
      l1Witness = True
      for c in annL:
        if c in l1 and c != src:
          l1Witness = False
      if l1Witness:
        resL.append(1)
      else:
        resL.append(x)
  return resL

def nonIntersectingLst(src, pLst, hLst):
  resL = []
  for (p1, p2) in pLst:
    l1 = nonIntersectingHands(p1, hLst)
    l2 = nonIntersectingHands(p2, hLst)
    if 0 in l1: 
      l1.remove(0)
    if 0 in l2: 
      l2.remove(0)
    resL.append((l1,l2))
  return resL
     
def pair2Fml(pair, hLst):
  p1,p2 = pair
  l1 = nonIntersectingHands(p1, hLst)
  l2 = nonIntersectingHands(p2, hLst)
  dL1, dL2 = [], []
  for i in l1:
    dL1.append(Not(boolHands[i]))
  for i in l2:
    dL2.append(Not(boolHands[i]))
  return (Or(And(dL1), And(dL2)))

def pair2FmlSrc(src, pair, hLst):
  p1,p2 = pair
  l1 = nonIntersectingHands(p1, hLst)
  l2 = nonIntersectingHands(p2, hLst)
  dL1, dL2 = [], []
  for i in l1:
    if i != src :
      dL1.append(Not(boolHands[i]))
  for i in l2:
    if i != src :
      dL2.append(Not(boolHands[i]))
  if dL1 == []:
    dL1 = [True]
  if dL2 == []:
    dL2 = [True]
  return (Or(And(dL1), And(dL2)))

def pLst2Fml(src, pL, hL):
  cL = []
  for i in range(len(pL)):
    p = pL[i]
    cL.append(pair2FmlSrc( src, p, hL))
  return And(cL)

def getUniquePairs(lst):
  k = len(lst)/2
  h0,rem0 = ut.minHand(4, lst)    
  pairLst = []
  processed = []
  while h0 != []:
    if h0 not in processed :
      processed.append(h0)
      processed.append(rem0)
      pairLst.append((h0, rem0))
    h0,rem0 = ut.succHand(h0, rem0)
  return pairLst

def getFinalList(fmlLst):
  finalFmlLst = []
  for i in range(len(boolHands)):
    h  = boolHands[i]
    impl = fmlLst[i]
    finalFmlLst.append(Implies(h, impl))
  return finalFmlLst

def ImplicandLst(pLst, hLst):
  fmlLst = []
  for i in range(len(pLst)):
    pL = pLst[i]
    fmlLst.append(pLst2Fml( i, pL, hLst))
  return fmlLst

def addToSolver(solvR, Lst):
  for f in Lst:
    solvR.add(f)
  return solvR

def nHandLst(k):
  hL = getHandLst()
  hL.append(k)
  return hL

def getHandLst():
  handBLst = []
  for h in boolHands:
    handBLst.append(h)
  return handBLst

pe  = {}
peN = {}
ke  = {}
keN = {}

for agt in ['a','b','c']:
  pe[agt] = z3.BoolVector('Pe'+agt, 12)
  peN[agt] = z3.BoolVector('PeN'+agt, 12)
  ke[agt] = z3.BoolVector('Ke'+agt, 12)
  keN[agt] = z3.BoolVector('KeN'+agt, 12)

def eavesK4Ann1():
  '''
  The +ve knowledge version of what Eaves knows
  '''
  eKP = []
  for i in range(12):
    f = ke[a][i]
    g = Not(peN[a][i])
    f1 = Implies(f, g)
    f2 = Implies(g, f)
    eKP.append(And(f1, f2))
  return eKP

def eavesKN4Ann1():
  '''
  The -ve knowledge version of what Eaves knows
  '''
  eKN = []
  for i in range(12):
    f  = keN[a][i]
    g  = Not(pe[a][i])
    f1 = Implies(f, g)
    f2 = Implies(g, f)
    eKN.append(And(f1, f2))
  return eKN

def peWitnesses():
  fmlLst = []
  for i in range(12):
    head1 = pe[a][i]
    head2 = peN[a][i]
    body1 = []
    body2 = []
    for j in range(len(hLst)):
      hand = hLst[j]
      hb   = boolHands[j]
      if i in hand:
        body1.append(hb)
      else:
        body2.append(hb)
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

def eavesP4Ann1():
  '''
  The formulation of what eaves thinks
  to be possible when the system has only  
  the first announcement by A.
  '''  
  eP = []
  for i in range(len(hLst)):
    hand = hLst[i]
    head = boolHands[i]
    cL = range(12)
    body = []
    for j in range(len(cL)):
      c = cL[j]
      if c in hand:
        body.append(pe[a][j])
      else:
        body.append(peN[a][j])
    body = And(body)
    f1 = Implies(head, body)
    f2 = Implies(body, head)
    fml = And(f1, f2)
    eP.append(fml)
  return eP

def getSafeSolver():
  solver = getAnn1Solver()
  solver.push()
  solver.add(eavesP4Ann1())
  solver.push()
  solver.add(eavesK4Ann1())
  solver.push()
  solver.add(peWitnesses())
  solver.push()
  solver.add(eavesIgnorant())
  solver.push()
  return solver

def eavesIgnorant():
  '''
  Safety of cards
  '''
  fml = []
  for i in range(12):
    fml.append(Not (ke[a][i]))
  return And(fml)
          
def getAnn1Solver():
  iLst = ImplicandLst(pLst, hLst)
  fLst = getFinalList(iLst)
  solver = z3.Solver()
  for f in fLst:
    solver.push()
    solver.add(f)
  return solver

def gEq5HandsSolver():
  solver = getAnn1Solver()
  solver.push()
  gEq5   = z3.AtLeast(nHandLst(5))
  solver.add(gEq5)
  solver.push()
  solver.add(boolHands[0])
  return solver

def gEqFml(n):
  gEqFmlN  = z3.AtLeast(nHandLst(n))
  return gEqFmlN

def indices2Fml(idL):
  cLst = []
  for i in idL:
    cLst.append(boolHands[i])
  return And(cLst)

def indices2AnnL(idL):
  if idL ==[]: return []
  return [hLst[idL[0]]] + indices2AnnL(idL[1:])

def getModels(solver, nRes):
  resM = []
  res = solver.check()
  i = 0
  while res == z3.sat and i < nRes:
    m = solver.model()
    resM.append(m)
    hL = getHandIndices(m)
    fml = indices2Fml(hL)
    solver.add(Not(fml))
    res = solver.check()
    i = i + 1
  return resM

def getMHandIndices(mL):
  hIL = []
  for m in mL:
    hIL.append(getHandIndices(m))
  return hIL

def getMHands(mL):
  handLst = []
  for m in mL:
    handLst.append(getHands(m))
  return handLst
    
def getHands(m):
  hI = getHandIndices(m)
  handL = []
  for i in hI:
    handL.append(hLst[i])
  return handL

def getHandIndices(m):
  iL, dL = getIndicesSet(m)
  hIndices = []
  for i in iL:
    dName = dL[i].name()
    if dName.startswith('h'):
      idx = int(dName.split('__')[1])
      hIndices.append(idx)
  return hIndices

def getIndicesSet(m):
  dL = sortModelDecls(m)
  indicesSet = []
  for i in range(len(dL)):
    d = dL[i]
    if m[d].sexpr() == 'true':
      indicesSet.append(i)
  return (indicesSet, dL)

def sortModelDecls(m):
  decls  = m.decls()
  resLst = []
  for d in decls:
    i = 0
    currDecl = d
    for i in range(len(resLst)):
      currName = currDecl.name()
      currIdx  = int(currName.split('__')[1])
      resDecl = resLst[i]
      resName = resDecl.name()
      resIdx  = int(resName.split('__')[1])
      if currIdx < resIdx:
        resLst[i] = currDecl
        currDecl  = resDecl
    resLst.append(currDecl)
  return resLst

z3 = cps.z3; And = z3.And;
Implies = z3.Implies; Not = z3.Not; Or = z3.Or;
cL = ut.allHands(4, range(12))
cL5 = filterHands(cL, [5])
hLst = [[0,1,2,3]] + cL5
boolHands = z3.BoolVector('h', len(hLst))
bH = boolHands

a,b,c,e = 'a', 'b', 'c', 'e'; dL,agtL, cards = [4,4,4,0],[a,b,c,e], range(12); \
deal = ut.minDeal(dL, agtL, cards); st = cps.cpState; s0 = st(dL,agtL, deal, [a,b,c], e)

remLst = []
for h in hLst:
  cS = set(cards)
  remCards = list(cS.difference(set(h)))    
  remLst.append(remCards)

pLst = []
for r in remLst:
  pLst.append(getUniquePairs(r))

ann1Indices = [0, 1, 2, 10, 46]

#iLst = ImplicandLst(pLst, hLst)
#fLst = getFinalList(iLst)
#fAnnFml = And(fLst)

################################################################
####  Overview of Second order safety
################################################################

def extendedAnn1(s0, deal, agt, k):
  '''
  Compute firstAnn and extend by k random non hands of agt.
  '''
  ann1, xCard = firstAnn(s0, deal, agt)
  hL  = ut.allHands(len(deal[agt]), s0.cards)
  hLx = filterHands(hL, [xCard])
  # Now to genuinely increas the ann length.
  nonAnn1L = []
  for h in hLx :
    if not h in ann1[1]:
      nonAnn1L.append(h)
  idL = range(len(nonAnn1L))
  resHands = ann1[1]
  choiceLst = []
  for x in idL:
    choiceLst.append(x)
  for i in range(k):
    idx = rand.randint(0, len(choiceLst) - 1)
    dId = choiceLst.pop(idx)
    resHands.append(nonAnn1L[dId])    
  return (resHands, nonAnn1L, xCard)

def computeLeakage(s0, dLst, ann1, agt):
  kb = []
  for d in dLst: 
    r0 = s0.newState()
    r0.deal = d
    rF = r0.updateAnn(ann1)
    kb.append(rF.getCards(agt))
  return kb

################################################################
