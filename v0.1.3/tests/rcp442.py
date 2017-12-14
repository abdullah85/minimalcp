import cpState as cps
import cpUtil as ut; 

deal = {'a' : [0, 1, 2, 3], 'b':[4, 5, 6, 7], 'c':[8,9] };
infAgts, eaves = ['a', 'b'],'c';
rus442 = cps.cpState([4, 4, 2], ['a','b', 'c'], deal, infAgts, eaves);

aCards = [[0], [1], [2], [3]]; 
A0 = ut.allHands(4, range(4,10)); 
A1 = ut.allHands(3, range(4,10)); 
aL = ut.crossProduct(aCards, A1, ''); 
aL = [[0,1,2,3]] + aL + A0; 
annA = ('a', aL); run = [annA]; 

s0 = rus442.updateAnn(annA); 
altC = s0.getAgtDeals('c'); 
altC = ut.sortDeals(altC);

aH = ut.allHands(4, range(10))

def nonHand(hand):
  '''
  All cards not in hand
  '''
  cLst = range(10)
  nH = []
  for c in cLst:
    if not c in hand:
      nH.append(c)
  return nH

def maxInfFor(hand):
  '''
  returns the announcement of maximum size
  that is informative to the agent 'b' for every
  deal that agent 'a' thinks possible initially.
  '''
  cLst = range(10)
  nH = nonHand(hand)  
  # All hands that do not contain any of a's cards.
  nilHand = ut.allHands(4, nH)
  # Convert the cards into a list of lists
  oneCard = ut.allHands(1, hand)
  # Set of all hands of size 3 not containing any of a's cards
  threeCH = ut.allHands(3, nH)
  # Set of all hands containing exactly one card from hand  
  oneCHL  = ut.crossProd(oneCard, threeCH)
  maxInfAnn = [hand] + oneCHL + nilHand
  maxInfAnn = ut.annSort(maxInfAnn)
  return maxInfAnn

maxInfAnn = []
for d in altC:
  mIA = maxInfFor(d['a'])
  maxInfAnn.append(mIA)

# The code for checking for a pairing deal.
restDls = altC[1:]
restMax = maxInfAnn[1:]
cardsLeaked = []
actualDeal  = deal
actualMax   = maxInfAnn[0]
iAnnL       = [] # The set of all intersecting announcements
for i in range(len(restDls)):
  possPair = restDls[i]
  pairAnn  = restMax[i]
  iAnn     = ut.annIntersection(actualMax, pairAnn)
  iAnnL.append(iAnn)

initA = rus442.getAgtDeals('a'); 
initA = ut.sortDeals(initA)

def getCardsLeaked(annL):
  cardsLeaked = []
  for annL in annL:
    ann = ('a', annL)
    run = [ann]
    res = rus442.getCards4Deals('c', run, initA)
    cardsLeaked.append(res)
  return cardsLeaked

def maxLeaked(leakedList):
  maxLen = 0
  maximalAnn = []
  for ann in leakedList:
    if len(ann) > maxLen:
      maximalAnn = ann
      maxLen = len(ann)
  return maximalAnn
