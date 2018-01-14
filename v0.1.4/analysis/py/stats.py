################################################################
####  TODO : Randomized runs with statistical guarantees.
################################################################

def getCards(deck, n):
  '''
  Get n distinct cards randomly from deck
  '''
  if len(deck) < n:
    return []
  rangeList = []
  for c in deck:
    rangeList.append(c)
  cardsL = []
  for i in range(n):
    maxId = len(rangeList) - 1
    idx = rand.randint(0, maxId)
    cardsL.append( rangeList[idx])
    rangeList.pop(idx)
  return cardsL

def getStrategy1(deal, agt):
  '''
  Return a possible announcement sequence for agt at deal.
  Since announcements are independent of actual history, we
  can generate the strategy apriori.
  '''
  hand = deal[agt]
  rest = []
  for agt1 in deal.keys():
    if agt1 != agt:
      rest = rest + deal[agt1]
  X = getCards(rest, 2)
  annL1 = ut.allHands(len(hand), hand + X)
  if rand.randint(0,1) == 0:
    X.pop() # drop an element of X
  annL2 = ut.allHands(len(hand), hand + X)
  return [annL1, annL2]

def getRun1(deal, infAgts):
  '''
  Return a possible run of protocol 1 at deal.
  '''
  annSequences = {}
  for agt in infAgts:
    annSequences[agt] =  getStrategy1(deal, agt)
  run = []
  for i in range(2):
    for agt in infAgts:
      ann = (agt, annSequences[agt][i])
      run.append( ann )
  return run

def getRuns1(deal, infAgts, k, cutoff):
  '''
  Get k distinct runs of protocol 1 starting at deal.
  '''
  runList = []
  for i in range(k):
    currRun = getRun1(deal, infAgts)
    j = 0
    while currRun in runList and j < cutoff:
      currRun = getRun1(deal, infAgts)
      j = j + 1
    if j == cutoff: # give up on obtaining k runs
      return runList
    runList.append(currRun)
  return runList
