import cpState as cps;
import cpUtil  as ut;
import random  as rand;

################################################################
####       Code relevant for analysis
################################################################
def getColPosK(stateList, agt):
  posK  = {}
  for state in stateList:
    nPos = len(state.getPosK('e'))
    if not nPos in posK:
      posK[nPos] = 1
    else:
      posK[nPos] = posK[nPos] + 1
  return posK

def getColumnP(startState, runLst, agt):
  stateL = []
  s0 = startState
  for r in runLst:
    stateL.append(s0.execRun(r))
  return getColPosK(stateL, agt)    

def getTablePosK(state, runL, interval, agt):  
  rL = []
  i = 0
  while i < len(runL):
    j = 0 
    rList = []
    while j < interval and i < len(runL):
      rList.append(runL[i])
      j = j + 1
      i = i + 1
    rL.append(rList)
  columns = []
  for rList in rL:
    columns.append(getColumnP(state, rList, agt))
  return columns                

def getLatexPosK(columns, colHeaders, agt):
  '''
  '''
  latex = ''

def getAgtResult(state, run, agt):
  '''
  Ensure that state is initialized to the required deal.
  Returns a record summarizing info that agt learns after
  this run.
  '''
  result = {}
  s1 = state.execRun(run)
  result['pos'] = len(s1.getPosK(agt))
  result['neg'] = len(s1.getNegK(agt))
  result['nD']  = len(s1.getAgtDeals(agt))
  return result

def getAgtRecords(state, runList, eaves):
  result = []
  for r in runList:
    record = getAgtResult(state, r, eaves)
    result.append(record)
  if result == []:
    return []
  rows = {}
  keyList = result[0].keys()
  for key in keyList:
    rows[key] = []
    for i in range(len(runList)):
      rows[key].append(result[i][key])
  return rows

def getEavesTable(state, eaves, runLst, keyLst):
  rows = getEavesRecords(state, runLst, eaves)
  tabTex = getTable(rows, keyLst, 'r')
  return tabTex

def getTable(rows, keyList, colPref):
  '''
  Print the actual latex table given rows and keyList
  '''
  if keyList == [] or rows ==[]:
    return ''
  k0 = keyList[0]
  nRuns = len(rows[k0])  
  header = '\\begin{tabular}{| c | '
  row1 = '  '
  for i in range(nRuns):
    header = header + 'c '
    row1   = row1 + '& $'+colPref+'_'+str(i)+'$ '
  header = header + '|}\n \hline\n'
  row1 = row1 + '\\\\'  
  header = header + row1 + '\n \\hline'
  body  = ''
  for k in keyList:
    body = body + '\n ' + str(k)
    for entry in rows[k]:
      body = body + ' & ' + str(entry) + ' '
    body = body + '\\\\'
  footer = '\hline \n\end{tabular}'
  tableLatex= header + body + footer
  return tableLatex

################################################################
####    Focus on efficiency. How long does it really take?
#### a) efficiency
#### b) coverage (more or all number of runs)
#### c) non trivial multi rounds?
################################################################
def getAnn1ForX(deal, agt, X):
  '''
  '''
  hand = deal[agt]
  annL1 = ut.allHands(len(hand), hand + X[agt])
  return (agt, annL1)

def getRun1ForX(deal, X1, X2):
  '''
  deal   - the actual deal.
  X1, X2 - dictionaries denoting the choice of X in rounds 1, 2 
           for every agt.
  Return the actual run.
  '''
  agts = ['a', 'b', 'c']
  resRun = []
  r1, r2 = [], [] # Rounds 1 and 2.
  for ag in agts:
    r1.append( getAnn1ForX(deal, ag, X1) )
    r2.append( getAnn1ForX(deal, ag, X2) )
  resRun = r1 + r2
  return resRun

def genX(deal, n):
  '''
  Return the set of all n cards that an agent doesn't have.
  (assume that n <= len(deck \ deal[agt]) for each agent).
  '''
  agts = ['a', 'b', 'c']
  possX = {}
  for ag in agts:
    hand = deal[ag]
    rest = []
    for ag1 in agts:
      if ag1 != ag :
        rest = rest + deal[ag1]
    # rest initialized.
    possX[ag] = ut.allHands(n, rest)
  return possX

def genXL(deal, n, cutoff):
  '''
  Return all possible combinations of choices of 
  X for each agent. Basically, a cross product of
  possible X of size n for each agent.  
  '''
  possX = genX(deal, n)
  Xa, Xb, Xc = possX['a'], possX['b'], possX['c']
  XL = []  
  i = 0
  for la in Xa:
    for lb in Xb:
      for lc in Xc:
        currX = {}
        currX['a'] = la
        currX['b'] = lb
        currX['c'] = lc
        XL.append(currX)
        i = i + 1
        if i >= cutoff:
          return XL
  return XL

def genXL2(deal, n, cutoff):
  '''
  returns a list of pairs (X1, X2)
  '''
  XL1 = genXL(deal, n, cutoff)
  resXL = []
  a,b,c = 'a', 'b', 'c'
  agts = [a, b, c]
  resPairL = []
  debug = False
  if cutoff <= 50:
    debug = True
  if debug:
    print 'Obtained XL1, len(XL1) = ', len(XL1)
  i = 0
  while i < len(XL1) and i < cutoff:
    xl = XL1[i]
    if debug:
      print 'processing ', xl
    la, lb, lc = [xl[a]], [xl[b]], [xl[c]]
    for x in xl[a]: 
      la.append([x])
    for y in xl[b]: 
      lb.append([y])
    for z in xl[c]: 
      lc.append([z])
    # Initialized la, lb, lc.
    for x in la:
      for y in lb:
        for z in lc:
          xll = {}
          xll[a], xll[b], xll[c] = x, y, z
          xPair = (xl, xll)
          resPairL.append(xPair)
    i = i + 1
  if debug:
    print
  return resPairL

def getRun1List2(deal, n, cutoff):
  '''
  Get a list of two round Xi at most upto cutoff.
  '''
  xPLst = genXL2(deal, n, cutoff)
  runLst = []
  i = 0
  for x1, x2 in xPLst:
    rn = getRun1ForX(deal, x1, x2)
    runLst.append(rn)
  return runLst

a,b,c,e = 'a', 'b', 'c', 'e'
agtLst  = [a, b, c, e]
infAgts = [a, b, c]
eaves   = 'e'

def getState(i):
  dLst = [i, i, i, 0]  
  deck = range(3*i)
  d = ut.minDeal(dLst, agtLst, deck)
  s = cps.cpState(dLst, agtLst, d, infAgts, eaves)
  return s

def getRuns1State(i, n, cutoff):
  s = getState(i)
  d = s.deal
  return getRun1List2(d, n, cutoff)
