import cpState as cps;
import cpUtil  as ut;
import random  as rand;

################################################################
####    Focus on efficiency. How long does it really take?
#### a) efficiency
#### b) coverage (more or all number of runs)
#### c) non trivial multi rounds?
################################################################
def getAnn1ForX(deal, agt, X):
  '''
  returns the announcement "My hand is a subset of H_agt \cup X".
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

################################################################
####  Obtaining latex tables (alongwith results)
################################################################
def getColPosK(stateList, agt):
  '''
  Get summary of +ve knowledge of agt for stateList.
  '''
  col  = {}
  for state in stateList:
    nPos = len(state.getPosK('e'))
    if not nPos in col.keys():
      col[nPos] = 1
    else:
      col[nPos] = col[nPos] + 1
  return col

def getRunsColPosK(startState, runLst, agt):
  '''
  Given a list of runs, return the summary of PosK
  '''
  stateL = []
  s0 = startState
  for r in runLst:
    stateL.append(s0.execRun(r))
  col = getColPosK(stateL, agt)
  return col

def getRunsColumns(state, runL, interval, agt):
  '''
  split runs up into intervals and return a list of columns
  '''
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
    columns.append( getRunsColPosK(state, rList, agt) )
  return columns

def getLatexPosK(columns, colHeaders):
  '''
  Obtain table from columns and colHeaders information
  '''
  latex = ''
  keyLst = []
  for col in columns:
    keyLst = keyLst + col.keys()
  keyLst = list(set(keyLst))
  header = '\n\n\\begin{tabular}{| c | ' # First column is basically the key.
  for cH in colHeaders:
    header = header + ' c '
  header = header + ' || c |}\n' # last column is for total.
  header = header + '\hline\n\t' # Header of first column is empty
  for cH in colHeaders :
    header = header + ' &\t ' + str(cH) + '\t'
  header = header + ' &\t total \t'
  header = header + '\\\\\n'
  header = header + '\hline \n'
  body = ''
  keyLst.sort()
  for key in keyLst:
    body = body+str(key)+'\t'
    total = 0
    for col in columns:
      if not key in col.keys():
        body = body + ' &\t 0 \t'
      else :
        body = body + ' &\t '+ str(col[key])+'\t'
        total = total + col[key]
    body = body + ' &\t '+ str(total)+'\t\\\\\n'
  footer = '\hline'
  footer = footer + '\end{tabular}\n\n'
  tableStr = header + body + footer
  return tableStr

def getTableFor(i, interval, cutOff, nRuns, fName):
  s0 = getState(i)
  d0 = s0.deal
  rL = getRun1List2(d0, 2, cutOff)
  rL = rL[:nRuns]
  cols = getRunsColumns(s0, rL, interval, 'e')
  colHeaders = []
  for i in range(len(cols)):
    colHeaders.append(i)
  tabTex = getLatexPosK(cols, colHeaders)
  f =  open(fName, 'w')
  f.write(tabTex)
  f.close()
  return tabTex
