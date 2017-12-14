import cpState as cps
import cpUtil as ut; 
import pickle as pk;
import time
import random as rand

deal = {'a' : [0, 1, 2, 3], 'b':[4, 5, 6, 7], 'c':[8,9] };
infAgts, eaves = ['a', 'b'],'c';
a,b,c = 'a', 'b', 'c'
s0 = cps.cpState([4, 4, 2], ['a','b', 'c'], deal, infAgts, eaves);
f = open('rcp442-Deals.txt', 'r')
dList = pk.load(f)
f.close()

f = open('rcp442-Rest1.txt', 'r')
dList1 = pk.load(f)
f.close()

ann1 = ('a', [[0,1,2,3], [0,1,4,5], [0,2,6,7], [0,3,8,9], [0,4,6,8],\
              [0,5,7,9], [1,2,8,9], [1,3,6,7], [1,4,7,9], [1,5,6,8],\
              [2,3,4,5], [2,4,7,8], [2,5,6,9], [3,4,6,9], [3,5,7,8]])
#dL1 = ut.sortDeals(s0.run2Deals([ann1]))
s1 = s0.updateAnn(ann1)

ann2 = ('c', [[0,3], [8,9], [1,2]])
s2 = s1.updateAnn(ann2)

ann3 = ('c', [[8,9]])
s3 = s2.updateAnn(ann3)

run2k11 = [ann1, ann2, ann3]
startIdx = 0

def genPermHand(hLen):
  perm = []
  rangeL = range(hLen)
  maxId = hLen - 1
  i = 0
  while maxId >= 0 : 
    idx = rand.randint(0, maxId)
    k   = rangeL[idx]
    perm.append(k)
    rangeL.pop(idx)
    maxId = maxId - 1
    i = i + 1
  return perm

def genPermAnn(aHand, ann):
  '''
  Get a permutation $f$ of ann such that aHand $\in$ $f(ann)$
  Returns $f(ann), f$ (The function is returned as a list of 
  length 10.
  '''
  # First make sure that aHand in $f(ann)
  aLen = len(ann[1]) 
  idx = rand.randint(0, aLen-1)
  handAnn = ann[1][idx]
  domL = range(0, 10) # Currnetly hardwired as 10
  rangeL = range(0,10) # The range of the permutation
  resPerm = range(0, 10) # The resulting permutation
  handLen = len(handAnn) # Assume that len(aHand) == len(handAnn)
  chosenIdx = idx
  if handLen != len(aHand):
    raise RuntimeError('Unequal lengths for hand')
  hPerm = genPermHand(len(handAnn))
  for i in range(handLen):
    fromCard = handAnn[i]
    idx      = hPerm[i]
    toCard   = aHand[idx]
    resPerm[fromCard] = toCard
    domL.remove(fromCard) # The resulting permutation has an assignment for c.
    rangeL.remove(toCard) # perm[c] has been added to the range of resulting permutation.
  maxId = len(domL) - 1
  while maxId >= 0: # Now to (arbitrarily) complete the permutation, resPerm
    c   = domL[0] # The value to be set next
    idx =  rand.randint(0, maxId) # Randomly choose an index to an element not yet set.
    resPerm[c] = rangeL[idx]
    domL = domL[1:]
    rangeL.pop(idx)
    maxId = maxId - 1 # Can use len(rangeL) as len(domL) = len(rangeL)
  resAnn1 = [] # Compute the new announcement.
  for disj in ann[1]:
    newDisj = []
    for c in disj:
      newDisj.append(resPerm[c])
    newDisj.sort()
    resAnn1.append(newDisj)
  resAnn = (ann[0], resAnn1)
  return (resAnn, resPerm, chosenIdx)

def minDeal(aH):
  remCards = []
  cL = range(10)
  for c in cL:
    if not c in aH:
      remCards.append(c)
  bH = remCards[:4]
  cH = remCards[4:]
  deal = {'a':aH, 'b':bH, 'c':cH}
  return deal

def CView(deal, ann):
  r0 = s0.newState()
  r0.deal = deal
  r1 = r0.updateAnn(ann)
  cview = r1.getAgtDeals('c')
  return cview

def isDistinct(d1, d2):
  aH1,aH2 = d1['a'], d2['a']
  bH1,bH2 = d1['b'], d2['b']
  aH1.sort(), aH2.sort()
  bH1.sort(), bH2.sort()
  if aH1 != aH2:
    return True
  elif bH1!= bH2:
    return True
  return False

def BCView(deal, ann):
  '''The BC connected part of model after 
  ann is announced starting from deal.'''
  cview = CView(deal, ann) # First get C's set.
  resView = []
  for d in cview:
    r0 = s0.newState()
    r0.deal = d
    r1 = r0.updateAnn(ann)
    bL = r1.getAgtDeals('b')
    i, found = 0, False
    for d1 in bL:
      while i < len(resView) and not found:
        currD = resView[i]
        if not isDistinct(currD, d1):
          found = True
        i = i + 1
      if not found:
        resView.append(d1)
  resView = ut.sortDeals(resView)
  return resView

def SecondAnn(deal, firstAnn):
  'returns the second announcement given firstAnn, deal.'
  cList  = []  
  bcView = BCView(deal, firstAnn)
  for d in bcView:
    cH = d['c']
    cH.sort()
    if not cH in cList:
      cList.append(cH)
  cList.sort()
  secAnn = ('c', cList)
  return secAnn

def tabs2k11(nRuns, nCols):
  '''
  nTabs denotes the number of tables to convert into.
  '''
  rL,hL,remL = runs2k11(nRuns)
  resTabs = ""
  nTabs = nRuns/nCols
  for i in range(nTabs):
    startIdx = i
    currentRunL = rL[:nCols]
    rL = rL[nCols:]
    lkdLst = compLstLeakage(currentRunL, 'c')
    currTab = getLatex(lkdLst, currentRunL, 'c')
    resTabs = resTabs + currTab + "\n\n\n"
  resTabs = resTabs +"%Sequence of hands for A \n"
  for i in range(nRuns):
    resTabs = resTabs+"% "+ str(hL[i]) + ") \n\n"
  remInfoA = "% Number of possible hands for A "
  remInfoB = "that have not occured in any of the previous runs\n"
  remInfo  = remInfoA + remInfoB
  resTabs = resTabs +  remInfo
  resTabs = resTabs + "% " +str(remL)+"\n\n"
  return resTabs

def genSaveTabs2k11(nRuns, nCols, fName):
  res = tabs2k11(nRuns, nCols)  
  timeStamp = time.strftime('%Y%m%d-%H%M%S')
  header = "%"+timeStamp+"\n"
  header = header + "\\documentclass{article} \n"
  header = header +"\\begin{document}\n"
  footer = "\end{document}\n"  + "%" + timeStamp +"\n"
  res =  header + res + footer
  f = open(fName, 'w')
  f.write(res)
  f.close()

def saveTabs2k11(resRuns2k11, nCols, fName):
  rL,hL,remL = resRuns2k11
  resTabs = ""
  nTabs = len(rL) / nCols
  for i in range(nTabs):
    currentRunL = rL[:nCols]
    rL = rL[nCols:]
    lkdLst = compLstLeakage(currentRunL, 'c')
    currTab = getLatex(lkdLst, currentRunL, 'c')
    resTabs = resTabs + currTab + "\n\n\n"
  resTabs = resTabs +"%Sequence of hands for A \n"
  for i in range(nTabs):
    resTabs = resTabs+"% "+ str(hL[i]) + "("+str(remL[i])+") \n\n"
  remInfoA = "% Number of possible hands for A "
  remInfoB = "that have not occured in any of the previous runs\n"
  remInfo  = remInfoA + remInfoB
  resTabs = resTabs +  remInfo
  resTabs = resTabs + "% " +str(remL) + "\n\n"
  timeStamp = time.strftime('%Y%m%d-%H%M%S')    
  header = "%"+timeStamp+"\n"
  header = header + "\\documentclass{article} \n"
  header = header + "\\begin{document}\n"
  footer = "\n\end{document}\n"
  footer = footer + "%" + str(timeStamp)
  res = header + resTabs + footer
  f = open(fName, 'w')
  f.write(res)
  f.close()

def runs2k11(nRuns):
  '''
  Generate as many distinct runs possible (within nRuns).
  The distinctness is obtained by modifying A's hands such that
  it has not occurred in the first announcement.
  '''
  uL = ut.allHands(4, range(10)) # Returns set of all hands in sorted order
  remSeq = [len(uL)] # Sequence of remainder hands (after each run)
  runSeq = []
  handL  = []
  firstAnn = ann1
  currDeal = deal
  i = 0
  while len(uL) > 0 and i < nRuns:
    secondAnn = SecondAnn(currDeal, firstAnn)
    thirdAnn = ('c', [currDeal['c']])
    ann1L = firstAnn[1]
    for hand in ann1L:
      if hand in uL:
        uL.remove(hand)
    currRun  = [firstAnn, secondAnn, thirdAnn]
    runSeq.append(currRun)
    remSeq.append(len(uL))
    handL.append(currDeal[a])
    maxId = len(uL) - 1
    idx = rand.randint(0, maxId)
    nextHand = uL[idx]
    currDeal = minDeal(nextHand)
    firstAnn = genPermAnn(nextHand, ann1)[0]
    i = i + 1
  return (runSeq, handL, remSeq)

def obtainClasses(dL, runL, agt):
  agtCl = []
  r0 = s0.newState()  
  for d in dL:
    r0.deal = d
    r1 = r0.execRun(runL)
    bDeals = ut.sortDeals(r1.getAgtDeals(agt))
    agtCl.append(bDeals)
  return agtCl

def computeLeakage(run, agt):
  result = {}
  tmLst = []
  leakedLst  = []
  r0 = s0.newState()
  # Evaluate only for those deals that 
  # can truthfully announce run
  deals = s0.run2Deals(run) 
  deals = ut.sortDeals(deals)
  pDeals = {}
  for d in deals:
    r0.deal = d
    s = time.time() 
    rF = r0.execRun(run)
    cL = rF.getCards(agt)
    e = time.time()
    tmLst.append(e-s)
    leakedLst.append(cL)
  # For computing possible deals according to agt
  #    The component according to agt.
  r0 = s0.newState()
  r0.deal = deals[0] 
  # Sufficient to compute for first deal
  #   as all deals will a) have the same hand for agt
  #                     b) for each of those deals, agt considers the same set to be possible.
  rFinal = r0.execRun(run)
  dKey = ut.deal2Key(d)
  pDList = rFinal.getAgtDeals(agt)
  pDeals = []
  for pd in pDList:
    pdKey = ut.deal2Key(pd)
    pDeals.append(pdKey)
  dealsUniverse = [dList]
  runPre = []
  for ann in run:
    runPre.append(ann)
    dealsUniverse.append(s0.run2Deals(runPre))
  result['dList'] = deals
  result['timings'] = tmLst
  result['leakage'] = leakedLst
  nLeaked = []
  for l in leakedLst:
    nLeaked.append(len(l))
  result['nLeaked']   = nLeaked
  result['publicLst'] = dealsUniverse # How the set of deals changes publicly.
  # Possible Deals that agt thinks to be possible.
  result['possibleDeals'] = pDeals
  return result

def tabulateCardLeakage(leakageDict, nInit):
  res = leakageDict
  result = {}
  rangeL = range(0,11)
  for nC in rangeL:
    result[nC] = 0
  for nK in res['nLeaked']:
    nLearnt = nK - nInit
    key = nLearnt
    result[key] = result[key] + 1
  kL = range(0,11)
  result['total'] = 0
  for k in kL:
    result['total'] = result['total'] + result[k]
  return result

def tabulatePossDeals(leakageDict):
  res = leakageDict
  pDeals = res['possibleDeals']
  return pDeals

def compLstLeakage(rL, agt):
  leakage = []
  for r in rL:
    l = computeLeakage(r, agt)
    leakage.append(l)
  return leakage

def cardsLeakedTabs(lkdLst, runList, agt):
  '''
  Given an array of runs, return a table 
  representing the cards Leaked to eaves 
  for each run
  '''
  leakTab = []
  for leakageRes in lkdLst:
    leakTab.append(tabulateCardLeakage(leakageRes, 2))
  resTab = "\\begin{tabular}{ | c |"
  for i in range(len(runList)):
    resTab = resTab + "| c "
  resTab = resTab + " | } \n \\hline \n"
  resTab = resTab + "$nCards$ "
  sI = startIdx
  for i in range(len(runList)):
    resTab = resTab + " & $r_{" + str(i + sI) + "}$"
  resTab = resTab + " \\\\ \n \\hline \n"
  kList = range(0,11)
  kList.sort()
  for k in kList:
    toPrint = False
    for i in range(len(runList)):
      if leakTab[i][k] != 0:
        toPrint = True
    if toPrint:
      resTab = resTab + str(k)
      for i in range(len(runList)):
        resTab = resTab + " & "+ str(leakTab[i][k]) 
      resTab = resTab + " \\\\ \n"
#  resTab = resTab + "\\hline \n"
# resTab = resTab + "total "
#  for i in range(len(runList)):
#    resTab = resTab + " & "+ str(leakTab[i]['total'])
#  resTab = resTab + "\\\\\n "
  resTab = resTab + "\\hline\n"
  resTab = resTab + "\\end{tabular}\n"
  return resTab

def dealsPossibleTabs(lkdLst, runList, agt):
  '''
  Given an array of runs, return a table 
  representing the number of deals agt considers
  possible after each run
  '''
  sI = startIdx
  possTab = []
  for leakageRes in lkdLst:
    possTab.append(tabulatePossDeals(leakageRes))
  resTab = "\\begin{tabular}{ | c |"
  for i in range(len(runList)):
    resTab = resTab + "| c "
  resTab = resTab + " | } \n\hline"
  resTab = resTab + "$\;$  " # Empty here
  for i in range(len(runList)):
    if i >= 0 :
      resTab = resTab + " & $r_{" + str(i+sI) + "}$"
  resTab = resTab + " \\\\ \n\hline \n"
# Following outdated, applies to global possibilities
#  rLen = []
#  for r in runList:
#    rLen.append(len(r))
#  maxLen = max(rLen)+1
  resTab = resTab + "$pDeals$ & "
  for i in range(len(runList)): # For each column,
    currRun = runList[i]
    if i > 0 :
      resTab = resTab + " & "
    resTab = resTab + str(len(possTab[i])) + " "
  resTab = resTab + " \\\\ \n"
  resTab = resTab + "\\hline \n"
  resTab = resTab + "\\end{tabular}\n"
  return resTab

def genRun2k11():
  return [s0.genAnnFullHand('a', 15), s0.genAnnFullHand('c', 3), s0.genAnnFullHand('c', 1)]

def genRL2k11(n):
  rL = []
  for i in range(n):
    rL.append(genRun2k11())
  return rL

def getLatex(lkdLst, runList, agt):
  sI = startIdx
  tC = cardsLeakedTabs(lkdLst, runList, agt)
  pD = dealsPossibleTabs(lkdLst, runList, agt)
  res = ""
  res = res + "\\begin{table}[ht] \n" 
  res = res + tC
  res = res + "\\caption{Cards Leaked}\n"
  res = res + "\\label{cLeaked-"+str(sI)+"}\n"
  res = res + "\\end{table}\n\n" # Cards Leaked table completed
  res = res + "\\begin{table}[ht] \n" 
  res = res + pD
  res = res + "\\caption{Possible Deals}\n"
  res = res + "\\label{pDeals-"+str(sI)+"}\n"
  res = res + "\\end{table}\n\n"
  timeStamp = time.strftime('%Y%m%d-%H%M%S')
  res = res + "%" +timeStamp + "\n"
  for r in runList:
    strRun = "% [('a', ["
    r0a0 = str(r[0][1][:6])[1:-1] + ',\n'
    r0a1 = '%' + space(9) + str(r[0][1][6:12])[1:-1]+ ',\n'
    r0a2 = '%' + space(9) + str(r[0][1][12:])[1:]   + '\n'
    strRun = strRun + r0a0 + r0a1 + r0a2
    rest = '%'+ space(2) + str(r[1:])[1:-1] + ",\n"
    strRun = strRun + rest
    res = res + strRun + '% ]\n\n'
  res = res+"\n"
  return res

def  space(n):
  res = ''
  for i in range(0,n):
    res = res+ ' '
  return res

def saveResults(lkLst, runList, agt, fileName):
  ltx = getLatex(lkLst, runList, agt)
  f = open(fileName, 'w')
  f.write(ltx)
  f.close()

def compSave(n, agt, fileName):
  rL = genRL2k11(n)
  lkL = compLstLeakage(rL, agt)
  saveResults(lkL, rL, agt, fileName)

def genTables(k, n, agt):
  '''
  Generate k tables with n runs each and save in k files.
  '''
  for i in range(0,k):
    timeStamp = time.strftime('%Y%m%d-%H%M%S')
    fName = 'table'+timeStamp+'.tex'
    compSave(n, agt, fName)
