from lk import *
import pickle as pk

def getLkObj(i):
  lObj = Leakage(i)
  lObj.initHands()
  lObj.initDeals()
  lObj.initAnn(1)
  return lObj

def getAgtFml(lObj, agt):
  '''
  Obtain (or read) optimized formula from optimized/i-sInfP.txt
  Assumes that the files have already been generated for
  lObj (via lObj.genSaveSInfFml(agt))  (see genAll_i.py)
  '''
  i = lObj.hSize
  aName = agt.upper()
  fName = 'optimized/' + str(i) + '-sInf' + aName + '.txt'
  fml   = lObj.rSInf4Agt(fName)
  return fml

def getSafety_Solver(lObj):
  '''
  lObj   - the leakage object initialized appropriately.
  '''
  solver, fLst = lObj.safetySynthSolver(True)
  return solver,fLst

def getStrongSafety_Solver(lObj):
  solver, fLst = getSafety_Solver(lObj)
  strongFml = lObj.eavesKNIgnorant()
  solver.add(strongFml)
  fLst.append(strongFml)
  return solver,fLst

def getfmlABC(lObj):
  fa = getAgtFml(lObj, 'a')
  fb = getAgtFml(lObj, 'b')
  fc = getAgtFml(lObj, 'c')
  return (fa,fb, fc)

def initSolver4KC(lObj, solver, aWidth):
  '''
  Add constraints to the solver for ensuring that
  C knows the deal at the end.
  '''
  nD = len(lObj.deals)
  aP = lObj.ann[a]
  bP = lObj.ann[b]
  cP = lObj.ann[c]
  # Since, we're currently looking at one shot protocols.
  aPass = And(aP[0])
  bPass = And(bP[0])
  cPass = And(cP[0])
  # Obtain
  sInfC = getAgtFml(lObj, 'c')
  solver.push()
  solver.add(sInfC)
  aWFml  = lObj.restrictWidth('a', aWidth)
  solver.add(aWFml)
  solver.add(lObj.possibleDeals[0])
  # not restricting b's width (consider the example)
  solver.add(cPass) # indicating that c passes
  return solver

def run2KC(lObj, solver):
  '''
  Obtaining a run to reveal the deal to C.
  solver must be initialized appropriately.
  '''
  res = solver.check()
  deals = []
  ann1I, ann2I = [], []
  dListI = []
  if res == z3.sat:
    m = solver.model()
    ann1P = lObj.getTruePropsPrefixedBy(m, 'a')
    ann2P = lObj.getTruePropsPrefixedBy(m, 'b')
    ann1I = lObj.getIndices(ann1P)
    ann2I = lObj.getIndices(ann2P)
    ann1I.sort(), ann2I.sort()
    f1 = lObj.getAnnFml(a, 0, ann1I)
    f2 = lObj.getAnnFml(b, 0, ann2I)
    ann1L = lObj.iL2AnnL(ann1I)
    ann2L = lObj.iL2AnnL(ann2I)
    cPass = And(lObj.ann['c'][0])
    dListP = lObj.extractDealsProps(And(f1, f2, cPass))
    dListI = lObj.getIndices(dListP)
    for i in dListI:
      deals.append(lObj.deals[i])
  return (ann1I, ann2I, dListI)

hashes = '################################################################'
lineHashes = hashes+'\n\n'
doubleHashes = lineHashes + lineHashes
tripleHashes = lineHashes + doubleHashes
quadHashes =  doubleHashes + doubleHashes

def getRunL(annMsg):
  aL1 = annMsg.split(quadHashes)[1:]
  aL2 = []
  for ln in aL1:
    lnLst = ln.split(lineHashes)
    for l in lnLst:
      aL2.append(l)
  runL = []
  for ln in aL2:
    rn = []
    lnLst = ln.split('(')[1:]
    for ann in lnLst:
      rn.append(eval('('+ann))
    runL.append(rn)
  return runL

def writeRunL(fName, runL):
  f = open(fName, 'w')
  for r in runL:
    f.write('[\n')
    for ann in r:
      f.write('  '+str(ann))
      if ann != r[-1]:
        f.write(',\n')
    f.write('\n]\n\n')
  f.close()

def readRunL(fTxt):
  runL = []
  runStrL = fTxt.split('\n\n')[:-1]
  for runStr in runStrL:
    runL.append(eval(runStr))
  return runL

import cpState as cps; import cpUtil  as ut ;
def getStateLst(runL):
  dealLst = [4,4,4,0]; agtLst = ['a','b', 'c', 'e']; 
  d0 = ut.minDeal(dealLst, agtLst, range(12)); 
  s0 = cps.cpState(dealLst, agtLst, d0, ['a', 'b', 'c'], 'e');
  stateL = []
  for r in runL:
    s1 = s0.execRun(r)
    stateL.append(s1)
  return stateL

def getInfo(stateL):
  infL = []
  for s in stateL:
    infL.append(s.getInfo())
  return infL

def getPosL(stateL, eaves):
  posL = []
  for s in stateL:
    posL.append(s.getPosK(eaves))
  return posL

def getNegL(stateL, eaves):
  negL = []
  for s in stateL:
    negL.append(s.getNegK(eaves))
  return negL

def genAAnn(lObj, synth, aWidth, sInfTriple, cutOffTriple, fPrefix):
  fa,fb,fc = sInfTriple
  aCutoff, bCutOff, cCutOff = cutOffTriple
  fwdCutOff = (bCutOff, cCutOff)
  nAnnA = 0
  resAnn = []
  remDLSI = range(0, len(lObj.deals))
  sInfFml = fa, fb, fc
  outMessage = ''
  annMessage = ''
  while nAnnA < aCutoff:
    synth.push()
    resB, outMsg, annMsg = genBAnn(lObj, synth, aWidth, sInfFml, fwdCutOff, fPrefix)
    synth.pop()
    if resB == []:
      return resAnn, outMessage, annMessage
    ann1I = resB[0]
    f1 = lObj.getAnnFml('a', 0, ann1I)
    # Fix first announcement by A for the rest of the search.
    synth.add( Not(f1) )
    resAnn.append(resB)
    outMessage = outMessage + '\n' + hashes + '\n' 
    outMessage = outMessage + '\n' + hashes + '\n' 
    outMessage = outMessage + '\n' + hashes + '\n\n'    
    outMessage = outMessage + outMsg
    annMessage = annMessage + '\n' + hashes + '\n'
    annMessage = annMessage + '\n' + hashes + '\n'
    annMessage = annMessage + '\n' + hashes + '\n'
    annMessage = annMessage + annMsg
    nAnnA = nAnnA + 1
    fName1 = fPrefix + '-a-'+str(nAnnA)+'.txt'
    fName2 = fPrefix + '-a-ann'+str(nAnnA)+'.txt'    
    f1 = open(fName1, 'w')
    f1.write(outMessage)
    f2 = open(fName2, 'w')    
    f2.write(annMessage)
    f1.close(); f2.close()
  fName = fPrefix + '-all.txt'
  f = open(fName, 'w')
  f.write(outMessage)
  f.close()
  fName = fPrefix+'-ann.txt'
  f = open(fName, 'w')
  f.write(annMessage)
  f.close()
  return resAnn, outMessage, annMessage

def genBAnn(lObj, synth, aWidth, sInfFml, cutOffL, fPrefix):
  '''
  synth is the solver with all required constraints 
           (to block unwanted results).
  '''
  fa, fb, fc = sInfFml
  bCutOff, cCutOff = cutOffL
  nD = len(lObj.deals)
  cP = lObj.ann[c]
  # Since, we're currently looking at one shot protocols.
  cPass = And(cP[0])
  synth.push() # Breakpoint for the first announcement
  aWFml = lObj.restrictWidth('a', aWidth)
  debug = fPrefix.startswith('debug')
  if debug:
    print 'debug : ', debug
  synth.add(aWFml)
  synth.add(lObj.possibleDeals[0])
  synth.add(fc)
  synth.add(cPass)
  if debug:
    print 'Initialized synth appropriately'
  ann1I, ann2I, dListI = run2KC(lObj, synth)
  if debug:
    print 'Initial ann1I, ann2I generated.'
  synth.pop() # Unroll the constraints for first two announcements.
  f1 = lObj.getAnnFml('a', 0, ann1I)
  # Fix first announcement by A for the rest of the search.
  synth.add(f1)
  # Compute remDLSI by setting f1.
  res = synth.check()
  if debug:
    print 'res (initial models for B): ', res
  # res has to be sat here
  if res != z3.sat:
    return [], '', ''
  m = synth.model()
  remDLSI = lObj.getIndices(lObj.getTruePropsPrefixedBy(m, 'd'))
  if debug:
    print 'Obtained deals'
    print 'Originally : ', str(remDLSI)
  resAnn = []
  resAnn.append(ann1I)
  nAnnB = 0
  outMessage = ''
  annMessage = ''
  fName = fPrefix + 'b-latest.py'
  # Save the latest intermediate version of runs generated
  #  Starts here.
  f = open(fName, 'w')
  while nAnnB < bCutOff and remDLSI != []:
    outFName = fPrefix + '-' + str(nAnnB) + '.py'
    outMessage = outMessage + '# ann1 Indices : \n' + str(ann1I) + '\n'
    outMessage = outMessage + '# ann2 Indices : \n' + str(ann2I) + '\n\n'
    synth.push()
    f2 = lObj.getAnnFml('b', 0, ann2I)
    synth.add(f2)
    dlsBI = []
    resb = synth.check()
    if resb == z3.sat:
      if debug:
        print 'Models are obtainable'
      m = synth.model()
      dlsBI = lObj.getIndices(lObj.getTruePropsPrefixedBy(m, 'd'))
    else :
      print 'unsat (models not attainable)'
    if debug:
      print dlsBI
    f.write(hashes+'\n'+hashes+'\n'+str(nAnnB)+'\n')
    ann3IL, cOut = informABwSynth(lObj, synth, f, cCutOff)
    if debug:
      print 'Obtained run'
      print 'len(ann3IL) : ', len(ann3IL)
    outMessage = outMessage + cOut
    resAnn.append((ann2I, ann3IL))
    aMsg = writeAnnL(lObj, ann1I, ann2I, ann3IL, fName)
    annMessage = annMessage + '\n'+hashes+'\n\n'+ aMsg
    synth.pop()
    newDLSI = []
    for idx in remDLSI:
      if idx not in dlsBI:
        newDLSI.append(idx)
    remDLSI = newDLSI
    if debug:
      print 'Remaining : ', str(remDLSI)
    synth.add( Or(lObj.dealsBL(remDLSI)) ) # Ensure B makes progress.
    # The following checks how else B could respond.
    synth.push()
    synth.add(fc)
    ann1I, ann2I, deals = run2KC(lObj, synth)
    if debug:
      print 'ann2I ( for nAnnB : ' +str(nAnnB)+') : ', ann2I
    synth.pop() # remove fc
    nAnnB = nAnnB + 1
    if debug:
      print
  f.close()
  return resAnn, outMessage, annMessage

def getRuns(lObj, msg):
  '''
  multiple occurrences are possible at the end
  denoting different possible announcements made
  by the agent at the last.
  '''
  msgList = msg.split('\n\n')
  agts    = lObj.agents
  annList = [] # filter out the valid announcements
  for m in msgList:
    if m.startswith('('):
      annList.append(eval(m))
  if annList == []:
    return []
  suffixAnnL  = [annList[-1]]
  j = 1
  lAgent = agts[-1]
  while j <= len(annList) and annList[j][0] == lAgent:
    suffixAnnL.append(annList[j])
    j = j + 1
  i = 0
  initialRun  = []
  while i < (len(annList)-j):
    initialRun.append(annList[i])
    i = i + 1
  runList = [] # set of runs
  for suff in suffixAnnL:
    runList.append(initialRun + [suff])
  return runList

def getDeals(lObj, solver, runList, debug):
  '''
  assumes that solver is the solver as a result of
  getSafety_Solver or getStrongSafetySOlver or the like.
  Assume the required formulae are already added to solver.
  '''
  i = 0
  nRound = 0
  agts = lObj.agents
  solver.push()
  annFList = []
  if debug:
    print 'Entering while loop'
  while i < len(runList):
    for agt in agts:
      ann = runList[i]
      if not ann[0] == (agt):
        print 'Incorrect format for runList'
        return []
      annI = []
      annL = ann[1]
      for disj in annL:
        annI.append(lObj.handList.index(disj))
      if debug:
        print 'ann : ', ann
        print 'agt : ', agt
        print 'annI obtained (len : ', len(annI), ')'
        print 'annI : ', annI
      # Completely specify the corresponding formula for the announcement.
      annFml = lObj.getAnnFml(agt, nRound, annI)
      annFList.append(annFml)
      solver.add(annFml)
      i = i + 1
    nRound = nRound + 1
  res = solver.check()
  deals = []
  if res == z3.sat:
    # This is the main reason for the above code
    m = solver.model()
    dlsBI = lObj.getIndices(lObj.getTruePropsPrefixedBy(m, 'd'))
    if debug:
      print 'dls indices : ', dlsBI
    for idx in dlsBI:
      deals.append(lObj.deals[idx])
  solver.pop()
  return  (deals, annFList)

################################################################
####    Onto the part where C informs A,B.
################################################################

def informABwSynth(lObj, synth, f, cCutOff) :
  '''
  fLst consists of all the formulae obtained from either
  a) getSafety_Solver + getFmlAB()
  b) getStrongSafety_Solver + getFmlAB()
  c) other formulae, blocking certain announcements.
  '''
  m = synth.model() # synth must be sat here
  remDLSI = lObj.getIndices(lObj.getTruePropsPrefixedBy(m, 'd'))
  # Documenting the solution
  outMessage = '# deals (after ann1;ann2) : \n'
  outMessage = outMessage + '['
  for idx in remDLSI :
    currDeal = lObj.deals[idx]
    outMessage = outMessage + '  ' + str(currDeal) + ',\n'
  outMessage = outMessage + ']\n\n'
  outMessage = outMessage + '# Now for C\'s announcement(s), \n'
  nAnnC = 0
  ann3L = []
  res = synth.check()
  while remDLSI != [] and res == z3.sat and nAnnC < cCutOff:
    m = synth.model()
    dlsCP  = lObj.getTruePropsPrefixedBy(m, 'd')
    dlsCI = lObj.getIndices(dlsCP)
    dlsC = []
    for i in dlsCI:    
      dlsC.append( lObj.deals[i] )
    annCP = lObj.getTruePropsPrefixedBy(m, 'c')
    annCI = lObj.getIndices(annCP)
    annCI.sort()
    ann3L.append(annCI)
    outMessage = outMessage + '# ' + str(nAnnC) + ') : \n' + str(annCI)+'\n'
    outMessage = outMessage + '\n  Deals : \n'
    for idx in dlsCI :
      currDeal = lObj.deals[idx]
      outMessage = outMessage + (str(currDeal) + ',\n')
    outMessage = outMessage + ']\n\n'
    newDLSI = []
    for idx in remDLSI:
      if idx not in dlsCI:
        newDLSI.append(idx)        
    remDLSI = newDLSI
    fml = Or(lObj.dealsBL(remDLSI))
    synth.add(fml)
    res = synth.check()
    nAnnC = nAnnC + 1
  f.write(outMessage)
  return ann3L, outMessage

def writeAnnL(lObj, ann1I, ann2I, ann3L, fName):
  '''
  Write out the actual announcements in full form.
  '''
  f = open(fName, 'a')
  f.write('\n'+hashes+'\n')
  annA = lObj.iL2AnnL(ann1I)
  annB = lObj.iL2AnnL(ann2I)
  aMsg = ''
  aMsg = aMsg + '(a, ' + getAnnStr(annA)+'\n\n'
  aMsg = aMsg + '(b, ' + getAnnStr(annB)+'\n\n'
  nC = 0
  for annCI in ann3L:
    annCL = lObj.iL2AnnL(annCI)
    aMsg  = aMsg +'(c, '+getAnnStr(annCL) + '\n\n'
    nC = nC + 1
  f.write(aMsg)
  f.close()
  return aMsg

def getAnnStr(annL):
  resStr = '['+ str(annL[0]) # Assume annL != []
  if len(annL) > 1:
    resStr = resStr + ','
  resStr = resStr + '\n'
  i = 1
  while i < len(annL):
    disj = annL[i]
    resStr = resStr+'     '+str(disj)
    if i != len(annL) - 1:
      resStr = resStr + ',\n'
    i = i + 1
  resStr = resStr+'])'
  return resStr
