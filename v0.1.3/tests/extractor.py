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
def genAAnn(lObj, synth, aWidth, sInfTriple, cuttoffTriple, fPrefix):
  fa,fb,fc = sInfTriple
  aCutoff, bCutOff, cCutOff = cutoffTriple
  nAnnA = 0
  resAnn = []
  remDLSI = range(0, len(lObj.deals))
  while nAnnA < aCutoff:
    resB = genBAnn(lObj, synth, aWidth, fa, fb, fc, bCutoff, cCutoff, fPrefix)
    ann1I = resB[0]
    resAnn.append(resB)
    nAnnA = nAnnA + 1
  return resAnn

def genBAnn(lObj, synth, aWidth, fa, fb, fc, bCutOff, cCutOff, fPrefix):
  '''
  synth is the solver with all required constraints 
           (to block unwanted results).
  '''
  nD = len(lObj.deals)
  cP = lObj.ann[c]
  # Since, we're currently looking at one shot protocols.
  cPass = And(cP[0])
  synth.push() # Breakpoint for the first announcement
  aWFml  = lObj.restrictWidth('a', aWidth)
  debug = fPrefix.startswith('debug')
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
  # res has to be sat here
  if res != z3.sat:
    return []
  m = synth.model()
  remDLSI = lObj.getIndices(lObj.getTruePropsPrefixedBy(m, 'd'))
  print 'Originally : ', str(remDLSI)
  resAnn = []
  resAnn.append(ann1I)
  nAnnB = 0
  outMessage = ''
  annMessage = ''
  while nAnnB < bCutOff and remDLSI != []:
    outFName = fPrefix + '-' + str(nAnnB) + '.py'
    f= open(outFName, 'a')
    outMessage = outMessage + '# ann1 Indices : \n' + str(ann1I) + '\n'
    outMessage = outMessage + '# ann2 Indices : \n' + str(ann2I) + '\n\n'
    f.write(outMessage)
    synth.push()
    f2 = lObj.getAnnFml('b', 0, ann2I)
    synth.add(f2)
    dlsBI = []
    resb = synth.check()
    if resb == z3.sat:
      print 'sat'
      m = synth.model()
      dlsBI = lObj.getIndices(lObj.getTruePropsPrefixedBy(m, 'd'))
    print dlsBI
    ann3IL, cOut = informABwSynth(lObj, synth, f, cCutOff)
    outMessage = outMessage + cOut
    resAnn.append((ann2I, ann3IL))
    fName = fPrefix + '-ann-' + str(nAnnB) + '.py'
    aMsg = writeAnnL(lObj, ann1I, ann2I, ann3IL, fName)
    annMessage = annMessage + '\n'+hashes+'\n'+ aMsg
    synth.pop()
    newDLSI = []
    for idx in remDLSI:
      if idx not in dlsBI:
        newDLSI.append(idx)        
    remDLSI = newDLSI
    print 'Remaining : ', str(remDLSI)
    synth.add( Or(lObj.dealsBL(remDLSI)) ) # Ensure B makes progress.
    # The following checks how else B could respond.
    synth.push()
    synth.add(fc)
    ann1I, ann2I, deals = run2KC(lObj, synth)
    synth.pop() # remove fc
    nAnnB = nAnnB + 1
  return resAnn, outMessage, annMessage

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
  f.close()
  return ann3L, outMessage

def writeAnnL(lObj, ann1I, ann2I, ann3L, fName):
  '''
  Write out the actual announcements in full form.
  '''
  f = open(fName, 'a')
  annA = lObj.iL2AnnL(ann1I)
  annB = lObj.iL2AnnL(ann2I)
  aMsg = ''
  aMsg = aMsg + '(a, ' + getAnnStr(annA)+'\n\n'
  aMsg = aMsg + '(b, ' + getAnnStr(annB)+'\n\n'
  nC = 0
  for annCI in ann3L:
    annCL = lObj.iL2AnnL(annCI)
    aMsg = aMst +'(c, '+getAnnStr(annCL) + ''
    nC = nC + 1
  f.write(aMsg)
  f.close()
  return aMsg

def getAnnStr(annL):
  resStr = '['
  i = 0
  while i < len(annL):
    disj = annL[i]
    resStr = resStr+'     '+str(disj)
    if i != len(annL) - 1:
      resStr = resStr + ',\n'
    i = i + 1
  resStr = resStr+'])\n\n'
  return resStr
