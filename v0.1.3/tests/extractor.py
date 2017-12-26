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
  return (ann1I, ann2I, deals)

def getfmlABC():
  fa = getAgtFml(lObj, 'a')
  fb = getAgtFml(lObj, 'b')
  fc = getAgtFml(lObj, 'c')
  return (fa,fb, fc)

################################################################
####    Onto the part where C informs A,B.
################################################################
def informAB(lObj, fLst, ann1I, ann2I, outFName) :
  '''
  fLst consists of all the formulae obtained from either
  a) getSafety_Solver + getFmlAB()
  b) getStrongSafety_Solver + getFmlAB()
  '''
  # for obtaining C's announcements that indicate how he can inform others
  synth = z3.Solver()
  synth = addToSolver(synth, fLst, True)
  ann1F = lObj.getAnnFml(a, 0, ann1I)
  ann2F = lObj.getAnnFml(b, 0, ann2I)
  synth.add(ann1F, ann2F)
  nAnnC = 0
  res = synth.check()
  # The assumption is that res is sat when we reach here.
  #          (can be checked before at run4KC).
  m = solver.model()
  # Get the original set of deals for which C knows.
  remDLSI = lObj.getIndices(lObj.getTruePropsPrefixedBy(m, 'd'))
  # Documenting the solution
  f= open(outFName, 'a')
  f.write('ann1 Indices : ' + str(ann1I) + '\n')
  f.write('ann2 Indices : ' + str(ann2I) + '\n\n')
  f.write('deals (after ann1;ann2) : \n' + str(remDLSI) + '\n\n')
  f.write('Now for C\'s announcement(s), \n' )
  ann3L = []
  while remDLSI != [] and res == z3.sat:
    m = synth.model()
    dlsCP  = lObj.getTruePropsPrefixedBy(m, 'd')
    dlsCI = lObj.getIndices(dlsCP)
    dlsC = []
    for i in dlsCI:    dlsC.append( lObj.deals[i] )
    annCP = lObj.getTruePropsPrefixedBy(m, 'c')
    annCI = lObj.getIndices(annCP)
    annCI.sort()
    ann3L.append(annCI)
    f.write(str(nAnnC) + ') : ' + str(annCI)) # the current Announcement
    f.write('\n\t Deals : \n' + str(dlsC) +'\n\n')
    remDLSI = elimDLI(remDLSI, dlsCI)
    fml = Or(lObj.dealsBL(remDLSI))
    synth.add(fml)
    res = synth.check()
    nAnnC = nAnnC + 1
  f.close()
  return (ann1I, ann2I, ann3L)

################################################################
####  Keep making progress with B's announcements (upto cutoff)
################################################################
def altBAnn(lObj, fLst, aWidth, cutoff, outFName) :
  '''
  fLst consists of all the formulae obtained from either
  a) getSafety_Solver
  b) getStrongSafety_Solver
  '''
  nD = len(lObj.deals)
  aP = lObj.ann[a]
  bP = lObj.ann[b]
  cP = lObj.ann[c]
  # Since, we're currently looking at one shot protocols.
  aPass = And(aP[0])
  bPass = And(bP[0])
  cPass = And(cP[0])
  fa, fb, fc = getfmlABC()
  # The solver code initialization
  synth = z3.Solver()
  synth = addToSolver(synth, fLst, True)
  # First, restrict aWidth
  aWFml  = lObj.restrictWidth('a', aWidth)
  synth.add(aWFml)
  # The part relevant for informing C
  synth.push()
  nAnnB = 0
  # Add d_0
  synth.add(lObj.possibleDeals[0])
  # C passes
  synth.add(cPass)
  synth.add(fc)
  resb = synth.check()
  remHndsB = []
  resAnnI = [[],[],[]] # Store all resulting announcements
  if resb == z3.sat:
    ann1P =  lObj.getTruePropsPrefixedBy(m, 'b')
    ann1I = lObj.getIndices(ann1P)
    ann1I.sort()
    f1 = lObj.getAnnFml(a, 0, ann1I)
    ann1L = lObj.iL2AnnL(ann1I)
    synth.add(f1) # Fix first announcement
    resAnnI.append(ann1I)
  while remHndsB != [] and resb == z3.sat and nAnnB < cutoff:
    m = solver.model()
    ann2P = lObj.getTruePropsPrefixedBy(m, 'b')
    ann2I = lObj.getIndices(ann2P)
    ann2I.sort()    
    resAnnI[1].append(ann2I)
    newRemB = []
    for h in remHndsB:
      if not h in ann2I:
        newRemB.append(h)
    remHndsB = newRemB
    ann2L = lObj.iL2AnnL(ann2I)
    # ann2 found such that c learns
    # Get the original set of deals for which C knows.
    remDLSI = lObj.getIndices(lObj.getTruePropsPrefixedBy(m, 'd'))
    # Documenting the solution
    f= open(outFName, 'a')
    f.write('ann1 Indices : ' + str(ann1I) + '\n')
    f.write('ann2 Indices : ' + str(ann2I) + '\n\n')
    f.write('deals (after ann1;ann2) : \n' + str(remDLSI) + '\n\n')
    f.write('Now for C\'s announcement(s), \n' )
    ann3L = []
    # Checkpoint the choice of ann2
    synth.push()
    f2 = lObj.getAnnFml(b, 0, ann2I)
    synth.add(f2)
    # C's objective is to ensure that A,B learn.
    synth.add(fa)
    synth.add(fb)
    resc = synth.check()
    while remDLSI != [] and resc == z3.sat:
      m = synth.model()
      dlsCP  = lObj.getTruePropsPrefixedBy(m, 'd')
      dlsCI = lObj.getIndices(dlsCP)
      dlsC = []
      for i in dlsCI:    dlsC.append( lObj.deals[i] )
      annCP = lObj.getTruePropsPrefixedBy(m, 'c')
      annCI = lObj.getIndices(annCP)
      annCI.sort()
      ann3L.append(annCI)
      f.write(str(nAnnC) + ') : ' + str(annCI)) # the current Announcement
      f.write('\n\t Deals : \n' + str(dlsC) +'\n\n')
      remDLSI = elimDLI(remDLSI, dlsCI)
      fml = Or(lObj.dealsBL(remDLSI))
      synth.add(fml)
      resc = synth.check()
      nAnnC = nAnnC + 1
    resAnnI[2].append(ann3L)
    # Roll back to the choice of second announcement.
    synth.pop()
    # Obtain a new ann2 that ensures progress.
    a2fml = lObj.annBL('b', 0, remHndsB)
    synth.add(a2fml)
    resb = synth.check()
    nAnnB = nAnnB + 1
  f.close()
  return (resAnnI[0], resAnnI[1], resAnnI[2])

def writeAnnL(lObj, ann1I, ann2I, ann3L, fName):
  '''
  Write out the actual announcements in full form.
  '''
  f = open(fName, 'a')
  f.write('# A\'s announcement :\n')
  annA = lObj.iL2AnnL(annn1I)
  f.write(getAnnStr(annA)+'\n')
  f.write('# B\'s announcement :\n')
  annB = lObj.iL2AnnL(ann2I)
  f.write(getAnnStr(annB) + '\n')
  f.write('# C\'s announcements :\n')
  nC = 0
  for annCI in ann3L:
    f.write('# Announcement '+str(nC)+') : \n')
    annC = getAnnStr(annCI)
    f.write(getAnnStr(annC) + '\n')
    nC = nC + 1
  f.close()

def writeAnnBL(lObj, ann1I, resBC, fName):
  '''
  Write out the actual announcements in full form.
  '''
  f = open(fName, 'a')
  f.write('# A\'s announcement :\n')
  annA = lObj.iL2AnnL(annn1I)
  f.write(getAnnStr(annA)+'\n')
  i = 0
  ann2L = resBC[1]
  for ann2I in ann2L:
    f.write('# B\'s announcement :\n')
    annB = lObj.iL2AnnL(ann2I)
    f.write(getAnnStr(annB) + '\n')
    f.write('# C\'s announcements :\n')
    nC = 0
    ann3L = resBC[2][i]
    for annCI in ann3L:
      f.write('# Announcement '+str(nC)+') : \n')
      annC = getAnnStr(annCI)
      f.write(getAnnStr(annC) + '\n')
      nC = nC + 1
    i = i + 1
  f.close()

def getAnnStr(annL):
  resStr = '[\n'
  for disj in annL:
    resStr = resStr+'  '+str(disj)+',\n'
  resStr = resStr+']\n'
