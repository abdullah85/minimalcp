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
  synth.add(aWFml)
  synth.add(lObj.possibleDeals[0])
  synth.add(fc)
  synth.add(cPass)
  ann1I, ann2I, deals = run2KC(lObj, synth)
  synth.pop() # Unroll the constraints for first announcement.
  f1 = lObj.getAnnFml('a', 0, ann1I)
  # Fix first announcement by A for the rest of the search.
  synth.add(f1)
  resAnn = []
  resAnn.append(ann1I)
  nAnnB = 0
  while nAnnB < bCutOff and deals != []: # deals == [] when synth is unsat
    outFName = fPrefix + str(nAnnB) + '.py'
    f= open(outFName, 'a')
    f.write('ann1 Indices : ' + str(ann1I) + '\n')
    f.write('ann2 Indices : ' + str(ann2I) + '\n\n')
    f2 = lObj.getAnnFml('b', 0, ann2I)
    synth.push()
    synth.add(f2)
    x, y, ann3IL = informABwSynth(lObj, synth, f, cCutOff)
    resAnnL.append(ann2I, ann3IL)
    fName = fPrefix + '-ann-' + str(nAnnB) + '.py'
    writeAnnL(lObj, ann1I, ann2I, ann3IL, fName)
    synth.pop()
    synth.add( Not(f2) ) # Block the above announcement by B
    # The following checks how else B could respond.
    synth.push()
    synth.add(fc)
    ann1I, ann2I, deals = run2KC(lObj, synth)
    synth.pop() # remove fc
    nAnnB = nAnnB + 1
  return resAnn

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
  f.write('deals (after ann1;ann2) : \n' + str(remDLSI) + '\n\n')
  f.write('Now for C\'s announcement(s), \n' )
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
    f.write(str(nAnnC) + ') : ' + str(annCI)) # the current Announcement
    f.write('\n\t Deals : \n' + str(dlsC) +'\n\n')
    newDLSI = []
    for idx in remDLSI:
      if idx not in dlsCI:
        newDLSI.append(idx)        
    remDLSI = newDLSI
    fml = Or(lObj.dealsBL(remDLSI))
    synth.add(fml)
    res = synth.check()
    nAnnC = nAnnC + 1
  f.close()
  return ann3L

def informAB(lObj, fLst, ann1I, ann2I, outFName, cCutOff) :
  '''
  fLst consists of all the formulae obtained from either
  a) getSafety_Solver + getFmlAB()
  b) getStrongSafety_Solver + getFmlAB()
  c) other formulae, blocking certain announcements.
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
  while remDLSI != [] and res == z3.sat and nAnnC < cCutOff:
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

def writeAnnL(lObj, ann1I, ann2I, ann3L, fName):
  '''
  Write out the actual announcements in full form.
  '''
  f = open(fName, 'a')
  f.write('# A\'s announcement :\n')
  annA = lObj.iL2AnnL(ann1I)
  f.write(getAnnStr(annA)+'\n')
  f.write('# B\'s announcement :\n')
  annB = lObj.iL2AnnL(ann2I)
  f.write(getAnnStr(annB) + '\n')
  f.write('# C\'s announcements :\n')
  nC = 0
  for annCI in ann3L:
    f.write('# Announcement '+str(nC)+') : \n')
    annCL = lObj.iL2AnnL(annCI)
    f.write(getAnnStr(annCL) + '\n')
    nC = nC + 1
  f.close()

def getAnnStr(annL):
  resStr = '[\n'
  for disj in annL:
    resStr = resStr+'  '+str(disj)+',\n'
  resStr = resStr+']\n'
  return resStr

################################################################
####    Buggy code follows ...
################################################################

################################################################
####  Keep making progress with B's announcements (upto cutoff)
################################################################
def allBAnn(lObj, fLst, fa, fb, fc, aWidth, cutoff, outFName) :
  '''
  fLst consists of all the formulae obtained from either
  a) getSafety_Solver
  b) getStrongSafety_Solver
  fa, fb, fc denote second order inf requirements for agents a,b,c
    (possibly obtained by $ fa, fb, fc = getfmlABC(lObj))
  '''
  nD = len(lObj.deals)
  # Since, we're currently looking at one shot protocols.
  cP = lObj.ann[c]
  cPass = And(cP[0])
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
  remHndsB = range(len(lObj.handList))
  resAnnI = [[],[],[]] # Store all resulting announcements
  if resb == z3.sat:
    m = synth.model()
    ann1P =  lObj.getTruePropsPrefixedBy(m, 'a')
    ann1I = lObj.getIndices(ann1P)
    ann1I.sort()
    f1 = lObj.getAnnFml(a, 0, ann1I)
    ann1L = lObj.iL2AnnL(ann1I)
    synth.add(f1) # Fix first announcement
    resAnnI[0].append(ann1I)
    f = open(outFName, 'a')
    f.write('# ann1 Indices : \n' + str(ann1I) + '\n')
    f.close()
  while remHndsB != [] and resb == z3.sat and nAnnB < cutoff:
    f = open(outFName, 'a')
    m = synth.model()
    ann2P = lObj.getTruePropsPrefixedBy(m, 'b')
    ann2I = lObj.getIndices(ann2P)
    ann2I.sort()    
    resAnnI[1].append(ann2I)
    newRemB = []
    for idx in remHndsB:
      if not idx in ann2I:
        newRemB.append(idx)
    remHndsB = newRemB
    ann2L = lObj.iL2AnnL(ann2I)
    # ann2 found such that c learns
    # Get the original set of deals for which C knows.
    remDLSI = lObj.getIndices(lObj.getTruePropsPrefixedBy(m, 'd'))
    deals = []
    for i in remDLSI: deals.append(lObj.deals[i])
    # Documenting the solution
    f.write('# ann2 Indices : \n' + str(ann2I) + '\n\n')
    f.write('# deals (after ann1;ann2) : \n' + str(deals) + '\n\n')
    f.write('# Now for C\'s announcement(s), \n' )
    ann3L = []
    # Roll back to revoke B's attempt to inform C which was successful.
    # and onto the part where C must now inform B as well as A.
    synth.pop()
    synth.push()
    f2 = lObj.getAnnFml(b, 0, ann2I)
    synth.add(f2)
    # C's objective is to ensure that A,B learn.
    synth.add(fa)
    synth.add(fb)
    resc = synth.check()
    nAnnC = 0
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
      f.write('# '+str(nAnnC) + ') : \n' + str(annCI) + '\n') # the current Announcement
      f.write('# Deals : \n' + str(dlsC) +'\n\n')
      newRem = []
      for idx in remDLSI:
        if idx not in dlsCI:
          newRem.append(idx)
      remDLSI = newRem
      fml = Or(lObj.dealsBL(remDLSI))
      synth.add(fml)
      resc = synth.check()
      nAnnC = nAnnC + 1
    # Roll back to undo C's search for informing A as well as B.
    synth.pop()    
    # The formulae needed to ensure ann2I is not repeated by B
    if remDLSI != []:
      synth.add(Not(And(lObj.getAnnFml('b', 0, ann2I))))
    # Note that the bad formula is added before push.
    synth.push()
    resAnnI[2].append(ann3L)
    # Obtain a new ann2 that ensures progress.
    bProgress = []
    for idx in remHndsB:
      bProgress.append(lObj.ann['b'][0][idx])
    synth.add(Or(bProgress))
    # Once again ensure that B's announcement guarantees 2nd order inf for C.
    synth.add(fc)
    resb = synth.check()
    nAnnB = nAnnB + 1
    f.close()
  return (resAnnI[0], resAnnI[1], resAnnI[2])

def writeAnnBL(lObj, ann1I, resBC, fName):
  '''
  Write out the actual announcements in full form.
  '''
  f = open(fName, 'a')
  f.write('# A\'s announcement :\n')
  annA = lObj.iL2AnnL(ann1I)
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
      annC = lObj.iL2AnnL(annCI)
      print getAnnStr(annC)
      f.write(getAnnStr(annC) + '\n')
      nC = nC + 1
    i = i + 1
  f.close()
