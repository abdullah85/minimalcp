from lk import *

def getLkObj(i):
  lObj = Leakage(i)
  lObj.initHands()
  lObj.initDeals()
  lObj.initAnn(1)
  return lObj

def writeAgtFml(lObj, agt):
  '''
  Save sInfFml to optimized/i-sInfP.txt
  where i is the hand size while P is the agent.
  '''
  i = lObj.hSize
  aName = agt.upper()
  fName = 'optimized/' + str(i) + '-sInf' + aName + '.txt'
  fml = lObj.sInf4Agt(agt)
  expr = fml.sexpr()
  f = open(fName, 'w')
  f.write(expr)
  f.close()

def getAgtFml(lObj, agt):
  '''
  Obtain (or read) optimized formula from optimized/i-sInfP.txt
  '''
  i = lObj.hSize
  aName = agt.upper()
  fName = 'optimized/' + str(i) + '-sInf' + aName + '.txt'
  fml   = lObj.rSInf4Agt(fName)
  return fml

def getSafety_Solver(lObj):
  '''
  lObj   - the leakage object initialized appropriately.
  cFile  - file containing second order formula for C's knowledge.
  aWidth - the width of a's first announcement.
  '''
  solver, fLst = lObj.safetySynthSolver(True)
  return solver,fLst

def getStrongSafety_Solver(lObj):
  solver, fLst = getSafety_Solver(lObj)
  strongFml = lObj.eavesKNIgnorant()
  solver.add(strongFml)
  fLst.append(strongFml)
  return solver,fLst

def initSolver4KC(lObj, solver, cFile, aWidth):
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
    f1 = getAnnFml(a, 0, ann1I)
    f2 = getAnnFml(b, 0, ann2I)
    ann1L = lObj.iL2AnnL(ann1I)
    ann2L = lObj.iL2AnnL(ann2I)
    dList = extractDealsProps(And(f1, f2, cPass))
    dListI = lObj.getIndices(dList)
    for i in dListI:
      deals.append(lObj.deals[i])
  return (ann1I, ann2I, deals)

hashes = '################################################################'
################################################################
####    Onto the part where C informs A,B.
################################################################
def informAB(lObj, fLst, ann1I, ann2I, outFName) :
  fa = getAgtFml(lObj, 'a')
  fb = getAgtFml(lObj, 'b')
  # for obtaining C's announcements that indicate how he can inform others
  synth = z3.Solver()
  synth = addToSolver(synth, fLst, True)
  ann1F = lObj.getAnnFml(a, 0, ann1I)
  ann2F = lObj.getAnnFml(b, 0, ann2I)
  synth.add(ann1F, ann2F)
  synth.add(fa)
  synth.add(fb)
  res = synth.check()
  nAnnC = 0
  # Get the original set of deals for which C knows.
  if res !=  z3.sat:
    f= open(outFName, 'a')
    f.write(hashes)
    f.write('\nunsat\n')
    f.write(hashes)
    f.close()
    return
  remDLSI = lObj.getIndices(lObj.getTruePropsPrefixedBy(solver.model(), 'd'))
  # Documenting the solution
  f= open(outFName, 'a')
  f.write('ann1 Indices : ' + str(ann1I) + '\n')
  f.write('ann2 Indices : ' + str(ann2I) + '\n\n')
  f.write('deals (after ann1;ann2) : \n' + str(deals) + '\n\n')
  f.write('Now for C\'s announcement(s), \n' )
  while remDLSI != [] and res == z3.sat:
    m1 = synth.model()
    dlsCP  = lObj.getTruePropsPrefixedBy(m1, 'd')
    dlsCI = lObj.getIndices(dlsCP)
    dlsC = []
    for i in dlsCI:    dlsC.append( lObj.deals[i] )
    annCP = lObj.getTruePropsPrefixedBy(m1, 'c')
    annCI = lObj.getIndices(annCP)
    annCI.sort()
    f.write(str(nAnnC) + ') : ' + str(annCI)) # the current Announcement
    f.write('\n\t Deals : \n' + str(dlsC) +'\n\n')
    remDLSI = elimDLI(remDLSI, dlsCI)
    fml = Or(lObj.dealsBL(remDLSI))
    synth.add(fml)
    res = synth.check()
    nAnnC = nAnnC + 1
  f.close()
