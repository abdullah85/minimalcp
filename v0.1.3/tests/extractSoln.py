from lk import *

solver, fLst = l4.safetySynthSolver(True)
sInfC = l4.rSInf4Agt('optimized/4-sInfC.txt')
solver.push()
solver.add(sInfC)
a5 = restrictWidth('a', 5)
solver.add(a5)
solver.add(l4.possibleDeals[0])

# not restricting b's width (consider the example)
solver.add(cPass) # indicating that c passes

res1 = solver.check()
if res1 == z3.sat:
  m = solver.model()
  ann1P = l4.getTruePropsPrefixedBy(m, 'a')
  ann2P = l4.getTruePropsPrefixedBy(m, 'b')
  ann1I = l4.getIndices(ann1P)
  ann2I = l4.getIndices(ann2P)
  ann1I.sort(), ann2I.sort()
  f1 = getAnnFml(a, 0, ann1I)
  f2 = getAnnFml(b, 0, ann2I)
  ann1L = l4.iL2AnnL(ann1I)
  ann2L = l4.iL2AnnL(ann2I)
  dList = extractDealsProps(And(f1, f2, cPass))
  dListI = l4.getIndices(dList)
  deals = []
  for i in dListI:
    deals.append(l4.deals[i])

sBL = []
def getBFml():
  sBL = l4.rSInf4Agt('optimized/4-sInfB.txt')
  return sBL

sAL = []
def getAFml():
  sAL = l4.rSInf4Agt('optimized/4-sInfA.txt')
  return sAL
