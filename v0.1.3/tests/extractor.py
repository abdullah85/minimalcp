from lk import *

################################################################
#  TO clean up, abstract
################################################################


# A possible target for 4 | 4 | 4.
# corresponds to the run
# ann1 = ('a', [[0, 1, 2, 3], [0, 1, 2, 5], [0, 1, 3, 5], [0, 2,  3,  5], [1, 2, 3,  5]])
# ann2 = ('b', [[4, 5, 6, 7], [3, 4, 7, 8], [2, 4, 8, 9], [1, 7, 10, 11], [0, 8, 9, 11]])
l4 = Leakage(4)
l4.initHands()
l4.initDeals()
l4.initAnn(1)
nD = len(l4.deals)

# Formulae for synthesizer.
# fLst [ 3 + 3 + nD + 3*24 + 1 + nD + nD + nD]
# where in order of apperance in fLst,
#
# a) 6 are relations that ensure Ke and Pe are compatible (kEaves)
#      And(And(Implies(Kea__0, Not(PeNa__0)), Implies(Not(PeNa__0), Kea__0)), ... Implies(Not(PeNa__11), Kea__11)))
#
# b) nD state that if d_i is true then the Pe that entail (pEaves)
#      Implies(d__0, And(Pea__0, Pea__1, ... , Pec_11))
#
# c) 3*24 of the form (pEWitnesses, why was a particular Pe set to true)
#      Implies(Pea__0, Or(d__0, ... , d_11549))
#
# d) 1 of the form  (safety)
#      And(Not(Kea__0), Not(Keb__0), Not(Kec__0), Not(Kea__1), ... , Not(Kec_11))
#
# e) nD of the form (deal2Ann) 
#      Implies(d__0, And(a0__0, b0__425, c0__494))
#
# f) nD of the form (ann2Deal)
#      Implies(And(a0__0, b0__425, c0__494), d__0)
#
# g) nD of the form (sInf)
#      Implies(d__0,  And(Not(d__1), ... , Not(d_29750)))
#

p1Indices = [0, 145, 709, 3250, 11652]
pDeals1   = []
for i in p1Indices:
  pDeals1.append(l4.possibleDeals[i])

pNDeals1 = []
for i in range(len(l4.deals)):
  if not i in p1Indices:
    pNDeals1.append(l4.possibleDeals[i])

pFml  = And(pDeals1)
pNFml = And(pNDeals1)

################################################################
####         (Safe) Solutions obtained
################################################################
# One round solutions
s1A = [0, 2, 6, 9, 10, 11, 17, 18, 21, 27, 46, 51, 68, 81, 82, 165, 174, 177, 180, 202, 232, 321]
s1B = [10, 78, 80, 124, 142, 150, 158, 235, 249, 261, 265, 270, 299, 302, 364, 366, 367, 385, 389, 417, 458, 490]
s1C = [349, 350, 362, 363, 395, 397, 398, 401, 405, 420, 429, 431, 438, 447, 463, 464, 471, 472, 482, 492, 493, 494]

s1annA = l4.iL2AnnL(s1A)
s1annB = l4.iL2AnnL(s1B)
s1annC = l4.iL2AnnL(s1C)

def getAnnFml(agt, rnd, annIL):
  '''
  Get an appropriate formula encoding the exact formula 
  to add to solver for the announcement consisting of disjuncts
  encoding by indices in annIL.
  '''
  notAnnL = []
  for i in range(len(l4.handList)):
    if not i in annIL:
      notAnnL.append(i)
  annProps = l4.iL2PropL(agt, rnd, annIL)
  notAnnProps = l4.iL2PropL(agt, rnd, notAnnL)
  annFL = []
  for p in annProps:
    annFL.append(p)
  for p in notAnnProps:
    annFL.append(Not(p))
  annFml   = And(annFL)
  return annFml

# Takes about 30 seconds. Switch of if not needed
da, ad = l4.deal2AnnAll(), l4.ann2Deals()

def restrictWidthRound(agt, rnd, w):
  pL = l4.ann[agt][rnd]
  fL = []
  for p in pL:
    fL.append(p)
  fL.append(w)
  fml = Or(AtMost(fL), And(pL)) 
  # Either all true (corresponding to pass) or width constraint enforced
  return fml

def restrictWidth(agt, w):
  '''
  Return a fml restricting the number of valid disjuncts in any announcement to w. 
  That is, the total number of disjuncts announced in any formula is at most w 
  (or pass which is equivalent to true). Hopefully, this aids in extracting the strategy. 
  '''
  resFml = []
  for i in range(l4.nRounds):
    fml = restrictWidthRound(agt, i, w)
    resFml.append(fml)
  return resFml

def restrictWidthAll(w):
  fL = []
  for agt in l4.agents:
    fL.append(restrictWidth(agt, w))
  return And(fL)

def extractDealsProps(fml):
  '''
  Obtain the set of deals enforced by fml as a set of propositions.
  Typically fml is an announcement or a sequence of announcements and
  we would like to obtain the set of deals satisfying them.
  '''
  solver = z3.Solver()
  solver.add(ad)
  solver.add(fml)
  dL  = []
  res = solver.check()
  if res == z3.sat:
    m  = solver.model()
    dL = l4.getTruePropsPrefixedBy(m, 'd')
    dL = l4.sortIndices(dL)
  return dL

def obtainSolns(synth, fixedFml, dList):
  '''
  fixedFml is usually ann
  '''
  synth.push()
  synth.add(fixedFml)
  synth.push()
  mLst = []
  i = 0
  res = z3.sat
  while i <len(dList) and res == z3.sat:
    d = dList[i]
    synth.push()
    synth.add(d)
    res = synth.check()
    if res == z3.sat:
      m = synth.model()                                   
      mLst.append(m)                                
    synth.pop()                                        
    i = i + 1         
  return mLst

def isFirstAnnTheSame(mLst):
  firstAnnSame = True
  i = 0
  while firstAnnSame and i < len(dL1):
    la = l4.getIndices(l4.getTruePropsPrefixedBy(m, a))
    la.sort()
    cEq1 = (la == s1A)
    firstAnnSame = firstAnnSame and cEq1
    i = i + 1
  return fistAnnSame

def getAnnBC(mLst):
  annL = []
  for i in range(len(mLst)):
    m = mLst[i]
    bP = l4.getIndices(l4.getTruePropsPrefixedBy(m, 'b'))
    cP = l4.getIndices(l4.getTruePropsPrefixedBy(m, 'c'))
    currAnnL = [bP, cP] #Note the order
    annL.append(currAnnL)
  return annL

def compAgtDeals4(fml, agt, rnd, iL):
  '''
  What does agt know for each hand indexed in iL with fml before
  '''
  agtDeals = []
  for i in iL:
    agtHand = l4.handList[i]
    agtHFml = getAnnFml(agt, rnd, [i])
    aD = extractDealsProps(And(fml, agtHFml))
    agtDeals.append(aD)
  return agtDeals

aP = l4.ann[a]
bP = l4.ann[b]
cP = l4.ann[c]

# Since, we're currently looking at one shot protocols.
aPass = And(aP[0])
bPass = And(bP[0])
cPass = And(cP[0])

# Given ann1 as above, what is B's uncertainty?
#
# Answer below, given as indices to the actual deals.

################################################################
#    ENd of clean up
################################################################

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
