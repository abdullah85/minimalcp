from strategy1 import *

a,b,c,e = 'a', 'b', 'c', 'e'
dealLst = [4,4,4,0];
agtLst  = ['a', 'b', 'c', 'e']
deck    = range(12)

infAgts = [a, b, c]
eaves   = e

d0 = ut.minDeal(dealLst, agtLst, deck)
s0 = cps.cpState(dealLst, agtLst, d0, infAgts, eaves)
