import cpState as cps
import cpUtil as ut; 

deal = {'a' : [0, 1, 2, 3], 'b':[4, 5, 6, 7], 'c':[8,9] };
infAgts, eaves = ['a', 'b'],'c';
rus442 = cps.cpState([4, 4, 2], ['a','b', 'c'], deal, infAgts, eaves);

s0 = rus442.newState()
dList = s0.fml2Deals(cps.z3.And(True))
dList = ut.sortDeals(dList)

ann1L = [[0,1,2,3], [0,1,4,5], [0,2,6,7], [0,3,8,9], [0,4,6,8],\
         [0,5,7,9], [1,2,8,9], [1,3,6,7], [1,4,7,9], [1,5,6,8],\
         [2,3,4,5], [2,4,7,8], [2,5,6,9], [3,4,6,9], [3,5,7,8]]

f1 =  ut.ann2DealFml('a', ann1L)
f  = cps.z3.Not(f1)
dList1 = s0.fml2Deals(f)
dList1 = ut.sortDeals(dList1)

import pickle as pk
f = open('rcp442-Deals.txt', 'w')
pk.dump(dList, f)
f.close()

f= open('rcp442-Rest1.txt', 'w')
pk.dump(dList1, f)
f.close()
